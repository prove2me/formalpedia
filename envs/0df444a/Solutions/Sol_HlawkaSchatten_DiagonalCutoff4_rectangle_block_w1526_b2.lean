-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1526_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:04:08.913954+00:00
-- url     : https://prove2.me/submissions/69e39041-806b-4654-badf-da681e0b5558

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
theorem support_rectangle_w1526_s6_0 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1847531917/10000000000 : ℝ)*x 0 + (1357854383/2500000000 : ℝ)*x 1 + (1043662623/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1847531917/10000000000 : ℝ)^4549 ≤ (11312003007691/100000000000000 : ℝ)^3525 := by
    have hnat : (1847531917 : ℕ)^4549*100000000000000^3525 ≤ 11312003007691^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1847531917 10000000000 11312003007691 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1357854383/2500000000 : ℝ)^4549 ≤ (5686125285117/12500000000000 : ℝ)^3525 := by
    have hnat : (1357854383 : ℕ)^4549*12500000000000^3525 ≤ 5686125285117^3525*2500000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357854383 2500000000 5686125285117 12500000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043662623/2000000000 : ℝ)^4549 ≤ (43198994701851/100000000000000 : ℝ)^3525 := by
    have hnat : (1043662623 : ℕ)^4549*100000000000000^3525 ≤ 43198994701851^3525*2000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043662623 2000000000 43198994701851 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1847531917/10000000000 : ℝ), (1357854383/2500000000 : ℝ), (1043662623/2000000000 : ℝ)] ![(11312003007691/100000000000000 : ℝ), (5686125285117/12500000000000 : ℝ), (43198994701851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1847531917/10000000000 : ℝ)|^4549 ≤ (11312003007691/100000000000000 : ℝ)^3525
        have hw : |(-1847531917/10000000000 : ℝ)|=(1847531917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1357854383/2500000000 : ℝ)|^4549 ≤ (5686125285117/12500000000000 : ℝ)^3525
        have hw : |(1357854383/2500000000 : ℝ)|=(1357854383/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043662623/2000000000 : ℝ)|^4549 ≤ (43198994701851/100000000000000 : ℝ)^3525
        have hw : |(1043662623/2000000000 : ℝ)|=(1043662623/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1526_s6_1 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350799421/10000000000 : ℝ)*x 0 + (-978321347/5000000000 : ℝ)*x 1 + (2609157573/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350799421/10000000000 : ℝ)^4549 ≤ (44619557449203/100000000000000 : ℝ)^3525 := by
    have hnat : (5350799421 : ℕ)^4549*100000000000000^3525 ≤ 44619557449203^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350799421 10000000000 44619557449203 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (978321347/5000000000 : ℝ)^4549 ≤ (3045356534217/25000000000000 : ℝ)^3525 := by
    have hnat : (978321347 : ℕ)^4549*25000000000000^3525 ≤ 3045356534217^3525*5000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      978321347 5000000000 3045356534217 25000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609157573/5000000000 : ℝ)^4549 ≤ (43199016399379/100000000000000 : ℝ)^3525 := by
    have hnat : (2609157573 : ℕ)^4549*100000000000000^3525 ≤ 43199016399379^3525*5000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609157573 5000000000 43199016399379 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350799421/10000000000 : ℝ), (-978321347/5000000000 : ℝ), (2609157573/5000000000 : ℝ)] ![(44619557449203/100000000000000 : ℝ), (3045356534217/25000000000000 : ℝ), (43199016399379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350799421/10000000000 : ℝ)|^4549 ≤ (44619557449203/100000000000000 : ℝ)^3525
        have hw : |(5350799421/10000000000 : ℝ)|=(5350799421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-978321347/5000000000 : ℝ)|^4549 ≤ (3045356534217/25000000000000 : ℝ)^3525
        have hw : |(-978321347/5000000000 : ℝ)|=(978321347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609157573/5000000000 : ℝ)|^4549 ≤ (43199016399379/100000000000000 : ℝ)^3525
        have hw : |(2609157573/5000000000 : ℝ)|=(2609157573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1526_s6_2 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350800447/10000000000 : ℝ)*x 0 + (1043662359/2000000000 : ℝ)*x 1 + (-78265831/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350800447/10000000000 : ℝ)^4549 ≤ (44619568490263/100000000000000 : ℝ)^3525 := by
    have hnat : (5350800447 : ℕ)^4549*100000000000000^3525 ≤ 44619568490263^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350800447 10000000000 44619568490263 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043662359/2000000000 : ℝ)^4549 ≤ (43198980600061/100000000000000 : ℝ)^3525 := by
    have hnat : (1043662359 : ℕ)^4549*100000000000000^3525 ≤ 43198980600061^3525*2000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043662359 2000000000 43198980600061 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (78265831/400000000 : ℝ)^4549 ≤ (761340680643/6250000000000 : ℝ)^3525 := by
    have hnat : (78265831 : ℕ)^4549*6250000000000^3525 ≤ 761340680643^3525*400000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78265831 400000000 761340680643 6250000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350800447/10000000000 : ℝ), (1043662359/2000000000 : ℝ), (-78265831/400000000 : ℝ)] ![(44619568490263/100000000000000 : ℝ), (43198980600061/100000000000000 : ℝ), (761340680643/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350800447/10000000000 : ℝ)|^4549 ≤ (44619568490263/100000000000000 : ℝ)^3525
        have hw : |(5350800447/10000000000 : ℝ)|=(5350800447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043662359/2000000000 : ℝ)|^4549 ≤ (43198980600061/100000000000000 : ℝ)^3525
        have hw : |(1043662359/2000000000 : ℝ)|=(1043662359/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-78265831/400000000 : ℝ)|^4549 ≤ (761340680643/6250000000000 : ℝ)^3525
        have hw : |(-78265831/400000000 : ℝ)|=(78265831/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1526_s6_3 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4263292553/10000000000 : ℝ)*x 0 + (2012579171/5000000000 : ℝ)*x 1 + (4513159469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4263292553/10000000000 : ℝ)^4549 ≤ (33280313630951/100000000000000 : ℝ)^3525 := by
    have hnat : (4263292553 : ℕ)^4549*100000000000000^3525 ≤ 33280313630951^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4263292553 10000000000 33280313630951 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2012579171/5000000000 : ℝ)^4549 ≤ (30901091743131/100000000000000 : ℝ)^3525 := by
    have hnat : (2012579171 : ℕ)^4549*100000000000000^3525 ≤ 30901091743131^3525*5000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2012579171 5000000000 30901091743131 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4513159469/10000000000 : ℝ)^4549 ≤ (35818594617513/100000000000000 : ℝ)^3525 := by
    have hnat : (4513159469 : ℕ)^4549*100000000000000^3525 ≤ 35818594617513^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4513159469 10000000000 35818594617513 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4263292553/10000000000 : ℝ), (2012579171/5000000000 : ℝ), (4513159469/10000000000 : ℝ)] ![(33280313630951/100000000000000 : ℝ), (30901091743131/100000000000000 : ℝ), (35818594617513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4263292553/10000000000 : ℝ)|^4549 ≤ (33280313630951/100000000000000 : ℝ)^3525
        have hw : |(4263292553/10000000000 : ℝ)|=(4263292553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2012579171/5000000000 : ℝ)|^4549 ≤ (30901091743131/100000000000000 : ℝ)^3525
        have hw : |(2012579171/5000000000 : ℝ)|=(2012579171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4513159469/10000000000 : ℝ)|^4549 ≤ (35818594617513/100000000000000 : ℝ)^3525
        have hw : |(4513159469/10000000000 : ℝ)|=(4513159469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1526_s6_4 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-230945101/1250000000 : ℝ)*x 0 + (5219413687/10000000000 : ℝ)*x 1 + (1086061699/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (230945101/1250000000 : ℝ)^4549 ≤ (1131223128773/10000000000000 : ℝ)^3525 := by
    have hnat : (230945101 : ℕ)^4549*10000000000000^3525 ≤ 1131223128773^3525*1250000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      230945101 1250000000 1131223128773 10000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219413687/10000000000 : ℝ)^4549 ≤ (4321075266471/10000000000000 : ℝ)^3525 := by
    have hnat : (5219413687 : ℕ)^4549*10000000000000^3525 ≤ 4321075266471^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219413687 10000000000 4321075266471 10000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1086061699/2000000000 : ℝ)^4549 ≤ (22738508017403/50000000000000 : ℝ)^3525 := by
    have hnat : (1086061699 : ℕ)^4549*50000000000000^3525 ≤ 22738508017403^3525*2000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086061699 2000000000 22738508017403 50000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-230945101/1250000000 : ℝ), (5219413687/10000000000 : ℝ), (1086061699/2000000000 : ℝ)] ![(1131223128773/10000000000000 : ℝ), (4321075266471/10000000000000 : ℝ), (22738508017403/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-230945101/1250000000 : ℝ)|^4549 ≤ (1131223128773/10000000000000 : ℝ)^3525
        have hw : |(-230945101/1250000000 : ℝ)|=(230945101/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219413687/10000000000 : ℝ)|^4549 ≤ (4321075266471/10000000000000 : ℝ)^3525
        have hw : |(5219413687/10000000000 : ℝ)|=(5219413687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1086061699/2000000000 : ℝ)|^4549 ≤ (22738508017403/50000000000000 : ℝ)^3525
        have hw : |(1086061699/2000000000 : ℝ)|=(1086061699/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1526_s6_5 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647371229/5000000000 : ℝ)*x 0 + (-1744647867/10000000000 : ℝ)*x 1 + (1086061917/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647371229/5000000000 : ℝ)^4549 ≤ (44017233734581/100000000000000 : ℝ)^3525 := by
    have hnat : (2647371229 : ℕ)^4549*100000000000000^3525 ≤ 44017233734581^3525*5000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647371229 5000000000 44017233734581 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1744647867/10000000000 : ℝ)^4549 ≤ (5252869219583/50000000000000 : ℝ)^3525 := by
    have hnat : (1744647867 : ℕ)^4549*50000000000000^3525 ≤ 5252869219583^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1744647867 10000000000 5252869219583 50000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1086061917/2000000000 : ℝ)^4549 ≤ (9095405562991/20000000000000 : ℝ)^3525 := by
    have hnat : (1086061917 : ℕ)^4549*20000000000000^3525 ≤ 9095405562991^3525*2000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086061917 2000000000 9095405562991 20000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647371229/5000000000 : ℝ), (-1744647867/10000000000 : ℝ), (1086061917/2000000000 : ℝ)] ![(44017233734581/100000000000000 : ℝ), (5252869219583/50000000000000 : ℝ), (9095405562991/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647371229/5000000000 : ℝ)|^4549 ≤ (44017233734581/100000000000000 : ℝ)^3525
        have hw : |(2647371229/5000000000 : ℝ)|=(2647371229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1744647867/10000000000 : ℝ)|^4549 ≤ (5252869219583/50000000000000 : ℝ)^3525
        have hw : |(-1744647867/10000000000 : ℝ)|=(1744647867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1086061917/2000000000 : ℝ)|^4549 ≤ (9095405562991/20000000000000 : ℝ)^3525
        have hw : |(1086061917/2000000000 : ℝ)|=(1086061917/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1526_s6_6 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647371459/5000000000 : ℝ)*x 0 + (5430309527/10000000000 : ℝ)*x 1 + (-1744647311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647371459/5000000000 : ℝ)^4549 ≤ (22008619334821/50000000000000 : ℝ)^3525 := by
    have hnat : (2647371459 : ℕ)^4549*50000000000000^3525 ≤ 22008619334821^3525*5000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647371459 5000000000 22008619334821 50000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5430309527/10000000000 : ℝ)^4549 ≤ (45477027188121/100000000000000 : ℝ)^3525 := by
    have hnat : (5430309527 : ℕ)^4549*100000000000000^3525 ≤ 45477027188121^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430309527 10000000000 45477027188121 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1744647311/10000000000 : ℝ)^4549 ≤ (10505734118503/100000000000000 : ℝ)^3525 := by
    have hnat : (1744647311 : ℕ)^4549*100000000000000^3525 ≤ 10505734118503^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1744647311 10000000000 10505734118503 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647371459/5000000000 : ℝ), (5430309527/10000000000 : ℝ), (-1744647311/10000000000 : ℝ)] ![(22008619334821/50000000000000 : ℝ), (45477027188121/100000000000000 : ℝ), (10505734118503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647371459/5000000000 : ℝ)|^4549 ≤ (22008619334821/50000000000000 : ℝ)^3525
        have hw : |(2647371459/5000000000 : ℝ)|=(2647371459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5430309527/10000000000 : ℝ)|^4549 ≤ (45477027188121/100000000000000 : ℝ)^3525
        have hw : |(5430309527/10000000000 : ℝ)|=(5430309527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1744647311/10000000000 : ℝ)|^4549 ≤ (10505734118503/100000000000000 : ℝ)^3525
        have hw : |(-1744647311/10000000000 : ℝ)|=(1744647311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1526_s6_7 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (426336267/1000000000 : ℝ)*x 0 + (451063781/1000000000 : ℝ)*x 1 + (4027693493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (426336267/1000000000 : ℝ)^4549 ≤ (33281019986651/100000000000000 : ℝ)^3525 := by
    have hnat : (426336267 : ℕ)^4549*100000000000000^3525 ≤ 33281019986651^3525*1000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426336267 1000000000 33281019986651 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (451063781/1000000000 : ℝ)^4549 ≤ (715855397757/2000000000000 : ℝ)^3525 := by
    have hnat : (451063781 : ℕ)^4549*2000000000000^3525 ≤ 715855397757^3525*1000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451063781 1000000000 715855397757 2000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4027693493/10000000000 : ℝ)^4549 ≤ (30926210099847/100000000000000 : ℝ)^3525 := by
    have hnat : (4027693493 : ℕ)^4549*100000000000000^3525 ≤ 30926210099847^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4027693493 10000000000 30926210099847 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(426336267/1000000000 : ℝ), (451063781/1000000000 : ℝ), (4027693493/10000000000 : ℝ)] ![(33281019986651/100000000000000 : ℝ), (715855397757/2000000000000 : ℝ), (30926210099847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(426336267/1000000000 : ℝ)|^4549 ≤ (33281019986651/100000000000000 : ℝ)^3525
        have hw : |(426336267/1000000000 : ℝ)|=(426336267/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(451063781/1000000000 : ℝ)|^4549 ≤ (715855397757/2000000000000 : ℝ)^3525
        have hw : |(451063781/1000000000 : ℝ)|=(451063781/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4027693493/10000000000 : ℝ)|^4549 ≤ (30926210099847/100000000000000 : ℝ)^3525
        have hw : |(4027693493/10000000000 : ℝ)|=(4027693493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1526_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164498657/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1371/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (10969/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15483/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1371/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1371/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1371/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1371/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1371/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1371/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1371/12500 : ℝ) ^ (4547/1024 : ℝ) ≤ (2733527205687/50000000000000000 : ℝ) := by
    have hpowers : (1371/12500 : ℝ)^4547 ≤ (2733527205687/50000000000000000 : ℝ)^1024 := by
      have hnat : (1371 : ℕ)^4547*50000000000000000^1024 ≤ 2733527205687^1024*12500^4547 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1371 12500 2733527205687 50000000000000000 4547 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1371/12500 : ℝ)) (X := (2733527205687/50000000000000000 : ℝ)) (by norm_num) (by norm_num) 4547 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3871/25000 : ℝ) ^ (4547/1024 : ℝ) ≤ (2527744331051979/10000000000000000000 : ℝ) := by
    have hpowers : (3871/25000 : ℝ)^4547 ≤ (2527744331051979/10000000000000000000 : ℝ)^1024 := by
      have hnat : (3871 : ℕ)^4547*10000000000000000000^1024 ≤ 2527744331051979^1024*25000^4547 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3871 25000 2527744331051979 10000000000000000000 4547 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3871/25000 : ℝ)) (X := (2527744331051979/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4547 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002733527205687/25000000000000000 : ℝ) ≤ (1000024622945231/1000000000000000 : ℝ) ^ (4547/1024 : ℝ) := by
    have hpowers : (25002733527205687/25000000000000000 : ℝ)^1024 ≤ (1000024622945231/1000000000000000 : ℝ)^4547 := by
      have hnat : (25002733527205687 : ℕ)^1024*1000000000000000^4547 ≤ 1000024622945231^4547*25000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002733527205687 25000000000000000 1000024622945231 1000000000000000 1024 4547 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000024622945231/1000000000000000 : ℝ)) (X := (25002733527205687/25000000000000000 : ℝ)) (by norm_num) 4547 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10003074449772189379/10000000000000000000 : ℝ) ≤ (10000692294187029/10000000000000000 : ℝ) ^ (4547/1024 : ℝ) := by
    have hpowers : (10003074449772189379/10000000000000000000 : ℝ)^1024 ≤ (10000692294187029/10000000000000000 : ℝ)^4547 := by
      have hnat : (10003074449772189379 : ℕ)^1024*10000000000000000^4547 ≤ 10000692294187029^4547*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003074449772189379 10000000000000000000 10000692294187029 10000000000000000 1024 4547 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000692294187029/10000000000000000 : ℝ)) (X := (10003074449772189379/10000000000000000000 : ℝ)) (by norm_num) 4547 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5002527744331051979/5000000000000000000 : ℝ) ≤ (2500284589730437/2500000000000000 : ℝ) ^ (4547/1024 : ℝ) := by
    have hpowers : (5002527744331051979/5000000000000000000 : ℝ)^1024 ≤ (2500284589730437/2500000000000000 : ℝ)^4547 := by
      have hnat : (5002527744331051979 : ℕ)^1024*2500000000000000^4547 ≤ 2500284589730437^4547*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002527744331051979 5000000000000000000 2500284589730437 2500000000000000 1024 4547 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500284589730437/2500000000000000 : ℝ)) (X := (5002527744331051979/5000000000000000000 : ℝ)) (by norm_num) 4547 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2733527205687/50000000000000000 : ℝ) ≤ ((5643915887023229497/5645000000000000000 : ℝ)+2*(446064734719/451600000000000 : ℝ)*(1371/12500 : ℝ))^(4547/1024 : ℝ) := by
    rw [show (5643915887023229497/5645000000000000000 : ℝ)+2*(446064734719/451600000000000 : ℝ)*(1371/12500 : ℝ)=(1000024622945231/1000000000000000 : ℝ) by norm_num, show 1+2*(2733527205687/50000000000000000 : ℝ)=(25002733527205687/25000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2527744331051979/10000000000000000000 : ℝ)+(2733527205687/50000000000000000 : ℝ) ≤ ((5643915887023229497/5645000000000000000 : ℝ)+(446064734719/451600000000000 : ℝ)*((3871/25000 : ℝ)+(1371/12500 : ℝ)))^(4547/1024 : ℝ) := by
    rw [show (5643915887023229497/5645000000000000000 : ℝ)+(446064734719/451600000000000 : ℝ)*((3871/25000 : ℝ)+(1371/12500 : ℝ))=(10000692294187029/10000000000000000 : ℝ) by norm_num, show 1+(2527744331051979/10000000000000000000 : ℝ)+(2733527205687/50000000000000000 : ℝ)=(10003074449772189379/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2527744331051979/10000000000000000000 : ℝ) ≤ ((5643915887023229497/5645000000000000000 : ℝ)+2*(446064734719/451600000000000 : ℝ)*(3871/25000 : ℝ))^(4547/1024 : ℝ) := by
    rw [show (5643915887023229497/5645000000000000000 : ℝ)+2*(446064734719/451600000000000 : ℝ)*(3871/25000 : ℝ)=(2500284589730437/2500000000000000 : ℝ) by norm_num, show 1+2*(2527744331051979/10000000000000000000 : ℝ)=(5002527744331051979/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5643915887023229497/5645000000000000000 : ℝ)*(X 1 0+X 2 0)+(446064734719/451600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4547/1024 : ℝ)) (lo := (1371/12500 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (5643915887023229497/5645000000000000000 : ℝ)) (alpha := (446064734719/451600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5643915887023229497/5645000000000000000 : ℝ)*(X 0 1+X 2 1)+(446064734719/451600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4547/1024 : ℝ)) (lo := (1371/12500 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (5643915887023229497/5645000000000000000 : ℝ)) (alpha := (446064734719/451600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5643915887023229497/5645000000000000000 : ℝ)*(X 0 2+X 1 2)+(446064734719/451600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4547/1024 : ℝ)) (lo := (1371/12500 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (5643915887023229497/5645000000000000000 : ℝ)) (alpha := (446064734719/451600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1847531917/10000000000 : ℝ)*X 0 0+(1357854383/2500000000 : ℝ)*X 0 1+(1043662623/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350799421/10000000000 : ℝ)*X 1 0+(-978321347/5000000000 : ℝ)*X 1 1+(2609157573/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350800447/10000000000 : ℝ)*X 2 0+(1043662359/2000000000 : ℝ)*X 2 1+(-78265831/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4263292553/10000000000 : ℝ)*X 0 0+(2012579171/5000000000 : ℝ)*X 0 1+(4513159469/10000000000 : ℝ)*X 0 2+(4263292553/10000000000 : ℝ)*X 1 0+(2012579171/5000000000 : ℝ)*X 1 1+(4513159469/10000000000 : ℝ)*X 1 2+(4263292553/10000000000 : ℝ)*X 2 0+(2012579171/5000000000 : ℝ)*X 2 1+(4513159469/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-230945101/1250000000 : ℝ)*X 0 0+(5219413687/10000000000 : ℝ)*X 0 1+(1086061699/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647371229/5000000000 : ℝ)*X 1 0+(-1744647867/10000000000 : ℝ)*X 1 1+(1086061917/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647371459/5000000000 : ℝ)*X 2 0+(5430309527/10000000000 : ℝ)*X 2 1+(-1744647311/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((426336267/1000000000 : ℝ)*X 0 0+(451063781/1000000000 : ℝ)*X 0 1+(4027693493/10000000000 : ℝ)*X 0 2+(426336267/1000000000 : ℝ)*X 1 0+(451063781/1000000000 : ℝ)*X 1 1+(4027693493/10000000000 : ℝ)*X 1 2+(426336267/1000000000 : ℝ)*X 2 0+(451063781/1000000000 : ℝ)*X 2 1+(4027693493/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (736089318183430471424569407/141125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (350976139/25000000000000 : ℝ)*(base15) + (16931129/4000000000000 : ℝ)*(base29) + (215858787/50000000000000 : ℝ)*(upper2) + (26138571/100000000000000 : ℝ)*(upper4) + (95555589/10000000000000 : ℝ)*(lower5) + (168544208467671/5000000000000 : ℝ)*(major0) + (1685442296315823/50000000000000 : ℝ)*(major1) + (1685442296315823/50000000000000 : ℝ)*(major2) + (4692582316441177/100000000000000 : ℝ)*(sp0) + (938516097851679/20000000000000 : ℝ)*(sp1) + (1173135022664401/25000000000000 : ℝ)*(sp2) + (1024589933583051/50000000000000 : ℝ)*(sp3) + (41802505347/100000000000000 : ℝ)*(sp6) + (853474219/12500000000000 : ℝ)*(sp7) + (1024593347479927/50000000000000 : ℝ)*(f.failure) + (4692582316441177/100000000000000 : ℝ)*(f.sum) + (40338730170007/11290000000000000000000000000 : ℝ)*base65 + (172399027337643531/282250000000000000000000000000000 : ℝ)*base67 + (241970615045393531/282250000000000000000000000000000 : ℝ)*base69 + (373677515691787737/28225000000000000000000000000000 : ℝ)*base71 + (71205294901693/22580000000000000000000000000 : ℝ)*base74 + (275670456333556031/282250000000000000000000000000000 : ℝ)*base75 + (247474074003987263/28225000000000000000000000000000 : ℝ)*base78 + (659463254756693969/282250000000000000000000000000000 : ℝ)*base80 + (12626242123833/22580000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (75958039/5000000000000000000000 : ℝ)*base89 + (25958039/5000000000000000000000 : ℝ)*base91 + (25958039/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (430043296178005372302462279/141125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (401413/3125000000000 : ℝ)*(base15) + (316142007/100000000000000 : ℝ)*(lower1) + (305681909/100000000000000 : ℝ)*(lower2) + (193726611/100000000000000 : ℝ)*(upper3) + (37359569/100000000000000 : ℝ)*(lower4) + (5080551/50000000000000 : ℝ)*(upper5) + (1703079560036823/50000000000000 : ℝ)*(major0) + (1703079560036823/50000000000000 : ℝ)*(major1) + (1703079560036823/50000000000000 : ℝ)*(major2) + (2508525963/25000000000000 : ℝ)*(sp2) + (2370843893407927/50000000000000 : ℝ)*(sp4) + (2370843886985319/50000000000000 : ℝ)*(sp5) + (4741677752712003/100000000000000 : ℝ)*(sp6) + (517657587939099/25000000000000 : ℝ)*(sp7) + (517657587939099/25000000000000 : ℝ)*(f.failure) + (2370843893407927/50000000000000 : ℝ)*(f.sum) + (127994432923783/11290000000000000000000000000 : ℝ)*base66 + (2280904023099019469/282250000000000000000000000000000 : ℝ)*base68 + (493607973224019469/282250000000000000000000000000000 : ℝ)*base70 + (1050226019477519469/282250000000000000000000000000000 : ℝ)*base72 + (30030158244323/11290000000000000000000000000 : ℝ)*base74 + (2769413855599019469/282250000000000000000000000000000 : ℝ)*base76 + (2585642986184019469/282250000000000000000000000000000 : ℝ)*base78 + (1323651235290769469/282250000000000000000000000000000 : ℝ)*base80 + (168986254334187/11290000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (33290043/2500000000000000000000 : ℝ)*base89 + (33290043/2500000000000000000000 : ℝ)*base91 + (33290043/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1526_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164498657/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1371/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10969/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1526_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1526_box_0 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-818189331/5000000000 : ℝ)*x 0 + (540131951/1000000000 : ℝ)*x 1 + (5401319307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (818189331/5000000000 : ℝ)^4549 ≤ (2418019785909/25000000000000 : ℝ)^3525 := by
    have hnat : (818189331 : ℕ)^4549*25000000000000^3525 ≤ 2418019785909^3525*5000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      818189331 5000000000 2418019785909 25000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540131951/1000000000 : ℝ)^4549 ≤ (4516396151433/10000000000000 : ℝ)^3525 := by
    have hnat : (540131951 : ℕ)^4549*10000000000000^3525 ≤ 4516396151433^3525*1000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540131951 1000000000 4516396151433 10000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5401319307/10000000000 : ℝ)^4549 ≤ (45163959323821/100000000000000 : ℝ)^3525 := by
    have hnat : (5401319307 : ℕ)^4549*100000000000000^3525 ≤ 45163959323821^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401319307 10000000000 45163959323821 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-818189331/5000000000 : ℝ), (540131951/1000000000 : ℝ), (5401319307/10000000000 : ℝ)] ![(2418019785909/25000000000000 : ℝ), (4516396151433/10000000000000 : ℝ), (45163959323821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-818189331/5000000000 : ℝ)|^4549 ≤ (2418019785909/25000000000000 : ℝ)^3525
        have hw : |(-818189331/5000000000 : ℝ)|=(818189331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540131951/1000000000 : ℝ)|^4549 ≤ (4516396151433/10000000000000 : ℝ)^3525
        have hw : |(540131951/1000000000 : ℝ)|=(540131951/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5401319307/10000000000 : ℝ)|^4549 ≤ (45163959323821/100000000000000 : ℝ)^3525
        have hw : |(5401319307/10000000000 : ℝ)|=(5401319307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1526_box_1 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5270935873/10000000000 : ℝ)*x 0 + (-908672723/5000000000 : ℝ)*x 1 + (1350329611/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5270935873/10000000000 : ℝ)^4549 ≤ (10940498571117/25000000000000 : ℝ)^3525 := by
    have hnat : (5270935873 : ℕ)^4549*25000000000000^3525 ≤ 10940498571117^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5270935873 10000000000 10940498571117 25000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (908672723/5000000000 : ℝ)^4549 ≤ (11074055688477/100000000000000 : ℝ)^3525 := by
    have hnat : (908672723 : ℕ)^4549*100000000000000^3525 ≤ 11074055688477^3525*5000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      908672723 5000000000 11074055688477 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1350329611/2500000000 : ℝ)^4549 ≤ (45163950011461/100000000000000 : ℝ)^3525 := by
    have hnat : (1350329611 : ℕ)^4549*100000000000000^3525 ≤ 45163950011461^3525*2500000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350329611 2500000000 45163950011461 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5270935873/10000000000 : ℝ), (-908672723/5000000000 : ℝ), (1350329611/2500000000 : ℝ)] ![(10940498571117/25000000000000 : ℝ), (11074055688477/100000000000000 : ℝ), (45163950011461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5270935873/10000000000 : ℝ)|^4549 ≤ (10940498571117/25000000000000 : ℝ)^3525
        have hw : |(5270935873/10000000000 : ℝ)|=(5270935873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-908672723/5000000000 : ℝ)|^4549 ≤ (11074055688477/100000000000000 : ℝ)^3525
        have hw : |(-908672723/5000000000 : ℝ)|=(908672723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1350329611/2500000000 : ℝ)|^4549 ≤ (45163950011461/100000000000000 : ℝ)^3525
        have hw : |(1350329611/2500000000 : ℝ)|=(1350329611/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1526_box_2 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (527093543/1000000000 : ℝ)*x 0 + (270065939/500000000 : ℝ)*x 1 + (-1817345589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527093543/1000000000 : ℝ)^4549 ≤ (43761989538007/100000000000000 : ℝ)^3525 := by
    have hnat : (527093543 : ℕ)^4549*100000000000000^3525 ≤ 43761989538007^3525*1000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527093543 1000000000 43761989538007 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270065939/500000000 : ℝ)^4549 ≤ (45163953637131/100000000000000 : ℝ)^3525 := by
    have hnat : (270065939 : ℕ)^4549*100000000000000^3525 ≤ 45163953637131^3525*500000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270065939 500000000 45163953637131 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1817345589/10000000000 : ℝ)^4549 ≤ (1384257101623/12500000000000 : ℝ)^3525 := by
    have hnat : (1817345589 : ℕ)^4549*12500000000000^3525 ≤ 1384257101623^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1817345589 10000000000 1384257101623 12500000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527093543/1000000000 : ℝ), (270065939/500000000 : ℝ), (-1817345589/10000000000 : ℝ)] ![(43761989538007/100000000000000 : ℝ), (45163953637131/100000000000000 : ℝ), (1384257101623/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527093543/1000000000 : ℝ)|^4549 ≤ (43761989538007/100000000000000 : ℝ)^3525
        have hw : |(527093543/1000000000 : ℝ)|=(527093543/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270065939/500000000 : ℝ)|^4549 ≤ (45163953637131/100000000000000 : ℝ)^3525
        have hw : |(270065939/500000000 : ℝ)|=(270065939/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1817345589/10000000000 : ℝ)|^4549 ≤ (1384257101623/12500000000000 : ℝ)^3525
        have hw : |(-1817345589/10000000000 : ℝ)|=(1817345589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1526_box_3 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2232868987/5000000000 : ℝ)*x 0 + (521121137/1250000000 : ℝ)*x 1 + (4168969397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2232868987/5000000000 : ℝ)^4549 ≤ (35333646871591/100000000000000 : ℝ)^3525 := by
    have hnat : (2232868987 : ℕ)^4549*100000000000000^3525 ≤ 35333646871591^3525*5000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2232868987 5000000000 35333646871591 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521121137/1250000000 : ℝ)^4549 ≤ (32333175049043/100000000000000 : ℝ)^3525 := by
    have hnat : (521121137 : ℕ)^4549*100000000000000^3525 ≤ 32333175049043^3525*1250000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521121137 1250000000 32333175049043 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4168969397/10000000000 : ℝ)^4549 ≤ (32333178061653/100000000000000 : ℝ)^3525 := by
    have hnat : (4168969397 : ℕ)^4549*100000000000000^3525 ≤ 32333178061653^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4168969397 10000000000 32333178061653 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2232868987/5000000000 : ℝ), (521121137/1250000000 : ℝ), (4168969397/10000000000 : ℝ)] ![(35333646871591/100000000000000 : ℝ), (32333175049043/100000000000000 : ℝ), (32333178061653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2232868987/5000000000 : ℝ)|^4549 ≤ (35333646871591/100000000000000 : ℝ)^3525
        have hw : |(2232868987/5000000000 : ℝ)|=(2232868987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521121137/1250000000 : ℝ)|^4549 ≤ (32333175049043/100000000000000 : ℝ)^3525
        have hw : |(521121137/1250000000 : ℝ)|=(521121137/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4168969397/10000000000 : ℝ)|^4549 ≤ (32333178061653/100000000000000 : ℝ)^3525
        have hw : |(4168969397/10000000000 : ℝ)|=(4168969397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1526_box_4 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2064114377/10000000000 : ℝ)*x 0 + (5244051859/10000000000 : ℝ)*x 1 + (1048810301/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2064114377/10000000000 : ℝ)^4549 ≤ (1631459731463/12500000000000 : ℝ)^3525 := by
    have hnat : (2064114377 : ℕ)^4549*12500000000000^3525 ≤ 1631459731463^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064114377 10000000000 1631459731463 12500000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244051859/10000000000 : ℝ)^4549 ≤ (43474162960703/100000000000000 : ℝ)^3525 := by
    have hnat : (5244051859 : ℕ)^4549*100000000000000^3525 ≤ 43474162960703^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244051859 10000000000 43474162960703 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048810301/2000000000 : ℝ)^4549 ≤ (869483183469/2000000000000 : ℝ)^3525 := by
    have hnat : (1048810301 : ℕ)^4549*2000000000000^3525 ≤ 869483183469^3525*2000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048810301 2000000000 869483183469 2000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2064114377/10000000000 : ℝ), (5244051859/10000000000 : ℝ), (1048810301/2000000000 : ℝ)] ![(1631459731463/12500000000000 : ℝ), (43474162960703/100000000000000 : ℝ), (869483183469/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2064114377/10000000000 : ℝ)|^4549 ≤ (1631459731463/12500000000000 : ℝ)^3525
        have hw : |(-2064114377/10000000000 : ℝ)|=(2064114377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244051859/10000000000 : ℝ)|^4549 ≤ (43474162960703/100000000000000 : ℝ)^3525
        have hw : |(5244051859/10000000000 : ℝ)|=(5244051859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048810301/2000000000 : ℝ)|^4549 ≤ (869483183469/2000000000000 : ℝ)^3525
        have hw : |(1048810301/2000000000 : ℝ)|=(1048810301/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1526_box_5 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1076062157/2000000000 : ℝ)*x 0 + (-941211743/5000000000 : ℝ)*x 1 + (5244051623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076062157/2000000000 : ℝ)^4549 ≤ (22468695596253/50000000000000 : ℝ)^3525 := by
    have hnat : (1076062157 : ℕ)^4549*50000000000000^3525 ≤ 22468695596253^3525*2000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076062157 2000000000 22468695596253 50000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (941211743/5000000000 : ℝ)^4549 ≤ (11588448357513/100000000000000 : ℝ)^3525 := by
    have hnat : (941211743 : ℕ)^4549*100000000000000^3525 ≤ 11588448357513^3525*5000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      941211743 5000000000 11588448357513 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244051623/10000000000 : ℝ)^4549 ≤ (10868540108967/25000000000000 : ℝ)^3525 := by
    have hnat : (5244051623 : ℕ)^4549*25000000000000^3525 ≤ 10868540108967^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244051623 10000000000 10868540108967 25000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1076062157/2000000000 : ℝ), (-941211743/5000000000 : ℝ), (5244051623/10000000000 : ℝ)] ![(22468695596253/50000000000000 : ℝ), (11588448357513/100000000000000 : ℝ), (10868540108967/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1076062157/2000000000 : ℝ)|^4549 ≤ (22468695596253/50000000000000 : ℝ)^3525
        have hw : |(1076062157/2000000000 : ℝ)|=(1076062157/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-941211743/5000000000 : ℝ)|^4549 ≤ (11588448357513/100000000000000 : ℝ)^3525
        have hw : |(-941211743/5000000000 : ℝ)|=(941211743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244051623/10000000000 : ℝ)|^4549 ≤ (10868540108967/25000000000000 : ℝ)^3525
        have hw : |(5244051623/10000000000 : ℝ)|=(5244051623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1526_box_6 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2690155139/5000000000 : ℝ)*x 0 + (5244051797/10000000000 : ℝ)*x 1 + (-1882423939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2690155139/5000000000 : ℝ)^4549 ≤ (44937385727819/100000000000000 : ℝ)^3525 := by
    have hnat : (2690155139 : ℕ)^4549*100000000000000^3525 ≤ 44937385727819^3525*5000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2690155139 5000000000 44937385727819 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244051797/10000000000 : ℝ)^4549 ≤ (43474162297399/100000000000000 : ℝ)^3525 := by
    have hnat : (5244051797 : ℕ)^4549*100000000000000^3525 ≤ 43474162297399^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244051797 10000000000 43474162297399 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1882423939/10000000000 : ℝ)^4549 ≤ (11588451956357/100000000000000 : ℝ)^3525 := by
    have hnat : (1882423939 : ℕ)^4549*100000000000000^3525 ≤ 11588451956357^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1882423939 10000000000 11588451956357 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2690155139/5000000000 : ℝ), (5244051797/10000000000 : ℝ), (-1882423939/10000000000 : ℝ)] ![(44937385727819/100000000000000 : ℝ), (43474162297399/100000000000000 : ℝ), (11588451956357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2690155139/5000000000 : ℝ)|^4549 ≤ (44937385727819/100000000000000 : ℝ)^3525
        have hw : |(2690155139/5000000000 : ℝ)|=(2690155139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244051797/10000000000 : ℝ)|^4549 ≤ (43474162297399/100000000000000 : ℝ)^3525
        have hw : |(5244051797/10000000000 : ℝ)|=(5244051797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1882423939/10000000000 : ℝ)|^4549 ≤ (11588451956357/100000000000000 : ℝ)^3525
        have hw : |(-1882423939/10000000000 : ℝ)|=(1882423939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1526_box_7 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4058369109/10000000000 : ℝ)*x 0 + (2186260711/5000000000 : ℝ)*x 1 + (1093130227/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4058369109/10000000000 : ℝ)^4549 ≤ (7807627130709/25000000000000 : ℝ)^3525 := by
    have hnat : (4058369109 : ℕ)^4549*25000000000000^3525 ≤ 7807627130709^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4058369109 10000000000 7807627130709 25000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2186260711/5000000000 : ℝ)^4549 ≤ (17192374171051/50000000000000 : ℝ)^3525 := by
    have hnat : (2186260711 : ℕ)^4549*50000000000000^3525 ≤ 17192374171051^3525*5000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186260711 5000000000 17192374171051 50000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1093130227/2500000000 : ℝ)^4549 ≤ (34384743125907/100000000000000 : ℝ)^3525 := by
    have hnat : (1093130227 : ℕ)^4549*100000000000000^3525 ≤ 34384743125907^3525*2500000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093130227 2500000000 34384743125907 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4058369109/10000000000 : ℝ), (2186260711/5000000000 : ℝ), (1093130227/2500000000 : ℝ)] ![(7807627130709/25000000000000 : ℝ), (17192374171051/50000000000000 : ℝ), (34384743125907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4058369109/10000000000 : ℝ)|^4549 ≤ (7807627130709/25000000000000 : ℝ)^3525
        have hw : |(4058369109/10000000000 : ℝ)|=(4058369109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2186260711/5000000000 : ℝ)|^4549 ≤ (17192374171051/50000000000000 : ℝ)^3525
        have hw : |(2186260711/5000000000 : ℝ)|=(2186260711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1093130227/2500000000 : ℝ)|^4549 ≤ (34384743125907/100000000000000 : ℝ)^3525
        have hw : |(1093130227/2500000000 : ℝ)|=(1093130227/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1526_box_8 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-3854789/19531250 : ℝ)*x 0 + (5133721543/10000000000 : ℝ)*x 1 + (338858101/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3854789/19531250 : ℝ)^4549 ≤ (769890905631/6250000000000 : ℝ)^3525 := by
    have hnat : (3854789 : ℕ)^4549*6250000000000^3525 ≤ 769890905631^3525*19531250^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3854789 19531250 769890905631 6250000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5133721543/10000000000 : ℝ)^4549 ≤ (10574356053831/25000000000000 : ℝ)^3525 := by
    have hnat : (5133721543 : ℕ)^4549*25000000000000^3525 ≤ 10574356053831^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5133721543 10000000000 10574356053831 25000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338858101/625000000 : ℝ)^4549 ≤ (45384321290237/100000000000000 : ℝ)^3525 := by
    have hnat : (338858101 : ℕ)^4549*100000000000000^3525 ≤ 45384321290237^3525*625000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338858101 625000000 45384321290237 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3854789/19531250 : ℝ), (5133721543/10000000000 : ℝ), (338858101/625000000 : ℝ)] ![(769890905631/6250000000000 : ℝ), (10574356053831/25000000000000 : ℝ), (45384321290237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3854789/19531250 : ℝ)|^4549 ≤ (769890905631/6250000000000 : ℝ)^3525
        have hw : |(-3854789/19531250 : ℝ)|=(3854789/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5133721543/10000000000 : ℝ)|^4549 ≤ (10574356053831/25000000000000 : ℝ)^3525
        have hw : |(5133721543/10000000000 : ℝ)|=(5133721543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338858101/625000000 : ℝ)|^4549 ≤ (45384321290237/100000000000000 : ℝ)^3525
        have hw : |(338858101/625000000 : ℝ)|=(338858101/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1526_box_9 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628367317/5000000000 : ℝ)*x 0 + (-1808656651/10000000000 : ℝ)*x 1 + (1084346011/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628367317/5000000000 : ℝ)^4549 ≤ (5451237087019/12500000000000 : ℝ)^3525 := by
    have hnat : (2628367317 : ℕ)^4549*12500000000000^3525 ≤ 5451237087019^3525*5000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628367317 5000000000 5451237087019 12500000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1808656651/10000000000 : ℝ)^4549 ≤ (5502888627737/50000000000000 : ℝ)^3525 := by
    have hnat : (1808656651 : ℕ)^4549*50000000000000^3525 ≤ 5502888627737^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1808656651 10000000000 5502888627737 50000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1084346011/2000000000 : ℝ)^4549 ≤ (2269216301627/5000000000000 : ℝ)^3525 := by
    have hnat : (1084346011 : ℕ)^4549*5000000000000^3525 ≤ 2269216301627^3525*2000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084346011 2000000000 2269216301627 5000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628367317/5000000000 : ℝ), (-1808656651/10000000000 : ℝ), (1084346011/2000000000 : ℝ)] ![(5451237087019/12500000000000 : ℝ), (5502888627737/50000000000000 : ℝ), (2269216301627/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628367317/5000000000 : ℝ)|^4549 ≤ (5451237087019/12500000000000 : ℝ)^3525
        have hw : |(2628367317/5000000000 : ℝ)|=(2628367317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1808656651/10000000000 : ℝ)|^4549 ≤ (5502888627737/50000000000000 : ℝ)^3525
        have hw : |(-1808656651/10000000000 : ℝ)|=(1808656651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1084346011/2000000000 : ℝ)|^4549 ≤ (2269216301627/5000000000000 : ℝ)^3525
        have hw : |(1084346011/2000000000 : ℝ)|=(1084346011/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1526_box_10 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628367273/5000000000 : ℝ)*x 0 + (2710864927/5000000000 : ℝ)*x 1 + (-226082131/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628367273/5000000000 : ℝ)^4549 ≤ (43609895754027/100000000000000 : ℝ)^3525 := by
    have hnat : (2628367273 : ℕ)^4549*100000000000000^3525 ≤ 43609895754027^3525*5000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628367273 5000000000 43609895754027 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2710864927/5000000000 : ℝ)^4549 ≤ (9076864772247/20000000000000 : ℝ)^3525 := by
    have hnat : (2710864927 : ℕ)^4549*20000000000000^3525 ≤ 9076864772247^3525*5000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710864927 5000000000 9076864772247 20000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (226082131/1250000000 : ℝ)^4549 ≤ (11005780373013/100000000000000 : ℝ)^3525 := by
    have hnat : (226082131 : ℕ)^4549*100000000000000^3525 ≤ 11005780373013^3525*1250000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226082131 1250000000 11005780373013 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628367273/5000000000 : ℝ), (2710864927/5000000000 : ℝ), (-226082131/1250000000 : ℝ)] ![(43609895754027/100000000000000 : ℝ), (9076864772247/20000000000000 : ℝ), (11005780373013/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628367273/5000000000 : ℝ)|^4549 ≤ (43609895754027/100000000000000 : ℝ)^3525
        have hw : |(2628367273/5000000000 : ℝ)|=(2628367273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2710864927/5000000000 : ℝ)|^4549 ≤ (9076864772247/20000000000000 : ℝ)^3525
        have hw : |(2710864927/5000000000 : ℝ)|=(2710864927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-226082131/1250000000 : ℝ)|^4549 ≤ (11005780373013/100000000000000 : ℝ)^3525
        have hw : |(-226082131/1250000000 : ℝ)|=(226082131/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1526_box_11 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2258728179/5000000000 : ℝ)*x 0 + (828503977/2000000000 : ℝ)*x 1 + (4142519369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2258728179/5000000000 : ℝ)^4549 ≤ (3586260942969/10000000000000 : ℝ)^3525 := by
    have hnat : (2258728179 : ℕ)^4549*10000000000000^3525 ≤ 3586260942969^3525*5000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2258728179 5000000000 3586260942969 10000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (828503977/2000000000 : ℝ)^4549 ≤ (32068697857/100000000000 : ℝ)^3525 := by
    have hnat : (828503977 : ℕ)^4549*100000000000^3525 ≤ 32068697857^3525*2000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      828503977 2000000000 32068697857 100000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4142519369/10000000000 : ℝ)^4549 ≤ (6413738540413/20000000000000 : ℝ)^3525 := by
    have hnat : (4142519369 : ℕ)^4549*20000000000000^3525 ≤ 6413738540413^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4142519369 10000000000 6413738540413 20000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2258728179/5000000000 : ℝ), (828503977/2000000000 : ℝ), (4142519369/10000000000 : ℝ)] ![(3586260942969/10000000000000 : ℝ), (32068697857/100000000000 : ℝ), (6413738540413/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2258728179/5000000000 : ℝ)|^4549 ≤ (3586260942969/10000000000000 : ℝ)^3525
        have hw : |(2258728179/5000000000 : ℝ)|=(2258728179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(828503977/2000000000 : ℝ)|^4549 ≤ (32068697857/100000000000 : ℝ)^3525
        have hw : |(828503977/2000000000 : ℝ)|=(828503977/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4142519369/10000000000 : ℝ)|^4549 ≤ (6413738540413/20000000000000 : ℝ)^3525
        have hw : |(4142519369/10000000000 : ℝ)|=(4142519369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1526_box_12 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1726717383/10000000000 : ℝ)*x 0 + (1377037433/2500000000 : ℝ)*x 1 + (130725381/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1726717383/10000000000 : ℝ)^4549 ≤ (1036660957043/10000000000000 : ℝ)^3525 := by
    have hnat : (1726717383 : ℕ)^4549*10000000000000^3525 ≤ 1036660957043^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1726717383 10000000000 1036660957043 10000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1377037433/2500000000 : ℝ)^4549 ≤ (23160014501149/50000000000000 : ℝ)^3525 := by
    have hnat : (1377037433 : ℕ)^4549*50000000000000^3525 ≤ 23160014501149^3525*2500000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1377037433 2500000000 23160014501149 50000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130725381/250000000 : ℝ)^4549 ≤ (43313361412129/100000000000000 : ℝ)^3525 := by
    have hnat : (130725381 : ℕ)^4549*100000000000000^3525 ≤ 43313361412129^3525*250000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130725381 250000000 43313361412129 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1726717383/10000000000 : ℝ), (1377037433/2500000000 : ℝ), (130725381/250000000 : ℝ)] ![(1036660957043/10000000000000 : ℝ), (23160014501149/50000000000000 : ℝ), (43313361412129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1726717383/10000000000 : ℝ)|^4549 ≤ (1036660957043/10000000000000 : ℝ)^3525
        have hw : |(-1726717383/10000000000 : ℝ)|=(1726717383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1377037433/2500000000 : ℝ)|^4549 ≤ (23160014501149/50000000000000 : ℝ)^3525
        have hw : |(1377037433/2500000000 : ℝ)|=(1377037433/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(130725381/250000000 : ℝ)|^4549 ≤ (43313361412129/100000000000000 : ℝ)^3525
        have hw : |(130725381/250000000 : ℝ)|=(130725381/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1526_box_13 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1078153507/2000000000 : ℝ)*x 0 + (-1888468887/10000000000 : ℝ)*x 1 + (5229016131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078153507/2000000000 : ℝ)^4549 ≤ (11262532702611/25000000000000 : ℝ)^3525 := by
    have hnat : (1078153507 : ℕ)^4549*25000000000000^3525 ≤ 11262532702611^3525*2000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078153507 2000000000 11262532702611 25000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1888468887/10000000000 : ℝ)^4549 ≤ (11636498233181/100000000000000 : ℝ)^3525 := by
    have hnat : (1888468887 : ℕ)^4549*100000000000000^3525 ≤ 11636498233181^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1888468887 10000000000 11636498233181 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5229016131/10000000000 : ℝ)^4549 ≤ (8662674187301/20000000000000 : ℝ)^3525 := by
    have hnat : (5229016131 : ℕ)^4549*20000000000000^3525 ≤ 8662674187301^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229016131 10000000000 8662674187301 20000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1078153507/2000000000 : ℝ), (-1888468887/10000000000 : ℝ), (5229016131/10000000000 : ℝ)] ![(11262532702611/25000000000000 : ℝ), (11636498233181/100000000000000 : ℝ), (8662674187301/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1078153507/2000000000 : ℝ)|^4549 ≤ (11262532702611/25000000000000 : ℝ)^3525
        have hw : |(1078153507/2000000000 : ℝ)|=(1078153507/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1888468887/10000000000 : ℝ)|^4549 ≤ (11636498233181/100000000000000 : ℝ)^3525
        have hw : |(-1888468887/10000000000 : ℝ)|=(1888468887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5229016131/10000000000 : ℝ)|^4549 ≤ (8662674187301/20000000000000 : ℝ)^3525
        have hw : |(5229016131/10000000000 : ℝ)|=(5229016131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1526_box_14 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1347691943/2500000000 : ℝ)*x 0 + (40851683/78125000 : ℝ)*x 1 + (-1888469517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1347691943/2500000000 : ℝ)^4549 ≤ (2815633335399/6250000000000 : ℝ)^3525 := by
    have hnat : (1347691943 : ℕ)^4549*6250000000000^3525 ≤ 2815633335399^3525*2500000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347691943 2500000000 2815633335399 6250000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40851683/78125000 : ℝ)^4549 ≤ (43313363379003/100000000000000 : ℝ)^3525 := by
    have hnat : (40851683 : ℕ)^4549*100000000000000^3525 ≤ 43313363379003^3525*78125000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40851683 78125000 43313363379003 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1888469517/10000000000 : ℝ)^4549 ≤ (11636503242859/100000000000000 : ℝ)^3525 := by
    have hnat : (1888469517 : ℕ)^4549*100000000000000^3525 ≤ 11636503242859^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1888469517 10000000000 11636503242859 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1347691943/2500000000 : ℝ), (40851683/78125000 : ℝ), (-1888469517/10000000000 : ℝ)] ![(2815633335399/6250000000000 : ℝ), (43313363379003/100000000000000 : ℝ), (11636503242859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1347691943/2500000000 : ℝ)|^4549 ≤ (2815633335399/6250000000000 : ℝ)^3525
        have hw : |(1347691943/2500000000 : ℝ)|=(1347691943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(40851683/78125000 : ℝ)|^4549 ≤ (43313363379003/100000000000000 : ℝ)^3525
        have hw : |(40851683/78125000 : ℝ)|=(40851683/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1888469517/10000000000 : ℝ)|^4549 ≤ (11636503242859/100000000000000 : ℝ)^3525
        have hw : |(-1888469517/10000000000 : ℝ)|=(1888469517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1526_box_15 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2009279553/5000000000 : ℝ)*x 0 + (137248729/312500000 : ℝ)*x 1 + (4391959319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2009279553/5000000000 : ℝ)^4549 ≤ (30835727858231/100000000000000 : ℝ)^3525 := by
    have hnat : (2009279553 : ℕ)^4549*100000000000000^3525 ≤ 30835727858231^3525*5000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2009279553 5000000000 30835727858231 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (137248729/312500000 : ℝ)^4549 ≤ (34582136109637/100000000000000 : ℝ)^3525 := by
    have hnat : (137248729 : ℕ)^4549*100000000000000^3525 ≤ 34582136109637^3525*312500000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137248729 312500000 34582136109637 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4391959319/10000000000 : ℝ)^4549 ≤ (6916427203637/20000000000000 : ℝ)^3525 := by
    have hnat : (4391959319 : ℕ)^4549*20000000000000^3525 ≤ 6916427203637^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4391959319 10000000000 6916427203637 20000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2009279553/5000000000 : ℝ), (137248729/312500000 : ℝ), (4391959319/10000000000 : ℝ)] ![(30835727858231/100000000000000 : ℝ), (34582136109637/100000000000000 : ℝ), (6916427203637/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2009279553/5000000000 : ℝ)|^4549 ≤ (30835727858231/100000000000000 : ℝ)^3525
        have hw : |(2009279553/5000000000 : ℝ)|=(2009279553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(137248729/312500000 : ℝ)|^4549 ≤ (34582136109637/100000000000000 : ℝ)^3525
        have hw : |(137248729/312500000 : ℝ)|=(137248729/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4391959319/10000000000 : ℝ)|^4549 ≤ (6916427203637/20000000000000 : ℝ)^3525
        have hw : |(4391959319/10000000000 : ℝ)|=(4391959319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1526_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164498657/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10969/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31879/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29347/50000 : ℝ) ∧ (20117/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (86091/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15483/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10969/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15483/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10969/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15483/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10969/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15483/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10969/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15483/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10969/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15483/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10969/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10969/100000 : ℝ) ^ (4547/1024 : ℝ) ≤ (5469268112909273/100000000000000000000 : ℝ) := by
    have hpowers : (10969/100000 : ℝ)^4547 ≤ (5469268112909273/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10969 : ℕ)^4547*100000000000000000000^1024 ≤ 5469268112909273^1024*100000^4547 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10969 100000 5469268112909273 100000000000000000000 4547 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10969/100000 : ℝ)) (X := (5469268112909273/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4547 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15483/100000 : ℝ) ^ (4547/1024 : ℝ) ≤ (25270195167881751/100000000000000000000 : ℝ) := by
    have hpowers : (15483/100000 : ℝ)^4547 ≤ (25270195167881751/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15483 : ℕ)^4547*100000000000000000000^1024 ≤ 25270195167881751^1024*100000^4547 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15483 100000 25270195167881751 100000000000000000000 4547 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15483/100000 : ℝ)) (X := (25270195167881751/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4547 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005469268112909273/50000000000000000000 : ℝ) ≤ (5000123164575249/5000000000000000 : ℝ) ^ (4547/1024 : ℝ) := by
    have hpowers : (50005469268112909273/50000000000000000000 : ℝ)^1024 ≤ (5000123164575249/5000000000000000 : ℝ)^4547 := by
      have hnat : (50005469268112909273 : ℕ)^1024*5000000000000000^4547 ≤ 5000123164575249^4547*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005469268112909273 50000000000000000000 5000123164575249 5000000000000000 1024 4547 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000123164575249/5000000000000000 : ℝ)) (X := (50005469268112909273/50000000000000000000 : ℝ)) (by norm_num) 4547 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6251921216455049439/6250000000000000000 : ℝ) ≤ (5000346090418343/5000000000000000 : ℝ) ^ (4547/1024 : ℝ) := by
    have hpowers : (6251921216455049439/6250000000000000000 : ℝ)^1024 ≤ (5000346090418343/5000000000000000 : ℝ)^4547 := by
      have hnat : (6251921216455049439 : ℕ)^1024*5000000000000000^4547 ≤ 5000346090418343^4547*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251921216455049439 6250000000000000000 5000346090418343 5000000000000000 1024 4547 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000346090418343/5000000000000000 : ℝ)) (X := (6251921216455049439/6250000000000000000 : ℝ)) (by norm_num) 4547 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50025270195167881751/50000000000000000000 : ℝ) ≤ (5000569016261437/5000000000000000 : ℝ) ^ (4547/1024 : ℝ) := by
    have hpowers : (50025270195167881751/50000000000000000000 : ℝ)^1024 ≤ (5000569016261437/5000000000000000 : ℝ)^4547 := by
      have hnat : (50025270195167881751 : ℕ)^1024*5000000000000000^4547 ≤ 5000569016261437^4547*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025270195167881751 50000000000000000000 5000569016261437 5000000000000000 1024 4547 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000569016261437/5000000000000000 : ℝ)) (X := (50025270195167881751/50000000000000000000 : ℝ)) (by norm_num) 4547 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5469268112909273/100000000000000000000 : ℝ) ≤ ((11282832708873438907/11285000000000000000 : ℝ)+2*(111462921547/112850000000000 : ℝ)*(10969/100000 : ℝ))^(4547/1024 : ℝ) := by
    rw [show (11282832708873438907/11285000000000000000 : ℝ)+2*(111462921547/112850000000000 : ℝ)*(10969/100000 : ℝ)=(5000123164575249/5000000000000000 : ℝ) by norm_num, show 1+2*(5469268112909273/100000000000000000000 : ℝ)=(50005469268112909273/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(25270195167881751/100000000000000000000 : ℝ)+(5469268112909273/100000000000000000000 : ℝ) ≤ ((11282832708873438907/11285000000000000000 : ℝ)+(111462921547/112850000000000 : ℝ)*((15483/100000 : ℝ)+(10969/100000 : ℝ)))^(4547/1024 : ℝ) := by
    rw [show (11282832708873438907/11285000000000000000 : ℝ)+(111462921547/112850000000000 : ℝ)*((15483/100000 : ℝ)+(10969/100000 : ℝ))=(5000346090418343/5000000000000000 : ℝ) by norm_num, show 1+(25270195167881751/100000000000000000000 : ℝ)+(5469268112909273/100000000000000000000 : ℝ)=(6251921216455049439/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(25270195167881751/100000000000000000000 : ℝ) ≤ ((11282832708873438907/11285000000000000000 : ℝ)+2*(111462921547/112850000000000 : ℝ)*(15483/100000 : ℝ))^(4547/1024 : ℝ) := by
    rw [show (11282832708873438907/11285000000000000000 : ℝ)+2*(111462921547/112850000000000 : ℝ)*(15483/100000 : ℝ)=(5000569016261437/5000000000000000 : ℝ) by norm_num, show 1+2*(25270195167881751/100000000000000000000 : ℝ)=(50025270195167881751/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11282832708873438907/11285000000000000000 : ℝ)*(X 1 0+X 2 0)+(111462921547/112850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4547/1024 : ℝ)) (lo := (10969/100000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (11282832708873438907/11285000000000000000 : ℝ)) (alpha := (111462921547/112850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11282832708873438907/11285000000000000000 : ℝ)*(X 0 1+X 2 1)+(111462921547/112850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4547/1024 : ℝ)) (lo := (10969/100000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (11282832708873438907/11285000000000000000 : ℝ)) (alpha := (111462921547/112850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11282832708873438907/11285000000000000000 : ℝ)*(X 0 2+X 1 2)+(111462921547/112850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4547/1024 : ℝ)) (lo := (10969/100000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (11282832708873438907/11285000000000000000 : ℝ)) (alpha := (111462921547/112850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-818189331/5000000000 : ℝ)*X 0 0+(540131951/1000000000 : ℝ)*X 0 1+(5401319307/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5270935873/10000000000 : ℝ)*X 1 0+(-908672723/5000000000 : ℝ)*X 1 1+(1350329611/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((527093543/1000000000 : ℝ)*X 2 0+(270065939/500000000 : ℝ)*X 2 1+(-1817345589/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2232868987/5000000000 : ℝ)*X 0 0+(521121137/1250000000 : ℝ)*X 0 1+(4168969397/10000000000 : ℝ)*X 0 2+(2232868987/5000000000 : ℝ)*X 1 0+(521121137/1250000000 : ℝ)*X 1 1+(4168969397/10000000000 : ℝ)*X 1 2+(2232868987/5000000000 : ℝ)*X 2 0+(521121137/1250000000 : ℝ)*X 2 1+(4168969397/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2064114377/10000000000 : ℝ)*X 0 0+(5244051859/10000000000 : ℝ)*X 0 1+(1048810301/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1076062157/2000000000 : ℝ)*X 1 0+(-941211743/5000000000 : ℝ)*X 1 1+(5244051623/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2690155139/5000000000 : ℝ)*X 2 0+(5244051797/10000000000 : ℝ)*X 2 1+(-1882423939/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4058369109/10000000000 : ℝ)*X 0 0+(2186260711/5000000000 : ℝ)*X 0 1+(1093130227/2500000000 : ℝ)*X 0 2+(4058369109/10000000000 : ℝ)*X 1 0+(2186260711/5000000000 : ℝ)*X 1 1+(1093130227/2500000000 : ℝ)*X 1 2+(4058369109/10000000000 : ℝ)*X 2 0+(2186260711/5000000000 : ℝ)*X 2 1+(1093130227/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-3854789/19531250 : ℝ)*X 0 0+(5133721543/10000000000 : ℝ)*X 0 1+(338858101/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2628367317/5000000000 : ℝ)*X 1 0+(-1808656651/10000000000 : ℝ)*X 1 1+(1084346011/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2628367273/5000000000 : ℝ)*X 2 0+(2710864927/5000000000 : ℝ)*X 2 1+(-226082131/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2258728179/5000000000 : ℝ)*X 0 0+(828503977/2000000000 : ℝ)*X 0 1+(4142519369/10000000000 : ℝ)*X 0 2+(2258728179/5000000000 : ℝ)*X 1 0+(828503977/2000000000 : ℝ)*X 1 1+(4142519369/10000000000 : ℝ)*X 1 2+(2258728179/5000000000 : ℝ)*X 2 0+(828503977/2000000000 : ℝ)*X 2 1+(4142519369/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1726717383/10000000000 : ℝ)*X 0 0+(1377037433/2500000000 : ℝ)*X 0 1+(130725381/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1078153507/2000000000 : ℝ)*X 1 0+(-1888468887/10000000000 : ℝ)*X 1 1+(5229016131/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1347691943/2500000000 : ℝ)*X 2 0+(40851683/78125000 : ℝ)*X 2 1+(-1888469517/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2009279553/5000000000 : ℝ)*X 0 0+(137248729/312500000 : ℝ)*X 0 1+(4391959319/10000000000 : ℝ)*X 0 2+(2009279553/5000000000 : ℝ)*X 1 0+(137248729/312500000 : ℝ)*X 1 1+(4391959319/10000000000 : ℝ)*X 1 2+(2009279553/5000000000 : ℝ)*X 2 0+(137248729/312500000 : ℝ)*X 2 1+(4391959319/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31879/50000 : ℝ) ≤ (-71948505593330556594117861181047/112850000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9076611/12500000000000 : ℝ)*(upper1) + (43840921/100000000000000 : ℝ)*(upper3) + (146950199/100000000000000 : ℝ)*(lower4) + (20673969/20000000000000 : ℝ)*(lower5) + (448806158755331/20000000000000 : ℝ)*(major0) + (448806158755331/20000000000000 : ℝ)*(major1) + (448806158755331/20000000000000 : ℝ)*(major2) + (681880347/100000000000000 : ℝ)*(sp3) + (314514995064343/10000000000000 : ℝ)*(sp4) + (1572553065584177/50000000000000 : ℝ)*(sp5) + (3145094172620737/100000000000000 : ℝ)*(sp6) + (682081456778289/50000000000000 : ℝ)*(sp7) + (43819475077/100000000000000 : ℝ)*(sp13) + (55778022693/100000000000000 : ℝ)*(sp14) + (54566543817477/4000000000000 : ℝ)*(f.failure) + (314514995064343/10000000000000 : ℝ)*(f.sum) + (3428396301631/564250000000000000000000000 : ℝ)*base65 + (955733484673836783/225700000000000000000000000000000 : ℝ)*base68 + (819868660443336783/225700000000000000000000000000000 : ℝ)*base70 + (761803573475736783/225700000000000000000000000000000 : ℝ)*base72 + (6912734090669/2257000000000000000000000000 : ℝ)*base73 + (1374084823653636783/225700000000000000000000000000000 : ℝ)*base76 + (1049788151058636783/225700000000000000000000000000000 : ℝ)*base78 + (650066812544536783/225700000000000000000000000000000 : ℝ)*base80 + (21600111092551/2257000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (371611/400000000000000000000 : ℝ)*base90 + (371611/400000000000000000000 : ℝ)*base92 + (371611/400000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (29347/50000 : ℝ) ≤ (10349786337915618717887143771587/17632812500000000000000000000000 : ℝ) := by norm_num
    linear_combination (28777887/100000000000000 : ℝ)*(lower1) + (88453849/100000000000000 : ℝ)*(lower4) + (65167761/100000000000000 : ℝ)*(lower5) + (145077404055497/6250000000000 : ℝ)*(major0) + (145077404055497/6250000000000 : ℝ)*(major1) + (145077404055497/6250000000000 : ℝ)*(major2) + (80295267027973/2500000000000 : ℝ)*(sp0) + (3211680842613783/100000000000000 : ℝ)*(sp1) + (3211718745024339/100000000000000 : ℝ)*(sp2) + (1411098650272693/100000000000000 : ℝ)*(sp3) + (41411963/50000000000000 : ℝ)*(sp7) + (131962672003/100000000000000 : ℝ)*(sp9) + (94060261447/100000000000000 : ℝ)*(sp10) + (2124166867/100000000000000 : ℝ)*(sp12) + (705549366548309/50000000000000 : ℝ)*(f.failure) + (1605906402642893/50000000000000 : ℝ)*(f.sum) + (4757793328787/11285000000000000000000000000 : ℝ)*base66 + (582505004384828221/70531250000000000000000000000000 : ℝ)*base68 + (410349882303109471/70531250000000000000000000000000 : ℝ)*base70 + (346721732256109471/70531250000000000000000000000000 : ℝ)*base72 + (47795423942277/11285000000000000000000000000 : ℝ)*base74 + (206543070061609279/70531250000000000000000000000000 : ℝ)*base75 + (320843066954453221/70531250000000000000000000000000 : ℝ)*base78 + (274104737844140721/70531250000000000000000000000000 : ℝ)*base80 + (13504233083959/5642500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (43878987/5000000000000000000000 : ℝ)*base90 + (43878987/5000000000000000000000 : ℝ)*base92 + (43878987/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (20117/25000 : ℝ) ≤ (3721780575491356535824671799743/4625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8100383/12500000000000 : ℝ)*(upper1) + (22186777/25000000000000 : ℝ)*(upper2) + (30896347/100000000000000 : ℝ)*(upper3) + (85381443/100000000000000 : ℝ)*(lower5) + (1256722324582037/50000000000000 : ℝ)*(major0) + (1256722324582037/50000000000000 : ℝ)*(major1) + (1256722324582037/50000000000000 : ℝ)*(major2) + (338138583/50000000000000 : ℝ)*(sp0) + (22990986981/25000000000000 : ℝ)*(sp1) + (637352729/1250000000000 : ℝ)*(sp2) + (3472122626026651/100000000000000 : ℝ)*(sp8) + (3472031338355893/100000000000000 : ℝ)*(sp9) + (1736036157042749/50000000000000 : ℝ)*(sp10) + (1527942352237/100000000000 : ℝ)*(sp11) + (1527942352237/100000000000 : ℝ)*(f.failure) + (1736061651151909/50000000000000 : ℝ)*(f.sum) + (18435765581/11562500000000000000000000 : ℝ)*base65 + (52899594187258419/9250000000000000000000000000000 : ℝ)*base67 + (44834026443991581/9250000000000000000000000000000 : ℝ)*base70 + (44779706823008419/9250000000000000000000000000000 : ℝ)*base71 + (486593849109/185000000000000000000000000 : ℝ)*base74 + (5207230420758419/9250000000000000000000000000000 : ℝ)*base75 + (2870586653508419/9250000000000000000000000000000 : ℝ)*base77 + (22552246398491581/9250000000000000000000000000000 : ℝ)*base80 + (72367980191/46250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (45709/10000000000000000000 : ℝ)*base89 + (45709/10000000000000000000 : ℝ)*base91 + (45709/10000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-86091/100000 : ℝ) ≤ (-388604890726928279169790449/451400000000000000000000000 : ℝ) := by norm_num
    linear_combination (52743573/100000000000000 : ℝ)*(lower0) + (100591869/100000000000000 : ℝ)*(lower1) + (178182371/100000000000000 : ℝ)*(upper3) + (41237693/50000000000000 : ℝ)*(lower4) + (510571915805337/20000000000000 : ℝ)*(major0) + (510571915805337/20000000000000 : ℝ)*(major1) + (510571915805337/20000000000000 : ℝ)*(major2) + (469259031/20000000000000 : ℝ)*(sp0) + (160058356973/100000000000000 : ℝ)*(sp6) + (3571592079/5000000000000 : ℝ)*(sp7) + (3582510090394127/100000000000000 : ℝ)*(sp12) + (1791256218344641/50000000000000 : ℝ)*(sp13) + (895588094583077/25000000000000 : ℝ)*(sp14) + (1551831559698761/100000000000000 : ℝ)*(sp15) + (775951495770171/50000000000000 : ℝ)*(f.failure) + (1791256218344641/50000000000000 : ℝ)*(f.sum) + (14652893020483/2257000000000000000000000000 : ℝ)*base65 + (1051270007909453341/225700000000000000000000000000000 : ℝ)*base68 + (3511624372216853341/225700000000000000000000000000000 : ℝ)*base70 + (192187494278746659/225700000000000000000000000000000 : ℝ)*base71 + (201947744273/112850000000000000000000000 : ℝ)*base74 + (212142402044246659/225700000000000000000000000000000 : ℝ)*base75 + (1453943843798746659/225700000000000000000000000000000 : ℝ)*base77 + (538536271925753341/225700000000000000000000000000000 : ℝ)*base80 + (216671926967/1128500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (60160347/5000000000000000000000 : ℝ)*base89 + (60160347/5000000000000000000000 : ℝ)*base91 + (60160347/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1526_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164498657/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10969/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31879/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29347/50000 : ℝ) else (20117/25000 : ℝ) ≤ X j i ∧ X j i ≤ (86091/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1526_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1526_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164498657/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1371/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31879/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29347/50000 : ℝ) else (20117/25000 : ℝ) ≤ X j i ∧ X j i ≤ (86091/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1526_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1526_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164498657/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1371/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31879/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29347/50000 : ℝ) else (20117/25000 : ℝ) ≤ X j i ∧ X j i ≤ (86091/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1526_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
