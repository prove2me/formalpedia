-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1704_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:48:07.906709+00:00
-- url     : https://prove2.me/submissions/90a3c024-ef06-41af-bc89-07fe6b20078a

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
theorem support_rectangle_w1704_s3_0 (p : ℝ) (hpa : (5247/1024 : ℝ) ≤ p) (hpb : p ≤ (5255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-286809899/2000000000 : ℝ)*x 0 + (218955953/400000000 : ℝ)*x 1 + (5137506927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (286809899/2000000000 : ℝ)^5255 ≤ (2240645422081/25000000000000 : ℝ)^4231 := by
    have hnat : (286809899 : ℕ)^5255*25000000000000^4231 ≤ 2240645422081^4231*2000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      286809899 2000000000 2240645422081 25000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (218955953/400000000 : ℝ)^5255 ≤ (47310607173057/100000000000000 : ℝ)^4231 := by
    have hnat : (218955953 : ℕ)^5255*100000000000000^4231 ≤ 47310607173057^4231*400000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218955953 400000000 47310607173057 100000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5137506927/10000000000 : ℝ)^5255 ≤ (21863405559131/50000000000000 : ℝ)^4231 := by
    have hnat : (5137506927 : ℕ)^5255*50000000000000^4231 ≤ 21863405559131^4231*10000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5137506927 10000000000 21863405559131 50000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5255/1024 : ℝ)) 5255 4231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-286809899/2000000000 : ℝ), (218955953/400000000 : ℝ), (5137506927/10000000000 : ℝ)] ![(2240645422081/25000000000000 : ℝ), (47310607173057/100000000000000 : ℝ), (21863405559131/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-286809899/2000000000 : ℝ)|^5255 ≤ (2240645422081/25000000000000 : ℝ)^4231
        have hw : |(-286809899/2000000000 : ℝ)|=(286809899/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(218955953/400000000 : ℝ)|^5255 ≤ (47310607173057/100000000000000 : ℝ)^4231
        have hw : |(218955953/400000000 : ℝ)|=(218955953/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5137506927/10000000000 : ℝ)|^5255 ≤ (21863405559131/50000000000000 : ℝ)^4231
        have hw : |(5137506927/10000000000 : ℝ)|=(5137506927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1704_s3_1 (p : ℝ) (hpa : (5247/1024 : ℝ) ≤ p) (hpb : p ≤ (5255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672766299/5000000000 : ℝ)*x 0 + (-402141559/2500000000 : ℝ)*x 1 + (5137506919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672766299/5000000000 : ℝ)^5255 ≤ (22968281591159/50000000000000 : ℝ)^4231 := by
    have hnat : (2672766299 : ℕ)^5255*50000000000000^4231 ≤ 22968281591159^4231*5000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672766299 5000000000 22968281591159 50000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (402141559/2500000000 : ℝ)^5255 ≤ (5168312886451/50000000000000 : ℝ)^4231 := by
    have hnat : (402141559 : ℕ)^5255*50000000000000^4231 ≤ 5168312886451^4231*2500000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402141559 2500000000 5168312886451 50000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5137506919/10000000000 : ℝ)^5255 ≤ (10931702758423/25000000000000 : ℝ)^4231 := by
    have hnat : (5137506919 : ℕ)^5255*25000000000000^4231 ≤ 10931702758423^4231*10000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5137506919 10000000000 10931702758423 25000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5255/1024 : ℝ)) 5255 4231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672766299/5000000000 : ℝ), (-402141559/2500000000 : ℝ), (5137506919/10000000000 : ℝ)] ![(22968281591159/50000000000000 : ℝ), (5168312886451/50000000000000 : ℝ), (10931702758423/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672766299/5000000000 : ℝ)|^5255 ≤ (22968281591159/50000000000000 : ℝ)^4231
        have hw : |(2672766299/5000000000 : ℝ)|=(2672766299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-402141559/2500000000 : ℝ)|^5255 ≤ (5168312886451/50000000000000 : ℝ)^4231
        have hw : |(-402141559/2500000000 : ℝ)|=(402141559/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5137506919/10000000000 : ℝ)|^5255 ≤ (10931702758423/25000000000000 : ℝ)^4231
        have hw : |(5137506919/10000000000 : ℝ)|=(5137506919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1704_s3_2 (p : ℝ) (hpa : (5247/1024 : ℝ) ≤ p) (hpb : p ≤ (5255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345532597/10000000000 : ℝ)*x 0 + (160547093/312500000 : ℝ)*x 1 + (-804283081/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345532597/10000000000 : ℝ)^5255 ≤ (9187312634329/20000000000000 : ℝ)^4231 := by
    have hnat : (5345532597 : ℕ)^5255*20000000000000^4231 ≤ 9187312634329^4231*10000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345532597 10000000000 9187312634329 20000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (160547093/312500000 : ℝ)^5255 ≤ (10931702909063/25000000000000 : ℝ)^4231 := by
    have hnat : (160547093 : ℕ)^5255*25000000000000^4231 ≤ 10931702909063^4231*312500000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160547093 312500000 10931702909063 25000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (804283081/5000000000 : ℝ)^5255 ≤ (10336625182291/100000000000000 : ℝ)^4231 := by
    have hnat : (804283081 : ℕ)^5255*100000000000000^4231 ≤ 10336625182291^4231*5000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      804283081 5000000000 10336625182291 100000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5255/1024 : ℝ)) 5255 4231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345532597/10000000000 : ℝ), (160547093/312500000 : ℝ), (-804283081/5000000000 : ℝ)] ![(9187312634329/20000000000000 : ℝ), (10931702909063/25000000000000 : ℝ), (10336625182291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345532597/10000000000 : ℝ)|^5255 ≤ (9187312634329/20000000000000 : ℝ)^4231
        have hw : |(5345532597/10000000000 : ℝ)|=(5345532597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(160547093/312500000 : ℝ)|^5255 ≤ (10931702909063/25000000000000 : ℝ)^4231
        have hw : |(160547093/312500000 : ℝ)|=(160547093/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-804283081/5000000000 : ℝ)|^5255 ≤ (10336625182291/100000000000000 : ℝ)^4231
        have hw : |(-804283081/5000000000 : ℝ)|=(804283081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1704_s3_3 (p : ℝ) (hpa : (5247/1024 : ℝ) ≤ p) (hpb : p ≤ (5255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4112485429/10000000000 : ℝ)*x 0 + (1824795219/5000000000 : ℝ)*x 1 + (1152882577/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4112485429/10000000000 : ℝ)^5255 ≤ (33167191020543/100000000000000 : ℝ)^4231 := by
    have hnat : (4112485429 : ℕ)^5255*100000000000000^4231 ≤ 33167191020543^4231*10000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4112485429 10000000000 33167191020543 100000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1824795219/5000000000 : ℝ)^5255 ≤ (28595458872963/100000000000000 : ℝ)^4231 := by
    have hnat : (1824795219 : ℕ)^5255*100000000000000^4231 ≤ 28595458872963^4231*5000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1824795219 5000000000 28595458872963 100000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1152882577/2500000000 : ℝ)^5255 ≤ (9559337523717/25000000000000 : ℝ)^4231 := by
    have hnat : (1152882577 : ℕ)^5255*25000000000000^4231 ≤ 9559337523717^4231*2500000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1152882577 2500000000 9559337523717 25000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5255/1024 : ℝ)) 5255 4231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4112485429/10000000000 : ℝ), (1824795219/5000000000 : ℝ), (1152882577/2500000000 : ℝ)] ![(33167191020543/100000000000000 : ℝ), (28595458872963/100000000000000 : ℝ), (9559337523717/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4112485429/10000000000 : ℝ)|^5255 ≤ (33167191020543/100000000000000 : ℝ)^4231
        have hw : |(4112485429/10000000000 : ℝ)|=(4112485429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1824795219/5000000000 : ℝ)|^5255 ≤ (28595458872963/100000000000000 : ℝ)^4231
        have hw : |(1824795219/5000000000 : ℝ)|=(1824795219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1152882577/2500000000 : ℝ)|^5255 ≤ (9559337523717/25000000000000 : ℝ)^4231
        have hw : |(1152882577/2500000000 : ℝ)|=(1152882577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1704_s3_4 (p : ℝ) (hpa : (5247/1024 : ℝ) ≤ p) (hpb : p ≤ (5255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-35855077/250000000 : ℝ)*x 0 + (5141212849/10000000000 : ℝ)*x 1 + (2735068831/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (35855077/250000000 : ℝ)^5255 ≤ (1120471737411/12500000000000 : ℝ)^4231 := by
    have hnat : (35855077 : ℕ)^5255*12500000000000^4231 ≤ 1120471737411^4231*250000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35855077 250000000 1120471737411 12500000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5141212849/10000000000 : ℝ)^5255 ≤ (43765990651431/100000000000000 : ℝ)^4231 := by
    have hnat : (5141212849 : ℕ)^5255*100000000000000^4231 ≤ 43765990651431^4231*10000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5141212849 10000000000 43765990651431 100000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2735068831/5000000000 : ℝ)^5255 ≤ (11817558857807/25000000000000 : ℝ)^4231 := by
    have hnat : (2735068831 : ℕ)^5255*25000000000000^4231 ≤ 11817558857807^4231*5000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2735068831 5000000000 11817558857807 25000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5255/1024 : ℝ)) 5255 4231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-35855077/250000000 : ℝ), (5141212849/10000000000 : ℝ), (2735068831/5000000000 : ℝ)] ![(1120471737411/12500000000000 : ℝ), (43765990651431/100000000000000 : ℝ), (11817558857807/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-35855077/250000000 : ℝ)|^5255 ≤ (1120471737411/12500000000000 : ℝ)^4231
        have hw : |(-35855077/250000000 : ℝ)|=(35855077/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5141212849/10000000000 : ℝ)|^5255 ≤ (43765990651431/100000000000000 : ℝ)^4231
        have hw : |(5141212849/10000000000 : ℝ)|=(5141212849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2735068831/5000000000 : ℝ)|^5255 ≤ (11817558857807/25000000000000 : ℝ)^4231
        have hw : |(2735068831/5000000000 : ℝ)|=(2735068831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1704_s3_5 (p : ℝ) (hpa : (5247/1024 : ℝ) ≤ p) (hpb : p ≤ (5255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5255508481/10000000000 : ℝ)*x 0 + (-1275935503/10000000000 : ℝ)*x 1 + (2735068843/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5255508481/10000000000 : ℝ)^5255 ≤ (4497767866887/10000000000000 : ℝ)^4231 := by
    have hnat : (5255508481 : ℕ)^5255*10000000000000^4231 ≤ 4497767866887^4231*10000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255508481 10000000000 4497767866887 10000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1275935503/10000000000 : ℝ)^5255 ≤ (3876042816177/50000000000000 : ℝ)^4231 := by
    have hnat : (1275935503 : ℕ)^5255*50000000000000^4231 ≤ 3876042816177^4231*10000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1275935503 10000000000 3876042816177 50000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2735068843/5000000000 : ℝ)^5255 ≤ (47270235688819/100000000000000 : ℝ)^4231 := by
    have hnat : (2735068843 : ℕ)^5255*100000000000000^4231 ≤ 47270235688819^4231*5000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2735068843 5000000000 47270235688819 100000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5255/1024 : ℝ)) 5255 4231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5255508481/10000000000 : ℝ), (-1275935503/10000000000 : ℝ), (2735068843/5000000000 : ℝ)] ![(4497767866887/10000000000000 : ℝ), (3876042816177/50000000000000 : ℝ), (47270235688819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5255508481/10000000000 : ℝ)|^5255 ≤ (4497767866887/10000000000000 : ℝ)^4231
        have hw : |(5255508481/10000000000 : ℝ)|=(5255508481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1275935503/10000000000 : ℝ)|^5255 ≤ (3876042816177/50000000000000 : ℝ)^4231
        have hw : |(-1275935503/10000000000 : ℝ)|=(1275935503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2735068843/5000000000 : ℝ)|^5255 ≤ (47270235688819/100000000000000 : ℝ)^4231
        have hw : |(2735068843/5000000000 : ℝ)|=(2735068843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1704_s3_6 (p : ℝ) (hpa : (5247/1024 : ℝ) ≤ p) (hpb : p ≤ (5255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1051101697/2000000000 : ℝ)*x 0 + (2735068837/5000000000 : ℝ)*x 1 + (-637967757/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051101697/2000000000 : ℝ)^5255 ≤ (11244419677847/25000000000000 : ℝ)^4231 := by
    have hnat : (1051101697 : ℕ)^5255*25000000000000^4231 ≤ 11244419677847^4231*2000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051101697 2000000000 11244419677847 25000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2735068837/5000000000 : ℝ)^5255 ≤ (47270235560023/100000000000000 : ℝ)^4231 := by
    have hnat : (2735068837 : ℕ)^5255*100000000000000^4231 ≤ 47270235560023^4231*5000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2735068837 5000000000 47270235560023 100000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (637967757/5000000000 : ℝ)^5255 ≤ (7752085715361/100000000000000 : ℝ)^4231 := by
    have hnat : (637967757 : ℕ)^5255*100000000000000^4231 ≤ 7752085715361^4231*5000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      637967757 5000000000 7752085715361 100000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5255/1024 : ℝ)) 5255 4231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051101697/2000000000 : ℝ), (2735068837/5000000000 : ℝ), (-637967757/5000000000 : ℝ)] ![(11244419677847/25000000000000 : ℝ), (47270235560023/100000000000000 : ℝ), (7752085715361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051101697/2000000000 : ℝ)|^5255 ≤ (11244419677847/25000000000000 : ℝ)^4231
        have hw : |(1051101697/2000000000 : ℝ)|=(1051101697/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2735068837/5000000000 : ℝ)|^5255 ≤ (47270235560023/100000000000000 : ℝ)^4231
        have hw : |(2735068837/5000000000 : ℝ)|=(2735068837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-637967757/5000000000 : ℝ)|^5255 ≤ (7752085715361/100000000000000 : ℝ)^4231
        have hw : |(-637967757/5000000000 : ℝ)|=(637967757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1704_s3_7 (p : ℝ) (hpa : (5247/1024 : ℝ) ≤ p) (hpb : p ≤ (5255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4112924767/10000000000 : ℝ)*x 0 + (143779159/312500000 : ℝ)*x 1 + (732069161/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4112924767/10000000000 : ℝ)^5255 ≤ (33171591889103/100000000000000 : ℝ)^4231 := by
    have hnat : (4112924767 : ℕ)^5255*100000000000000^4231 ≤ 33171591889103^4231*10000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4112924767 10000000000 33171591889103 100000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (143779159/312500000 : ℝ)^5255 ≤ (38128245382459/100000000000000 : ℝ)^4231 := by
    have hnat : (143779159 : ℕ)^5255*100000000000000^4231 ≤ 38128245382459^4231*312500000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      143779159 312500000 38128245382459 100000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (732069161/2000000000 : ℝ)^5255 ≤ (28700162711941/100000000000000 : ℝ)^4231 := by
    have hnat : (732069161 : ℕ)^5255*100000000000000^4231 ≤ 28700162711941^4231*2000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      732069161 2000000000 28700162711941 100000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5255/1024 : ℝ)) 5255 4231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4112924767/10000000000 : ℝ), (143779159/312500000 : ℝ), (732069161/2000000000 : ℝ)] ![(33171591889103/100000000000000 : ℝ), (38128245382459/100000000000000 : ℝ), (28700162711941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4112924767/10000000000 : ℝ)|^5255 ≤ (33171591889103/100000000000000 : ℝ)^4231
        have hw : |(4112924767/10000000000 : ℝ)|=(4112924767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(143779159/312500000 : ℝ)|^5255 ≤ (38128245382459/100000000000000 : ℝ)^4231
        have hw : |(143779159/312500000 : ℝ)|=(143779159/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(732069161/2000000000 : ℝ)|^5255 ≤ (28700162711941/100000000000000 : ℝ)^4231
        have hw : |(732069161/2000000000 : ℝ)|=(732069161/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1704_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5247/1024 : ℝ) ≤ p) (hpb : p ≤ (5255/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (96489539/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (343/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9949/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9961/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1071/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (343/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9949/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (343/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9949/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (343/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9949/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (343/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9949/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (343/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9949/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (343/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9949/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9949/100000 : ℝ) ^ (5247/1024 : ℝ) ≤ (183036761393253/25000000000000000000 : ℝ) := by
    have hpowers : (9949/100000 : ℝ)^5247 ≤ (183036761393253/25000000000000000000 : ℝ)^1024 := by
      have hnat : (9949 : ℕ)^5247*25000000000000000000^1024 ≤ 183036761393253^1024*100000^5247 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9949 100000 183036761393253 25000000000000000000 5247 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9949/100000 : ℝ)) (X := (183036761393253/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5247 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (343/2000 : ℝ) ^ (5247/1024 : ℝ) ≤ (5961031691222729/50000000000000000000 : ℝ) := by
    have hpowers : (343/2000 : ℝ)^5247 ≤ (5961031691222729/50000000000000000000 : ℝ)^1024 := by
      have hnat : (343 : ℕ)^5247*50000000000000000000^1024 ≤ 5961031691222729^1024*2000^5247 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        343 2000 5961031691222729 50000000000000000000 5247 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (343/2000 : ℝ)) (X := (5961031691222729/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5247 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500183036761393253/12500000000000000000 : ℝ) ≤ (200000571537379/200000000000000 : ℝ) ^ (5247/1024 : ℝ) := by
    have hpowers : (12500183036761393253/12500000000000000000 : ℝ)^1024 ≤ (200000571537379/200000000000000 : ℝ)^5247 := by
      have hnat : (12500183036761393253 : ℕ)^1024*200000000000000^5247 ≤ 200000571537379^5247*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500183036761393253 12500000000000000000 200000571537379 200000000000000 1024 5247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200000571537379/200000000000000 : ℝ)) (X := (12500183036761393253/12500000000000000000 : ℝ)) (by norm_num) 5247 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10001265421042801847/10000000000000000000 : ℝ) ≤ (10000246945905683/10000000000000000 : ℝ) ^ (5247/1024 : ℝ) := by
    have hpowers : (10001265421042801847/10000000000000000000 : ℝ)^1024 ≤ (10000246945905683/10000000000000000 : ℝ)^5247 := by
      have hnat : (10001265421042801847 : ℕ)^1024*10000000000000000^5247 ≤ 10000246945905683^5247*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001265421042801847 10000000000000000000 10000246945905683 10000000000000000 1024 5247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000246945905683/10000000000000000 : ℝ)) (X := (10001265421042801847/10000000000000000000 : ℝ)) (by norm_num) 5247 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25005961031691222729/25000000000000000000 : ℝ) ≤ (625029082183901/625000000000000 : ℝ) ^ (5247/1024 : ℝ) := by
    have hpowers : (25005961031691222729/25000000000000000000 : ℝ)^1024 ≤ (625029082183901/625000000000000 : ℝ)^5247 := by
      have hnat : (25005961031691222729 : ℕ)^1024*625000000000000^5247 ≤ 625029082183901^5247*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005961031691222729 25000000000000000000 625029082183901 625000000000000 1024 5247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625029082183901/625000000000000 : ℝ)) (X := (25005961031691222729/25000000000000000000 : ℝ)) (by norm_num) 5247 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(183036761393253/25000000000000000000 : ℝ) ≤ ((18001465168735098929/18002500000000000000 : ℝ)+2*(218369036733/720100000000000 : ℝ)*(9949/100000 : ℝ))^(5247/1024 : ℝ) := by
    rw [show (18001465168735098929/18002500000000000000 : ℝ)+2*(218369036733/720100000000000 : ℝ)*(9949/100000 : ℝ)=(200000571537379/200000000000000 : ℝ) by norm_num, show 1+2*(183036761393253/25000000000000000000 : ℝ)=(12500183036761393253/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5961031691222729/50000000000000000000 : ℝ)+(183036761393253/25000000000000000000 : ℝ) ≤ ((18001465168735098929/18002500000000000000 : ℝ)+(218369036733/720100000000000 : ℝ)*((343/2000 : ℝ)+(9949/100000 : ℝ)))^(5247/1024 : ℝ) := by
    rw [show (18001465168735098929/18002500000000000000 : ℝ)+(218369036733/720100000000000 : ℝ)*((343/2000 : ℝ)+(9949/100000 : ℝ))=(10000246945905683/10000000000000000 : ℝ) by norm_num, show 1+(5961031691222729/50000000000000000000 : ℝ)+(183036761393253/25000000000000000000 : ℝ)=(10001265421042801847/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5961031691222729/50000000000000000000 : ℝ) ≤ ((18001465168735098929/18002500000000000000 : ℝ)+2*(218369036733/720100000000000 : ℝ)*(343/2000 : ℝ))^(5247/1024 : ℝ) := by
    rw [show (18001465168735098929/18002500000000000000 : ℝ)+2*(218369036733/720100000000000 : ℝ)*(343/2000 : ℝ)=(625029082183901/625000000000000 : ℝ) by norm_num, show 1+2*(5961031691222729/50000000000000000000 : ℝ)=(25005961031691222729/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18001465168735098929/18002500000000000000 : ℝ)*(X 1 0+X 2 0)+(218369036733/720100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5247/1024 : ℝ)) (lo := (9949/100000 : ℝ)) (hi := (343/2000 : ℝ)) (c := (18001465168735098929/18002500000000000000 : ℝ)) (alpha := (218369036733/720100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18001465168735098929/18002500000000000000 : ℝ)*(X 0 1+X 2 1)+(218369036733/720100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5247/1024 : ℝ)) (lo := (9949/100000 : ℝ)) (hi := (343/2000 : ℝ)) (c := (18001465168735098929/18002500000000000000 : ℝ)) (alpha := (218369036733/720100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18001465168735098929/18002500000000000000 : ℝ)*(X 0 2+X 1 2)+(218369036733/720100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5247/1024 : ℝ)) (lo := (9949/100000 : ℝ)) (hi := (343/2000 : ℝ)) (c := (18001465168735098929/18002500000000000000 : ℝ)) (alpha := (218369036733/720100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-286809899/2000000000 : ℝ)*X 0 0+(218955953/400000000 : ℝ)*X 0 1+(5137506927/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1704_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672766299/5000000000 : ℝ)*X 1 0+(-402141559/2500000000 : ℝ)*X 1 1+(5137506919/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1704_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345532597/10000000000 : ℝ)*X 2 0+(160547093/312500000 : ℝ)*X 2 1+(-804283081/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1704_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4112485429/10000000000 : ℝ)*X 0 0+(1824795219/5000000000 : ℝ)*X 0 1+(1152882577/2500000000 : ℝ)*X 0 2+(4112485429/10000000000 : ℝ)*X 1 0+(1824795219/5000000000 : ℝ)*X 1 1+(1152882577/2500000000 : ℝ)*X 1 2+(4112485429/10000000000 : ℝ)*X 2 0+(1824795219/5000000000 : ℝ)*X 2 1+(1152882577/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1704_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-35855077/250000000 : ℝ)*X 0 0+(5141212849/10000000000 : ℝ)*X 0 1+(2735068831/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1704_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5255508481/10000000000 : ℝ)*X 1 0+(-1275935503/10000000000 : ℝ)*X 1 1+(2735068843/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1704_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1051101697/2000000000 : ℝ)*X 2 0+(2735068837/5000000000 : ℝ)*X 2 1+(-637967757/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1704_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4112924767/10000000000 : ℝ)*X 0 0+(143779159/312500000 : ℝ)*X 0 1+(732069161/2000000000 : ℝ)*X 0 2+(4112924767/10000000000 : ℝ)*X 1 0+(143779159/312500000 : ℝ)*X 1 1+(732069161/2000000000 : ℝ)*X 1 2+(4112924767/10000000000 : ℝ)*X 2 0+(143779159/312500000 : ℝ)*X 2 1+(732069161/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1704_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2405418410541313786429805733/900125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9204543/2000000000000 : ℝ)*(base19) + (224747371/50000000000000 : ℝ)*(base23) + (47931139/100000000000000 : ℝ)*(upper3) + (5439771/100000000000000 : ℝ)*(upper4) + (21919631/25000000000000 : ℝ)*(upper5) + (2006150961325653/100000000000000 : ℝ)*(major0) + (2006150961325653/100000000000000 : ℝ)*(major1) + (2006150961325653/100000000000000 : ℝ)*(major2) + (371590933507093/12500000000000 : ℝ)*(sp0) + (59454644461931/2000000000000 : ℝ)*(sp1) + (1486366116914479/50000000000000 : ℝ)*(sp2) + (41582706752151/4000000000000 : ℝ)*(sp3) + (1303816739/25000000000000 : ℝ)*(sp4) + (46295207/3125000000000 : ℝ)*(sp7) + (519784575125199/50000000000000 : ℝ)*(f.failure) + (2972732683323699/100000000000000 : ℝ)*(f.sum) + (42052615363983/18002500000000000000000000000 : ℝ)*base66 + (17585576444019749363/1800250000000000000000000000000000 : ℝ)*base68 + (7905354548663249363/1800250000000000000000000000000000 : ℝ)*base70 + (23929884594163999363/1800250000000000000000000000000000 : ℝ)*base72 + (55439858583161/36005000000000000000000000000 : ℝ)*base74 + (8447710267385749363/1800250000000000000000000000000000 : ℝ)*base76 + (14181903542720499363/1800250000000000000000000000000000 : ℝ)*base78 + (6331435201110749363/1800250000000000000000000000000000 : ℝ)*base80 + (32236159518529/36005000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (6206739/2500000000000000000000 : ℝ)*base90 + (6206739/2500000000000000000000 : ℝ)*base92 + (6206739/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9695059733512539746894916819/900125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (185191269/12500000000000 : ℝ)*(base19) + (1987659/125000000000 : ℝ)*(base23) + (451752387/100000000000000 : ℝ)*(lower1) + (226656849/100000000000000 : ℝ)*(upper3) + (48738569/100000000000000 : ℝ)*(lower4) + (224970089/100000000000000 : ℝ)*(upper5) + (2051677526188863/100000000000000 : ℝ)*(major0) + (2051677526188863/100000000000000 : ℝ)*(major1) + (2051677526188863/100000000000000 : ℝ)*(major2) + (197686511/25000000000000 : ℝ)*(sp2) + (760048522994573/25000000000000 : ℝ)*(sp4) + (152009630522407/5000000000000 : ℝ)*(sp5) + (380023963888131/12500000000000 : ℝ)*(sp6) + (265790150343249/25000000000000 : ℝ)*(sp7) + (265790150343249/25000000000000 : ℝ)*(f.failure) + (760048522994573/25000000000000 : ℝ)*(f.sum) + (80286380649719/36005000000000000000000000000 : ℝ)*base65 + (11693028292931497273/1800250000000000000000000000000000 : ℝ)*base68 + (10239328294286502727/1800250000000000000000000000000000 : ℝ)*base69 + (58697198832160497273/1800250000000000000000000000000000 : ℝ)*base72 + (106432836589561/36005000000000000000000000000 : ℝ)*base74 + (188811579226802502727/1800250000000000000000000000000000 : ℝ)*base75 + (6723070280137502727/1800250000000000000000000000000000 : ℝ)*base77 + (2940650581821502727/1800250000000000000000000000000000 : ℝ)*base79 + (111742376995321/36005000000000000000000000000 : ℝ)*base82 + (272211/1250000000000000000000 : ℝ)*base89 + (272211/1250000000000000000000 : ℝ)*base91 + (272211/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1704_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5247/1024 : ℝ) ≤ p) (hpb : p ≤ (5255/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (96489539/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (343/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9949/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9961/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1071/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1704_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1704_s4_0 (p : ℝ) (hpa : (5247/1024 : ℝ) ≤ p) (hpb : p ≤ (5255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-717028107/5000000000 : ℝ)*x 0 + (5473873007/10000000000 : ℝ)*x 1 + (5137528211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (717028107/5000000000 : ℝ)^5255 ≤ (8962633844239/100000000000000 : ℝ)^4231 := by
    have hnat : (717028107 : ℕ)^5255*100000000000000^4231 ≤ 8962633844239^4231*5000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      717028107 5000000000 8962633844239 100000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5473873007/10000000000 : ℝ)^5255 ≤ (11827582505937/25000000000000 : ℝ)^4231 := by
    have hnat : (5473873007 : ℕ)^5255*25000000000000^4231 ≤ 11827582505937^4231*10000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5473873007 10000000000 11827582505937 25000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5137528211/10000000000 : ℝ)^5255 ≤ (21863518058103/50000000000000 : ℝ)^4231 := by
    have hnat : (5137528211 : ℕ)^5255*50000000000000^4231 ≤ 21863518058103^4231*10000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5137528211 10000000000 21863518058103 50000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5255/1024 : ℝ)) 5255 4231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-717028107/5000000000 : ℝ), (5473873007/10000000000 : ℝ), (5137528211/10000000000 : ℝ)] ![(8962633844239/100000000000000 : ℝ), (11827582505937/25000000000000 : ℝ), (21863518058103/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-717028107/5000000000 : ℝ)|^5255 ≤ (8962633844239/100000000000000 : ℝ)^4231
        have hw : |(-717028107/5000000000 : ℝ)|=(717028107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5473873007/10000000000 : ℝ)|^5255 ≤ (11827582505937/25000000000000 : ℝ)^4231
        have hw : |(5473873007/10000000000 : ℝ)|=(5473873007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5137528211/10000000000 : ℝ)|^5255 ≤ (21863518058103/50000000000000 : ℝ)^4231
        have hw : |(5137528211/10000000000 : ℝ)|=(5137528211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1704_s4_1 (p : ℝ) (hpa : (5247/1024 : ℝ) ≤ p) (hpb : p ≤ (5255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (213821017/400000000 : ℝ)*x 0 + (-4021369/25000000 : ℝ)*x 1 + (5137528231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213821017/400000000 : ℝ)^5255 ≤ (9187297324603/20000000000000 : ℝ)^4231 := by
    have hnat : (213821017 : ℕ)^5255*20000000000000^4231 ≤ 9187297324603^4231*400000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213821017 400000000 9187297324603 20000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4021369/25000000 : ℝ)^5255 ≤ (5168238517503/50000000000000 : ℝ)^4231 := by
    have hnat : (4021369 : ℕ)^5255*50000000000000^4231 ≤ 5168238517503^4231*25000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4021369 25000000 5168238517503 50000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5137528231/10000000000 : ℝ)^5255 ≤ (43727036327631/100000000000000 : ℝ)^4231 := by
    have hnat : (5137528231 : ℕ)^5255*100000000000000^4231 ≤ 43727036327631^4231*10000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5137528231 10000000000 43727036327631 100000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5255/1024 : ℝ)) 5255 4231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213821017/400000000 : ℝ), (-4021369/25000000 : ℝ), (5137528231/10000000000 : ℝ)] ![(9187297324603/20000000000000 : ℝ), (5168238517503/50000000000000 : ℝ), (43727036327631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213821017/400000000 : ℝ)|^5255 ≤ (9187297324603/20000000000000 : ℝ)^4231
        have hw : |(213821017/400000000 : ℝ)|=(213821017/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4021369/25000000 : ℝ)|^5255 ≤ (5168238517503/50000000000000 : ℝ)^4231
        have hw : |(-4021369/25000000 : ℝ)|=(4021369/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5137528231/10000000000 : ℝ)|^5255 ≤ (43727036327631/100000000000000 : ℝ)^4231
        have hw : |(5137528231/10000000000 : ℝ)|=(5137528231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1704_s4_2 (p : ℝ) (hpa : (5247/1024 : ℝ) ≤ p) (hpb : p ≤ (5255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-358552441/2500000000 : ℝ)*x 0 + (1028246433/2000000000 : ℝ)*x 1 + (5470113799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (358552441/2500000000 : ℝ)^5255 ≤ (4481912892431/50000000000000 : ℝ)^4231 := by
    have hnat : (358552441 : ℕ)^5255*50000000000000^4231 ≤ 4481912892431^4231*2500000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      358552441 2500000000 4481912892431 50000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1028246433/2000000000 : ℝ)^5255 ≤ (21883097440417/50000000000000 : ℝ)^4231 := by
    have hnat : (1028246433 : ℕ)^5255*50000000000000^4231 ≤ 21883097440417^4231*2000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028246433 2000000000 21883097440417 50000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5470113799/10000000000 : ℝ)^5255 ≤ (47269979310919/100000000000000 : ℝ)^4231 := by
    have hnat : (5470113799 : ℕ)^5255*100000000000000^4231 ≤ 47269979310919^4231*10000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5470113799 10000000000 47269979310919 100000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5255/1024 : ℝ)) 5255 4231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-358552441/2500000000 : ℝ), (1028246433/2000000000 : ℝ), (5470113799/10000000000 : ℝ)] ![(4481912892431/50000000000000 : ℝ), (21883097440417/50000000000000 : ℝ), (47269979310919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-358552441/2500000000 : ℝ)|^5255 ≤ (4481912892431/50000000000000 : ℝ)^4231
        have hw : |(-358552441/2500000000 : ℝ)|=(358552441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1028246433/2000000000 : ℝ)|^5255 ≤ (21883097440417/50000000000000 : ℝ)^4231
        have hw : |(1028246433/2000000000 : ℝ)|=(1028246433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5470113799/10000000000 : ℝ)|^5255 ≤ (47269979310919/100000000000000 : ℝ)^4231
        have hw : |(5470113799/10000000000 : ℝ)|=(5470113799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1704_s4_3 (p : ℝ) (hpa : (5247/1024 : ℝ) ≤ p) (hpb : p ≤ (5255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2627757007/5000000000 : ℝ)*x 0 + (-79747673/625000000 : ℝ)*x 1 + (5470113037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2627757007/5000000000 : ℝ)^5255 ≤ (44977737481787/100000000000000 : ℝ)^4231 := by
    have hnat : (2627757007 : ℕ)^5255*100000000000000^4231 ≤ 44977737481787^4231*5000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627757007 5000000000 44977737481787 100000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (79747673/625000000 : ℝ)^5255 ≤ (30282388187/390625000000 : ℝ)^4231 := by
    have hnat : (79747673 : ℕ)^5255*390625000000^4231 ≤ 30282388187^4231*625000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79747673 625000000 30282388187 390625000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5470113037/10000000000 : ℝ)^5255 ≤ (23634985566209/50000000000000 : ℝ)^4231 := by
    have hnat : (5470113037 : ℕ)^5255*50000000000000^4231 ≤ 23634985566209^4231*10000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5470113037 10000000000 23634985566209 50000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5255/1024 : ℝ)) 5255 4231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2627757007/5000000000 : ℝ), (-79747673/625000000 : ℝ), (5470113037/10000000000 : ℝ)] ![(44977737481787/100000000000000 : ℝ), (30282388187/390625000000 : ℝ), (23634985566209/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2627757007/5000000000 : ℝ)|^5255 ≤ (44977737481787/100000000000000 : ℝ)^4231
        have hw : |(2627757007/5000000000 : ℝ)|=(2627757007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-79747673/625000000 : ℝ)|^5255 ≤ (30282388187/390625000000 : ℝ)^4231
        have hw : |(-79747673/625000000 : ℝ)|=(79747673/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5470113037/10000000000 : ℝ)|^5255 ≤ (23634985566209/50000000000000 : ℝ)^4231
        have hw : |(5470113037/10000000000 : ℝ)|=(5470113037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1704_s4_4 (p : ℝ) (hpa : (5247/1024 : ℝ) ≤ p) (hpb : p ≤ (5255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5255515229/10000000000 : ℝ)*x 0 + (5470111721/10000000000 : ℝ)*x 1 + (-1275962929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5255515229/10000000000 : ℝ)^5255 ≤ (702777349947/1562500000000 : ℝ)^4231 := by
    have hnat : (5255515229 : ℕ)^5255*1562500000000^4231 ≤ 702777349947^4231*10000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255515229 10000000000 702777349947 1562500000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5470111721/10000000000 : ℝ)^5255 ≤ (47269957007869/100000000000000 : ℝ)^4231 := by
    have hnat : (5470111721 : ℕ)^5255*100000000000000^4231 ≤ 47269957007869^4231*10000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5470111721 10000000000 47269957007869 100000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1275962929/10000000000 : ℝ)^5255 ≤ (7752292590791/100000000000000 : ℝ)^4231 := by
    have hnat : (1275962929 : ℕ)^5255*100000000000000^4231 ≤ 7752292590791^4231*10000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1275962929 10000000000 7752292590791 100000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5255/1024 : ℝ)) 5255 4231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5255515229/10000000000 : ℝ), (5470111721/10000000000 : ℝ), (-1275962929/10000000000 : ℝ)] ![(702777349947/1562500000000 : ℝ), (47269957007869/100000000000000 : ℝ), (7752292590791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5255515229/10000000000 : ℝ)|^5255 ≤ (702777349947/1562500000000 : ℝ)^4231
        have hw : |(5255515229/10000000000 : ℝ)|=(5255515229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5470111721/10000000000 : ℝ)|^5255 ≤ (47269957007869/100000000000000 : ℝ)^4231
        have hw : |(5470111721/10000000000 : ℝ)|=(5470111721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1275962929/10000000000 : ℝ)|^5255 ≤ (7752292590791/100000000000000 : ℝ)^4231
        have hw : |(-1275962929/10000000000 : ℝ)|=(1275962929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1704_s4_5 (p : ℝ) (hpa : (5247/1024 : ℝ) ≤ p) (hpb : p ≤ (5255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4112930399/10000000000 : ℝ)*x 0 + (184034707/400000000 : ℝ)*x 1 + (915102287/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4112930399/10000000000 : ℝ)^5255 ≤ (414645603823/1250000000000 : ℝ)^4231 := by
    have hnat : (4112930399 : ℕ)^5255*1250000000000^4231 ≤ 414645603823^4231*10000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4112930399 10000000000 414645603823 1250000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (184034707/400000000 : ℝ)^5255 ≤ (9531893026311/25000000000000 : ℝ)^4231 := by
    have hnat : (184034707 : ℕ)^5255*25000000000000^4231 ≤ 9531893026311^4231*400000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      184034707 400000000 9531893026311 25000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (915102287/2500000000 : ℝ)^5255 ≤ (7175194894713/25000000000000 : ℝ)^4231 := by
    have hnat : (915102287 : ℕ)^5255*25000000000000^4231 ≤ 7175194894713^4231*2500000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      915102287 2500000000 7175194894713 25000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5255/1024 : ℝ)) 5255 4231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4112930399/10000000000 : ℝ), (184034707/400000000 : ℝ), (915102287/2500000000 : ℝ)] ![(414645603823/1250000000000 : ℝ), (9531893026311/25000000000000 : ℝ), (7175194894713/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4112930399/10000000000 : ℝ)|^5255 ≤ (414645603823/1250000000000 : ℝ)^4231
        have hw : |(4112930399/10000000000 : ℝ)|=(4112930399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(184034707/400000000 : ℝ)|^5255 ≤ (9531893026311/25000000000000 : ℝ)^4231
        have hw : |(184034707/400000000 : ℝ)|=(184034707/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(915102287/2500000000 : ℝ)|^5255 ≤ (7175194894713/25000000000000 : ℝ)^4231
        have hw : |(915102287/2500000000 : ℝ)|=(915102287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1704_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5247/1024 : ℝ) ≤ p) (hpb : p ≤ (5255/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (96489539/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1071/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9961/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9961/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3427/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1071/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9961/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1071/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9961/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1071/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9961/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1071/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9961/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1071/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9961/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1071/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9961/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9961/100000 : ℝ) ^ (5247/1024 : ℝ) ≤ (736683237101517/100000000000000000000 : ℝ) := by
    have hpowers : (9961/100000 : ℝ)^5247 ≤ (736683237101517/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9961 : ℕ)^5247*100000000000000000000^1024 ≤ 736683237101517^1024*100000^5247 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9961 100000 736683237101517 100000000000000000000 5247 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9961/100000 : ℝ)) (X := (736683237101517/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5247 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1071/6250 : ℝ) ^ (5247/1024 : ℝ) ≤ (11872278737461561/100000000000000000000 : ℝ) := by
    have hpowers : (1071/6250 : ℝ)^5247 ≤ (11872278737461561/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1071 : ℕ)^5247*100000000000000000000^1024 ≤ 11872278737461561^1024*6250^5247 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1071 6250 11872278737461561 100000000000000000000 5247 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1071/6250 : ℝ)) (X := (11872278737461561/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5247 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000736683237101517/50000000000000000000 : ℝ) ≤ (625001797120169/625000000000000 : ℝ) ^ (5247/1024 : ℝ) := by
    have hpowers : (50000736683237101517/50000000000000000000 : ℝ)^1024 ≤ (625001797120169/625000000000000 : ℝ)^5247 := by
      have hnat : (50000736683237101517 : ℕ)^1024*625000000000000^5247 ≤ 625001797120169^5247*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000736683237101517 50000000000000000000 625001797120169 625000000000000 1024 5247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625001797120169/625000000000000 : ℝ)) (X := (50000736683237101517/50000000000000000000 : ℝ)) (by norm_num) 5247 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50006304480987281539/50000000000000000000 : ℝ) ≤ (10000246062930529/10000000000000000 : ℝ) ^ (5247/1024 : ℝ) := by
    have hpowers : (50006304480987281539/50000000000000000000 : ℝ)^1024 ≤ (10000246062930529/10000000000000000 : ℝ)^5247 := by
      have hnat : (50006304480987281539 : ℕ)^1024*10000000000000000^5247 ≤ 10000246062930529^5247*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006304480987281539 50000000000000000000 10000246062930529 10000000000000000 1024 5247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000246062930529/10000000000000000 : ℝ)) (X := (50006304480987281539/50000000000000000000 : ℝ)) (by norm_num) 5247 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50011872278737461561/50000000000000000000 : ℝ) ≤ (5000231685969177/5000000000000000 : ℝ) ^ (5247/1024 : ℝ) := by
    have hpowers : (50011872278737461561/50000000000000000000 : ℝ)^1024 ≤ (5000231685969177/5000000000000000 : ℝ)^5247 := by
      have hnat : (50011872278737461561 : ℕ)^1024*5000000000000000^5247 ≤ 5000231685969177^5247*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50011872278737461561 50000000000000000000 5000231685969177 5000000000000000 1024 5247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000231685969177/5000000000000000 : ℝ)) (X := (50011872278737461561/50000000000000000000 : ℝ)) (by norm_num) 5247 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(736683237101517/100000000000000000000 : ℝ) ≤ ((204988220226690033/205000000000000000 : ℝ)+2*(1241765759/4100000000000 : ℝ)*(9961/100000 : ℝ))^(5247/1024 : ℝ) := by
    rw [show (204988220226690033/205000000000000000 : ℝ)+2*(1241765759/4100000000000 : ℝ)*(9961/100000 : ℝ)=(625001797120169/625000000000000 : ℝ) by norm_num, show 1+2*(736683237101517/100000000000000000000 : ℝ)=(50000736683237101517/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11872278737461561/100000000000000000000 : ℝ)+(736683237101517/100000000000000000000 : ℝ) ≤ ((204988220226690033/205000000000000000 : ℝ)+(1241765759/4100000000000 : ℝ)*((1071/6250 : ℝ)+(9961/100000 : ℝ)))^(5247/1024 : ℝ) := by
    rw [show (204988220226690033/205000000000000000 : ℝ)+(1241765759/4100000000000 : ℝ)*((1071/6250 : ℝ)+(9961/100000 : ℝ))=(10000246062930529/10000000000000000 : ℝ) by norm_num, show 1+(11872278737461561/100000000000000000000 : ℝ)+(736683237101517/100000000000000000000 : ℝ)=(50006304480987281539/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11872278737461561/100000000000000000000 : ℝ) ≤ ((204988220226690033/205000000000000000 : ℝ)+2*(1241765759/4100000000000 : ℝ)*(1071/6250 : ℝ))^(5247/1024 : ℝ) := by
    rw [show (204988220226690033/205000000000000000 : ℝ)+2*(1241765759/4100000000000 : ℝ)*(1071/6250 : ℝ)=(5000231685969177/5000000000000000 : ℝ) by norm_num, show 1+2*(11872278737461561/100000000000000000000 : ℝ)=(50011872278737461561/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (204988220226690033/205000000000000000 : ℝ)*(X 1 0+X 2 0)+(1241765759/4100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5247/1024 : ℝ)) (lo := (9961/100000 : ℝ)) (hi := (1071/6250 : ℝ)) (c := (204988220226690033/205000000000000000 : ℝ)) (alpha := (1241765759/4100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (204988220226690033/205000000000000000 : ℝ)*(X 0 1+X 2 1)+(1241765759/4100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5247/1024 : ℝ)) (lo := (9961/100000 : ℝ)) (hi := (1071/6250 : ℝ)) (c := (204988220226690033/205000000000000000 : ℝ)) (alpha := (1241765759/4100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (204988220226690033/205000000000000000 : ℝ)*(X 0 2+X 1 2)+(1241765759/4100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5247/1024 : ℝ)) (lo := (9961/100000 : ℝ)) (hi := (1071/6250 : ℝ)) (c := (204988220226690033/205000000000000000 : ℝ)) (alpha := (1241765759/4100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-717028107/5000000000 : ℝ)*X 0 0+(5473873007/10000000000 : ℝ)*X 0 1+(5137528211/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1704_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((213821017/400000000 : ℝ)*X 1 0+(-4021369/25000000 : ℝ)*X 1 1+(5137528231/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1704_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-358552441/2500000000 : ℝ)*X 0 0+(1028246433/2000000000 : ℝ)*X 0 1+(5470113799/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1704_s4_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2627757007/5000000000 : ℝ)*X 1 0+(-79747673/625000000 : ℝ)*X 1 1+(5470113037/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1704_s4_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((5255515229/10000000000 : ℝ)*X 2 0+(5470111721/10000000000 : ℝ)*X 2 1+(-1275962929/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1704_s4_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4112930399/10000000000 : ℝ)*X 0 0+(184034707/400000000 : ℝ)*X 0 1+(915102287/2500000000 : ℝ)*X 0 2+(4112930399/10000000000 : ℝ)*X 1 0+(184034707/400000000 : ℝ)*X 1 1+(915102287/2500000000 : ℝ)*X 1 2+(4112930399/10000000000 : ℝ)*X 2 0+(184034707/400000000 : ℝ)*X 2 1+(915102287/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1704_s4_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18091140072698384067780117/5125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (444440289/50000000000000 : ℝ)*(base19) + (900994679/50000000000000 : ℝ)*(base23) + (100247299/50000000000000 : ℝ)*(lower1) + (134074841/100000000000000 : ℝ)*(lower4) + (29235697/10000000000000 : ℝ)*(upper5) + (2051961040001817/100000000000000 : ℝ)*(major0) + (2051961040001817/100000000000000 : ℝ)*(major1) + (2051961040001817/100000000000000 : ℝ)*(major2) + (3512603321/100000000000000 : ℝ)*(sp0) + (52490407/2000000000000 : ℝ)*(sp1) + (760152733521641/25000000000000 : ℝ)*(sp2) + (3040610933288957/100000000000000 : ℝ)*(sp3) + (1520306322350263/50000000000000 : ℝ)*(sp4) + (1063307515647793/100000000000000 : ℝ)*(sp5) + (1063307515647793/100000000000000 : ℝ)*(f.failure) + (608122889337977/20000000000000 : ℝ)*(f.sum) + (16411644191/102500000000000000000000000 : ℝ)*base66 + (12568124489939961/20500000000000000000000000000000 : ℝ)*base67 + (2161972935439961/20500000000000000000000000000000 : ℝ)*base69 + (39131553543439961/20500000000000000000000000000000 : ℝ)*base71 + (23006895899/25625000000000000000000000 : ℝ)*base74 + (60284058850560039/20500000000000000000000000000000 : ℝ)*base76 + (68703453270439961/20500000000000000000000000000000 : ℝ)*base77 + (115972626740439961/20500000000000000000000000000000 : ℝ)*base79 + (77764393553/205000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (17062573/5000000000000000000000 : ℝ)*base90 + (17062573/5000000000000000000000 : ℝ)*base92 + (17062573/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1704_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5247/1024 : ℝ) ≤ p) (hpb : p ≤ (5255/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (96489539/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1071/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9961/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9961/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3427/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1704_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1704_box_0 (p : ℝ) (hpa : (5247/1024 : ℝ) ≤ p) (hpb : p ≤ (5255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1110714353/10000000000 : ℝ)*x 0 + (169388217/312500000 : ℝ)*x 1 + (5420422027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1110714353/10000000000 : ℝ)^5255 ≤ (50980734139/781250000000 : ℝ)^4231 := by
    have hnat : (1110714353 : ℕ)^5255*781250000000^4231 ≤ 50980734139^4231*10000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1110714353 10000000000 50980734139 781250000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169388217/312500000 : ℝ)^5255 ≤ (23368618959213/50000000000000 : ℝ)^4231 := by
    have hnat : (169388217 : ℕ)^5255*50000000000000^4231 ≤ 23368618959213^4231*312500000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169388217 312500000 23368618959213 50000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5420422027/10000000000 : ℝ)^5255 ≤ (46737228098033/100000000000000 : ℝ)^4231 := by
    have hnat : (5420422027 : ℕ)^5255*100000000000000^4231 ≤ 46737228098033^4231*10000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420422027 10000000000 46737228098033 100000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5255/1024 : ℝ)) 5255 4231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1110714353/10000000000 : ℝ), (169388217/312500000 : ℝ), (5420422027/10000000000 : ℝ)] ![(50980734139/781250000000 : ℝ), (23368618959213/50000000000000 : ℝ), (46737228098033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1110714353/10000000000 : ℝ)|^5255 ≤ (50980734139/781250000000 : ℝ)^4231
        have hw : |(-1110714353/10000000000 : ℝ)|=(1110714353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169388217/312500000 : ℝ)|^5255 ≤ (23368618959213/50000000000000 : ℝ)^4231
        have hw : |(169388217/312500000 : ℝ)|=(169388217/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5420422027/10000000000 : ℝ)|^5255 ≤ (46737228098033/100000000000000 : ℝ)^4231
        have hw : |(5420422027/10000000000 : ℝ)|=(5420422027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1704_box_1 (p : ℝ) (hpa : (5247/1024 : ℝ) ≤ p) (hpb : p ≤ (5255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (653208011/1250000000 : ℝ)*x 0 + (-693712371/5000000000 : ℝ)*x 1 + (5420422957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (653208011/1250000000 : ℝ)^5255 ≤ (5582583327613/12500000000000 : ℝ)^4231 := by
    have hnat : (653208011 : ℕ)^5255*12500000000000^4231 ≤ 5582583327613^4231*1250000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653208011 1250000000 5582583327613 12500000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (693712371/5000000000 : ℝ)^5255 ≤ (1075261912927/12500000000000 : ℝ)^4231 := by
    have hnat : (693712371 : ℕ)^5255*12500000000000^4231 ≤ 1075261912927^4231*5000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      693712371 5000000000 1075261912927 12500000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5420422957/10000000000 : ℝ)^5255 ≤ (46737238057647/100000000000000 : ℝ)^4231 := by
    have hnat : (5420422957 : ℕ)^5255*100000000000000^4231 ≤ 46737238057647^4231*10000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420422957 10000000000 46737238057647 100000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5255/1024 : ℝ)) 5255 4231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(653208011/1250000000 : ℝ), (-693712371/5000000000 : ℝ), (5420422957/10000000000 : ℝ)] ![(5582583327613/12500000000000 : ℝ), (1075261912927/12500000000000 : ℝ), (46737238057647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(653208011/1250000000 : ℝ)|^5255 ≤ (5582583327613/12500000000000 : ℝ)^4231
        have hw : |(653208011/1250000000 : ℝ)|=(653208011/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-693712371/5000000000 : ℝ)|^5255 ≤ (1075261912927/12500000000000 : ℝ)^4231
        have hw : |(-693712371/5000000000 : ℝ)|=(693712371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5420422957/10000000000 : ℝ)|^5255 ≤ (46737238057647/100000000000000 : ℝ)^4231
        have hw : |(5420422957/10000000000 : ℝ)|=(5420422957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1704_box_2 (p : ℝ) (hpa : (5247/1024 : ℝ) ≤ p) (hpb : p ≤ (5255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (522566471/1000000000 : ℝ)*x 0 + (42347049/78125000 : ℝ)*x 1 + (-1387424837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (522566471/1000000000 : ℝ)^5255 ≤ (22330336611667/50000000000000 : ℝ)^4231 := by
    have hnat : (522566471 : ℕ)^5255*50000000000000^4231 ≤ 22330336611667^4231*1000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522566471 1000000000 22330336611667 50000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42347049/78125000 : ℝ)^5255 ≤ (23368615360901/50000000000000 : ℝ)^4231 := by
    have hnat : (42347049 : ℕ)^5255*50000000000000^4231 ≤ 23368615360901^4231*78125000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42347049 78125000 23368615360901 50000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1387424837/10000000000 : ℝ)^5255 ≤ (8602096034973/100000000000000 : ℝ)^4231 := by
    have hnat : (1387424837 : ℕ)^5255*100000000000000^4231 ≤ 8602096034973^4231*10000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1387424837 10000000000 8602096034973 100000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5255/1024 : ℝ)) 5255 4231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(522566471/1000000000 : ℝ), (42347049/78125000 : ℝ), (-1387424837/10000000000 : ℝ)] ![(22330336611667/50000000000000 : ℝ), (23368615360901/50000000000000 : ℝ), (8602096034973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(522566471/1000000000 : ℝ)|^5255 ≤ (22330336611667/50000000000000 : ℝ)^4231
        have hw : |(522566471/1000000000 : ℝ)|=(522566471/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42347049/78125000 : ℝ)|^5255 ≤ (23368615360901/50000000000000 : ℝ)^4231
        have hw : |(42347049/78125000 : ℝ)|=(42347049/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1387424837/10000000000 : ℝ)|^5255 ≤ (8602096034973/100000000000000 : ℝ)^4231
        have hw : |(-1387424837/10000000000 : ℝ)|=(1387424837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1704_box_3 (p : ℝ) (hpa : (5247/1024 : ℝ) ≤ p) (hpb : p ≤ (5255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1123753757/2500000000 : ℝ)*x 0 + (61611609/156250000 : ℝ)*x 1 + (3943142731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1123753757/2500000000 : ℝ)^5255 ≤ (37041114239277/100000000000000 : ℝ)^4231 := by
    have hnat : (1123753757 : ℕ)^5255*100000000000000^4231 ≤ 37041114239277^4231*2500000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123753757 2500000000 37041114239277 100000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (61611609/156250000 : ℝ)^5255 ≤ (3934930511057/12500000000000 : ℝ)^4231 := by
    have hnat : (61611609 : ℕ)^5255*12500000000000^4231 ≤ 3934930511057^4231*156250000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61611609 156250000 3934930511057 12500000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3943142731/10000000000 : ℝ)^5255 ≤ (31479441659161/100000000000000 : ℝ)^4231 := by
    have hnat : (3943142731 : ℕ)^5255*100000000000000^4231 ≤ 31479441659161^4231*10000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3943142731 10000000000 31479441659161 100000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5255/1024 : ℝ)) 5255 4231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1123753757/2500000000 : ℝ), (61611609/156250000 : ℝ), (3943142731/10000000000 : ℝ)] ![(37041114239277/100000000000000 : ℝ), (3934930511057/12500000000000 : ℝ), (31479441659161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1123753757/2500000000 : ℝ)|^5255 ≤ (37041114239277/100000000000000 : ℝ)^4231
        have hw : |(1123753757/2500000000 : ℝ)|=(1123753757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(61611609/156250000 : ℝ)|^5255 ≤ (3934930511057/12500000000000 : ℝ)^4231
        have hw : |(61611609/156250000 : ℝ)|=(61611609/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3943142731/10000000000 : ℝ)|^5255 ≤ (31479441659161/100000000000000 : ℝ)^4231
        have hw : |(3943142731/10000000000 : ℝ)|=(3943142731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1704_box_4 (p : ℝ) (hpa : (5247/1024 : ℝ) ≤ p) (hpb : p ≤ (5255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-444531691/2500000000 : ℝ)*x 0 + (323573939/625000000 : ℝ)*x 1 + (2588591343/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (444531691/2500000000 : ℝ)^5255 ≤ (11706749467553/100000000000000 : ℝ)^4231 := by
    have hnat : (444531691 : ℕ)^5255*100000000000000^4231 ≤ 11706749467553^4231*2500000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      444531691 2500000000 11706749467553 100000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (323573939/625000000 : ℝ)^5255 ≤ (44146627051369/100000000000000 : ℝ)^4231 := by
    have hnat : (323573939 : ℕ)^5255*100000000000000^4231 ≤ 44146627051369^4231*625000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323573939 625000000 44146627051369 100000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2588591343/5000000000 : ℝ)^5255 ≤ (22073311735819/50000000000000 : ℝ)^4231 := by
    have hnat : (2588591343 : ℕ)^5255*50000000000000^4231 ≤ 22073311735819^4231*5000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588591343 5000000000 22073311735819 50000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5255/1024 : ℝ)) 5255 4231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-444531691/2500000000 : ℝ), (323573939/625000000 : ℝ), (2588591343/5000000000 : ℝ)] ![(11706749467553/100000000000000 : ℝ), (44146627051369/100000000000000 : ℝ), (22073311735819/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-444531691/2500000000 : ℝ)|^5255 ≤ (11706749467553/100000000000000 : ℝ)^4231
        have hw : |(-444531691/2500000000 : ℝ)|=(444531691/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(323573939/625000000 : ℝ)|^5255 ≤ (44146627051369/100000000000000 : ℝ)^4231
        have hw : |(323573939/625000000 : ℝ)|=(323573939/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2588591343/5000000000 : ℝ)|^5255 ≤ (22073311735819/50000000000000 : ℝ)^4231
        have hw : |(2588591343/5000000000 : ℝ)|=(2588591343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1704_box_5 (p : ℝ) (hpa : (5247/1024 : ℝ) ≤ p) (hpb : p ≤ (5255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5390863331/10000000000 : ℝ)*x 0 + (-46696353/312500000 : ℝ)*x 1 + (5177182297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5390863331/10000000000 : ℝ)^5255 ≤ (46420885458593/100000000000000 : ℝ)^4231 := by
    have hnat : (5390863331 : ℕ)^5255*100000000000000^4231 ≤ 46420885458593^4231*10000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390863331 10000000000 46420885458593 100000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (46696353/312500000 : ℝ)^5255 ≤ (4716247584761/50000000000000 : ℝ)^4231 := by
    have hnat : (46696353 : ℕ)^5255*50000000000000^4231 ≤ 4716247584761^4231*312500000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46696353 312500000 4716247584761 50000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5177182297/10000000000 : ℝ)^5255 ≤ (4414661935177/10000000000000 : ℝ)^4231 := by
    have hnat : (5177182297 : ℕ)^5255*10000000000000^4231 ≤ 4414661935177^4231*10000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177182297 10000000000 4414661935177 10000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5255/1024 : ℝ)) 5255 4231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5390863331/10000000000 : ℝ), (-46696353/312500000 : ℝ), (5177182297/10000000000 : ℝ)] ![(46420885458593/100000000000000 : ℝ), (4716247584761/50000000000000 : ℝ), (4414661935177/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5390863331/10000000000 : ℝ)|^5255 ≤ (46420885458593/100000000000000 : ℝ)^4231
        have hw : |(5390863331/10000000000 : ℝ)|=(5390863331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-46696353/312500000 : ℝ)|^5255 ≤ (4716247584761/50000000000000 : ℝ)^4231
        have hw : |(-46696353/312500000 : ℝ)|=(46696353/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5177182297/10000000000 : ℝ)|^5255 ≤ (4414661935177/10000000000000 : ℝ)^4231
        have hw : |(5177182297/10000000000 : ℝ)|=(5177182297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1704_box_6 (p : ℝ) (hpa : (5247/1024 : ℝ) ≤ p) (hpb : p ≤ (5255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5390863803/10000000000 : ℝ)*x 0 + (258859099/500000000 : ℝ)*x 1 + (-1494283081/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5390863803/10000000000 : ℝ)^5255 ≤ (1160522262667/2500000000000 : ℝ)^4231 := by
    have hnat : (5390863803 : ℕ)^5255*2500000000000^4231 ≤ 1160522262667^4231*10000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390863803 10000000000 1160522262667 2500000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (258859099/500000000 : ℝ)^5255 ≤ (2759163499653/6250000000000 : ℝ)^4231 := by
    have hnat : (258859099 : ℕ)^5255*6250000000000^4231 ≤ 2759163499653^4231*500000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258859099 500000000 2759163499653 6250000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1494283081/10000000000 : ℝ)^5255 ≤ (4716246741947/50000000000000 : ℝ)^4231 := by
    have hnat : (1494283081 : ℕ)^5255*50000000000000^4231 ≤ 4716246741947^4231*10000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1494283081 10000000000 4716246741947 50000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5255/1024 : ℝ)) 5255 4231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5390863803/10000000000 : ℝ), (258859099/500000000 : ℝ), (-1494283081/10000000000 : ℝ)] ![(1160522262667/2500000000000 : ℝ), (2759163499653/6250000000000 : ℝ), (4716246741947/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5390863803/10000000000 : ℝ)|^5255 ≤ (1160522262667/2500000000000 : ℝ)^4231
        have hw : |(5390863803/10000000000 : ℝ)|=(5390863803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(258859099/500000000 : ℝ)|^5255 ≤ (2759163499653/6250000000000 : ℝ)^4231
        have hw : |(258859099/500000000 : ℝ)|=(258859099/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1494283081/10000000000 : ℝ)|^5255 ≤ (4716246741947/50000000000000 : ℝ)^4231
        have hw : |(-1494283081/10000000000 : ℝ)|=(1494283081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1704_box_7 (p : ℝ) (hpa : (5247/1024 : ℝ) ≤ p) (hpb : p ≤ (5255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (58041081/156250000 : ℝ)*x 0 + (2166249379/5000000000 : ℝ)*x 1 + (4332499063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (58041081/156250000 : ℝ)^5255 ≤ (29229746410339/100000000000000 : ℝ)^4231 := by
    have hnat : (58041081 : ℕ)^5255*100000000000000^4231 ≤ 29229746410339^4231*156250000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58041081 156250000 29229746410339 100000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2166249379/5000000000 : ℝ)^5255 ≤ (17692562618921/50000000000000 : ℝ)^4231 := by
    have hnat : (2166249379 : ℕ)^5255*50000000000000^4231 ≤ 17692562618921^4231*5000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166249379 5000000000 17692562618921 50000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4332499063/10000000000 : ℝ)^5255 ≤ (17692564165891/50000000000000 : ℝ)^4231 := by
    have hnat : (4332499063 : ℕ)^5255*50000000000000^4231 ≤ 17692564165891^4231*10000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4332499063 10000000000 17692564165891 50000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5255/1024 : ℝ)) 5255 4231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(58041081/156250000 : ℝ), (2166249379/5000000000 : ℝ), (4332499063/10000000000 : ℝ)] ![(29229746410339/100000000000000 : ℝ), (17692562618921/50000000000000 : ℝ), (17692564165891/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(58041081/156250000 : ℝ)|^5255 ≤ (29229746410339/100000000000000 : ℝ)^4231
        have hw : |(58041081/156250000 : ℝ)|=(58041081/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2166249379/5000000000 : ℝ)|^5255 ≤ (17692562618921/50000000000000 : ℝ)^4231
        have hw : |(2166249379/5000000000 : ℝ)|=(2166249379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4332499063/10000000000 : ℝ)|^5255 ≤ (17692564165891/50000000000000 : ℝ)^4231
        have hw : |(4332499063/10000000000 : ℝ)|=(4332499063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1704_box_8 (p : ℝ) (hpa : (5247/1024 : ℝ) ≤ p) (hpb : p ≤ (5255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-40866819/250000000 : ℝ)*x 0 + (499796093/1000000000 : ℝ)*x 1 + (5463414087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (40866819/250000000 : ℝ)^5255 ≤ (421815814427/4000000000000 : ℝ)^4231 := by
    have hnat : (40866819 : ℕ)^5255*4000000000000^4231 ≤ 421815814427^4231*250000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40866819 250000000 421815814427 4000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (499796093/1000000000 : ℝ)^5255 ≤ (1056413056657/2500000000000 : ℝ)^4231 := by
    have hnat : (499796093 : ℕ)^5255*2500000000000^4231 ≤ 1056413056657^4231*1000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499796093 1000000000 1056413056657 2500000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5463414087/10000000000 : ℝ)^5255 ≤ (47198082357621/100000000000000 : ℝ)^4231 := by
    have hnat : (5463414087 : ℕ)^5255*100000000000000^4231 ≤ 47198082357621^4231*10000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5463414087 10000000000 47198082357621 100000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5255/1024 : ℝ)) 5255 4231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-40866819/250000000 : ℝ), (499796093/1000000000 : ℝ), (5463414087/10000000000 : ℝ)] ![(421815814427/4000000000000 : ℝ), (1056413056657/2500000000000 : ℝ), (47198082357621/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-40866819/250000000 : ℝ)|^5255 ≤ (421815814427/4000000000000 : ℝ)^4231
        have hw : |(-40866819/250000000 : ℝ)|=(40866819/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(499796093/1000000000 : ℝ)|^5255 ≤ (1056413056657/2500000000000 : ℝ)^4231
        have hw : |(499796093/1000000000 : ℝ)|=(499796093/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5463414087/10000000000 : ℝ)|^5255 ≤ (47198082357621/100000000000000 : ℝ)^4231
        have hw : |(5463414087/10000000000 : ℝ)|=(5463414087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1704_box_9 (p : ℝ) (hpa : (5247/1024 : ℝ) ≤ p) (hpb : p ≤ (5255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5196483503/10000000000 : ℝ)*x 0 + (-1367742083/10000000000 : ℝ)*x 1 + (5463414127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5196483503/10000000000 : ℝ)^5255 ≤ (1108778225423/2500000000000 : ℝ)^4231 := by
    have hnat : (5196483503 : ℕ)^5255*2500000000000^4231 ≤ 1108778225423^4231*10000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196483503 10000000000 1108778225423 2500000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1367742083/10000000000 : ℝ)^5255 ≤ (4225394089313/50000000000000 : ℝ)^4231 := by
    have hnat : (1367742083 : ℕ)^5255*50000000000000^4231 ≤ 4225394089313^4231*10000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367742083 10000000000 4225394089313 50000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5463414127/10000000000 : ℝ)^5255 ≤ (47198082786811/100000000000000 : ℝ)^4231 := by
    have hnat : (5463414127 : ℕ)^5255*100000000000000^4231 ≤ 47198082786811^4231*10000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5463414127 10000000000 47198082786811 100000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5255/1024 : ℝ)) 5255 4231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5196483503/10000000000 : ℝ), (-1367742083/10000000000 : ℝ), (5463414127/10000000000 : ℝ)] ![(1108778225423/2500000000000 : ℝ), (4225394089313/50000000000000 : ℝ), (47198082786811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5196483503/10000000000 : ℝ)|^5255 ≤ (1108778225423/2500000000000 : ℝ)^4231
        have hw : |(5196483503/10000000000 : ℝ)|=(5196483503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1367742083/10000000000 : ℝ)|^5255 ≤ (4225394089313/50000000000000 : ℝ)^4231
        have hw : |(-1367742083/10000000000 : ℝ)|=(1367742083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5463414127/10000000000 : ℝ)|^5255 ≤ (47198082786811/100000000000000 : ℝ)^4231
        have hw : |(5463414127/10000000000 : ℝ)|=(5463414127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1704_box_10 (p : ℝ) (hpa : (5247/1024 : ℝ) ≤ p) (hpb : p ≤ (5255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1039296649/2000000000 : ℝ)*x 0 + (8741463/16000000 : ℝ)*x 1 + (-683871047/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1039296649/2000000000 : ℝ)^5255 ≤ (44351126282001/100000000000000 : ℝ)^4231 := by
    have hnat : (1039296649 : ℕ)^5255*100000000000000^4231 ≤ 44351126282001^4231*2000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039296649 2000000000 44351126282001 100000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8741463/16000000 : ℝ)^5255 ≤ (47198085447791/100000000000000 : ℝ)^4231 := by
    have hnat : (8741463 : ℕ)^5255*100000000000000^4231 ≤ 47198085447791^4231*16000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8741463 16000000 47198085447791 100000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (683871047/5000000000 : ℝ)^5255 ≤ (13204356661/156250000000 : ℝ)^4231 := by
    have hnat : (683871047 : ℕ)^5255*156250000000^4231 ≤ 13204356661^4231*5000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683871047 5000000000 13204356661 156250000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5255/1024 : ℝ)) 5255 4231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1039296649/2000000000 : ℝ), (8741463/16000000 : ℝ), (-683871047/5000000000 : ℝ)] ![(44351126282001/100000000000000 : ℝ), (47198085447791/100000000000000 : ℝ), (13204356661/156250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1039296649/2000000000 : ℝ)|^5255 ≤ (44351126282001/100000000000000 : ℝ)^4231
        have hw : |(1039296649/2000000000 : ℝ)|=(1039296649/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8741463/16000000 : ℝ)|^5255 ≤ (47198085447791/100000000000000 : ℝ)^4231
        have hw : |(8741463/16000000 : ℝ)|=(8741463/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-683871047/5000000000 : ℝ)|^5255 ≤ (13204356661/156250000000 : ℝ)^4231
        have hw : |(-683871047/5000000000 : ℝ)|=(683871047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1704_box_11 (p : ℝ) (hpa : (5247/1024 : ℝ) ≤ p) (hpb : p ≤ (5255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1156986927/2500000000 : ℝ)*x 0 + (3874145139/10000000000 : ℝ)*x 1 + (774829019/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1156986927/2500000000 : ℝ)^5255 ≤ (3840649685559/10000000000000 : ℝ)^4231 := by
    have hnat : (1156986927 : ℕ)^5255*10000000000000^4231 ≤ 3840649685559^4231*2500000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1156986927 2500000000 3840649685559 10000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3874145139/10000000000 : ℝ)^5255 ≤ (7699187945343/25000000000000 : ℝ)^4231 := by
    have hnat : (3874145139 : ℕ)^5255*25000000000000^4231 ≤ 7699187945343^4231*10000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3874145139 10000000000 7699187945343 25000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (774829019/2000000000 : ℝ)^5255 ≤ (30796751346951/100000000000000 : ℝ)^4231 := by
    have hnat : (774829019 : ℕ)^5255*100000000000000^4231 ≤ 30796751346951^4231*2000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      774829019 2000000000 30796751346951 100000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5255/1024 : ℝ)) 5255 4231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1156986927/2500000000 : ℝ), (3874145139/10000000000 : ℝ), (774829019/2000000000 : ℝ)] ![(3840649685559/10000000000000 : ℝ), (7699187945343/25000000000000 : ℝ), (30796751346951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1156986927/2500000000 : ℝ)|^5255 ≤ (3840649685559/10000000000000 : ℝ)^4231
        have hw : |(1156986927/2500000000 : ℝ)|=(1156986927/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3874145139/10000000000 : ℝ)|^5255 ≤ (7699187945343/25000000000000 : ℝ)^4231
        have hw : |(3874145139/10000000000 : ℝ)|=(3874145139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(774829019/2000000000 : ℝ)|^5255 ≤ (30796751346951/100000000000000 : ℝ)^4231
        have hw : |(774829019/2000000000 : ℝ)|=(774829019/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1704_box_12 (p : ℝ) (hpa : (5247/1024 : ℝ) ≤ p) (hpb : p ≤ (5255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-312223479/2500000000 : ℝ)*x 0 + (2795522611/5000000000 : ℝ)*x 1 + (2575999533/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (312223479/2500000000 : ℝ)^5255 ≤ (7548554698929/100000000000000 : ℝ)^4231 := by
    have hnat : (312223479 : ℕ)^5255*100000000000000^4231 ≤ 7548554698929^4231*2500000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      312223479 2500000000 7548554698929 100000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2795522611/5000000000 : ℝ)^5255 ≤ (48571382324247/100000000000000 : ℝ)^4231 := by
    have hnat : (2795522611 : ℕ)^5255*100000000000000^4231 ≤ 48571382324247^4231*5000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2795522611 5000000000 48571382324247 100000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2575999533/5000000000 : ℝ)^5255 ≤ (21940031477813/50000000000000 : ℝ)^4231 := by
    have hnat : (2575999533 : ℕ)^5255*50000000000000^4231 ≤ 21940031477813^4231*5000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2575999533 5000000000 21940031477813 50000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5255/1024 : ℝ)) 5255 4231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-312223479/2500000000 : ℝ), (2795522611/5000000000 : ℝ), (2575999533/5000000000 : ℝ)] ![(7548554698929/100000000000000 : ℝ), (48571382324247/100000000000000 : ℝ), (21940031477813/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-312223479/2500000000 : ℝ)|^5255 ≤ (7548554698929/100000000000000 : ℝ)^4231
        have hw : |(-312223479/2500000000 : ℝ)|=(312223479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2795522611/5000000000 : ℝ)|^5255 ≤ (48571382324247/100000000000000 : ℝ)^4231
        have hw : |(2795522611/5000000000 : ℝ)|=(2795522611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2575999533/5000000000 : ℝ)|^5255 ≤ (21940031477813/50000000000000 : ℝ)^4231
        have hw : |(2575999533/5000000000 : ℝ)|=(2575999533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1704_box_13 (p : ℝ) (hpa : (5247/1024 : ℝ) ≤ p) (hpb : p ≤ (5255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5407996757/10000000000 : ℝ)*x 0 + (-300978357/2000000000 : ℝ)*x 1 + (2575999487/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5407996757/10000000000 : ℝ)^5255 ≤ (46604199558897/100000000000000 : ℝ)^4231 := by
    have hnat : (5407996757 : ℕ)^5255*100000000000000^4231 ≤ 46604199558897^4231*10000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407996757 10000000000 46604199558897 100000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (300978357/2000000000 : ℝ)^5255 ≤ (4757869221877/50000000000000 : ℝ)^4231 := by
    have hnat : (300978357 : ℕ)^5255*50000000000000^4231 ≤ 4757869221877^4231*2000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      300978357 2000000000 4757869221877 50000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2575999487/5000000000 : ℝ)^5255 ≤ (4388006198241/10000000000000 : ℝ)^4231 := by
    have hnat : (2575999487 : ℕ)^5255*10000000000000^4231 ≤ 4388006198241^4231*5000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2575999487 5000000000 4388006198241 10000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5255/1024 : ℝ)) 5255 4231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5407996757/10000000000 : ℝ), (-300978357/2000000000 : ℝ), (2575999487/5000000000 : ℝ)] ![(46604199558897/100000000000000 : ℝ), (4757869221877/50000000000000 : ℝ), (4388006198241/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5407996757/10000000000 : ℝ)|^5255 ≤ (46604199558897/100000000000000 : ℝ)^4231
        have hw : |(5407996757/10000000000 : ℝ)|=(5407996757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-300978357/2000000000 : ℝ)|^5255 ≤ (4757869221877/50000000000000 : ℝ)^4231
        have hw : |(-300978357/2000000000 : ℝ)|=(300978357/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2575999487/5000000000 : ℝ)|^5255 ≤ (4388006198241/10000000000000 : ℝ)^4231
        have hw : |(2575999487/5000000000 : ℝ)|=(2575999487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1704_box_14 (p : ℝ) (hpa : (5247/1024 : ℝ) ≤ p) (hpb : p ≤ (5255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (540799649/1000000000 : ℝ)*x 0 + (1030399799/2000000000 : ℝ)*x 1 + (-1504892121/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540799649/1000000000 : ℝ)^5255 ≤ (5825524587639/12500000000000 : ℝ)^4231 := by
    have hnat : (540799649 : ℕ)^5255*12500000000000^4231 ≤ 5825524587639^4231*1000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540799649 1000000000 5825524587639 12500000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1030399799/2000000000 : ℝ)^5255 ≤ (43880062204557/100000000000000 : ℝ)^4231 := by
    have hnat : (1030399799 : ℕ)^5255*100000000000000^4231 ≤ 43880062204557^4231*2000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030399799 2000000000 43880062204557 100000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1504892121/10000000000 : ℝ)^5255 ≤ (1189467635319/12500000000000 : ℝ)^4231 := by
    have hnat : (1504892121 : ℕ)^5255*12500000000000^4231 ≤ 1189467635319^4231*10000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1504892121 10000000000 1189467635319 12500000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5255/1024 : ℝ)) 5255 4231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540799649/1000000000 : ℝ), (1030399799/2000000000 : ℝ), (-1504892121/10000000000 : ℝ)] ![(5825524587639/12500000000000 : ℝ), (43880062204557/100000000000000 : ℝ), (1189467635319/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540799649/1000000000 : ℝ)|^5255 ≤ (5825524587639/12500000000000 : ℝ)^4231
        have hw : |(540799649/1000000000 : ℝ)|=(540799649/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1030399799/2000000000 : ℝ)|^5255 ≤ (43880062204557/100000000000000 : ℝ)^4231
        have hw : |(1030399799/2000000000 : ℝ)|=(1030399799/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1504892121/10000000000 : ℝ)|^5255 ≤ (1189467635319/12500000000000 : ℝ)^4231
        have hw : |(-1504892121/10000000000 : ℝ)|=(1504892121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1704_box_15 (p : ℝ) (hpa : (5247/1024 : ℝ) ≤ p) (hpb : p ≤ (5255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (907712099/2500000000 : ℝ)*x 0 + (874540549/2000000000 : ℝ)*x 1 + (437270167/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (907712099/2500000000 : ℝ)^5255 ≤ (5682636597347/20000000000000 : ℝ)^4231 := by
    have hnat : (907712099 : ℕ)^5255*20000000000000^4231 ≤ 5682636597347^4231*2500000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      907712099 2500000000 5682636597347 20000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (874540549/2000000000 : ℝ)^5255 ≤ (7158682792351/20000000000000 : ℝ)^4231 := by
    have hnat : (874540549 : ℕ)^5255*20000000000000^4231 ≤ 7158682792351^4231*2000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874540549 2000000000 7158682792351 20000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (437270167/1000000000 : ℝ)^5255 ≤ (35793403032481/100000000000000 : ℝ)^4231 := by
    have hnat : (437270167 : ℕ)^5255*100000000000000^4231 ≤ 35793403032481^4231*1000000000^5255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437270167 1000000000 35793403032481 100000000000000 5255 4231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5255/1024 : ℝ)) 5255 4231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(907712099/2500000000 : ℝ), (874540549/2000000000 : ℝ), (437270167/1000000000 : ℝ)] ![(5682636597347/20000000000000 : ℝ), (7158682792351/20000000000000 : ℝ), (35793403032481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(907712099/2500000000 : ℝ)|^5255 ≤ (5682636597347/20000000000000 : ℝ)^4231
        have hw : |(907712099/2500000000 : ℝ)|=(907712099/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(874540549/2000000000 : ℝ)|^5255 ≤ (7158682792351/20000000000000 : ℝ)^4231
        have hw : |(874540549/2000000000 : ℝ)|=(874540549/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(437270167/1000000000 : ℝ)|^5255 ≤ (35793403032481/100000000000000 : ℝ)^4231
        have hw : |(437270167/1000000000 : ℝ)|=(437270167/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1704_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5247/1024 : ℝ) ≤ p) (hpb : p ≤ (5255/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (96489539/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3427/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9961/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(16673/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29131/50000 : ℝ) ∧ (20321/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (90337/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3427/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9961/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3427/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9961/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3427/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9961/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3427/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9961/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3427/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9961/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3427/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9961/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9961/100000 : ℝ) ^ (5247/1024 : ℝ) ≤ (736683237101517/100000000000000000000 : ℝ) := by
    have hpowers : (9961/100000 : ℝ)^5247 ≤ (736683237101517/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9961 : ℕ)^5247*100000000000000000000^1024 ≤ 736683237101517^1024*100000^5247 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9961 100000 736683237101517 100000000000000000000 5247 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9961/100000 : ℝ)) (X := (736683237101517/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5247 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3427/20000 : ℝ) ^ (5247/1024 : ℝ) ≤ (1483591138031449/12500000000000000000 : ℝ) := by
    have hpowers : (3427/20000 : ℝ)^5247 ≤ (1483591138031449/12500000000000000000 : ℝ)^1024 := by
      have hnat : (3427 : ℕ)^5247*12500000000000000000^1024 ≤ 1483591138031449^1024*20000^5247 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3427 20000 1483591138031449 12500000000000000000 5247 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3427/20000 : ℝ)) (X := (1483591138031449/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 5247 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000736683237101517/50000000000000000000 : ℝ) ≤ (625001797120169/625000000000000 : ℝ) ^ (5247/1024 : ℝ) := by
    have hpowers : (50000736683237101517/50000000000000000000 : ℝ)^1024 ≤ (625001797120169/625000000000000 : ℝ)^5247 := by
      have hnat : (50000736683237101517 : ℕ)^1024*625000000000000^5247 ≤ 625001797120169^5247*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000736683237101517 50000000000000000000 625001797120169 625000000000000 1024 5247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625001797120169/625000000000000 : ℝ)) (X := (50000736683237101517/50000000000000000000 : ℝ)) (by norm_num) 5247 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100012605412341353109/100000000000000000000 : ℝ) ≤ (10000245993663221/10000000000000000 : ℝ) ^ (5247/1024 : ℝ) := by
    have hpowers : (100012605412341353109/100000000000000000000 : ℝ)^1024 ≤ (10000245993663221/10000000000000000 : ℝ)^5247 := by
      have hnat : (100012605412341353109 : ℕ)^1024*10000000000000000^5247 ≤ 10000245993663221^5247*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100012605412341353109 100000000000000000000 10000245993663221 10000000000000000 1024 5247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000245993663221/10000000000000000 : ℝ)) (X := (100012605412341353109/100000000000000000000 : ℝ)) (by norm_num) 5247 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6251483591138031449/6250000000000000000 : ℝ) ≤ (5000231616701869/5000000000000000 : ℝ) ^ (5247/1024 : ℝ) := by
    have hpowers : (6251483591138031449/6250000000000000000 : ℝ)^1024 ≤ (5000231616701869/5000000000000000 : ℝ)^5247 := by
      have hnat : (6251483591138031449 : ℕ)^1024*5000000000000000^5247 ≤ 5000231616701869^5247*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251483591138031449 6250000000000000000 5000231616701869 5000000000000000 1024 5247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000231616701869/5000000000000000 : ℝ)) (X := (6251483591138031449/6250000000000000000 : ℝ)) (by norm_num) 5247 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(736683237101517/100000000000000000000 : ℝ) ≤ ((35867939215265449411/35870000000000000000 : ℝ)+2*(217239740517/717400000000000 : ℝ)*(9961/100000 : ℝ))^(5247/1024 : ℝ) := by
    rw [show (35867939215265449411/35870000000000000000 : ℝ)+2*(217239740517/717400000000000 : ℝ)*(9961/100000 : ℝ)=(625001797120169/625000000000000 : ℝ) by norm_num, show 1+2*(736683237101517/100000000000000000000 : ℝ)=(50000736683237101517/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1483591138031449/12500000000000000000 : ℝ)+(736683237101517/100000000000000000000 : ℝ) ≤ ((35867939215265449411/35870000000000000000 : ℝ)+(217239740517/717400000000000 : ℝ)*((3427/20000 : ℝ)+(9961/100000 : ℝ)))^(5247/1024 : ℝ) := by
    rw [show (35867939215265449411/35870000000000000000 : ℝ)+(217239740517/717400000000000 : ℝ)*((3427/20000 : ℝ)+(9961/100000 : ℝ))=(10000245993663221/10000000000000000 : ℝ) by norm_num, show 1+(1483591138031449/12500000000000000000 : ℝ)+(736683237101517/100000000000000000000 : ℝ)=(100012605412341353109/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1483591138031449/12500000000000000000 : ℝ) ≤ ((35867939215265449411/35870000000000000000 : ℝ)+2*(217239740517/717400000000000 : ℝ)*(3427/20000 : ℝ))^(5247/1024 : ℝ) := by
    rw [show (35867939215265449411/35870000000000000000 : ℝ)+2*(217239740517/717400000000000 : ℝ)*(3427/20000 : ℝ)=(5000231616701869/5000000000000000 : ℝ) by norm_num, show 1+2*(1483591138031449/12500000000000000000 : ℝ)=(6251483591138031449/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (35867939215265449411/35870000000000000000 : ℝ)*(X 1 0+X 2 0)+(217239740517/717400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5247/1024 : ℝ)) (lo := (9961/100000 : ℝ)) (hi := (3427/20000 : ℝ)) (c := (35867939215265449411/35870000000000000000 : ℝ)) (alpha := (217239740517/717400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (35867939215265449411/35870000000000000000 : ℝ)*(X 0 1+X 2 1)+(217239740517/717400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5247/1024 : ℝ)) (lo := (9961/100000 : ℝ)) (hi := (3427/20000 : ℝ)) (c := (35867939215265449411/35870000000000000000 : ℝ)) (alpha := (217239740517/717400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (35867939215265449411/35870000000000000000 : ℝ)*(X 0 2+X 1 2)+(217239740517/717400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5247/1024 : ℝ)) (lo := (9961/100000 : ℝ)) (hi := (3427/20000 : ℝ)) (c := (35867939215265449411/35870000000000000000 : ℝ)) (alpha := (217239740517/717400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1110714353/10000000000 : ℝ)*X 0 0+(169388217/312500000 : ℝ)*X 0 1+(5420422027/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1704_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((653208011/1250000000 : ℝ)*X 1 0+(-693712371/5000000000 : ℝ)*X 1 1+(5420422957/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1704_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((522566471/1000000000 : ℝ)*X 2 0+(42347049/78125000 : ℝ)*X 2 1+(-1387424837/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1704_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1123753757/2500000000 : ℝ)*X 0 0+(61611609/156250000 : ℝ)*X 0 1+(3943142731/10000000000 : ℝ)*X 0 2+(1123753757/2500000000 : ℝ)*X 1 0+(61611609/156250000 : ℝ)*X 1 1+(3943142731/10000000000 : ℝ)*X 1 2+(1123753757/2500000000 : ℝ)*X 2 0+(61611609/156250000 : ℝ)*X 2 1+(3943142731/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1704_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-444531691/2500000000 : ℝ)*X 0 0+(323573939/625000000 : ℝ)*X 0 1+(2588591343/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1704_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5390863331/10000000000 : ℝ)*X 1 0+(-46696353/312500000 : ℝ)*X 1 1+(5177182297/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1704_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5390863803/10000000000 : ℝ)*X 2 0+(258859099/500000000 : ℝ)*X 2 1+(-1494283081/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1704_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((58041081/156250000 : ℝ)*X 0 0+(2166249379/5000000000 : ℝ)*X 0 1+(4332499063/10000000000 : ℝ)*X 0 2+(58041081/156250000 : ℝ)*X 1 0+(2166249379/5000000000 : ℝ)*X 1 1+(4332499063/10000000000 : ℝ)*X 1 2+(58041081/156250000 : ℝ)*X 2 0+(2166249379/5000000000 : ℝ)*X 2 1+(4332499063/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1704_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-40866819/250000000 : ℝ)*X 0 0+(499796093/1000000000 : ℝ)*X 0 1+(5463414087/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1704_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5196483503/10000000000 : ℝ)*X 1 0+(-1367742083/10000000000 : ℝ)*X 1 1+(5463414127/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1704_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1039296649/2000000000 : ℝ)*X 2 0+(8741463/16000000 : ℝ)*X 2 1+(-683871047/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1704_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1156986927/2500000000 : ℝ)*X 0 0+(3874145139/10000000000 : ℝ)*X 0 1+(774829019/2000000000 : ℝ)*X 0 2+(1156986927/2500000000 : ℝ)*X 1 0+(3874145139/10000000000 : ℝ)*X 1 1+(774829019/2000000000 : ℝ)*X 1 2+(1156986927/2500000000 : ℝ)*X 2 0+(3874145139/10000000000 : ℝ)*X 2 1+(774829019/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1704_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-312223479/2500000000 : ℝ)*X 0 0+(2795522611/5000000000 : ℝ)*X 0 1+(2575999533/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1704_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5407996757/10000000000 : ℝ)*X 1 0+(-300978357/2000000000 : ℝ)*X 1 1+(2575999487/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1704_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((540799649/1000000000 : ℝ)*X 2 0+(1030399799/2000000000 : ℝ)*X 2 1+(-1504892121/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1704_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((907712099/2500000000 : ℝ)*X 0 0+(874540549/2000000000 : ℝ)*X 0 1+(437270167/1000000000 : ℝ)*X 0 2+(907712099/2500000000 : ℝ)*X 1 0+(874540549/2000000000 : ℝ)*X 1 1+(437270167/1000000000 : ℝ)*X 1 2+(907712099/2500000000 : ℝ)*X 2 0+(874540549/2000000000 : ℝ)*X 2 1+(437270167/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1704_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-16673/25000 : ℝ) ≤ (-1196072258934078391952888600197647/1793500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14501/32000000000 : ℝ)*(upper0) + (75215049/100000000000000 : ℝ)*(lower2) + (31812647/100000000000000 : ℝ)*(lower3) + (1341416192254359/100000000000000 : ℝ)*(major0) + (1341416192254359/100000000000000 : ℝ)*(major1) + (1341416192254359/100000000000000 : ℝ)*(major2) + (832376277/20000000000000 : ℝ)*(sp1) + (5351644049/100000000000000 : ℝ)*(sp2) + (155954583/50000000000000 : ℝ)*(sp3) + (2009950579038823/100000000000000 : ℝ)*(sp4) + (200994833376659/10000000000000 : ℝ)*(sp5) + (2009947144003927/100000000000000 : ℝ)*(sp6) + (173777334340737/25000000000000 : ℝ)*(sp7) + (14973509/781250000000 : ℝ)*(sp8) + (347554824636057/50000000000000 : ℝ)*(f.failure) + (80398099825919/4000000000000 : ℝ)*(f.sum) + (45406795041957/35870000000000000000000000000 : ℝ)*base66 + (11817032925594882549/3587000000000000000000000000000000 : ℝ)*base67 + (17876465363674882549/3587000000000000000000000000000000 : ℝ)*base69 + (12190348020788882549/3587000000000000000000000000000000 : ℝ)*base71 + (94924092598697/35870000000000000000000000000 : ℝ)*base74 + (12941937529223882549/3587000000000000000000000000000000 : ℝ)*base75 + (4456388106798117451/3587000000000000000000000000000000 : ℝ)*base78 + (47298601913217117451/3587000000000000000000000000000000 : ℝ)*base80 + (69483983419703/35870000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (7707723/2500000000000000000000 : ℝ)*base89 + (7707723/2500000000000000000000 : ℝ)*base91 + (7707723/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (29131/50000 : ℝ) ≤ (208993207055606745909766600869681/358700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11931439/25000000000000 : ℝ)*(upper0) + (53506101/100000000000000 : ℝ)*(upper3) + (81362887/100000000000000 : ℝ)*(upper4) + (288898108300381/20000000000000 : ℝ)*(major0) + (288898108300381/20000000000000 : ℝ)*(major1) + (288898108300381/20000000000000 : ℝ)*(major2) + (2121034363807931/100000000000000 : ℝ)*(sp0) + (2121032602861241/100000000000000 : ℝ)*(sp1) + (2121035663749099/100000000000000 : ℝ)*(sp2) + (748521362510533/100000000000000 : ℝ)*(sp3) + (1321661401/25000000000000 : ℝ)*(sp5) + (1112878873/50000000000000 : ℝ)*(sp6) + (59429761/12500000000000 : ℝ)*(sp7) + (1762849457/50000000000000 : ℝ)*(sp8) + (374260918974311/50000000000000 : ℝ)*(f.failure) + (424207577901369/20000000000000 : ℝ)*(f.sum) + (10408324183807/1434800000000000000000000000 : ℝ)*base65 + (6428081159545975591/717400000000000000000000000000000 : ℝ)*base67 + (8635208871893575591/717400000000000000000000000000000 : ℝ)*base69 + (10589251925281175591/717400000000000000000000000000000 : ℝ)*base71 + (60172119771733/7174000000000000000000000000 : ℝ)*base73 + (7138938904855575591/717400000000000000000000000000000 : ℝ)*base75 + (6026513175070775591/717400000000000000000000000000000 : ℝ)*base77 + (7748706143188375591/717400000000000000000000000000000 : ℝ)*base79 + (8967790658441/1434800000000000000000000000 : ℝ)*base81 + (3767371/2500000000000000000000 : ℝ)*base90 + (3767371/2500000000000000000000 : ℝ)*base92 + (3767371/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (20321/25000 : ℝ) ≤ (29157628075224921909632038779/35870000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14986289/100000000000000 : ℝ)*(upper0) + (34832407/100000000000000 : ℝ)*(upper1) + (8209957/20000000000000 : ℝ)*(upper2) + (3288829/50000000000000 : ℝ)*(upper4) + (1468164487675461/100000000000000 : ℝ)*(major0) + (1468164487675461/100000000000000 : ℝ)*(major1) + (1468164487675461/100000000000000 : ℝ)*(major2) + (10175584979/100000000000000 : ℝ)*(sp1) + (17357140101/100000000000000 : ℝ)*(sp2) + (1396807/12500000000000 : ℝ)*(sp4) + (2148443853839309/100000000000000 : ℝ)*(sp8) + (1074216844714393/50000000000000 : ℝ)*(sp9) + (16784582092763/781250000000 : ℝ)*(sp10) + (760789461164003/100000000000000 : ℝ)*(sp11) + (760789461164003/100000000000000 : ℝ)*(f.failure) + (429688773002753/20000000000000 : ℝ)*(f.sum) + (533952700099663/35870000000000000000000000000 : ℝ)*base66 + (9263988997451453471/3587000000000000000000000000000000 : ℝ)*base67 + (328534347940453471/3587000000000000000000000000000000 : ℝ)*base69 + (35581556295609546529/3587000000000000000000000000000000 : ℝ)*base72 + (151071473326267/35870000000000000000000000000 : ℝ)*base73 + (3671716841321546529/3587000000000000000000000000000000 : ℝ)*base76 + (59899421493169546529/3587000000000000000000000000000000 : ℝ)*base78 + (18301732651705453471/3587000000000000000000000000000000 : ℝ)*base79 + (56452347264497/35870000000000000000000000000 : ℝ)*base81 + (2864617/5000000000000000000000 : ℝ)*base89 + (2864617/5000000000000000000000 : ℝ)*base91 + (2864617/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-90337/100000 : ℝ) ≤ (-5956440650945160967266184863531/6593750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (67729967/100000000000000 : ℝ)*(upper1) + (93079251/100000000000000 : ℝ)*(upper3) + (61150753/100000000000000 : ℝ)*(lower4) + (189595573900781/12500000000000 : ℝ)*(major0) + (189595573900781/12500000000000 : ℝ)*(major1) + (189595573900781/12500000000000 : ℝ)*(major2) + (1584352439/100000000000000 : ℝ)*(sp4) + (9985536091/50000000000000 : ℝ)*(sp5) + (20168656829/100000000000000 : ℝ)*(sp6) + (2670492409/20000000000000 : ℝ)*(sp7) + (569416388588283/25000000000000 : ℝ)*(sp12) + (569411791908347/25000000000000 : ℝ)*(sp13) + (2277646970048741/100000000000000 : ℝ)*(sp14) + (785960239559287/100000000000000 : ℝ)*(sp15) + (196493398005333/25000000000000 : ℝ)*(f.failure) + (227766713870557/10000000000000 : ℝ)*(f.sum) + (1667829687701/263750000000000000000000000 : ℝ)*base65 + (248403662082596177/26375000000000000000000000000000 : ℝ)*base68 + (233744574918346177/26375000000000000000000000000000 : ℝ)*base70 + (99531589370528823/26375000000000000000000000000000 : ℝ)*base71 + (870147155109/1055000000000000000000000000 : ℝ)*base73 + (490448760055846177/26375000000000000000000000000000 : ℝ)*base76 + (76518866980596177/26375000000000000000000000000000 : ℝ)*base78 + (75452919535721177/26375000000000000000000000000000 : ℝ)*base80 + (24295611678201/1055000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (711487/1250000000000000000000 : ℝ)*base89 + (711487/1250000000000000000000 : ℝ)*base91 + (711487/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1704_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5247/1024 : ℝ) ≤ p) (hpb : p ≤ (5255/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (96489539/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3427/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9961/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(16673/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(29131/50000 : ℝ) else (20321/25000 : ℝ) ≤ X j i ∧ X j i ≤ (90337/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1704_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1704_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5247/1024 : ℝ) ≤ p) (hpb : p ≤ (5255/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (96489539/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (343/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9949/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(16673/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(29131/50000 : ℝ) else (20321/25000 : ℝ) ≤ X j i ∧ X j i ≤ (90337/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1704_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1704_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1704_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5247/1024 : ℝ) ≤ p) (hpb : p ≤ (5255/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (96489539/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (343/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9949/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(16673/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(29131/50000 : ℝ) else (20321/25000 : ℝ) ≤ X j i ∧ X j i ≤ (90337/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1704_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
