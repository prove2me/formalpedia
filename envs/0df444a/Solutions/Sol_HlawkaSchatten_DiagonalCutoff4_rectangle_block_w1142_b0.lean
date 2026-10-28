-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1142_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:31:49.256264+00:00
-- url     : https://prove2.me/submissions/c909e0c9-2a9e-4b65-be90-672f24d4e695

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
theorem support_rectangle_w1142_s0_0 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-59119083/312500000 : ℝ)*x 0 + (6054330253/10000000000 : ℝ)*x 1 + (1195118071/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (59119083/312500000 : ℝ)^8335 ≤ (10998145125819/100000000000000 : ℝ)^6287 := by
    have hnat : (59119083 : ℕ)^8335*100000000000000^6287 ≤ 10998145125819^6287*312500000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59119083 312500000 10998145125819 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6054330253/10000000000 : ℝ)^8335 ≤ (102826203051/200000000000 : ℝ)^6287 := by
    have hnat : (6054330253 : ℕ)^8335*200000000000^6287 ≤ 102826203051^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6054330253 10000000000 102826203051 200000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1195118071/2500000000 : ℝ)^8335 ≤ (9397188332409/25000000000000 : ℝ)^6287 := by
    have hnat : (1195118071 : ℕ)^8335*25000000000000^6287 ≤ 9397188332409^6287*2500000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1195118071 2500000000 9397188332409 25000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-59119083/312500000 : ℝ), (6054330253/10000000000 : ℝ), (1195118071/2500000000 : ℝ)] ![(10998145125819/100000000000000 : ℝ), (102826203051/200000000000 : ℝ), (9397188332409/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-59119083/312500000 : ℝ)|^8335 ≤ (10998145125819/100000000000000 : ℝ)^6287
        have hw : |(-59119083/312500000 : ℝ)|=(59119083/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6054330253/10000000000 : ℝ)|^8335 ≤ (102826203051/200000000000 : ℝ)^6287
        have hw : |(6054330253/10000000000 : ℝ)|=(6054330253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1195118071/2500000000 : ℝ)|^8335 ≤ (9397188332409/25000000000000 : ℝ)^6287
        have hw : |(1195118071/2500000000 : ℝ)|=(1195118071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s0_1 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1103358769/2000000000 : ℝ)*x 0 + (-2622855573/10000000000 : ℝ)*x 1 + (4780472197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1103358769/2000000000 : ℝ)^8335 ≤ (4545072500147/10000000000000 : ℝ)^6287 := by
    have hnat : (1103358769 : ℕ)^8335*10000000000000^6287 ≤ 4545072500147^6287*2000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103358769 2000000000 4545072500147 10000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622855573/10000000000 : ℝ)^8335 ≤ (4240130639173/25000000000000 : ℝ)^6287 := by
    have hnat : (2622855573 : ℕ)^8335*25000000000000^6287 ≤ 4240130639173^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622855573 10000000000 4240130639173 25000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4780472197/10000000000 : ℝ)^8335 ≤ (37588752422717/100000000000000 : ℝ)^6287 := by
    have hnat : (4780472197 : ℕ)^8335*100000000000000^6287 ≤ 37588752422717^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4780472197 10000000000 37588752422717 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1103358769/2000000000 : ℝ), (-2622855573/10000000000 : ℝ), (4780472197/10000000000 : ℝ)] ![(4545072500147/10000000000000 : ℝ), (4240130639173/25000000000000 : ℝ), (37588752422717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1103358769/2000000000 : ℝ)|^8335 ≤ (4545072500147/10000000000000 : ℝ)^6287
        have hw : |(1103358769/2000000000 : ℝ)|=(1103358769/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2622855573/10000000000 : ℝ)|^8335 ≤ (4240130639173/25000000000000 : ℝ)^6287
        have hw : |(-2622855573/10000000000 : ℝ)|=(2622855573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4780472197/10000000000 : ℝ)|^8335 ≤ (37588752422717/100000000000000 : ℝ)^6287
        have hw : |(4780472197/10000000000 : ℝ)|=(4780472197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s0_2 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5516793451/10000000000 : ℝ)*x 0 + (4780472373/10000000000 : ℝ)*x 1 + (-2622855861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5516793451/10000000000 : ℝ)^8335 ≤ (45450720698063/100000000000000 : ℝ)^6287 := by
    have hnat : (5516793451 : ℕ)^8335*100000000000000^6287 ≤ 45450720698063^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5516793451 10000000000 45450720698063 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4780472373/10000000000 : ℝ)^8335 ≤ (37588754257403/100000000000000 : ℝ)^6287 := by
    have hnat : (4780472373 : ℕ)^8335*100000000000000^6287 ≤ 37588754257403^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4780472373 10000000000 37588754257403 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622855861/10000000000 : ℝ)^8335 ≤ (8480262512841/50000000000000 : ℝ)^6287 := by
    have hnat : (2622855861 : ℕ)^8335*50000000000000^6287 ≤ 8480262512841^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622855861 10000000000 8480262512841 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5516793451/10000000000 : ℝ), (4780472373/10000000000 : ℝ), (-2622855861/10000000000 : ℝ)] ![(45450720698063/100000000000000 : ℝ), (37588754257403/100000000000000 : ℝ), (8480262512841/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5516793451/10000000000 : ℝ)|^8335 ≤ (45450720698063/100000000000000 : ℝ)^6287
        have hw : |(5516793451/10000000000 : ℝ)|=(5516793451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4780472373/10000000000 : ℝ)|^8335 ≤ (37588754257403/100000000000000 : ℝ)^6287
        have hw : |(4780472373/10000000000 : ℝ)|=(4780472373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2622855861/10000000000 : ℝ)|^8335 ≤ (8480262512841/50000000000000 : ℝ)^6287
        have hw : |(-2622855861/10000000000 : ℝ)|=(2622855861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s0_3 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4200990717/10000000000 : ℝ)*x 0 + (1560539229/5000000000 : ℝ)*x 1 + (5655385879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4200990717/10000000000 : ℝ)^8335 ≤ (31670721783149/100000000000000 : ℝ)^6287 := by
    have hnat : (4200990717 : ℕ)^8335*100000000000000^6287 ≤ 31670721783149^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4200990717 10000000000 31670721783149 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1560539229/5000000000 : ℝ)^8335 ≤ (2135864283497/10000000000000 : ℝ)^6287 := by
    have hnat : (1560539229 : ℕ)^8335*10000000000000^6287 ≤ 2135864283497^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1560539229 5000000000 2135864283497 10000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5655385879/10000000000 : ℝ)^8335 ≤ (46970635370691/100000000000000 : ℝ)^6287 := by
    have hnat : (5655385879 : ℕ)^8335*100000000000000^6287 ≤ 46970635370691^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5655385879 10000000000 46970635370691 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4200990717/10000000000 : ℝ), (1560539229/5000000000 : ℝ), (5655385879/10000000000 : ℝ)] ![(31670721783149/100000000000000 : ℝ), (2135864283497/10000000000000 : ℝ), (46970635370691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4200990717/10000000000 : ℝ)|^8335 ≤ (31670721783149/100000000000000 : ℝ)^6287
        have hw : |(4200990717/10000000000 : ℝ)|=(4200990717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1560539229/5000000000 : ℝ)|^8335 ≤ (2135864283497/10000000000000 : ℝ)^6287
        have hw : |(1560539229/5000000000 : ℝ)|=(1560539229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5655385879/10000000000 : ℝ)|^8335 ≤ (46970635370691/100000000000000 : ℝ)^6287
        have hw : |(5655385879/10000000000 : ℝ)|=(5655385879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s0_4 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-474239077/2500000000 : ℝ)*x 0 + (1203333557/2500000000 : ℝ)*x 1 + (6020312869/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (474239077/2500000000 : ℝ)^8335 ≤ (11037821919887/100000000000000 : ℝ)^6287 := by
    have hnat : (474239077 : ℕ)^8335*100000000000000^6287 ≤ 11037821919887^6287*2500000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      474239077 2500000000 11037821919887 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1203333557/2500000000 : ℝ)^8335 ≤ (9482925228149/25000000000000 : ℝ)^6287 := by
    have hnat : (1203333557 : ℕ)^8335*25000000000000^6287 ≤ 9482925228149^6287*2500000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1203333557 2500000000 9482925228149 25000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6020312869/10000000000 : ℝ)^8335 ≤ (797351205609/1562500000000 : ℝ)^6287 := by
    have hnat : (6020312869 : ℕ)^8335*1562500000000^6287 ≤ 797351205609^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6020312869 10000000000 797351205609 1562500000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-474239077/2500000000 : ℝ), (1203333557/2500000000 : ℝ), (6020312869/10000000000 : ℝ)] ![(11037821919887/100000000000000 : ℝ), (9482925228149/25000000000000 : ℝ), (797351205609/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-474239077/2500000000 : ℝ)|^8335 ≤ (11037821919887/100000000000000 : ℝ)^6287
        have hw : |(-474239077/2500000000 : ℝ)|=(474239077/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1203333557/2500000000 : ℝ)|^8335 ≤ (9482925228149/25000000000000 : ℝ)^6287
        have hw : |(1203333557/2500000000 : ℝ)|=(1203333557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6020312869/10000000000 : ℝ)|^8335 ≤ (797351205609/1562500000000 : ℝ)^6287
        have hw : |(6020312869/10000000000 : ℝ)|=(6020312869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s0_5 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2585328949/5000000000 : ℝ)*x 0 + (-1383015217/10000000000 : ℝ)*x 1 + (6020312737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2585328949/5000000000 : ℝ)^8335 ≤ (20854650255821/50000000000000 : ℝ)^6287 := by
    have hnat : (2585328949 : ℕ)^8335*50000000000000^6287 ≤ 20854650255821^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2585328949 5000000000 20854650255821 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1383015217/10000000000 : ℝ)^8335 ≤ (1452044758877/20000000000000 : ℝ)^6287 := by
    have hnat : (1383015217 : ℕ)^8335*20000000000000^6287 ≤ 1452044758877^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1383015217 10000000000 1452044758877 20000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6020312737/10000000000 : ℝ)^8335 ≤ (1594702364863/3125000000000 : ℝ)^6287 := by
    have hnat : (6020312737 : ℕ)^8335*3125000000000^6287 ≤ 1594702364863^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6020312737 10000000000 1594702364863 3125000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2585328949/5000000000 : ℝ), (-1383015217/10000000000 : ℝ), (6020312737/10000000000 : ℝ)] ![(20854650255821/50000000000000 : ℝ), (1452044758877/20000000000000 : ℝ), (1594702364863/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2585328949/5000000000 : ℝ)|^8335 ≤ (20854650255821/50000000000000 : ℝ)^6287
        have hw : |(2585328949/5000000000 : ℝ)|=(2585328949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1383015217/10000000000 : ℝ)|^8335 ≤ (1452044758877/20000000000000 : ℝ)^6287
        have hw : |(-1383015217/10000000000 : ℝ)|=(1383015217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6020312737/10000000000 : ℝ)|^8335 ≤ (1594702364863/3125000000000 : ℝ)^6287
        have hw : |(6020312737/10000000000 : ℝ)|=(6020312737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s0_6 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2585328951/5000000000 : ℝ)*x 0 + (6020312761/10000000000 : ℝ)*x 1 + (-1383015173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2585328951/5000000000 : ℝ)^8335 ≤ (41709300554419/100000000000000 : ℝ)^6287 := by
    have hnat : (2585328951 : ℕ)^8335*100000000000000^6287 ≤ 41709300554419^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2585328951 5000000000 41709300554419 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6020312761/10000000000 : ℝ)^8335 ≤ (25515237972659/50000000000000 : ℝ)^6287 := by
    have hnat : (6020312761 : ℕ)^8335*50000000000000^6287 ≤ 25515237972659^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6020312761 10000000000 25515237972659 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1383015173/10000000000 : ℝ)^8335 ≤ (3630111744081/50000000000000 : ℝ)^6287 := by
    have hnat : (1383015173 : ℕ)^8335*50000000000000^6287 ≤ 3630111744081^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1383015173 10000000000 3630111744081 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2585328951/5000000000 : ℝ), (6020312761/10000000000 : ℝ), (-1383015173/10000000000 : ℝ)] ![(41709300554419/100000000000000 : ℝ), (25515237972659/50000000000000 : ℝ), (3630111744081/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2585328951/5000000000 : ℝ)|^8335 ≤ (41709300554419/100000000000000 : ℝ)^6287
        have hw : |(2585328951/5000000000 : ℝ)|=(2585328951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6020312761/10000000000 : ℝ)|^8335 ≤ (25515237972659/50000000000000 : ℝ)^6287
        have hw : |(6020312761/10000000000 : ℝ)|=(6020312761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1383015173/10000000000 : ℝ)|^8335 ≤ (3630111744081/50000000000000 : ℝ)^6287
        have hw : |(-1383015173/10000000000 : ℝ)|=(1383015173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s0_7 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4211227977/10000000000 : ℝ)*x 0 + (1118001531/2000000000 : ℝ)*x 1 + (3188755219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4211227977/10000000000 : ℝ)^8335 ≤ (992908762159/3125000000000 : ℝ)^6287 := by
    have hnat : (4211227977 : ℕ)^8335*3125000000000^6287 ≤ 992908762159^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4211227977 10000000000 992908762159 3125000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1118001531/2000000000 : ℝ)^8335 ≤ (462521154533/1000000000000 : ℝ)^6287 := by
    have hnat : (1118001531 : ℕ)^8335*1000000000000^6287 ≤ 462521154533^6287*2000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1118001531 2000000000 462521154533 1000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3188755219/10000000000 : ℝ)^8335 ≤ (10987402066949/50000000000000 : ℝ)^6287 := by
    have hnat : (3188755219 : ℕ)^8335*50000000000000^6287 ≤ 10987402066949^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3188755219 10000000000 10987402066949 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4211227977/10000000000 : ℝ), (1118001531/2000000000 : ℝ), (3188755219/10000000000 : ℝ)] ![(992908762159/3125000000000 : ℝ), (462521154533/1000000000000 : ℝ), (10987402066949/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4211227977/10000000000 : ℝ)|^8335 ≤ (992908762159/3125000000000 : ℝ)^6287
        have hw : |(4211227977/10000000000 : ℝ)|=(4211227977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1118001531/2000000000 : ℝ)|^8335 ≤ (462521154533/1000000000000 : ℝ)^6287
        have hw : |(1118001531/2000000000 : ℝ)|=(1118001531/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3188755219/10000000000 : ℝ)|^8335 ≤ (10987402066949/50000000000000 : ℝ)^6287
        have hw : |(3188755219/10000000000 : ℝ)|=(3188755219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1142_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37368427/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (207/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5563/20000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4167/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4167 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4167*1^1024 ≤ 0^1024*1^4167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4167 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4167/1024 : ℝ) ≤ (480483432507294019/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4167 ≤ (480483432507294019/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4167*20000000000000000000^1024 ≤ 480483432507294019^1024*5^4167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 480483432507294019 20000000000000000000 4167 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (480483432507294019/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4167/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4167 := by
      have hnat : (1 : ℕ)^1024*1^4167 ≤ 1^4167*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20480483432507294019/20000000000000000000 : ℝ) ≤ (10058509583723333/10000000000000000 : ℝ) ^ (4167/1024 : ℝ) := by
    have hpowers : (20480483432507294019/20000000000000000000 : ℝ)^1024 ≤ (10058509583723333/10000000000000000 : ℝ)^4167 := by
      have hnat : (20480483432507294019 : ℕ)^1024*10000000000000000^4167 ≤ 10058509583723333^4167*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20480483432507294019 20000000000000000000 10058509583723333 10000000000000000 1024 4167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10058509583723333/10000000000000000 : ℝ)) (X := (20480483432507294019/20000000000000000000 : ℝ)) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10480483432507294019/10000000000000000000 : ℝ) ≤ (5058509583723333/5000000000000000 : ℝ) ^ (4167/1024 : ℝ) := by
    have hpowers : (10480483432507294019/10000000000000000000 : ℝ)^1024 ≤ (5058509583723333/5000000000000000 : ℝ)^4167 := by
      have hnat : (10480483432507294019 : ℕ)^1024*5000000000000000^4167 ≤ 5058509583723333^4167*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10480483432507294019 10000000000000000000 5058509583723333 5000000000000000 1024 4167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5058509583723333/5000000000000000 : ℝ)) (X := (10480483432507294019/10000000000000000000 : ℝ)) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(58509583723333/4000000000000000 : ℝ)*(0 : ℝ))^(4167/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(58509583723333/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(480483432507294019/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(58509583723333/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4167/1024 : ℝ) := by
    rw [show (1 : ℝ)+(58509583723333/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10058509583723333/10000000000000000 : ℝ) by norm_num, show 1+(480483432507294019/20000000000000000000 : ℝ)+(0 : ℝ)=(20480483432507294019/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(480483432507294019/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(58509583723333/4000000000000000 : ℝ)*(2/5 : ℝ))^(4167/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(58509583723333/4000000000000000 : ℝ)*(2/5 : ℝ)=(5058509583723333/5000000000000000 : ℝ) by norm_num, show 1+2*(480483432507294019/20000000000000000000 : ℝ)=(10480483432507294019/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(58509583723333/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4167/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (58509583723333/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(58509583723333/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4167/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (58509583723333/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(58509583723333/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4167/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (58509583723333/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-59119083/312500000 : ℝ)*X 0 0+(6054330253/10000000000 : ℝ)*X 0 1+(1195118071/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1103358769/2000000000 : ℝ)*X 1 0+(-2622855573/10000000000 : ℝ)*X 1 1+(4780472197/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5516793451/10000000000 : ℝ)*X 2 0+(4780472373/10000000000 : ℝ)*X 2 1+(-2622855861/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4200990717/10000000000 : ℝ)*X 0 0+(1560539229/5000000000 : ℝ)*X 0 1+(5655385879/10000000000 : ℝ)*X 0 2+(4200990717/10000000000 : ℝ)*X 1 0+(1560539229/5000000000 : ℝ)*X 1 1+(5655385879/10000000000 : ℝ)*X 1 2+(4200990717/10000000000 : ℝ)*X 2 0+(1560539229/5000000000 : ℝ)*X 2 1+(5655385879/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-474239077/2500000000 : ℝ)*X 0 0+(1203333557/2500000000 : ℝ)*X 0 1+(6020312869/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2585328949/5000000000 : ℝ)*X 1 0+(-1383015217/10000000000 : ℝ)*X 1 1+(6020312737/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2585328951/5000000000 : ℝ)*X 2 0+(6020312761/10000000000 : ℝ)*X 2 1+(-1383015173/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4211227977/10000000000 : ℝ)*X 0 0+(1118001531/2000000000 : ℝ)*X 0 1+(3188755219/10000000000 : ℝ)*X 0 2+(4211227977/10000000000 : ℝ)*X 1 0+(1118001531/2000000000 : ℝ)*X 1 1+(3188755219/10000000000 : ℝ)*X 1 2+(4211227977/10000000000 : ℝ)*X 2 0+(1118001531/2000000000 : ℝ)*X 2 1+(3188755219/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (289904679728684876119659/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20464523/100000000000000 : ℝ)*(base1) + (48867/800000000000 : ℝ)*(base16) + (41423189/12500000000000 : ℝ)*(base19) + (56285843/20000000000000 : ℝ)*(base23) + (33786267/50000000000000 : ℝ)*(upper3) + (589802367683447/100000000000000 : ℝ)*(major0) + (589802367683447/100000000000000 : ℝ)*(major1) + (589802367683447/100000000000000 : ℝ)*(major2) + (392508993365789/50000000000000 : ℝ)*(sp0) + (19625458032501/2500000000000 : ℝ)*(sp1) + (785018377364713/100000000000000 : ℝ)*(sp2) + (98646369670873/25000000000000 : ℝ)*(sp3) + (692526873/100000000000000 : ℝ)*(sp4) + (529107501/100000000000000 : ℝ)*(sp7) + (98646507063879/25000000000000 : ℝ)*(f.failure) + (98127332349241/12500000000000 : ℝ)*(f.sum) + (575191666031149/200000000000000000000000000000 : ℝ)*base66 + (78353335831149/400000000000000000000000000000 : ℝ)*base68 + (508068181368851/400000000000000000000000000000 : ℝ)*base69 + (517934955368851/400000000000000000000000000000 : ℝ)*base71 + (1618046342431149/200000000000000000000000000000 : ℝ)*base74 + (472798144968851/400000000000000000000000000000 : ℝ)*base75 + (380721349831149/400000000000000000000000000000 : ℝ)*base78 + (936367604231149/400000000000000000000000000000 : ℝ)*base80 + (157278687031149/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (2998333/625000000000000000000 : ℝ)*base89 + (2998333/625000000000000000000 : ℝ)*base91 + (2998333/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (918668168088098545036557/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (61046373/100000000000000 : ℝ)*(base1) + (1131015929/100000000000000 : ℝ)*(base19) + (1130911921/100000000000000 : ℝ)*(base23) + (120467389/100000000000000 : ℝ)*(upper3) + (134362141/100000000000000 : ℝ)*(upper5) + (622482311273443/100000000000000 : ℝ)*(major0) + (622482311273443/100000000000000 : ℝ)*(major1) + (622482311273443/100000000000000 : ℝ)*(major2) + (227410981/10000000000000 : ℝ)*(sp1) + (2262984297/100000000000000 : ℝ)*(sp2) + (82851516316343/10000000000000 : ℝ)*(sp4) + (414255848495659/50000000000000 : ℝ)*(sp5) + (414255854110419/50000000000000 : ℝ)*(sp6) + (416449306272087/100000000000000 : ℝ)*(sp7) + (416449367318461/100000000000000 : ℝ)*(f.failure) + (828515102117057/100000000000000 : ℝ)*(f.sum) + (31532310545519/200000000000000000000000000000 : ℝ)*base65 + (1541318587654481/400000000000000000000000000000 : ℝ)*base68 + (2747216466854481/400000000000000000000000000000 : ℝ)*base70 + (40633817145519/400000000000000000000000000000 : ℝ)*base71 + (885329147454481/200000000000000000000000000000 : ℝ)*base74 + (4181052173254481/400000000000000000000000000000 : ℝ)*base76 + (98653093545519/400000000000000000000000000000 : ℝ)*base77 + (2625898028745519/400000000000000000000000000000 : ℝ)*base79 + (1119251850054481/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (20630847/2500000000000000000000 : ℝ)*base89 + (20630847/2500000000000000000000 : ℝ)*base91 + (20630847/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1142_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37368427/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (207/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5563/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1142_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1142_s1_0 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-262059397/1250000000 : ℝ)*x 0 + (712687779/1250000000 : ℝ)*x 1 + (1250568663/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262059397/1250000000 : ℝ)^8335 ≤ (12602710202369/100000000000000 : ℝ)^6287 := by
    have hnat : (262059397 : ℕ)^8335*100000000000000^6287 ≤ 12602710202369^6287*1250000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262059397 1250000000 12602710202369 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (712687779/1250000000 : ℝ)^8335 ≤ (2967443451411/6250000000000 : ℝ)^6287 := by
    have hnat : (712687779 : ℕ)^8335*6250000000000^6287 ≤ 2967443451411^6287*1250000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      712687779 1250000000 2967443451411 6250000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1250568663/2500000000 : ℝ)^8335 ≤ (9979548639823/25000000000000 : ℝ)^6287 := by
    have hnat : (1250568663 : ℕ)^8335*25000000000000^6287 ≤ 9979548639823^6287*2500000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1250568663 2500000000 9979548639823 25000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-262059397/1250000000 : ℝ), (712687779/1250000000 : ℝ), (1250568663/2500000000 : ℝ)] ![(12602710202369/100000000000000 : ℝ), (2967443451411/6250000000000 : ℝ), (9979548639823/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-262059397/1250000000 : ℝ)|^8335 ≤ (12602710202369/100000000000000 : ℝ)^6287
        have hw : |(-262059397/1250000000 : ℝ)|=(262059397/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(712687779/1250000000 : ℝ)|^8335 ≤ (2967443451411/6250000000000 : ℝ)^6287
        have hw : |(712687779/1250000000 : ℝ)|=(712687779/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1250568663/2500000000 : ℝ)|^8335 ≤ (9979548639823/25000000000000 : ℝ)^6287
        have hw : |(1250568663/2500000000 : ℝ)|=(1250568663/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s1_1 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1083824381/2000000000 : ℝ)*x 0 + (-618454091/2500000000 : ℝ)*x 1 + (125056849/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083824381/2000000000 : ℝ)^8335 ≤ (2774187888519/6250000000000 : ℝ)^6287 := by
    have hnat : (1083824381 : ℕ)^8335*6250000000000^6287 ≤ 2774187888519^6287*2000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083824381 2000000000 2774187888519 6250000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (618454091/2500000000 : ℝ)^8335 ≤ (7847403267699/50000000000000 : ℝ)^6287 := by
    have hnat : (618454091 : ℕ)^8335*50000000000000^6287 ≤ 7847403267699^6287*2500000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      618454091 2500000000 7847403267699 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (125056849/250000000 : ℝ)^8335 ≤ (311860837799/781250000000 : ℝ)^6287 := by
    have hnat : (125056849 : ℕ)^8335*781250000000^6287 ≤ 311860837799^6287*250000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125056849 250000000 311860837799 781250000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083824381/2000000000 : ℝ), (-618454091/2500000000 : ℝ), (125056849/250000000 : ℝ)] ![(2774187888519/6250000000000 : ℝ), (7847403267699/50000000000000 : ℝ), (311860837799/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083824381/2000000000 : ℝ)|^8335 ≤ (2774187888519/6250000000000 : ℝ)^6287
        have hw : |(1083824381/2000000000 : ℝ)|=(1083824381/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-618454091/2500000000 : ℝ)|^8335 ≤ (7847403267699/50000000000000 : ℝ)^6287
        have hw : |(-618454091/2500000000 : ℝ)|=(618454091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(125056849/250000000 : ℝ)|^8335 ≤ (311860837799/781250000000 : ℝ)^6287
        have hw : |(125056849/250000000 : ℝ)|=(125056849/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s1_2 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2709561921/5000000000 : ℝ)*x 0 + (2501136119/5000000000 : ℝ)*x 1 + (-2473816029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2709561921/5000000000 : ℝ)^8335 ≤ (44387027250151/100000000000000 : ℝ)^6287 := by
    have hnat : (2709561921 : ℕ)^8335*100000000000000^6287 ≤ 44387027250151^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709561921 5000000000 44387027250151 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2501136119/5000000000 : ℝ)^8335 ≤ (997954225509/2500000000000 : ℝ)^6287 := by
    have hnat : (2501136119 : ℕ)^8335*2500000000000^6287 ≤ 997954225509^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2501136119 5000000000 997954225509 2500000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2473816029/10000000000 : ℝ)^8335 ≤ (7847401858847/50000000000000 : ℝ)^6287 := by
    have hnat : (2473816029 : ℕ)^8335*50000000000000^6287 ≤ 7847401858847^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2473816029 10000000000 7847401858847 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2709561921/5000000000 : ℝ), (2501136119/5000000000 : ℝ), (-2473816029/10000000000 : ℝ)] ![(44387027250151/100000000000000 : ℝ), (997954225509/2500000000000 : ℝ), (7847401858847/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2709561921/5000000000 : ℝ)|^8335 ≤ (44387027250151/100000000000000 : ℝ)^6287
        have hw : |(2709561921/5000000000 : ℝ)|=(2709561921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2501136119/5000000000 : ℝ)|^8335 ≤ (997954225509/2500000000000 : ℝ)^6287
        have hw : |(2501136119/5000000000 : ℝ)|=(2501136119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2473816029/10000000000 : ℝ)|^8335 ≤ (7847401858847/50000000000000 : ℝ)^6287
        have hw : |(-2473816029/10000000000 : ℝ)|=(2473816029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s1_3 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1079360093/2500000000 : ℝ)*x 0 + (3677050741/10000000000 : ℝ)*x 1 + (633517903/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079360093/2500000000 : ℝ)^8335 ≤ (32839819809679/100000000000000 : ℝ)^6287 := by
    have hnat : (1079360093 : ℕ)^8335*100000000000000^6287 ≤ 32839819809679^6287*2500000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079360093 2500000000 32839819809679 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3677050741/10000000000 : ℝ)^8335 ≤ (26543638329057/100000000000000 : ℝ)^6287 := by
    have hnat : (3677050741 : ℕ)^8335*100000000000000^6287 ≤ 26543638329057^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3677050741 10000000000 26543638329057 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (633517903/1250000000 : ℝ)^8335 ≤ (40616541844629/100000000000000 : ℝ)^6287 := by
    have hnat : (633517903 : ℕ)^8335*100000000000000^6287 ≤ 40616541844629^6287*1250000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      633517903 1250000000 40616541844629 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079360093/2500000000 : ℝ), (3677050741/10000000000 : ℝ), (633517903/1250000000 : ℝ)] ![(32839819809679/100000000000000 : ℝ), (26543638329057/100000000000000 : ℝ), (40616541844629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079360093/2500000000 : ℝ)|^8335 ≤ (32839819809679/100000000000000 : ℝ)^6287
        have hw : |(1079360093/2500000000 : ℝ)|=(1079360093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3677050741/10000000000 : ℝ)|^8335 ≤ (26543638329057/100000000000000 : ℝ)^6287
        have hw : |(3677050741/10000000000 : ℝ)|=(3677050741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(633517903/1250000000 : ℝ)|^8335 ≤ (40616541844629/100000000000000 : ℝ)^6287
        have hw : |(633517903/1250000000 : ℝ)|=(633517903/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s1_4 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-83891267/400000000 : ℝ)*x 0 + (5011821571/10000000000 : ℝ)*x 1 + (2845882939/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83891267/400000000 : ℝ)^8335 ≤ (3152284519299/25000000000000 : ℝ)^6287 := by
    have hnat : (83891267 : ℕ)^8335*25000000000000^6287 ≤ 3152284519299^6287*400000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83891267 400000000 3152284519299 25000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5011821571/10000000000 : ℝ)^8335 ≤ (10004806913801/25000000000000 : ℝ)^6287 := by
    have hnat : (5011821571 : ℕ)^8335*25000000000000^6287 ≤ 10004806913801^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5011821571 10000000000 10004806913801 25000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2845882939/5000000000 : ℝ)^8335 ≤ (1480363570231/3125000000000 : ℝ)^6287 := by
    have hnat : (2845882939 : ℕ)^8335*3125000000000^6287 ≤ 1480363570231^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2845882939 5000000000 1480363570231 3125000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-83891267/400000000 : ℝ), (5011821571/10000000000 : ℝ), (2845882939/5000000000 : ℝ)] ![(3152284519299/25000000000000 : ℝ), (10004806913801/25000000000000 : ℝ), (1480363570231/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-83891267/400000000 : ℝ)|^8335 ≤ (3152284519299/25000000000000 : ℝ)^6287
        have hw : |(-83891267/400000000 : ℝ)|=(83891267/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5011821571/10000000000 : ℝ)|^8335 ≤ (10004806913801/25000000000000 : ℝ)^6287
        have hw : |(5011821571/10000000000 : ℝ)|=(5011821571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2845882939/5000000000 : ℝ)|^8335 ≤ (1480363570231/3125000000000 : ℝ)^6287
        have hw : |(2845882939/5000000000 : ℝ)|=(2845882939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s1_5 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5239852507/10000000000 : ℝ)*x 0 + (-111520263/625000000 : ℝ)*x 1 + (5691765537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5239852507/10000000000 : ℝ)^8335 ≤ (42450891171907/100000000000000 : ℝ)^6287 := by
    have hnat : (5239852507 : ℕ)^8335*100000000000000^6287 ≤ 42450891171907^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239852507 10000000000 42450891171907 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (111520263/625000000 : ℝ)^8335 ≤ (10177478335589/100000000000000 : ℝ)^6287 := by
    have hnat : (111520263 : ℕ)^8335*100000000000000^6287 ≤ 10177478335589^6287*625000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111520263 625000000 10177478335589 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5691765537/10000000000 : ℝ)^8335 ≤ (47371630484793/100000000000000 : ℝ)^6287 := by
    have hnat : (5691765537 : ℕ)^8335*100000000000000^6287 ≤ 47371630484793^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5691765537 10000000000 47371630484793 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5239852507/10000000000 : ℝ), (-111520263/625000000 : ℝ), (5691765537/10000000000 : ℝ)] ![(42450891171907/100000000000000 : ℝ), (10177478335589/100000000000000 : ℝ), (47371630484793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5239852507/10000000000 : ℝ)|^8335 ≤ (42450891171907/100000000000000 : ℝ)^6287
        have hw : |(5239852507/10000000000 : ℝ)|=(5239852507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-111520263/625000000 : ℝ)|^8335 ≤ (10177478335589/100000000000000 : ℝ)^6287
        have hw : |(-111520263/625000000 : ℝ)|=(111520263/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5691765537/10000000000 : ℝ)|^8335 ≤ (47371630484793/100000000000000 : ℝ)^6287
        have hw : |(5691765537/10000000000 : ℝ)|=(5691765537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s1_6 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1309963143/2500000000 : ℝ)*x 0 + (711470717/1250000000 : ℝ)*x 1 + (-71372953/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1309963143/2500000000 : ℝ)^8335 ≤ (1326590370939/3125000000000 : ℝ)^6287 := by
    have hnat : (1309963143 : ℕ)^8335*3125000000000^6287 ≤ 1326590370939^6287*2500000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309963143 2500000000 1326590370939 3125000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (711470717/1250000000 : ℝ)^8335 ≤ (23685816340281/50000000000000 : ℝ)^6287 := by
    have hnat : (711470717 : ℕ)^8335*50000000000000^6287 ≤ 23685816340281^6287*1250000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      711470717 1250000000 23685816340281 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (71372953/400000000 : ℝ)^8335 ≤ (10177475439397/100000000000000 : ℝ)^6287 := by
    have hnat : (71372953 : ℕ)^8335*100000000000000^6287 ≤ 10177475439397^6287*400000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71372953 400000000 10177475439397 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1309963143/2500000000 : ℝ), (711470717/1250000000 : ℝ), (-71372953/400000000 : ℝ)] ![(1326590370939/3125000000000 : ℝ), (23685816340281/50000000000000 : ℝ), (10177475439397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1309963143/2500000000 : ℝ)|^8335 ≤ (1326590370939/3125000000000 : ℝ)^6287
        have hw : |(1309963143/2500000000 : ℝ)|=(1309963143/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(711470717/1250000000 : ℝ)|^8335 ≤ (23685816340281/50000000000000 : ℝ)^6287
        have hw : |(711470717/1250000000 : ℝ)|=(711470717/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-71372953/400000000 : ℝ)|^8335 ≤ (10177475439397/100000000000000 : ℝ)^6287
        have hw : |(-71372953/400000000 : ℝ)|=(71372953/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s1_7 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4319040739/10000000000 : ℝ)*x 0 + (2524575517/5000000000 : ℝ)*x 1 + (3696419609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4319040739/10000000000 : ℝ)^8335 ≤ (32855959023139/100000000000000 : ℝ)^6287 := by
    have hnat : (4319040739 : ℕ)^8335*100000000000000^6287 ≤ 32855959023139^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4319040739 10000000000 32855959023139 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2524575517/5000000000 : ℝ)^8335 ≤ (323319032047/800000000000 : ℝ)^6287 := by
    have hnat : (2524575517 : ℕ)^8335*800000000000^6287 ≤ 323319032047^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2524575517 5000000000 323319032047 800000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3696419609/10000000000 : ℝ)^8335 ≤ (26729161950957/100000000000000 : ℝ)^6287 := by
    have hnat : (3696419609 : ℕ)^8335*100000000000000^6287 ≤ 26729161950957^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3696419609 10000000000 26729161950957 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4319040739/10000000000 : ℝ), (2524575517/5000000000 : ℝ), (3696419609/10000000000 : ℝ)] ![(32855959023139/100000000000000 : ℝ), (323319032047/800000000000 : ℝ), (26729161950957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4319040739/10000000000 : ℝ)|^8335 ≤ (32855959023139/100000000000000 : ℝ)^6287
        have hw : |(4319040739/10000000000 : ℝ)|=(4319040739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2524575517/5000000000 : ℝ)|^8335 ≤ (323319032047/800000000000 : ℝ)^6287
        have hw : |(2524575517/5000000000 : ℝ)|=(2524575517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3696419609/10000000000 : ℝ)|^8335 ≤ (26729161950957/100000000000000 : ℝ)^6287
        have hw : |(3696419609/10000000000 : ℝ)|=(3696419609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1142_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37368427/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5563/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (207/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (113/2000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20437/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5563/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (207/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5563/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (207/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5563/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (207/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5563/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (207/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5563/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (207/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5563/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (207/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base37 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
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
  have hpowlo : (207/50000 : ℝ) ^ (4167/1024 : ℝ) ≤ (10040234433/50000000000000000000 : ℝ) := by
    have hpowers : (207/50000 : ℝ)^4167 ≤ (10040234433/50000000000000000000 : ℝ)^1024 := by
      have hnat : (207 : ℕ)^4167*50000000000000000000^1024 ≤ 10040234433^1024*50000^4167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        207 50000 10040234433 50000000000000000000 4167 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (207/50000 : ℝ)) (X := (10040234433/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (5563/20000 : ℝ) ^ (4167/1024 : ℝ) ≤ (1095506151866233/200000000000000000 : ℝ) := by
    have hpowers : (5563/20000 : ℝ)^4167 ≤ (1095506151866233/200000000000000000 : ℝ)^1024 := by
      have hnat : (5563 : ℕ)^4167*200000000000000000^1024 ≤ 1095506151866233^1024*20000^4167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5563 20000 1095506151866233 200000000000000000 4167 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5563/20000 : ℝ)) (X := (1095506151866233/200000000000000000 : ℝ)) (by norm_num) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000010040234433/25000000000000000000 : ℝ) ≤ (10000000000986917/10000000000000000 : ℝ) ^ (4167/1024 : ℝ) := by
    have hpowers : (25000000010040234433/25000000000000000000 : ℝ)^1024 ≤ (10000000000986917/10000000000000000 : ℝ)^4167 := by
      have hnat : (25000000010040234433 : ℕ)^1024*10000000000000000^4167 ≤ 10000000000986917^4167*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000010040234433 25000000000000000000 10000000000986917 10000000000000000 1024 4167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000000986917/10000000000000000 : ℝ)) (X := (25000000010040234433/25000000000000000000 : ℝ)) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50273876548006792683/50000000000000000000 : ℝ) ≤ (10013432786070999/10000000000000000 : ℝ) ^ (4167/1024 : ℝ) := by
    have hpowers : (50273876548006792683/50000000000000000000 : ℝ)^1024 ≤ (10013432786070999/10000000000000000 : ℝ)^4167 := by
      have hnat : (50273876548006792683 : ℕ)^1024*10000000000000000^4167 ≤ 10013432786070999^4167*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50273876548006792683 50000000000000000000 10013432786070999 10000000000000000 1024 4167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10013432786070999/10000000000000000 : ℝ)) (X := (50273876548006792683/50000000000000000000 : ℝ)) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (101095506151866233/100000000000000000 : ℝ) ≤ (10026865571155081/10000000000000000 : ℝ) ^ (4167/1024 : ℝ) := by
    have hpowers : (101095506151866233/100000000000000000 : ℝ)^1024 ≤ (10026865571155081/10000000000000000 : ℝ)^4167 := by
      have hnat : (101095506151866233 : ℕ)^1024*10000000000000000^4167 ≤ 10026865571155081^4167*100000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101095506151866233 100000000000000000 10026865571155081 10000000000000000 1024 4167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10026865571155081/10000000000000000 : ℝ)) (X := (101095506151866233/100000000000000000 : ℝ)) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10040234433/50000000000000000000 : ℝ) ≤ ((273998877680992892821/274010000000000000000 : ℝ)+2*(6716392542041/1370050000000000 : ℝ)*(207/50000 : ℝ))^(4167/1024 : ℝ) := by
    rw [show (273998877680992892821/274010000000000000000 : ℝ)+2*(6716392542041/1370050000000000 : ℝ)*(207/50000 : ℝ)=(10000000000986917/10000000000000000 : ℝ) by norm_num, show 1+2*(10040234433/50000000000000000000 : ℝ)=(25000000010040234433/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1095506151866233/200000000000000000 : ℝ)+(10040234433/50000000000000000000 : ℝ) ≤ ((273998877680992892821/274010000000000000000 : ℝ)+(6716392542041/1370050000000000 : ℝ)*((5563/20000 : ℝ)+(207/50000 : ℝ)))^(4167/1024 : ℝ) := by
    rw [show (273998877680992892821/274010000000000000000 : ℝ)+(6716392542041/1370050000000000 : ℝ)*((5563/20000 : ℝ)+(207/50000 : ℝ))=(10013432786070999/10000000000000000 : ℝ) by norm_num, show 1+(1095506151866233/200000000000000000 : ℝ)+(10040234433/50000000000000000000 : ℝ)=(50273876548006792683/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1095506151866233/200000000000000000 : ℝ) ≤ ((273998877680992892821/274010000000000000000 : ℝ)+2*(6716392542041/1370050000000000 : ℝ)*(5563/20000 : ℝ))^(4167/1024 : ℝ) := by
    rw [show (273998877680992892821/274010000000000000000 : ℝ)+2*(6716392542041/1370050000000000 : ℝ)*(5563/20000 : ℝ)=(10026865571155081/10000000000000000 : ℝ) by norm_num, show 1+2*(1095506151866233/200000000000000000 : ℝ)=(101095506151866233/100000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (273998877680992892821/274010000000000000000 : ℝ)*(X 1 0+X 2 0)+(6716392542041/1370050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4167/1024 : ℝ)) (lo := (207/50000 : ℝ)) (hi := (5563/20000 : ℝ)) (c := (273998877680992892821/274010000000000000000 : ℝ)) (alpha := (6716392542041/1370050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (273998877680992892821/274010000000000000000 : ℝ)*(X 0 1+X 2 1)+(6716392542041/1370050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4167/1024 : ℝ)) (lo := (207/50000 : ℝ)) (hi := (5563/20000 : ℝ)) (c := (273998877680992892821/274010000000000000000 : ℝ)) (alpha := (6716392542041/1370050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (273998877680992892821/274010000000000000000 : ℝ)*(X 0 2+X 1 2)+(6716392542041/1370050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4167/1024 : ℝ)) (lo := (207/50000 : ℝ)) (hi := (5563/20000 : ℝ)) (c := (273998877680992892821/274010000000000000000 : ℝ)) (alpha := (6716392542041/1370050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-262059397/1250000000 : ℝ)*X 0 0+(712687779/1250000000 : ℝ)*X 0 1+(1250568663/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1083824381/2000000000 : ℝ)*X 1 0+(-618454091/2500000000 : ℝ)*X 1 1+(125056849/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2709561921/5000000000 : ℝ)*X 2 0+(2501136119/5000000000 : ℝ)*X 2 1+(-2473816029/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1079360093/2500000000 : ℝ)*X 0 0+(3677050741/10000000000 : ℝ)*X 0 1+(633517903/1250000000 : ℝ)*X 0 2+(1079360093/2500000000 : ℝ)*X 1 0+(3677050741/10000000000 : ℝ)*X 1 1+(633517903/1250000000 : ℝ)*X 1 2+(1079360093/2500000000 : ℝ)*X 2 0+(3677050741/10000000000 : ℝ)*X 2 1+(633517903/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-83891267/400000000 : ℝ)*X 0 0+(5011821571/10000000000 : ℝ)*X 0 1+(2845882939/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5239852507/10000000000 : ℝ)*X 1 0+(-111520263/625000000 : ℝ)*X 1 1+(5691765537/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1309963143/2500000000 : ℝ)*X 2 0+(711470717/1250000000 : ℝ)*X 2 1+(-71372953/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4319040739/10000000000 : ℝ)*X 0 0+(2524575517/5000000000 : ℝ)*X 0 1+(3696419609/10000000000 : ℝ)*X 0 2+(4319040739/10000000000 : ℝ)*X 1 0+(2524575517/5000000000 : ℝ)*X 1 1+(3696419609/10000000000 : ℝ)*X 1 2+(4319040739/10000000000 : ℝ)*X 2 0+(2524575517/5000000000 : ℝ)*X 2 1+(3696419609/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (40858716840818231538951/17125625000000000000000000000 : ℝ) := by norm_num
    linear_combination (82039243/50000000000000 : ℝ)*(base1) + (440410751/100000000000000 : ℝ)*(base19) + (340086781/50000000000000 : ℝ)*(base23) + (170386673/100000000000000 : ℝ)*(base37) + (28933659/20000000000000 : ℝ)*(lower2) + (1074503316646417/100000000000000 : ℝ)*(major0) + (1074503316646417/100000000000000 : ℝ)*(major1) + (1074503316646417/100000000000000 : ℝ)*(major2) + (715074206514337/50000000000000 : ℝ)*(sp0) + (1430148375078399/100000000000000 : ℝ)*(sp1) + (286029600053673/20000000000000 : ℝ)*(sp2) + (718857403811071/100000000000000 : ℝ)*(sp3) + (566538963/100000000000000 : ℝ)*(sp4) + (135047223/100000000000000 : ℝ)*(sp6) + (71885773827623/10000000000000 : ℝ)*(f.failure) + (28602976309783/2000000000000 : ℝ)*(f.sum) + (464220931709379/137005000000000000000000000000 : ℝ)*base65 + (74028392488997927643/27401000000000000000000000000000000 : ℝ)*base68 + (112422235656611927643/27401000000000000000000000000000000 : ℝ)*base70 + (140103198100347072357/27401000000000000000000000000000000 : ℝ)*base71 + (147729296497319/137005000000000000000000000000 : ℝ)*base73 + (47095897307889927643/27401000000000000000000000000000000 : ℝ)*base76 + (144634342791156072357/27401000000000000000000000000000000 : ℝ)*base77 + (4444488638445072357/27401000000000000000000000000000000 : ℝ)*base79 + (235204244102763/68502500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1840979/250000000000000000000 : ℝ)*base90 + (1840979/250000000000000000000 : ℝ)*base92 + (1840979/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (288007127468501593299/53517578125000000000000000 : ℝ) := by norm_num
    linear_combination (18304153/25000000000000 : ℝ)*(base1) + (1199084069/100000000000000 : ℝ)*(base19) + (1242663869/100000000000000 : ℝ)*(base23) + (104160227/100000000000000 : ℝ)*(upper3) + (59030453/50000000000000 : ℝ)*(upper5) + (5524885382569/500000000000 : ℝ)*(major0) + (5524885382569/500000000000 : ℝ)*(major1) + (5524885382569/500000000000 : ℝ)*(major2) + (1162483203/25000000000000 : ℝ)*(sp1) + (5390414101/100000000000000 : ℝ)*(sp2) + (183838617158601/12500000000000 : ℝ)*(sp4) + (294140603007063/20000000000000 : ℝ)*(sp5) + (1470702230974227/100000000000000 : ℝ)*(sp6) + (739245036374033/100000000000000 : ℝ)*(sp7) + (147849021918129/20000000000000 : ℝ)*(f.failure) + (367677216013049/25000000000000 : ℝ)*(f.sum) + (69447608014467/27401000000000000000000000000 : ℝ)*base66 + (465891999153012851/137005000000000000000000000000000 : ℝ)*base68 + (219586620154832149/137005000000000000000000000000000 : ℝ)*base69 + (224557787530677149/137005000000000000000000000000000 : ℝ)*base71 + (91936024012157/13700500000000000000000000000 : ℝ)*base74 + (756100768861577149/137005000000000000000000000000000 : ℝ)*base75 + (64526368577927851/137005000000000000000000000000000 : ℝ)*base78 + (1032251042090722851/137005000000000000000000000000000 : ℝ)*base80 + (119862513531773/27401000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (3513083/500000000000000000000 : ℝ)*base89 + (3513083/500000000000000000000 : ℝ)*base91 + (3513083/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1142_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37368427/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5563/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (207/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (113/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20437/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1142_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1142_s2_0 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2149708147/10000000000 : ℝ)*x 0 + (688850301/1250000000 : ℝ)*x 1 + (2579562213/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2149708147/10000000000 : ℝ)^8335 ≤ (13028700173917/100000000000000 : ℝ)^6287 := by
    have hnat : (2149708147 : ℕ)^8335*100000000000000^6287 ≤ 13028700173917^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149708147 10000000000 13028700173917 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (688850301/1250000000 : ℝ)^8335 ≤ (22692647995413/50000000000000 : ℝ)^6287 := by
    have hnat : (688850301 : ℕ)^8335*50000000000000^6287 ≤ 22692647995413^6287*1250000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      688850301 1250000000 22692647995413 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2579562213/5000000000 : ℝ)^8335 ≤ (8317200764081/20000000000000 : ℝ)^6287 := by
    have hnat : (2579562213 : ℕ)^8335*20000000000000^6287 ≤ 8317200764081^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2579562213 5000000000 8317200764081 20000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2149708147/10000000000 : ℝ), (688850301/1250000000 : ℝ), (2579562213/5000000000 : ℝ)] ![(13028700173917/100000000000000 : ℝ), (22692647995413/50000000000000 : ℝ), (8317200764081/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2149708147/10000000000 : ℝ)|^8335 ≤ (13028700173917/100000000000000 : ℝ)^6287
        have hw : |(-2149708147/10000000000 : ℝ)|=(2149708147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(688850301/1250000000 : ℝ)|^8335 ≤ (22692647995413/50000000000000 : ℝ)^6287
        have hw : |(688850301/1250000000 : ℝ)|=(688850301/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2579562213/5000000000 : ℝ)|^8335 ≤ (8317200764081/20000000000000 : ℝ)^6287
        have hw : |(2579562213/5000000000 : ℝ)|=(2579562213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s2_1 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (83966607/156250000 : ℝ)*x 0 + (-2332545389/10000000000 : ℝ)*x 1 + (5159126469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83966607/156250000 : ℝ)^8335 ≤ (2743513048223/6250000000000 : ℝ)^6287 := by
    have hnat : (83966607 : ℕ)^8335*6250000000000^6287 ≤ 2743513048223^6287*156250000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83966607 156250000 2743513048223 6250000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2332545389/10000000000 : ℝ)^8335 ≤ (580710622837/4000000000000 : ℝ)^6287 := by
    have hnat : (2332545389 : ℕ)^8335*4000000000000^6287 ≤ 580710622837^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2332545389 10000000000 580710622837 4000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5159126469/10000000000 : ℝ)^8335 ≤ (41586025652817/100000000000000 : ℝ)^6287 := by
    have hnat : (5159126469 : ℕ)^8335*100000000000000^6287 ≤ 41586025652817^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5159126469 10000000000 41586025652817 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83966607/156250000 : ℝ), (-2332545389/10000000000 : ℝ), (5159126469/10000000000 : ℝ)] ![(2743513048223/6250000000000 : ℝ), (580710622837/4000000000000 : ℝ), (41586025652817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83966607/156250000 : ℝ)|^8335 ≤ (2743513048223/6250000000000 : ℝ)^6287
        have hw : |(83966607/156250000 : ℝ)|=(83966607/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2332545389/10000000000 : ℝ)|^8335 ≤ (580710622837/4000000000000 : ℝ)^6287
        have hw : |(-2332545389/10000000000 : ℝ)|=(2332545389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5159126469/10000000000 : ℝ)|^8335 ≤ (41586025652817/100000000000000 : ℝ)^6287
        have hw : |(5159126469/10000000000 : ℝ)|=(5159126469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s2_2 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (83966607/156250000 : ℝ)*x 0 + (64489079/125000000 : ℝ)*x 1 + (-116627279/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83966607/156250000 : ℝ)^8335 ≤ (2743513048223/6250000000000 : ℝ)^6287 := by
    have hnat : (83966607 : ℕ)^8335*6250000000000^6287 ≤ 2743513048223^6287*156250000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83966607 156250000 2743513048223 6250000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (64489079/125000000 : ℝ)^8335 ≤ (41586024060537/100000000000000 : ℝ)^6287 := by
    have hnat : (64489079 : ℕ)^8335*100000000000000^6287 ≤ 41586024060537^6287*125000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64489079 125000000 41586024060537 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (116627279/500000000 : ℝ)^8335 ≤ (14517767146957/100000000000000 : ℝ)^6287 := by
    have hnat : (116627279 : ℕ)^8335*100000000000000^6287 ≤ 14517767146957^6287*500000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116627279 500000000 14517767146957 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83966607/156250000 : ℝ), (64489079/125000000 : ℝ), (-116627279/500000000 : ℝ)] ![(2743513048223/6250000000000 : ℝ), (41586024060537/100000000000000 : ℝ), (14517767146957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83966607/156250000 : ℝ)|^8335 ≤ (2743513048223/6250000000000 : ℝ)^6287
        have hw : |(83966607/156250000 : ℝ)|=(83966607/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(64489079/125000000 : ℝ)|^8335 ≤ (41586024060537/100000000000000 : ℝ)^6287
        have hw : |(64489079/125000000 : ℝ)|=(64489079/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-116627279/500000000 : ℝ)|^8335 ≤ (14517767146957/100000000000000 : ℝ)^6287
        have hw : |(-116627279/500000000 : ℝ)|=(116627279/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s2_3 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2176979577/5000000000 : ℝ)*x 0 + (2009030831/5000000000 : ℝ)*x 1 + (4717711189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2176979577/5000000000 : ℝ)^8335 ≤ (33208584744287/100000000000000 : ℝ)^6287 := by
    have hnat : (2176979577 : ℕ)^8335*100000000000000^6287 ≤ 33208584744287^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176979577 5000000000 33208584744287 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2009030831/5000000000 : ℝ)^8335 ≤ (14927751403551/50000000000000 : ℝ)^6287 := by
    have hnat : (2009030831 : ℕ)^8335*50000000000000^6287 ≤ 14927751403551^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2009030831 5000000000 14927751403551 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4717711189/10000000000 : ℝ)^8335 ≤ (36935912437121/100000000000000 : ℝ)^6287 := by
    have hnat : (4717711189 : ℕ)^8335*100000000000000^6287 ≤ 36935912437121^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4717711189 10000000000 36935912437121 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2176979577/5000000000 : ℝ), (2009030831/5000000000 : ℝ), (4717711189/10000000000 : ℝ)] ![(33208584744287/100000000000000 : ℝ), (14927751403551/50000000000000 : ℝ), (36935912437121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2176979577/5000000000 : ℝ)|^8335 ≤ (33208584744287/100000000000000 : ℝ)^6287
        have hw : |(2176979577/5000000000 : ℝ)|=(2176979577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2009030831/5000000000 : ℝ)|^8335 ≤ (14927751403551/50000000000000 : ℝ)^6287
        have hw : |(2009030831/5000000000 : ℝ)|=(2009030831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4717711189/10000000000 : ℝ)|^8335 ≤ (36935912437121/100000000000000 : ℝ)^6287
        have hw : |(4717711189/10000000000 : ℝ)|=(4717711189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s2_4 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-67181587/312500000 : ℝ)*x 0 + (322596847/625000000 : ℝ)*x 1 + (550835293/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67181587/312500000 : ℝ)^8335 ≤ (6514762432271/50000000000000 : ℝ)^6287 := by
    have hnat : (67181587 : ℕ)^8335*50000000000000^6287 ≤ 6514762432271^6287*312500000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67181587 312500000 6514762432271 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (322596847/625000000 : ℝ)^8335 ≤ (20805960892263/50000000000000 : ℝ)^6287 := by
    have hnat : (322596847 : ℕ)^8335*50000000000000^6287 ≤ 20805960892263^6287*625000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      322596847 625000000 20805960892263 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (550835293/1000000000 : ℝ)^8335 ≤ (45358553332593/100000000000000 : ℝ)^6287 := by
    have hnat : (550835293 : ℕ)^8335*100000000000000^6287 ≤ 45358553332593^6287*1000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550835293 1000000000 45358553332593 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-67181587/312500000 : ℝ), (322596847/625000000 : ℝ), (550835293/1000000000 : ℝ)] ![(6514762432271/50000000000000 : ℝ), (20805960892263/50000000000000 : ℝ), (45358553332593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-67181587/312500000 : ℝ)|^8335 ≤ (6514762432271/50000000000000 : ℝ)^6287
        have hw : |(-67181587/312500000 : ℝ)|=(67181587/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(322596847/625000000 : ℝ)|^8335 ≤ (20805960892263/50000000000000 : ℝ)^6287
        have hw : |(322596847/625000000 : ℝ)|=(322596847/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(550835293/1000000000 : ℝ)|^8335 ≤ (45358553332593/100000000000000 : ℝ)^6287
        have hw : |(550835293/1000000000 : ℝ)|=(550835293/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s2_5 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5284632851/10000000000 : ℝ)*x 0 + (-991658429/5000000000 : ℝ)*x 1 + (2754176803/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5284632851/10000000000 : ℝ)^8335 ≤ (5366566079461/12500000000000 : ℝ)^6287 := by
    have hnat : (5284632851 : ℕ)^8335*12500000000000^6287 ≤ 5366566079461^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5284632851 10000000000 5366566079461 12500000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (991658429/5000000000 : ℝ)^8335 ≤ (5854455317851/50000000000000 : ℝ)^6287 := by
    have hnat : (991658429 : ℕ)^8335*50000000000000^6287 ≤ 5854455317851^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      991658429 5000000000 5854455317851 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2754176803/5000000000 : ℝ)^8335 ≤ (22679280356211/50000000000000 : ℝ)^6287 := by
    have hnat : (2754176803 : ℕ)^8335*50000000000000^6287 ≤ 22679280356211^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2754176803 5000000000 22679280356211 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5284632851/10000000000 : ℝ), (-991658429/5000000000 : ℝ), (2754176803/5000000000 : ℝ)] ![(5366566079461/12500000000000 : ℝ), (5854455317851/50000000000000 : ℝ), (22679280356211/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5284632851/10000000000 : ℝ)|^8335 ≤ (5366566079461/12500000000000 : ℝ)^6287
        have hw : |(5284632851/10000000000 : ℝ)|=(5284632851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-991658429/5000000000 : ℝ)|^8335 ≤ (5854455317851/50000000000000 : ℝ)^6287
        have hw : |(-991658429/5000000000 : ℝ)|=(991658429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2754176803/5000000000 : ℝ)|^8335 ≤ (22679280356211/50000000000000 : ℝ)^6287
        have hw : |(2754176803/5000000000 : ℝ)|=(2754176803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s2_6 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1321157837/2500000000 : ℝ)*x 0 + (2754176699/5000000000 : ℝ)*x 1 + (-1983319217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321157837/2500000000 : ℝ)^8335 ≤ (8586502489541/20000000000000 : ℝ)^6287 := by
    have hnat : (1321157837 : ℕ)^8335*20000000000000^6287 ≤ 8586502489541^6287*2500000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321157837 2500000000 8586502489541 20000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2754176699/5000000000 : ℝ)^8335 ≤ (22679279220853/50000000000000 : ℝ)^6287 := by
    have hnat : (2754176699 : ℕ)^8335*50000000000000^6287 ≤ 22679279220853^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2754176699 5000000000 22679279220853 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1983319217/10000000000 : ℝ)^8335 ≤ (1463616137403/12500000000000 : ℝ)^6287 := by
    have hnat : (1983319217 : ℕ)^8335*12500000000000^6287 ≤ 1463616137403^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1983319217 10000000000 1463616137403 12500000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321157837/2500000000 : ℝ), (2754176699/5000000000 : ℝ), (-1983319217/10000000000 : ℝ)] ![(8586502489541/20000000000000 : ℝ), (22679279220853/50000000000000 : ℝ), (1463616137403/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321157837/2500000000 : ℝ)|^8335 ≤ (8586502489541/20000000000000 : ℝ)^6287
        have hw : |(1321157837/2500000000 : ℝ)|=(1321157837/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2754176699/5000000000 : ℝ)|^8335 ≤ (22679279220853/50000000000000 : ℝ)^6287
        have hw : |(2754176699/5000000000 : ℝ)|=(2754176699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1983319217/10000000000 : ℝ)|^8335 ≤ (1463616137403/12500000000000 : ℝ)^6287
        have hw : |(-1983319217/10000000000 : ℝ)|=(1983319217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s2_7 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (217708123/500000000 : ℝ)*x 0 + (4712888213/10000000000 : ℝ)*x 1 + (1005733261/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (217708123/500000000 : ℝ)^8335 ≤ (1037832517127/3125000000000 : ℝ)^6287 := by
    have hnat : (217708123 : ℕ)^8335*3125000000000^6287 ≤ 1037832517127^6287*500000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217708123 500000000 1037832517127 3125000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4712888213/10000000000 : ℝ)^8335 ≤ (3688586032727/10000000000000 : ℝ)^6287 := by
    have hnat : (4712888213 : ℕ)^8335*10000000000000^6287 ≤ 3688586032727^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4712888213 10000000000 3688586032727 10000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1005733261/2500000000 : ℝ)^8335 ≤ (29903499117117/100000000000000 : ℝ)^6287 := by
    have hnat : (1005733261 : ℕ)^8335*100000000000000^6287 ≤ 29903499117117^6287*2500000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005733261 2500000000 29903499117117 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(217708123/500000000 : ℝ), (4712888213/10000000000 : ℝ), (1005733261/2500000000 : ℝ)] ![(1037832517127/3125000000000 : ℝ), (3688586032727/10000000000000 : ℝ), (29903499117117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(217708123/500000000 : ℝ)|^8335 ≤ (1037832517127/3125000000000 : ℝ)^6287
        have hw : |(217708123/500000000 : ℝ)|=(217708123/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4712888213/10000000000 : ℝ)|^8335 ≤ (3688586032727/10000000000000 : ℝ)^6287
        have hw : |(4712888213/10000000000 : ℝ)|=(4712888213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1005733261/2500000000 : ℝ)|^8335 ≤ (29903499117117/100000000000000 : ℝ)^6287
        have hw : |(1005733261/2500000000 : ℝ)|=(1005733261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1142_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37368427/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20437/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (113/2000 : ℝ)*pair X i i ≤ pair X i h) :
    (907/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8251/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20437/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (113/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20437/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (113/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20437/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (113/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20437/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (113/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20437/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (113/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20437/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (113/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (113/2000 : ℝ) ^ (4167/1024 : ℝ) ≤ (834960442177981/100000000000000000000 : ℝ) := by
    have hpowers : (113/2000 : ℝ)^4167 ≤ (834960442177981/100000000000000000000 : ℝ)^1024 := by
      have hnat : (113 : ℕ)^4167*100000000000000000000^1024 ≤ 834960442177981^1024*2000^4167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        113 2000 834960442177981 100000000000000000000 4167 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (113/2000 : ℝ)) (X := (834960442177981/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (20437/100000 : ℝ) ^ (4167/1024 : ℝ) ≤ (156262837430457137/100000000000000000000 : ℝ) := by
    have hpowers : (20437/100000 : ℝ)^4167 ≤ (156262837430457137/100000000000000000000 : ℝ)^1024 := by
      have hnat : (20437 : ℕ)^4167*100000000000000000000^1024 ≤ 156262837430457137^1024*100000^4167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20437 100000 156262837430457137 100000000000000000000 4167 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20437/100000 : ℝ)) (X := (156262837430457137/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000834960442177981/50000000000000000000 : ℝ) ≤ (5000020518217141/5000000000000000 : ℝ) ^ (4167/1024 : ℝ) := by
    have hpowers : (50000834960442177981/50000000000000000000 : ℝ)^1024 ≤ (5000020518217141/5000000000000000 : ℝ)^4167 := by
      have hnat : (50000834960442177981 : ℕ)^1024*5000000000000000^4167 ≤ 5000020518217141^4167*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000834960442177981 50000000000000000000 5000020518217141 5000000000000000 1024 4167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000020518217141/5000000000000000 : ℝ)) (X := (50000834960442177981/50000000000000000000 : ℝ)) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50078548898936317559/50000000000000000000 : ℝ) ≤ (10003858241519363/10000000000000000 : ℝ) ^ (4167/1024 : ℝ) := by
    have hpowers : (50078548898936317559/50000000000000000000 : ℝ)^1024 ≤ (10003858241519363/10000000000000000 : ℝ)^4167 := by
      have hnat : (50078548898936317559 : ℕ)^1024*10000000000000000^4167 ≤ 10003858241519363^4167*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50078548898936317559 50000000000000000000 10003858241519363 10000000000000000 1024 4167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003858241519363/10000000000000000 : ℝ)) (X := (50078548898936317559/50000000000000000000 : ℝ)) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50156262837430457137/50000000000000000000 : ℝ) ≤ (2501918861651111/2500000000000000 : ℝ) ^ (4167/1024 : ℝ) := by
    have hpowers : (50156262837430457137/50000000000000000000 : ℝ)^1024 ≤ (2501918861651111/2500000000000000 : ℝ)^4167 := by
      have hnat : (50156262837430457137 : ℕ)^1024*2500000000000000^4167 ≤ 2501918861651111^4167*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50156262837430457137 50000000000000000000 2501918861651111 2500000000000000 1024 4167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501918861651111/2500000000000000 : ℝ)) (X := (50156262837430457137/50000000000000000000 : ℝ)) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(834960442177981/100000000000000000000 : ℝ) ≤ ((24637912064715385439/24645000000000000000 : ℝ)+2*(1272401695027/492900000000000 : ℝ)*(113/2000 : ℝ))^(4167/1024 : ℝ) := by
    rw [show (24637912064715385439/24645000000000000000 : ℝ)+2*(1272401695027/492900000000000 : ℝ)*(113/2000 : ℝ)=(5000020518217141/5000000000000000 : ℝ) by norm_num, show 1+2*(834960442177981/100000000000000000000 : ℝ)=(50000834960442177981/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(156262837430457137/100000000000000000000 : ℝ)+(834960442177981/100000000000000000000 : ℝ) ≤ ((24637912064715385439/24645000000000000000 : ℝ)+(1272401695027/492900000000000 : ℝ)*((20437/100000 : ℝ)+(113/2000 : ℝ)))^(4167/1024 : ℝ) := by
    rw [show (24637912064715385439/24645000000000000000 : ℝ)+(1272401695027/492900000000000 : ℝ)*((20437/100000 : ℝ)+(113/2000 : ℝ))=(10003858241519363/10000000000000000 : ℝ) by norm_num, show 1+(156262837430457137/100000000000000000000 : ℝ)+(834960442177981/100000000000000000000 : ℝ)=(50078548898936317559/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(156262837430457137/100000000000000000000 : ℝ) ≤ ((24637912064715385439/24645000000000000000 : ℝ)+2*(1272401695027/492900000000000 : ℝ)*(20437/100000 : ℝ))^(4167/1024 : ℝ) := by
    rw [show (24637912064715385439/24645000000000000000 : ℝ)+2*(1272401695027/492900000000000 : ℝ)*(20437/100000 : ℝ)=(2501918861651111/2500000000000000 : ℝ) by norm_num, show 1+2*(156262837430457137/100000000000000000000 : ℝ)=(50156262837430457137/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (24637912064715385439/24645000000000000000 : ℝ)*(X 1 0+X 2 0)+(1272401695027/492900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4167/1024 : ℝ)) (lo := (113/2000 : ℝ)) (hi := (20437/100000 : ℝ)) (c := (24637912064715385439/24645000000000000000 : ℝ)) (alpha := (1272401695027/492900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (24637912064715385439/24645000000000000000 : ℝ)*(X 0 1+X 2 1)+(1272401695027/492900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4167/1024 : ℝ)) (lo := (113/2000 : ℝ)) (hi := (20437/100000 : ℝ)) (c := (24637912064715385439/24645000000000000000 : ℝ)) (alpha := (1272401695027/492900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (24637912064715385439/24645000000000000000 : ℝ)*(X 0 2+X 1 2)+(1272401695027/492900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4167/1024 : ℝ)) (lo := (113/2000 : ℝ)) (hi := (20437/100000 : ℝ)) (c := (24637912064715385439/24645000000000000000 : ℝ)) (alpha := (1272401695027/492900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2149708147/10000000000 : ℝ)*X 0 0+(688850301/1250000000 : ℝ)*X 0 1+(2579562213/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((83966607/156250000 : ℝ)*X 1 0+(-2332545389/10000000000 : ℝ)*X 1 1+(5159126469/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((83966607/156250000 : ℝ)*X 2 0+(64489079/125000000 : ℝ)*X 2 1+(-116627279/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2176979577/5000000000 : ℝ)*X 0 0+(2009030831/5000000000 : ℝ)*X 0 1+(4717711189/10000000000 : ℝ)*X 0 2+(2176979577/5000000000 : ℝ)*X 1 0+(2009030831/5000000000 : ℝ)*X 1 1+(4717711189/10000000000 : ℝ)*X 1 2+(2176979577/5000000000 : ℝ)*X 2 0+(2009030831/5000000000 : ℝ)*X 2 1+(4717711189/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-67181587/312500000 : ℝ)*X 0 0+(322596847/625000000 : ℝ)*X 0 1+(550835293/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5284632851/10000000000 : ℝ)*X 1 0+(-991658429/5000000000 : ℝ)*X 1 1+(2754176803/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1321157837/2500000000 : ℝ)*X 2 0+(2754176699/5000000000 : ℝ)*X 2 1+(-1983319217/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((217708123/500000000 : ℝ)*X 0 0+(4712888213/10000000000 : ℝ)*X 0 1+(1005733261/2500000000 : ℝ)*X 0 2+(217708123/500000000 : ℝ)*X 1 0+(4712888213/10000000000 : ℝ)*X 1 1+(1005733261/2500000000 : ℝ)*X 1 2+(217708123/500000000 : ℝ)*X 2 0+(4712888213/10000000000 : ℝ)*X 2 1+(1005733261/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (553279994252584129399572927/51343750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (642703653/50000000000000 : ℝ)*(base19) + (966405277/100000000000000 : ℝ)*(base23) + (386049121/100000000000000 : ℝ)*(upper3) + (34285463/20000000000000 : ℝ)*(upper4) + (10477407/50000000000000 : ℝ)*(upper5) + (534108167276493/25000000000000 : ℝ)*(major0) + (534108167276493/25000000000000 : ℝ)*(major1) + (534108167276493/25000000000000 : ℝ)*(major2) + (710884565456929/25000000000000 : ℝ)*(sp0) + (2843560374852599/100000000000000 : ℝ)*(sp1) + (710890173463657/25000000000000 : ℝ)*(sp2) + (285858684102443/20000000000000 : ℝ)*(sp3) + (5849608047/25000000000000 : ℝ)*(sp4) + (1979647997/20000000000000 : ℝ)*(sp7) + (7146516593761/500000000000 : ℝ)*(f.failure) + (568712332051981/20000000000000 : ℝ)*(f.sum) + (17420344190471/4107500000000000000000000000 : ℝ)*base66 + (1265761790705286809/205375000000000000000000000000000 : ℝ)*base67 + (198032459826713191/205375000000000000000000000000000 : ℝ)*base70 + (155916481930838191/205375000000000000000000000000000 : ℝ)*base72 + (729164202659/256718750000000000000000000 : ℝ)*base73 + (666049445604838191/205375000000000000000000000000000 : ℝ)*base76 + (583038687762838191/205375000000000000000000000000000 : ℝ)*base78 + (1667175799170713191/205375000000000000000000000000000 : ℝ)*base80 + (36779281899277/8215000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (83947/12500000000000000000 : ℝ)*base89 + (83947/12500000000000000000 : ℝ)*base91 + (83947/12500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1710607702947730475275551439/410750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (52708607/10000000000000 : ℝ)*(base19) + (68837/50000000000 : ℝ)*(base23) + (87712317/25000000000000 : ℝ)*(upper2) + (4503229/3125000000000 : ℝ)*(upper3) + (19339579/100000000000000 : ℝ)*(upper5) + (2166423125194001/100000000000000 : ℝ)*(major0) + (2166423125194001/100000000000000 : ℝ)*(major1) + (2166423125194001/100000000000000 : ℝ)*(major2) + (2789224523/50000000000000 : ℝ)*(sp0) + (552515599/4000000000000 : ℝ)*(sp1) + (360434147504563/12500000000000 : ℝ)*(sp4) + (45054131539211/1562500000000 : ℝ)*(sp5) + (2883478620811549/100000000000000 : ℝ)*(sp6) + (1449367353082591/100000000000000 : ℝ)*(sp7) + (1449367353082591/100000000000000 : ℝ)*(f.failure) + (2883478758485549/100000000000000 : ℝ)*(f.sum) + (100036033304537/24645000000000000000000000000 : ℝ)*base65 + (24993866039988598561/2464500000000000000000000000000000 : ℝ)*base68 + (484276764876901439/2464500000000000000000000000000000 : ℝ)*base69 + (1356476137961098561/2464500000000000000000000000000000 : ℝ)*base72 + (10474838274493/24645000000000000000000000000 : ℝ)*base74 + (9897273378473401439/2464500000000000000000000000000000 : ℝ)*base75 + (340050654107098561/2464500000000000000000000000000000 : ℝ)*base78 + (3515365374315598561/2464500000000000000000000000000000 : ℝ)*base80 + (18852123014029/3080625000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1754357/2500000000000000000000 : ℝ)*base89 + (1754357/2500000000000000000000 : ℝ)*base91 + (1754357/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1142_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37368427/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20437/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (113/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (907/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8251/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1142_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1142_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37368427/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (907/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8251/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1142_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1142_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1142_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37368427/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (907/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8251/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1142_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
