-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1534_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:05:36.140825+00:00
-- url     : https://prove2.me/submissions/e8ca20e8-4831-49e9-96f9-9faf13afa53f

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
theorem support_rectangle_w1534_s0_0 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-831373683/5000000000 : ℝ)*x 0 + (5896089653/10000000000 : ℝ)*x 1 + (608076947/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (831373683/5000000000 : ℝ)^4565 ≤ (9896959928619/100000000000000 : ℝ)^3541 := by
    have hnat : (831373683 : ℕ)^4565*100000000000000^3541 ≤ 9896959928619^3541*5000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      831373683 5000000000 9896959928619 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5896089653/10000000000 : ℝ)^4565 ≤ (50607503790589/100000000000000 : ℝ)^3541 := by
    have hnat : (5896089653 : ℕ)^4565*100000000000000^3541 ≤ 50607503790589^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5896089653 10000000000 50607503790589 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (608076947/1250000000 : ℝ)^4565 ≤ (9873884068047/25000000000000 : ℝ)^3541 := by
    have hnat : (608076947 : ℕ)^4565*25000000000000^3541 ≤ 9873884068047^3541*1250000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      608076947 1250000000 9873884068047 25000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-831373683/5000000000 : ℝ), (5896089653/10000000000 : ℝ), (608076947/1250000000 : ℝ)] ![(9896959928619/100000000000000 : ℝ), (50607503790589/100000000000000 : ℝ), (9873884068047/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-831373683/5000000000 : ℝ)|^4565 ≤ (9896959928619/100000000000000 : ℝ)^3541
        have hw : |(-831373683/5000000000 : ℝ)|=(831373683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5896089653/10000000000 : ℝ)|^4565 ≤ (50607503790589/100000000000000 : ℝ)^3541
        have hw : |(5896089653/10000000000 : ℝ)|=(5896089653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(608076947/1250000000 : ℝ)|^4565 ≤ (9873884068047/25000000000000 : ℝ)^3541
        have hw : |(608076947/1250000000 : ℝ)|=(608076947/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_s0_1 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (547320897/1000000000 : ℝ)*x 0 + (-111964601/500000000 : ℝ)*x 1 + (243230781/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (547320897/1000000000 : ℝ)^4565 ≤ (45977552977963/100000000000000 : ℝ)^3541 := by
    have hnat : (547320897 : ℕ)^4565*100000000000000^3541 ≤ 45977552977963^3541*1000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547320897 1000000000 45977552977963 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (111964601/500000000 : ℝ)^4565 ≤ (14526910281577/100000000000000 : ℝ)^3541 := by
    have hnat : (111964601 : ℕ)^4565*100000000000000^3541 ≤ 14526910281577^3541*500000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111964601 500000000 14526910281577 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (243230781/500000000 : ℝ)^4565 ≤ (4936942091591/12500000000000 : ℝ)^3541 := by
    have hnat : (243230781 : ℕ)^4565*12500000000000^3541 ≤ 4936942091591^3541*500000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      243230781 500000000 4936942091591 12500000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(547320897/1000000000 : ℝ), (-111964601/500000000 : ℝ), (243230781/500000000 : ℝ)] ![(45977552977963/100000000000000 : ℝ), (14526910281577/100000000000000 : ℝ), (4936942091591/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(547320897/1000000000 : ℝ)|^4565 ≤ (45977552977963/100000000000000 : ℝ)^3541
        have hw : |(547320897/1000000000 : ℝ)|=(547320897/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-111964601/500000000 : ℝ)|^4565 ≤ (14526910281577/100000000000000 : ℝ)^3541
        have hw : |(-111964601/500000000 : ℝ)|=(111964601/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(243230781/500000000 : ℝ)|^4565 ≤ (4936942091591/12500000000000 : ℝ)^3541
        have hw : |(243230781/500000000 : ℝ)|=(243230781/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_s0_2 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5473208929/10000000000 : ℝ)*x 0 + (4864615601/10000000000 : ℝ)*x 1 + (-447858419/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5473208929/10000000000 : ℝ)^4565 ≤ (45977552533943/100000000000000 : ℝ)^3541 := by
    have hnat : (5473208929 : ℕ)^4565*100000000000000^3541 ≤ 45977552533943^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5473208929 10000000000 45977552533943 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4864615601/10000000000 : ℝ)^4565 ≤ (39495536533859/100000000000000 : ℝ)^3541 := by
    have hnat : (4864615601 : ℕ)^4565*100000000000000^3541 ≤ 39495536533859^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4864615601 10000000000 39495536533859 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (447858419/2000000000 : ℝ)^4565 ≤ (1815863863603/12500000000000 : ℝ)^3541 := by
    have hnat : (447858419 : ℕ)^4565*12500000000000^3541 ≤ 1815863863603^3541*2000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447858419 2000000000 1815863863603 12500000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5473208929/10000000000 : ℝ), (4864615601/10000000000 : ℝ), (-447858419/2000000000 : ℝ)] ![(45977552533943/100000000000000 : ℝ), (39495536533859/100000000000000 : ℝ), (1815863863603/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5473208929/10000000000 : ℝ)|^4565 ≤ (45977552533943/100000000000000 : ℝ)^3541
        have hw : |(5473208929/10000000000 : ℝ)|=(5473208929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4864615601/10000000000 : ℝ)|^4565 ≤ (39495536533859/100000000000000 : ℝ)^3541
        have hw : |(4864615601/10000000000 : ℝ)|=(4864615601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-447858419/2000000000 : ℝ)|^4565 ≤ (1815863863603/12500000000000 : ℝ)^3541
        have hw : |(-447858419/2000000000 : ℝ)|=(447858419/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_s0_3 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2069631573/5000000000 : ℝ)*x 0 + (772914977/2500000000 : ℝ)*x 1 + (5466919829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2069631573/5000000000 : ℝ)^4565 ≤ (4009159920427/12500000000000 : ℝ)^3541 := by
    have hnat : (2069631573 : ℕ)^4565*12500000000000^3541 ≤ 4009159920427^3541*5000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069631573 5000000000 4009159920427 12500000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (772914977/2500000000 : ℝ)^4565 ≤ (688039568519/3125000000000 : ℝ)^3541 := by
    have hnat : (772914977 : ℕ)^4565*3125000000000^3541 ≤ 688039568519^3541*2500000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      772914977 2500000000 688039568519 3125000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5466919829/10000000000 : ℝ)^4565 ≤ (11477363608447/25000000000000 : ℝ)^3541 := by
    have hnat : (5466919829 : ℕ)^4565*25000000000000^3541 ≤ 11477363608447^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5466919829 10000000000 11477363608447 25000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2069631573/5000000000 : ℝ), (772914977/2500000000 : ℝ), (5466919829/10000000000 : ℝ)] ![(4009159920427/12500000000000 : ℝ), (688039568519/3125000000000 : ℝ), (11477363608447/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2069631573/5000000000 : ℝ)|^4565 ≤ (4009159920427/12500000000000 : ℝ)^3541
        have hw : |(2069631573/5000000000 : ℝ)|=(2069631573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(772914977/2500000000 : ℝ)|^4565 ≤ (688039568519/3125000000000 : ℝ)^3541
        have hw : |(772914977/2500000000 : ℝ)|=(772914977/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5466919829/10000000000 : ℝ)|^4565 ≤ (11477363608447/25000000000000 : ℝ)^3541
        have hw : |(5466919829/10000000000 : ℝ)|=(5466919829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_s0_4 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-3254071/19531250 : ℝ)*x 0 + (9552367/19531250 : ℝ)*x 1 + (2934479127/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3254071/19531250 : ℝ)^4565 ≤ (4961286767461/50000000000000 : ℝ)^3541 := by
    have hnat : (3254071 : ℕ)^4565*50000000000000^3541 ≤ 4961286767461^3541*19531250^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3254071 19531250 4961286767461 50000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9552367/19531250 : ℝ)^4565 ≤ (9942485371737/25000000000000 : ℝ)^3541 := by
    have hnat : (9552367 : ℕ)^4565*25000000000000^3541 ≤ 9942485371737^3541*19531250^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9552367 19531250 9942485371737 25000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2934479127/5000000000 : ℝ)^4565 ≤ (6288435620349/12500000000000 : ℝ)^3541 := by
    have hnat : (2934479127 : ℕ)^4565*12500000000000^3541 ≤ 6288435620349^3541*5000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2934479127 5000000000 6288435620349 12500000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3254071/19531250 : ℝ), (9552367/19531250 : ℝ), (2934479127/5000000000 : ℝ)] ![(4961286767461/50000000000000 : ℝ), (9942485371737/25000000000000 : ℝ), (6288435620349/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3254071/19531250 : ℝ)|^4565 ≤ (4961286767461/50000000000000 : ℝ)^3541
        have hw : |(-3254071/19531250 : ℝ)|=(3254071/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(9552367/19531250 : ℝ)|^4565 ≤ (9942485371737/25000000000000 : ℝ)^3541
        have hw : |(9552367/19531250 : ℝ)|=(9552367/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2934479127/5000000000 : ℝ)|^4565 ≤ (6288435620349/12500000000000 : ℝ)^3541
        have hw : |(2934479127/5000000000 : ℝ)|=(2934479127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_s0_5 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (162228561/312500000 : ℝ)*x 0 + (-617474801/5000000000 : ℝ)*x 1 + (1467239583/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (162228561/312500000 : ℝ)^4565 ≤ (42947717428931/100000000000000 : ℝ)^3541 := by
    have hnat : (162228561 : ℕ)^4565*100000000000000^3541 ≤ 42947717428931^3541*312500000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162228561 312500000 42947717428931 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (617474801/5000000000 : ℝ)^4565 ≤ (843099592303/12500000000000 : ℝ)^3541 := by
    have hnat : (617474801 : ℕ)^4565*12500000000000^3541 ≤ 843099592303^3541*5000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      617474801 5000000000 843099592303 12500000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1467239583/2500000000 : ℝ)^4565 ≤ (2515374291237/5000000000000 : ℝ)^3541 := by
    have hnat : (1467239583 : ℕ)^4565*5000000000000^3541 ≤ 2515374291237^3541*2500000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1467239583 2500000000 2515374291237 5000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(162228561/312500000 : ℝ), (-617474801/5000000000 : ℝ), (1467239583/2500000000 : ℝ)] ![(42947717428931/100000000000000 : ℝ), (843099592303/12500000000000 : ℝ), (2515374291237/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(162228561/312500000 : ℝ)|^4565 ≤ (42947717428931/100000000000000 : ℝ)^3541
        have hw : |(162228561/312500000 : ℝ)|=(162228561/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-617474801/5000000000 : ℝ)|^4565 ≤ (843099592303/12500000000000 : ℝ)^3541
        have hw : |(-617474801/5000000000 : ℝ)|=(617474801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1467239583/2500000000 : ℝ)|^4565 ≤ (2515374291237/5000000000000 : ℝ)^3541
        have hw : |(1467239583/2500000000 : ℝ)|=(1467239583/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_s0_6 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1038262783/2000000000 : ℝ)*x 0 + (1173791723/2000000000 : ℝ)*x 1 + (-617474607/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1038262783/2000000000 : ℝ)^4565 ≤ (42947717034311/100000000000000 : ℝ)^3541 := by
    have hnat : (1038262783 : ℕ)^4565*100000000000000^3541 ≤ 42947717034311^3541*2000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038262783 2000000000 42947717034311 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1173791723/2000000000 : ℝ)^4565 ≤ (196513628719/390625000000 : ℝ)^3541 := by
    have hnat : (1173791723 : ℕ)^4565*390625000000^3541 ≤ 196513628719^3541*2000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1173791723 2000000000 196513628719 390625000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (617474607/5000000000 : ℝ)^4565 ≤ (1348958801303/20000000000000 : ℝ)^3541 := by
    have hnat : (617474607 : ℕ)^4565*20000000000000^3541 ≤ 1348958801303^3541*5000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      617474607 5000000000 1348958801303 20000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1038262783/2000000000 : ℝ), (1173791723/2000000000 : ℝ), (-617474607/5000000000 : ℝ)] ![(42947717034311/100000000000000 : ℝ), (196513628719/390625000000 : ℝ), (1348958801303/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1038262783/2000000000 : ℝ)|^4565 ≤ (42947717034311/100000000000000 : ℝ)^3541
        have hw : |(1038262783/2000000000 : ℝ)|=(1038262783/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1173791723/2000000000 : ℝ)|^4565 ≤ (196513628719/390625000000 : ℝ)^3541
        have hw : |(1173791723/2000000000 : ℝ)|=(1173791723/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-617474607/5000000000 : ℝ)|^4565 ≤ (1348958801303/20000000000000 : ℝ)^3541
        have hw : |(-617474607/5000000000 : ℝ)|=(617474607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_s0_7 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4146946393/10000000000 : ℝ)*x 0 + (1351648831/2500000000 : ℝ)*x 1 + (3154137131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4146946393/10000000000 : ℝ)^4565 ≤ (6430010047091/20000000000000 : ℝ)^3541 := by
    have hnat : (4146946393 : ℕ)^4565*20000000000000^3541 ≤ 6430010047091^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4146946393 10000000000 6430010047091 20000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351648831/2500000000 : ℝ)^4565 ≤ (45257416656683/100000000000000 : ℝ)^3541 := by
    have hnat : (1351648831 : ℕ)^4565*100000000000000^3541 ≤ 45257416656683^3541*2500000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351648831 2500000000 45257416656683 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3154137131/10000000000 : ℝ)^4565 ≤ (22592533091471/100000000000000 : ℝ)^3541 := by
    have hnat : (3154137131 : ℕ)^4565*100000000000000^3541 ≤ 22592533091471^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3154137131 10000000000 22592533091471 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4146946393/10000000000 : ℝ), (1351648831/2500000000 : ℝ), (3154137131/10000000000 : ℝ)] ![(6430010047091/20000000000000 : ℝ), (45257416656683/100000000000000 : ℝ), (22592533091471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4146946393/10000000000 : ℝ)|^4565 ≤ (6430010047091/20000000000000 : ℝ)^3541
        have hw : |(4146946393/10000000000 : ℝ)|=(4146946393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351648831/2500000000 : ℝ)|^4565 ≤ (45257416656683/100000000000000 : ℝ)^3541
        have hw : |(1351648831/2500000000 : ℝ)|=(1351648831/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3154137131/10000000000 : ℝ)|^4565 ≤ (22592533091471/100000000000000 : ℝ)^3541
        have hw : |(3154137131/10000000000 : ℝ)|=(3154137131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1534_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165139109/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1553/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (12601/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4563/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4563 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4563*1^1024 ≤ 0^1024*1^4563 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4563 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4563 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4563/1024 : ℝ) ≤ (210701473135188619/12500000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4563 ≤ (210701473135188619/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4563*12500000000000000000^1024 ≤ 210701473135188619^1024*5^4563 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 210701473135188619 12500000000000000000 4563 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (210701473135188619/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4563 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4563/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4563 := by
      have hnat : (1 : ℕ)^1024*1^4563 ≤ 1^4563*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4563 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4563 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12710701473135188619/12500000000000000000 : ℝ) ≤ (313674456891619/312500000000000 : ℝ) ^ (4563/1024 : ℝ) := by
    have hpowers : (12710701473135188619/12500000000000000000 : ℝ)^1024 ≤ (313674456891619/312500000000000 : ℝ)^4563 := by
      have hnat : (12710701473135188619 : ℕ)^1024*312500000000000^4563 ≤ 313674456891619^4563*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12710701473135188619 12500000000000000000 313674456891619 312500000000000 1024 4563 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (313674456891619/312500000000000 : ℝ)) (X := (12710701473135188619/12500000000000000000 : ℝ)) (by norm_num) 4563 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6460701473135188619/6250000000000000000 : ℝ) ≤ (157424456891619/156250000000000 : ℝ) ^ (4563/1024 : ℝ) := by
    have hpowers : (6460701473135188619/6250000000000000000 : ℝ)^1024 ≤ (157424456891619/156250000000000 : ℝ)^4563 := by
      have hnat : (6460701473135188619 : ℕ)^1024*156250000000000^4563 ≤ 157424456891619^4563*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6460701473135188619 6250000000000000000 157424456891619 156250000000000 1024 4563 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (157424456891619/156250000000000 : ℝ)) (X := (6460701473135188619/6250000000000000000 : ℝ)) (by norm_num) 4563 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(1174456891619/125000000000000 : ℝ)*(0 : ℝ))^(4563/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(1174456891619/125000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(210701473135188619/12500000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(1174456891619/125000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4563/1024 : ℝ) := by
    rw [show (1 : ℝ)+(1174456891619/125000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(313674456891619/312500000000000 : ℝ) by norm_num, show 1+(210701473135188619/12500000000000000000 : ℝ)+(0 : ℝ)=(12710701473135188619/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(210701473135188619/12500000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(1174456891619/125000000000000 : ℝ)*(2/5 : ℝ))^(4563/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(1174456891619/125000000000000 : ℝ)*(2/5 : ℝ)=(157424456891619/156250000000000 : ℝ) by norm_num, show 1+2*(210701473135188619/12500000000000000000 : ℝ)=(6460701473135188619/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(1174456891619/125000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4563/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1174456891619/125000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(1174456891619/125000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4563/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1174456891619/125000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(1174456891619/125000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4563/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1174456891619/125000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-831373683/5000000000 : ℝ)*X 0 0+(5896089653/10000000000 : ℝ)*X 0 1+(608076947/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((547320897/1000000000 : ℝ)*X 1 0+(-111964601/500000000 : ℝ)*X 1 1+(243230781/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5473208929/10000000000 : ℝ)*X 2 0+(4864615601/10000000000 : ℝ)*X 2 1+(-447858419/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2069631573/5000000000 : ℝ)*X 0 0+(772914977/2500000000 : ℝ)*X 0 1+(5466919829/10000000000 : ℝ)*X 0 2+(2069631573/5000000000 : ℝ)*X 1 0+(772914977/2500000000 : ℝ)*X 1 1+(5466919829/10000000000 : ℝ)*X 1 2+(2069631573/5000000000 : ℝ)*X 2 0+(772914977/2500000000 : ℝ)*X 2 1+(5466919829/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-3254071/19531250 : ℝ)*X 0 0+(9552367/19531250 : ℝ)*X 0 1+(2934479127/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((162228561/312500000 : ℝ)*X 1 0+(-617474801/5000000000 : ℝ)*X 1 1+(1467239583/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1038262783/2000000000 : ℝ)*X 2 0+(1173791723/2000000000 : ℝ)*X 2 1+(-617474607/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4146946393/10000000000 : ℝ)*X 0 0+(1351648831/2500000000 : ℝ)*X 0 1+(3154137131/10000000000 : ℝ)*X 0 2+(4146946393/10000000000 : ℝ)*X 1 0+(1351648831/2500000000 : ℝ)*X 1 1+(3154137131/10000000000 : ℝ)*X 1 2+(4146946393/10000000000 : ℝ)*X 2 0+(1351648831/2500000000 : ℝ)*X 2 1+(3154137131/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2026499277864083410221/250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21521633/25000000000000 : ℝ)*(base1) + (1720048459/100000000000000 : ℝ)*(base19) + (856392963/50000000000000 : ℝ)*(base23) + (232962263/100000000000000 : ℝ)*(upper3) + (208847011/100000000000000 : ℝ)*(upper5) + (27810208072453/4000000000000 : ℝ)*(major0) + (27810208072453/4000000000000 : ℝ)*(major1) + (27810208072453/4000000000000 : ℝ)*(major2) + (969492278363003/100000000000000 : ℝ)*(sp0) + (121187071637661/12500000000000 : ℝ)*(sp1) + (48474829018191/5000000000000 : ℝ)*(sp2) + (421009053467439/100000000000000 : ℝ)*(sp3) + (1525218319/25000000000000 : ℝ)*(sp4) + (2700719023/100000000000000 : ℝ)*(sp7) + (210505920136497/50000000000000 : ℝ)*(f.failure) + (484749146574873/50000000000000 : ℝ)*(f.sum) + (225919499343/250000000000000000000000000 : ℝ)*base66 + (995935707907/500000000000000000000000000 : ℝ)*base67 + (5368802416593/500000000000000000000000000 : ℝ)*base70 + (1678174775093/500000000000000000000000000 : ℝ)*base72 + (807104895407/250000000000000000000000000 : ℝ)*base73 + (3110184280593/500000000000000000000000000 : ℝ)*base76 + (575627514907/500000000000000000000000000 : ℝ)*base77 + (1893250529407/500000000000000000000000000 : ℝ)*base79 + (1719901539593/250000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (22961173/5000000000000000000000 : ℝ)*base89 + (22961173/5000000000000000000000 : ℝ)*base91 + (22961173/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14482558591478026929753/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (191244553/50000000000000 : ℝ)*(base19) + (548175733/100000000000000 : ℝ)*(base23) + (87871761/50000000000000 : ℝ)*(base39) + (21661911/50000000000000 : ℝ)*(upper3) + (71689569/50000000000000 : ℝ)*(upper5) + (733150136845363/100000000000000 : ℝ)*(major0) + (733150136845363/100000000000000 : ℝ)*(major1) + (366574980550921/50000000000000 : ℝ)*(major2) + (1221279141/100000000000000 : ℝ)*(sp1) + (1228836417/100000000000000 : ℝ)*(sp2) + (255585224911321/25000000000000 : ℝ)*(sp4) + (1022339295877037/100000000000000 : ℝ)*(sp5) + (63896206148541/6250000000000 : ℝ)*(sp6) + (110989780265401/25000000000000 : ℝ)*(sp7) + (110989780265401/25000000000000 : ℝ)*(f.failure) + (511170537694403/50000000000000 : ℝ)*(f.sum) + (5613582215021/2500000000000000000000000000 : ℝ)*base66 + (22860945068901/6250000000000000000000000000 : ℝ)*base68 + (43026550462697/12500000000000000000000000000 : ℝ)*base69 + (36743500906401/6250000000000000000000000000 : ℝ)*base72 + (964174789979/2500000000000000000000000000 : ℝ)*base73 + (42608668362697/12500000000000000000000000000 : ℝ)*base75 + (51080171349803/12500000000000000000000000000 : ℝ)*base78 + (126283205699803/12500000000000000000000000000 : ℝ)*base80 + (289915431447/6250000000000000000000000000 : ℝ)*base81 + (29667709/2500000000000000000000 : ℝ)*base89 + (29667709/2500000000000000000000 : ℝ)*base91 + (4667709/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1534_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165139109/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1553/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (12601/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1534_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1534_s1_0 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-905313091/5000000000 : ℝ)*x 0 + (2778153449/5000000000 : ℝ)*x 1 + (1277314213/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (905313091/5000000000 : ℝ)^4565 ≤ (11045995771599/100000000000000 : ℝ)^3541 := by
    have hnat : (905313091 : ℕ)^4565*100000000000000^3541 ≤ 11045995771599^3541*5000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      905313091 5000000000 11045995771599 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2778153449/5000000000 : ℝ)^4565 ≤ (46879451824307/100000000000000 : ℝ)^3541 := by
    have hnat : (2778153449 : ℕ)^4565*100000000000000^3541 ≤ 46879451824307^3541*5000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2778153449 5000000000 46879451824307 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1277314213/2500000000 : ℝ)^4565 ≤ (42074552384783/100000000000000 : ℝ)^3541 := by
    have hnat : (1277314213 : ℕ)^4565*100000000000000^3541 ≤ 42074552384783^3541*2500000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1277314213 2500000000 42074552384783 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-905313091/5000000000 : ℝ), (2778153449/5000000000 : ℝ), (1277314213/2500000000 : ℝ)] ![(11045995771599/100000000000000 : ℝ), (46879451824307/100000000000000 : ℝ), (42074552384783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-905313091/5000000000 : ℝ)|^4565 ≤ (11045995771599/100000000000000 : ℝ)^3541
        have hw : |(-905313091/5000000000 : ℝ)|=(905313091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2778153449/5000000000 : ℝ)|^4565 ≤ (46879451824307/100000000000000 : ℝ)^3541
        have hw : |(2778153449/5000000000 : ℝ)|=(2778153449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1277314213/2500000000 : ℝ)|^4565 ≤ (42074552384783/100000000000000 : ℝ)^3541
        have hw : |(1277314213/2500000000 : ℝ)|=(1277314213/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_s1_1 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5382667187/10000000000 : ℝ)*x 0 + (-2045401083/10000000000 : ℝ)*x 1 + (1277314401/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5382667187/10000000000 : ℝ)^4565 ≤ (359994897711/800000000000 : ℝ)^3541 := by
    have hnat : (5382667187 : ℕ)^4565*800000000000^3541 ≤ 359994897711^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5382667187 10000000000 359994897711 800000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2045401083/10000000000 : ℝ)^4565 ≤ (12926077392719/100000000000000 : ℝ)^3541 := by
    have hnat : (2045401083 : ℕ)^4565*100000000000000^3541 ≤ 12926077392719^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2045401083 10000000000 12926077392719 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1277314401/2500000000 : ℝ)^4565 ≤ (2629660023019/6250000000000 : ℝ)^3541 := by
    have hnat : (1277314401 : ℕ)^4565*6250000000000^3541 ≤ 2629660023019^3541*2500000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1277314401 2500000000 2629660023019 6250000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5382667187/10000000000 : ℝ), (-2045401083/10000000000 : ℝ), (1277314401/2500000000 : ℝ)] ![(359994897711/800000000000 : ℝ), (12926077392719/100000000000000 : ℝ), (2629660023019/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5382667187/10000000000 : ℝ)|^4565 ≤ (359994897711/800000000000 : ℝ)^3541
        have hw : |(5382667187/10000000000 : ℝ)|=(5382667187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2045401083/10000000000 : ℝ)|^4565 ≤ (12926077392719/100000000000000 : ℝ)^3541
        have hw : |(-2045401083/10000000000 : ℝ)|=(2045401083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1277314401/2500000000 : ℝ)|^4565 ≤ (2629660023019/6250000000000 : ℝ)^3541
        have hw : |(1277314401/2500000000 : ℝ)|=(1277314401/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_s1_2 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2691333949/5000000000 : ℝ)*x 0 + (319328531/625000000 : ℝ)*x 1 + (-2045401587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2691333949/5000000000 : ℝ)^4565 ≤ (44999369876777/100000000000000 : ℝ)^3541 := by
    have hnat : (2691333949 : ℕ)^4565*100000000000000^3541 ≤ 44999369876777^3541*5000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2691333949 5000000000 44999369876777 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (319328531/625000000 : ℝ)^4565 ≤ (42074548605351/100000000000000 : ℝ)^3541 := by
    have hnat : (319328531 : ℕ)^4565*100000000000000^3541 ≤ 42074548605351^3541*625000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319328531 625000000 42074548605351 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2045401587/10000000000 : ℝ)^4565 ≤ (6463040749429/50000000000000 : ℝ)^3541 := by
    have hnat : (2045401587 : ℕ)^4565*50000000000000^3541 ≤ 6463040749429^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2045401587 10000000000 6463040749429 50000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2691333949/5000000000 : ℝ), (319328531/625000000 : ℝ), (-2045401587/10000000000 : ℝ)] ![(44999369876777/100000000000000 : ℝ), (42074548605351/100000000000000 : ℝ), (6463040749429/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2691333949/5000000000 : ℝ)|^4565 ≤ (44999369876777/100000000000000 : ℝ)^3541
        have hw : |(2691333949/5000000000 : ℝ)|=(2691333949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(319328531/625000000 : ℝ)|^4565 ≤ (42074548605351/100000000000000 : ℝ)^3541
        have hw : |(319328531/625000000 : ℝ)|=(319328531/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2045401587/10000000000 : ℝ)|^4565 ≤ (6463040749429/50000000000000 : ℝ)^3541
        have hw : |(-2045401587/10000000000 : ℝ)|=(2045401587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_s1_3 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2120791713/5000000000 : ℝ)*x 0 + (3752762723/10000000000 : ℝ)*x 1 + (4782220449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2120791713/5000000000 : ℝ)^4565 ≤ (16549509859421/50000000000000 : ℝ)^3541 := by
    have hnat : (2120791713 : ℕ)^4565*50000000000000^3541 ≤ 16549509859421^3541*5000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120791713 5000000000 16549509859421 50000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3752762723/10000000000 : ℝ)^4565 ≤ (14132868758053/50000000000000 : ℝ)^3541 := by
    have hnat : (3752762723 : ℕ)^4565*50000000000000^3541 ≤ 14132868758053^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3752762723 10000000000 14132868758053 50000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4782220449/10000000000 : ℝ)^4565 ≤ (19317621378293/50000000000000 : ℝ)^3541 := by
    have hnat : (4782220449 : ℕ)^4565*50000000000000^3541 ≤ 19317621378293^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4782220449 10000000000 19317621378293 50000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2120791713/5000000000 : ℝ), (3752762723/10000000000 : ℝ), (4782220449/10000000000 : ℝ)] ![(16549509859421/50000000000000 : ℝ), (14132868758053/50000000000000 : ℝ), (19317621378293/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2120791713/5000000000 : ℝ)|^4565 ≤ (16549509859421/50000000000000 : ℝ)^3541
        have hw : |(2120791713/5000000000 : ℝ)|=(2120791713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3752762723/10000000000 : ℝ)|^4565 ≤ (14132868758053/50000000000000 : ℝ)^3541
        have hw : |(3752762723/10000000000 : ℝ)|=(3752762723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4782220449/10000000000 : ℝ)|^4565 ≤ (19317621378293/50000000000000 : ℝ)^3541
        have hw : |(4782220449/10000000000 : ℝ)|=(4782220449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_s1_4 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-452722331/2500000000 : ℝ)*x 0 + (2557052209/5000000000 : ℝ)*x 1 + (111027679/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (452722331/2500000000 : ℝ)^4565 ≤ (1104806538977/10000000000000 : ℝ)^3541 := by
    have hnat : (452722331 : ℕ)^4565*10000000000000^3541 ≤ 1104806538977^3541*2500000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452722331 2500000000 1104806538977 10000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2557052209/5000000000 : ℝ)^4565 ≤ (42126023065963/100000000000000 : ℝ)^3541 := by
    have hnat : (2557052209 : ℕ)^4565*100000000000000^3541 ≤ 42126023065963^3541*5000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2557052209 5000000000 42126023065963 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (111027679/200000000 : ℝ)^4565 ≤ (23412955765261/50000000000000 : ℝ)^3541 := by
    have hnat : (111027679 : ℕ)^4565*50000000000000^3541 ≤ 23412955765261^3541*200000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111027679 200000000 23412955765261 50000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-452722331/2500000000 : ℝ), (2557052209/5000000000 : ℝ), (111027679/200000000 : ℝ)] ![(1104806538977/10000000000000 : ℝ), (42126023065963/100000000000000 : ℝ), (23412955765261/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-452722331/2500000000 : ℝ)|^4565 ≤ (1104806538977/10000000000000 : ℝ)^3541
        have hw : |(-452722331/2500000000 : ℝ)|=(452722331/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2557052209/5000000000 : ℝ)|^4565 ≤ (42126023065963/100000000000000 : ℝ)^3541
        have hw : |(2557052209/5000000000 : ℝ)|=(2557052209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(111027679/200000000 : ℝ)|^4565 ≤ (23412955765261/50000000000000 : ℝ)^3541
        have hw : |(111027679/200000000 : ℝ)|=(111027679/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_s1_5 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5264616557/10000000000 : ℝ)*x 0 + (-160327427/1000000000 : ℝ)*x 1 + (2775692009/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5264616557/10000000000 : ℝ)^4565 ≤ (8746222161757/20000000000000 : ℝ)^3541 := by
    have hnat : (5264616557 : ℕ)^4565*20000000000000^3541 ≤ 8746222161757^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264616557 10000000000 8746222161757 20000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (160327427/1000000000 : ℝ)^4565 ≤ (9442976899761/100000000000000 : ℝ)^3541 := by
    have hnat : (160327427 : ℕ)^4565*100000000000000^3541 ≤ 9442976899761^3541*1000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160327427 1000000000 9442976899761 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2775692009/5000000000 : ℝ)^4565 ≤ (11706478067493/25000000000000 : ℝ)^3541 := by
    have hnat : (2775692009 : ℕ)^4565*25000000000000^3541 ≤ 11706478067493^3541*5000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2775692009 5000000000 11706478067493 25000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5264616557/10000000000 : ℝ), (-160327427/1000000000 : ℝ), (2775692009/5000000000 : ℝ)] ![(8746222161757/20000000000000 : ℝ), (9442976899761/100000000000000 : ℝ), (11706478067493/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5264616557/10000000000 : ℝ)|^4565 ≤ (8746222161757/20000000000000 : ℝ)^3541
        have hw : |(5264616557/10000000000 : ℝ)|=(5264616557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-160327427/1000000000 : ℝ)|^4565 ≤ (9442976899761/100000000000000 : ℝ)^3541
        have hw : |(-160327427/1000000000 : ℝ)|=(160327427/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2775692009/5000000000 : ℝ)|^4565 ≤ (11706478067493/25000000000000 : ℝ)^3541
        have hw : |(2775692009/5000000000 : ℝ)|=(2775692009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_s1_6 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1316154157/2500000000 : ℝ)*x 0 + (5551384059/10000000000 : ℝ)*x 1 + (-12525579/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1316154157/2500000000 : ℝ)^4565 ≤ (21865555784553/50000000000000 : ℝ)^3541 := by
    have hnat : (1316154157 : ℕ)^4565*50000000000000^3541 ≤ 21865555784553^3541*2500000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316154157 2500000000 21865555784553 50000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5551384059/10000000000 : ℝ)^4565 ≤ (5853239089477/12500000000000 : ℝ)^3541 := by
    have hnat : (5551384059 : ℕ)^4565*12500000000000^3541 ≤ 5853239089477^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5551384059 10000000000 5853239089477 12500000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (12525579/78125000 : ℝ)^4565 ≤ (472148785003/5000000000000 : ℝ)^3541 := by
    have hnat : (12525579 : ℕ)^4565*5000000000000^3541 ≤ 472148785003^3541*78125000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12525579 78125000 472148785003 5000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1316154157/2500000000 : ℝ), (5551384059/10000000000 : ℝ), (-12525579/78125000 : ℝ)] ![(21865555784553/50000000000000 : ℝ), (5853239089477/12500000000000 : ℝ), (472148785003/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1316154157/2500000000 : ℝ)|^4565 ≤ (21865555784553/50000000000000 : ℝ)^3541
        have hw : |(1316154157/2500000000 : ℝ)|=(1316154157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5551384059/10000000000 : ℝ)|^4565 ≤ (5853239089477/12500000000000 : ℝ)^3541
        have hw : |(5551384059/10000000000 : ℝ)|=(5551384059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-12525579/78125000 : ℝ)|^4565 ≤ (472148785003/5000000000000 : ℝ)^3541
        have hw : |(-12525579/78125000 : ℝ)|=(12525579/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_s1_7 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4242190601/10000000000 : ℝ)*x 0 + (2385528901/5000000000 : ℝ)*x 1 + (3764097909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4242190601/10000000000 : ℝ)^4565 ≤ (33105128081921/100000000000000 : ℝ)^3541 := by
    have hnat : (4242190601 : ℕ)^4565*100000000000000^3541 ≤ 33105128081921^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242190601 10000000000 33105128081921 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2385528901/5000000000 : ℝ)^4565 ≤ (9629755117441/25000000000000 : ℝ)^3541 := by
    have hnat : (2385528901 : ℕ)^4565*25000000000000^3541 ≤ 9629755117441^3541*5000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2385528901 5000000000 9629755117441 25000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3764097909/10000000000 : ℝ)^4565 ≤ (3546981429333/12500000000000 : ℝ)^3541 := by
    have hnat : (3764097909 : ℕ)^4565*12500000000000^3541 ≤ 3546981429333^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3764097909 10000000000 3546981429333 12500000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4242190601/10000000000 : ℝ), (2385528901/5000000000 : ℝ), (3764097909/10000000000 : ℝ)] ![(33105128081921/100000000000000 : ℝ), (9629755117441/25000000000000 : ℝ), (3546981429333/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4242190601/10000000000 : ℝ)|^4565 ≤ (33105128081921/100000000000000 : ℝ)^3541
        have hw : |(4242190601/10000000000 : ℝ)|=(4242190601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2385528901/5000000000 : ℝ)|^4565 ≤ (9629755117441/25000000000000 : ℝ)^3541
        have hw : |(2385528901/5000000000 : ℝ)|=(2385528901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3764097909/10000000000 : ℝ)|^4565 ≤ (3546981429333/12500000000000 : ℝ)^3541
        have hw : |(3764097909/10000000000 : ℝ)|=(3764097909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1534_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165139109/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (12601/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1553/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (4321/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9051/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (12601/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1553/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (12601/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1553/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (12601/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1553/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (12601/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1553/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (12601/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1553/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (12601/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1553/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1553/50000 : ℝ) ^ (4563/1024 : ℝ) ≤ (19105887213331/100000000000000000000 : ℝ) := by
    have hpowers : (1553/50000 : ℝ)^4563 ≤ (19105887213331/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1553 : ℕ)^4563*100000000000000000000^1024 ≤ 19105887213331^1024*50000^4563 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1553 50000 19105887213331 100000000000000000000 4563 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1553/50000 : ℝ)) (X := (19105887213331/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4563 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (12601/50000 : ℝ) ^ (4563/1024 : ℝ) ≤ (26895007591352231/12500000000000000000 : ℝ) := by
    have hpowers : (12601/50000 : ℝ)^4563 ≤ (26895007591352231/12500000000000000000 : ℝ)^1024 := by
      have hnat : (12601 : ℕ)^4563*12500000000000000000^1024 ≤ 26895007591352231^1024*50000^4563 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12601 50000 26895007591352231 12500000000000000000 4563 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12601/50000 : ℝ)) (X := (26895007591352231/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4563 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000019105887213331/50000000000000000000 : ℝ) ≤ (5000000428762341/5000000000000000 : ℝ) ^ (4563/1024 : ℝ) := by
    have hpowers : (50000019105887213331/50000000000000000000 : ℝ)^1024 ≤ (5000000428762341/5000000000000000 : ℝ)^4563 := by
      have hnat : (50000019105887213331 : ℕ)^1024*5000000000000000^4563 ≤ 5000000428762341^4563*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000019105887213331 50000000000000000000 5000000428762341 5000000000000000 1024 4563 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000428762341/5000000000000000 : ℝ)) (X := (50000019105887213331/50000000000000000000 : ℝ)) (by norm_num) 4563 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100215179166618031179/100000000000000000000 : ℝ) ≤ (400192995691279/400000000000000 : ℝ) ^ (4563/1024 : ℝ) := by
    have hpowers : (100215179166618031179/100000000000000000000 : ℝ)^1024 ≤ (400192995691279/400000000000000 : ℝ)^4563 := by
      have hnat : (100215179166618031179 : ℕ)^1024*400000000000000^4563 ≤ 400192995691279^4563*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100215179166618031179 100000000000000000000 400192995691279 400000000000000 1024 4563 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400192995691279/400000000000000 : ℝ)) (X := (100215179166618031179/100000000000000000000 : ℝ)) (by norm_num) 4563 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6276895007591352231/6250000000000000000 : ℝ) ≤ (2502412231759817/2500000000000000 : ℝ) ^ (4563/1024 : ℝ) := by
    have hpowers : (6276895007591352231/6250000000000000000 : ℝ)^1024 ≤ (2502412231759817/2500000000000000 : ℝ)^4563 := by
      have hnat : (6276895007591352231 : ℕ)^1024*2500000000000000^4563 ≤ 2502412231759817^4563*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6276895007591352231 6250000000000000000 2502412231759817 2500000000000000 1024 4563 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2502412231759817/2500000000000000 : ℝ)) (X := (6276895007591352231/6250000000000000000 : ℝ)) (by norm_num) 4563 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(19105887213331/100000000000000000000 : ℝ) ≤ ((55232513010988267339/55240000000000000000 : ℝ)+2*(4824034757293/2209600000000000 : ℝ)*(1553/50000 : ℝ))^(4563/1024 : ℝ) := by
    rw [show (55232513010988267339/55240000000000000000 : ℝ)+2*(4824034757293/2209600000000000 : ℝ)*(1553/50000 : ℝ)=(5000000428762341/5000000000000000 : ℝ) by norm_num, show 1+2*(19105887213331/100000000000000000000 : ℝ)=(50000019105887213331/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26895007591352231/12500000000000000000 : ℝ)+(19105887213331/100000000000000000000 : ℝ) ≤ ((55232513010988267339/55240000000000000000 : ℝ)+(4824034757293/2209600000000000 : ℝ)*((12601/50000 : ℝ)+(1553/50000 : ℝ)))^(4563/1024 : ℝ) := by
    rw [show (55232513010988267339/55240000000000000000 : ℝ)+(4824034757293/2209600000000000 : ℝ)*((12601/50000 : ℝ)+(1553/50000 : ℝ))=(400192995691279/400000000000000 : ℝ) by norm_num, show 1+(26895007591352231/12500000000000000000 : ℝ)+(19105887213331/100000000000000000000 : ℝ)=(100215179166618031179/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26895007591352231/12500000000000000000 : ℝ) ≤ ((55232513010988267339/55240000000000000000 : ℝ)+2*(4824034757293/2209600000000000 : ℝ)*(12601/50000 : ℝ))^(4563/1024 : ℝ) := by
    rw [show (55232513010988267339/55240000000000000000 : ℝ)+2*(4824034757293/2209600000000000 : ℝ)*(12601/50000 : ℝ)=(2502412231759817/2500000000000000 : ℝ) by norm_num, show 1+2*(26895007591352231/12500000000000000000 : ℝ)=(6276895007591352231/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (55232513010988267339/55240000000000000000 : ℝ)*(X 1 0+X 2 0)+(4824034757293/2209600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4563/1024 : ℝ)) (lo := (1553/50000 : ℝ)) (hi := (12601/50000 : ℝ)) (c := (55232513010988267339/55240000000000000000 : ℝ)) (alpha := (4824034757293/2209600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (55232513010988267339/55240000000000000000 : ℝ)*(X 0 1+X 2 1)+(4824034757293/2209600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4563/1024 : ℝ)) (lo := (1553/50000 : ℝ)) (hi := (12601/50000 : ℝ)) (c := (55232513010988267339/55240000000000000000 : ℝ)) (alpha := (4824034757293/2209600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (55232513010988267339/55240000000000000000 : ℝ)*(X 0 2+X 1 2)+(4824034757293/2209600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4563/1024 : ℝ)) (lo := (1553/50000 : ℝ)) (hi := (12601/50000 : ℝ)) (c := (55232513010988267339/55240000000000000000 : ℝ)) (alpha := (4824034757293/2209600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-905313091/5000000000 : ℝ)*X 0 0+(2778153449/5000000000 : ℝ)*X 0 1+(1277314213/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5382667187/10000000000 : ℝ)*X 1 0+(-2045401083/10000000000 : ℝ)*X 1 1+(1277314401/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2691333949/5000000000 : ℝ)*X 2 0+(319328531/625000000 : ℝ)*X 2 1+(-2045401587/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2120791713/5000000000 : ℝ)*X 0 0+(3752762723/10000000000 : ℝ)*X 0 1+(4782220449/10000000000 : ℝ)*X 0 2+(2120791713/5000000000 : ℝ)*X 1 0+(3752762723/10000000000 : ℝ)*X 1 1+(4782220449/10000000000 : ℝ)*X 1 2+(2120791713/5000000000 : ℝ)*X 2 0+(3752762723/10000000000 : ℝ)*X 2 1+(4782220449/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-452722331/2500000000 : ℝ)*X 0 0+(2557052209/5000000000 : ℝ)*X 0 1+(111027679/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5264616557/10000000000 : ℝ)*X 1 0+(-160327427/1000000000 : ℝ)*X 1 1+(2775692009/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1316154157/2500000000 : ℝ)*X 2 0+(5551384059/10000000000 : ℝ)*X 2 1+(-12525579/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4242190601/10000000000 : ℝ)*X 0 0+(2385528901/5000000000 : ℝ)*X 0 1+(3764097909/10000000000 : ℝ)*X 0 2+(4242190601/10000000000 : ℝ)*X 1 0+(2385528901/5000000000 : ℝ)*X 1 1+(3764097909/10000000000 : ℝ)*X 1 2+(4242190601/10000000000 : ℝ)*X 2 0+(2385528901/5000000000 : ℝ)*X 2 1+(3764097909/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2455098075065658473503757601/552400000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20541301/10000000000000 : ℝ)*(base19) + (646445333/100000000000000 : ℝ)*(base23) + (20521587/25000000000000 : ℝ)*(upper2) + (99503679/100000000000000 : ℝ)*(upper3) + (1868261/50000000000000 : ℝ)*(upper4) + (320828336599051/20000000000000 : ℝ)*(major0) + (320828336599051/20000000000000 : ℝ)*(major1) + (320828336599051/20000000000000 : ℝ)*(major2) + (1118445636750037/50000000000000 : ℝ)*(sp0) + (2236894894431231/100000000000000 : ℝ)*(sp1) + (559223613349727/25000000000000 : ℝ)*(sp2) + (971386265358997/100000000000000 : ℝ)*(sp3) + (1913172083/50000000000000 : ℝ)*(sp4) + (370527981/20000000000000 : ℝ)*(sp7) + (485694058999451/50000000000000 : ℝ)*(f.failure) + (27961188748053/1250000000000 : ℝ)*(f.sum) + (38661903477057/22096000000000000000000000000 : ℝ)*base66 + (5942668369143529711/1104800000000000000000000000000000 : ℝ)*base68 + (3663065550955529711/1104800000000000000000000000000000 : ℝ)*base70 + (6739163260089929711/1104800000000000000000000000000000 : ℝ)*base72 + (1444799184803/4419200000000000000000000000 : ℝ)*base73 + (8995148285880329711/1104800000000000000000000000000000 : ℝ)*base76 + (9996266329087529711/1104800000000000000000000000000000 : ℝ)*base78 + (6030467408477929711/1104800000000000000000000000000000 : ℝ)*base80 + (30517890760049/22096000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (19629159/5000000000000000000000 : ℝ)*base89 + (19629159/5000000000000000000000 : ℝ)*base91 + (19629159/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6624446418991627955383566711/690500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (200586633/12500000000000 : ℝ)*(base19) + (1805589813/100000000000000 : ℝ)*(base23) + (122132881/50000000000000 : ℝ)*(upper3) + (31761777/50000000000000 : ℝ)*(lower4) + (51152081/25000000000000 : ℝ)*(upper5) + (819988599690483/50000000000000 : ℝ)*(major0) + (819988599690483/50000000000000 : ℝ)*(major1) + (819988599690483/50000000000000 : ℝ)*(major2) + (342910443/3125000000000 : ℝ)*(sp1) + (13175858879/100000000000000 : ℝ)*(sp2) + (2286865761303523/100000000000000 : ℝ)*(sp4) + (571713295869071/25000000000000 : ℝ)*(sp5) + (2286850779854831/100000000000000 : ℝ)*(sp6) + (99308831766857/10000000000000 : ℝ)*(sp7) + (99308831766857/10000000000000 : ℝ)*(f.failure) + (2286865761303523/100000000000000 : ℝ)*(f.sum) + (10075533144199/55240000000000000000000000000 : ℝ)*base65 + (4269765056873009737/2762000000000000000000000000000000 : ℝ)*base67 + (12608066303338990263/2762000000000000000000000000000000 : ℝ)*base70 + (19992416071118990263/2762000000000000000000000000000000 : ℝ)*base72 + (297393371198039/55240000000000000000000000000 : ℝ)*base73 + (24924508080630990263/2762000000000000000000000000000000 : ℝ)*base76 + (8981921572938990263/2762000000000000000000000000000000 : ℝ)*base78 + (8557798169164990263/2762000000000000000000000000000000 : ℝ)*base80 + (71354964312881/55240000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (710413/1000000000000000000000 : ℝ)*base89 + (710413/1000000000000000000000 : ℝ)*base91 + (710413/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1534_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165139109/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (12601/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1553/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4321/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9051/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1534_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1534_s2_0 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1832723421/10000000000 : ℝ)*x 0 + (681400159/1250000000 : ℝ)*x 1 + (5200016209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1832723421/10000000000 : ℝ)^4565 ≤ (11220093232367/100000000000000 : ℝ)^3541 := by
    have hnat : (1832723421 : ℕ)^4565*100000000000000^3541 ≤ 11220093232367^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1832723421 10000000000 11220093232367 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (681400159/1250000000 : ℝ)^4565 ≤ (22869676838651/50000000000000 : ℝ)^3541 := by
    have hnat : (681400159 : ℕ)^4565*50000000000000^3541 ≤ 22869676838651^3541*1250000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681400159 1250000000 22869676838651 50000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5200016209/10000000000 : ℝ)^4565 ≤ (43040553074781/100000000000000 : ℝ)^3541 := by
    have hnat : (5200016209 : ℕ)^4565*100000000000000^3541 ≤ 43040553074781^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5200016209 10000000000 43040553074781 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1832723421/10000000000 : ℝ), (681400159/1250000000 : ℝ), (5200016209/10000000000 : ℝ)] ![(11220093232367/100000000000000 : ℝ), (22869676838651/50000000000000 : ℝ), (43040553074781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1832723421/10000000000 : ℝ)|^4565 ≤ (11220093232367/100000000000000 : ℝ)^3541
        have hw : |(-1832723421/10000000000 : ℝ)|=(1832723421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(681400159/1250000000 : ℝ)|^4565 ≤ (22869676838651/50000000000000 : ℝ)^3541
        have hw : |(681400159/1250000000 : ℝ)|=(681400159/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5200016209/10000000000 : ℝ)|^4565 ≤ (43040553074781/100000000000000 : ℝ)^3541
        have hw : |(5200016209/10000000000 : ℝ)|=(5200016209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_s2_1 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (214231417/400000000 : ℝ)*x 0 + (-196186931/1000000000 : ℝ)*x 1 + (1040003307/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214231417/400000000 : ℝ)^4565 ≤ (22354924855857/50000000000000 : ℝ)^3541 := by
    have hnat : (214231417 : ℕ)^4565*50000000000000^3541 ≤ 22354924855857^3541*400000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214231417 400000000 22354924855857 50000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (196186931/1000000000 : ℝ)^4565 ≤ (6124796858303/50000000000000 : ℝ)^3541 := by
    have hnat : (196186931 : ℕ)^4565*50000000000000^3541 ≤ 6124796858303^3541*1000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196186931 1000000000 6124796858303 50000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1040003307/2000000000 : ℝ)^4565 ≤ (4304055655339/10000000000000 : ℝ)^3541 := by
    have hnat : (1040003307 : ℕ)^4565*10000000000000^3541 ≤ 4304055655339^3541*2000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040003307 2000000000 4304055655339 10000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214231417/400000000 : ℝ), (-196186931/1000000000 : ℝ), (1040003307/2000000000 : ℝ)] ![(22354924855857/50000000000000 : ℝ), (6124796858303/50000000000000 : ℝ), (4304055655339/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214231417/400000000 : ℝ)|^4565 ≤ (22354924855857/50000000000000 : ℝ)^3541
        have hw : |(214231417/400000000 : ℝ)|=(214231417/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-196186931/1000000000 : ℝ)|^4565 ≤ (6124796858303/50000000000000 : ℝ)^3541
        have hw : |(-196186931/1000000000 : ℝ)|=(196186931/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1040003307/2000000000 : ℝ)|^4565 ≤ (4304055655339/10000000000000 : ℝ)^3541
        have hw : |(1040003307/2000000000 : ℝ)|=(1040003307/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_s2_2 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334736631/625000000 : ℝ)*x 0 + (5200016149/10000000000 : ℝ)*x 1 + (-78474757/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334736631/625000000 : ℝ)^4565 ≤ (5588732116631/12500000000000 : ℝ)^3541 := by
    have hnat : (334736631 : ℕ)^4565*12500000000000^3541 ≤ 5588732116631^3541*625000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334736631 625000000 5588732116631 12500000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5200016149/10000000000 : ℝ)^4565 ≤ (43040552434547/100000000000000 : ℝ)^3541 := by
    have hnat : (5200016149 : ℕ)^4565*100000000000000^3541 ≤ 43040552434547^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5200016149 10000000000 43040552434547 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (78474757/400000000 : ℝ)^4565 ≤ (6124795308783/50000000000000 : ℝ)^3541 := by
    have hnat : (78474757 : ℕ)^4565*50000000000000^3541 ≤ 6124795308783^3541*400000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78474757 400000000 6124795308783 50000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334736631/625000000 : ℝ), (5200016149/10000000000 : ℝ), (-78474757/400000000 : ℝ)] ![(5588732116631/12500000000000 : ℝ), (43040552434547/100000000000000 : ℝ), (6124795308783/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334736631/625000000 : ℝ)|^4565 ≤ (5588732116631/12500000000000 : ℝ)^3541
        have hw : |(334736631/625000000 : ℝ)|=(334736631/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5200016149/10000000000 : ℝ)|^4565 ≤ (43040552434547/100000000000000 : ℝ)^3541
        have hw : |(5200016149/10000000000 : ℝ)|=(5200016149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-78474757/400000000 : ℝ)|^4565 ≤ (6124795308783/50000000000000 : ℝ)^3541
        have hw : |(-78474757/400000000 : ℝ)|=(78474757/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_s2_3 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1064377219/2500000000 : ℝ)*x 0 + (3976479519/10000000000 : ℝ)*x 1 + (4554905427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1064377219/2500000000 : ℝ)^4565 ≤ (33259318117869/100000000000000 : ℝ)^3541 := by
    have hnat : (1064377219 : ℕ)^4565*100000000000000^3541 ≤ 33259318117869^3541*2500000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064377219 2500000000 33259318117869 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3976479519/10000000000 : ℝ)^4565 ≤ (1218260741577/4000000000000 : ℝ)^3541 := by
    have hnat : (3976479519 : ℕ)^4565*4000000000000^3541 ≤ 1218260741577^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3976479519 10000000000 1218260741577 4000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4554905427/10000000000 : ℝ)^4565 ≤ (4535520415227/12500000000000 : ℝ)^3541 := by
    have hnat : (4554905427 : ℕ)^4565*12500000000000^3541 ≤ 4535520415227^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4554905427 10000000000 4535520415227 12500000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1064377219/2500000000 : ℝ), (3976479519/10000000000 : ℝ), (4554905427/10000000000 : ℝ)] ![(33259318117869/100000000000000 : ℝ), (1218260741577/4000000000000 : ℝ), (4535520415227/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1064377219/2500000000 : ℝ)|^4565 ≤ (33259318117869/100000000000000 : ℝ)^3541
        have hw : |(1064377219/2500000000 : ℝ)|=(1064377219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3976479519/10000000000 : ℝ)|^4565 ≤ (1218260741577/4000000000000 : ℝ)^3541
        have hw : |(3976479519/10000000000 : ℝ)|=(3976479519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4554905427/10000000000 : ℝ)|^4565 ≤ (4535520415227/12500000000000 : ℝ)^3541
        have hw : |(4554905427/10000000000 : ℝ)|=(4554905427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_s2_4 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-916384987/5000000000 : ℝ)*x 0 + (1300388667/2500000000 : ℝ)*x 1 + (5449649563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (916384987/5000000000 : ℝ)^4565 ≤ (112204606531/1000000000000 : ℝ)^3541 := by
    have hnat : (916384987 : ℕ)^4565*1000000000000^3541 ≤ 112204606531^3541*5000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      916384987 5000000000 112204606531 1000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1300388667/2500000000 : ℝ)^4565 ≤ (8611394005177/20000000000000 : ℝ)^3541 := by
    have hnat : (1300388667 : ℕ)^4565*20000000000000^3541 ≤ 8611394005177^3541*2500000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1300388667 2500000000 8611394005177 20000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5449649563/10000000000 : ℝ)^4565 ≤ (22861284653287/50000000000000 : ℝ)^3541 := by
    have hnat : (5449649563 : ℕ)^4565*50000000000000^3541 ≤ 22861284653287^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5449649563 10000000000 22861284653287 50000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-916384987/5000000000 : ℝ), (1300388667/2500000000 : ℝ), (5449649563/10000000000 : ℝ)] ![(112204606531/1000000000000 : ℝ), (8611394005177/20000000000000 : ℝ), (22861284653287/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-916384987/5000000000 : ℝ)|^4565 ≤ (112204606531/1000000000000 : ℝ)^3541
        have hw : |(-916384987/5000000000 : ℝ)|=(916384987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1300388667/2500000000 : ℝ)|^4565 ≤ (8611394005177/20000000000000 : ℝ)^3541
        have hw : |(1300388667/2500000000 : ℝ)|=(1300388667/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5449649563/10000000000 : ℝ)|^4565 ≤ (22861284653287/50000000000000 : ℝ)^3541
        have hw : |(5449649563/10000000000 : ℝ)|=(5449649563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_s2_5 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644812491/5000000000 : ℝ)*x 0 + (-1712235793/10000000000 : ℝ)*x 1 + (2724824677/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644812491/5000000000 : ℝ)^4565 ≤ (21999551709643/50000000000000 : ℝ)^3541 := by
    have hnat : (2644812491 : ℕ)^4565*50000000000000^3541 ≤ 21999551709643^3541*5000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644812491 5000000000 21999551709643 50000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1712235793/10000000000 : ℝ)^4565 ≤ (10278329521733/100000000000000 : ℝ)^3541 := by
    have hnat : (1712235793 : ℕ)^4565*100000000000000^3541 ≤ 10278329521733^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1712235793 10000000000 10278329521733 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2724824677/5000000000 : ℝ)^4565 ≤ (45722567045977/100000000000000 : ℝ)^3541 := by
    have hnat : (2724824677 : ℕ)^4565*100000000000000^3541 ≤ 45722567045977^3541*5000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2724824677 5000000000 45722567045977 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644812491/5000000000 : ℝ), (-1712235793/10000000000 : ℝ), (2724824677/5000000000 : ℝ)] ![(21999551709643/50000000000000 : ℝ), (10278329521733/100000000000000 : ℝ), (45722567045977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644812491/5000000000 : ℝ)|^4565 ≤ (21999551709643/50000000000000 : ℝ)^3541
        have hw : |(2644812491/5000000000 : ℝ)|=(2644812491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1712235793/10000000000 : ℝ)|^4565 ≤ (10278329521733/100000000000000 : ℝ)^3541
        have hw : |(-1712235793/10000000000 : ℝ)|=(1712235793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2724824677/5000000000 : ℝ)|^4565 ≤ (45722567045977/100000000000000 : ℝ)^3541
        have hw : |(2724824677/5000000000 : ℝ)|=(2724824677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_s2_6 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289624607/10000000000 : ℝ)*x 0 + (2724824777/5000000000 : ℝ)*x 1 + (-856118017/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289624607/10000000000 : ℝ)^4565 ≤ (43999099397999/100000000000000 : ℝ)^3541 := by
    have hnat : (5289624607 : ℕ)^4565*100000000000000^3541 ≤ 43999099397999^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289624607 10000000000 43999099397999 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2724824777/5000000000 : ℝ)^4565 ≤ (11430642302307/25000000000000 : ℝ)^3541 := by
    have hnat : (2724824777 : ℕ)^4565*25000000000000^3541 ≤ 11430642302307^3541*5000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2724824777 5000000000 11430642302307 25000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (856118017/5000000000 : ℝ)^4565 ≤ (2055666277357/20000000000000 : ℝ)^3541 := by
    have hnat : (856118017 : ℕ)^4565*20000000000000^3541 ≤ 2055666277357^3541*5000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      856118017 5000000000 2055666277357 20000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289624607/10000000000 : ℝ), (2724824777/5000000000 : ℝ), (-856118017/5000000000 : ℝ)] ![(43999099397999/100000000000000 : ℝ), (11430642302307/25000000000000 : ℝ), (2055666277357/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289624607/10000000000 : ℝ)|^4565 ≤ (43999099397999/100000000000000 : ℝ)^3541
        have hw : |(5289624607/10000000000 : ℝ)|=(5289624607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2724824777/5000000000 : ℝ)|^4565 ≤ (11430642302307/25000000000000 : ℝ)^3541
        have hw : |(2724824777/5000000000 : ℝ)|=(2724824777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-856118017/5000000000 : ℝ)|^4565 ≤ (2055666277357/20000000000000 : ℝ)^3541
        have hw : |(-856118017/5000000000 : ℝ)|=(856118017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_s2_7 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4257616831/10000000000 : ℝ)*x 0 + (4551361701/10000000000 : ℝ)*x 1 + (3980054201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4257616831/10000000000 : ℝ)^4565 ≤ (6652081067351/20000000000000 : ℝ)^3541 := by
    have hnat : (4257616831 : ℕ)^4565*20000000000000^3541 ≤ 6652081067351^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4257616831 10000000000 6652081067351 20000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4551361701/10000000000 : ℝ)^4565 ≤ (18123887422693/50000000000000 : ℝ)^3541 := by
    have hnat : (4551361701 : ℕ)^4565*50000000000000^3541 ≤ 18123887422693^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4551361701 10000000000 18123887422693 50000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3980054201/10000000000 : ℝ)^4565 ≤ (30491819799789/100000000000000 : ℝ)^3541 := by
    have hnat : (3980054201 : ℕ)^4565*100000000000000^3541 ≤ 30491819799789^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3980054201 10000000000 30491819799789 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4257616831/10000000000 : ℝ), (4551361701/10000000000 : ℝ), (3980054201/10000000000 : ℝ)] ![(6652081067351/20000000000000 : ℝ), (18123887422693/50000000000000 : ℝ), (30491819799789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4257616831/10000000000 : ℝ)|^4565 ≤ (6652081067351/20000000000000 : ℝ)^3541
        have hw : |(4257616831/10000000000 : ℝ)|=(4257616831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4551361701/10000000000 : ℝ)|^4565 ≤ (18123887422693/50000000000000 : ℝ)^3541
        have hw : |(4551361701/10000000000 : ℝ)|=(4551361701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3980054201/10000000000 : ℝ)|^4565 ≤ (30491819799789/100000000000000 : ℝ)^3541
        have hw : |(3980054201/10000000000 : ℝ)|=(3980054201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1534_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165139109/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9051/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4321/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5299/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7959/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9051/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4321/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9051/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4321/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9051/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4321/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9051/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4321/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9051/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4321/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9051/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4321/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4321/50000 : ℝ) ^ (4563/1024 : ℝ) ≤ (1825975715926917/100000000000000000000 : ℝ) := by
    have hpowers : (4321/50000 : ℝ)^4563 ≤ (1825975715926917/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4321 : ℕ)^4563*100000000000000000000^1024 ≤ 1825975715926917^1024*50000^4563 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4321 50000 1825975715926917 100000000000000000000 4563 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4321/50000 : ℝ)) (X := (1825975715926917/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4563 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9051/50000 : ℝ) ^ (4563/1024 : ℝ) ≤ (49248041120199791/100000000000000000000 : ℝ) := by
    have hpowers : (9051/50000 : ℝ)^4563 ≤ (49248041120199791/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9051 : ℕ)^4563*100000000000000000000^1024 ≤ 49248041120199791^1024*50000^4563 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9051 50000 49248041120199791 100000000000000000000 4563 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9051/50000 : ℝ)) (X := (49248041120199791/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4563 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001825975715926917/50000000000000000000 : ℝ) ≤ (5000040976827823/5000000000000000 : ℝ) ^ (4563/1024 : ℝ) := by
    have hpowers : (50001825975715926917/50000000000000000000 : ℝ)^1024 ≤ (5000040976827823/5000000000000000 : ℝ)^4563 := by
      have hnat : (50001825975715926917 : ℕ)^1024*5000000000000000^4563 ≤ 5000040976827823^4563*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001825975715926917 50000000000000000000 5000040976827823 5000000000000000 1024 4563 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000040976827823/5000000000000000 : ℝ)) (X := (50001825975715926917/50000000000000000000 : ℝ)) (by norm_num) 4563 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012768504209031677/25000000000000000000 : ℝ) ≤ (2000229188857303/2000000000000000 : ℝ) ^ (4563/1024 : ℝ) := by
    have hpowers : (25012768504209031677/25000000000000000000 : ℝ)^1024 ≤ (2000229188857303/2000000000000000 : ℝ)^4563 := by
      have hnat : (25012768504209031677 : ℕ)^1024*2000000000000000^4563 ≤ 2000229188857303^4563*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012768504209031677 25000000000000000000 2000229188857303 2000000000000000 1024 4563 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000229188857303/2000000000000000 : ℝ)) (X := (25012768504209031677/25000000000000000000 : ℝ)) (by norm_num) 4563 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50049248041120199791/50000000000000000000 : ℝ) ≤ (1250276241864673/1250000000000000 : ℝ) ^ (4563/1024 : ℝ) := by
    have hpowers : (50049248041120199791/50000000000000000000 : ℝ)^1024 ≤ (1250276241864673/1250000000000000 : ℝ)^4563 := by
      have hnat : (50049248041120199791 : ℕ)^1024*1250000000000000^4563 ≤ 1250276241864673^4563*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50049248041120199791 50000000000000000000 1250276241864673 1250000000000000 1024 4563 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250276241864673/1250000000000000 : ℝ)) (X := (50049248041120199791/50000000000000000000 : ℝ)) (by norm_num) 4563 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1825975715926917/100000000000000000000 : ℝ) ≤ ((23645596316879617841/23650000000000000000 : ℝ)+2*(1063990630869/946000000000000 : ℝ)*(4321/50000 : ℝ))^(4563/1024 : ℝ) := by
    rw [show (23645596316879617841/23650000000000000000 : ℝ)+2*(1063990630869/946000000000000 : ℝ)*(4321/50000 : ℝ)=(5000040976827823/5000000000000000 : ℝ) by norm_num, show 1+2*(1825975715926917/100000000000000000000 : ℝ)=(50001825975715926917/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(49248041120199791/100000000000000000000 : ℝ)+(1825975715926917/100000000000000000000 : ℝ) ≤ ((23645596316879617841/23650000000000000000 : ℝ)+(1063990630869/946000000000000 : ℝ)*((9051/50000 : ℝ)+(4321/50000 : ℝ)))^(4563/1024 : ℝ) := by
    rw [show (23645596316879617841/23650000000000000000 : ℝ)+(1063990630869/946000000000000 : ℝ)*((9051/50000 : ℝ)+(4321/50000 : ℝ))=(2000229188857303/2000000000000000 : ℝ) by norm_num, show 1+(49248041120199791/100000000000000000000 : ℝ)+(1825975715926917/100000000000000000000 : ℝ)=(25012768504209031677/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(49248041120199791/100000000000000000000 : ℝ) ≤ ((23645596316879617841/23650000000000000000 : ℝ)+2*(1063990630869/946000000000000 : ℝ)*(9051/50000 : ℝ))^(4563/1024 : ℝ) := by
    rw [show (23645596316879617841/23650000000000000000 : ℝ)+2*(1063990630869/946000000000000 : ℝ)*(9051/50000 : ℝ)=(1250276241864673/1250000000000000 : ℝ) by norm_num, show 1+2*(49248041120199791/100000000000000000000 : ℝ)=(50049248041120199791/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23645596316879617841/23650000000000000000 : ℝ)*(X 1 0+X 2 0)+(1063990630869/946000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4563/1024 : ℝ)) (lo := (4321/50000 : ℝ)) (hi := (9051/50000 : ℝ)) (c := (23645596316879617841/23650000000000000000 : ℝ)) (alpha := (1063990630869/946000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23645596316879617841/23650000000000000000 : ℝ)*(X 0 1+X 2 1)+(1063990630869/946000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4563/1024 : ℝ)) (lo := (4321/50000 : ℝ)) (hi := (9051/50000 : ℝ)) (c := (23645596316879617841/23650000000000000000 : ℝ)) (alpha := (1063990630869/946000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23645596316879617841/23650000000000000000 : ℝ)*(X 0 2+X 1 2)+(1063990630869/946000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4563/1024 : ℝ)) (lo := (4321/50000 : ℝ)) (hi := (9051/50000 : ℝ)) (c := (23645596316879617841/23650000000000000000 : ℝ)) (alpha := (1063990630869/946000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1832723421/10000000000 : ℝ)*X 0 0+(681400159/1250000000 : ℝ)*X 0 1+(5200016209/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((214231417/400000000 : ℝ)*X 1 0+(-196186931/1000000000 : ℝ)*X 1 1+(1040003307/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334736631/625000000 : ℝ)*X 2 0+(5200016149/10000000000 : ℝ)*X 2 1+(-78474757/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1064377219/2500000000 : ℝ)*X 0 0+(3976479519/10000000000 : ℝ)*X 0 1+(4554905427/10000000000 : ℝ)*X 0 2+(1064377219/2500000000 : ℝ)*X 1 0+(3976479519/10000000000 : ℝ)*X 1 1+(4554905427/10000000000 : ℝ)*X 1 2+(1064377219/2500000000 : ℝ)*X 2 0+(3976479519/10000000000 : ℝ)*X 2 1+(4554905427/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-916384987/5000000000 : ℝ)*X 0 0+(1300388667/2500000000 : ℝ)*X 0 1+(5449649563/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2644812491/5000000000 : ℝ)*X 1 0+(-1712235793/10000000000 : ℝ)*X 1 1+(2724824677/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5289624607/10000000000 : ℝ)*X 2 0+(2724824777/5000000000 : ℝ)*X 2 1+(-856118017/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4257616831/10000000000 : ℝ)*X 0 0+(4551361701/10000000000 : ℝ)*X 0 1+(3980054201/10000000000 : ℝ)*X 0 2+(4257616831/10000000000 : ℝ)*X 1 0+(4551361701/10000000000 : ℝ)*X 1 1+(3980054201/10000000000 : ℝ)*X 1 2+(4257616831/10000000000 : ℝ)*X 2 0+(4551361701/10000000000 : ℝ)*X 2 1+(3980054201/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5533298869488591683492422179/591250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (957595593/50000000000000 : ℝ)*(base19) + (426485583/20000000000000 : ℝ)*(base23) + (9945003/6250000000000 : ℝ)*(upper3) + (150790301/100000000000000 : ℝ)*(upper4) + (371323301/100000000000000 : ℝ)*(upper5) + (1427512432994927/50000000000000 : ℝ)*(major0) + (1427512432994927/50000000000000 : ℝ)*(major1) + (1427512432994927/50000000000000 : ℝ)*(major2) + (497644155630173/12500000000000 : ℝ)*(sp0) + (3981186980347109/100000000000000 : ℝ)*(sp1) + (199059338155519/5000000000000 : ℝ)*(sp2) + (432211313802813/25000000000000 : ℝ)*(sp3) + (35650496911/100000000000000 : ℝ)*(sp4) + (15269275321/100000000000000 : ℝ)*(sp7) + (1728860524486573/100000000000000 : ℝ)*(f.failure) + (796237779107659/20000000000000 : ℝ)*(f.sum) + (33207487564687/23650000000000000000000000000 : ℝ)*base66 + (4804380732478267607/1182500000000000000000000000000000 : ℝ)*base67 + (2886801520385767607/1182500000000000000000000000000000 : ℝ)*base69 + (5377908577780767607/1182500000000000000000000000000000 : ℝ)*base71 + (81687823447787/23650000000000000000000000000 : ℝ)*base74 + (8228289530909232393/1182500000000000000000000000000000 : ℝ)*base76 + (4084028719493267607/1182500000000000000000000000000000 : ℝ)*base77 + (6292738042901732393/1182500000000000000000000000000000 : ℝ)*base80 + (33130736420313/23650000000000000000000000000 : ℝ)*base81 + (52316543/10000000000000000000000 : ℝ)*base90 + (52316543/10000000000000000000000 : ℝ)*base92 + (52316543/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (290355443921120451285305763/118250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (50364717/6250000000000 : ℝ)*(base19) + (572529449/100000000000000 : ℝ)*(base23) + (63639479/100000000000000 : ℝ)*(upper2) + (29531961/25000000000000 : ℝ)*(upper5) + (289054338025119/10000000000000 : ℝ)*(major0) + (289054338025119/10000000000000 : ℝ)*(major1) + (289054338025119/10000000000000 : ℝ)*(major2) + (28520559/3125000000000 : ℝ)*(sp0) + (12226933077/100000000000000 : ℝ)*(sp1) + (170024191/2500000000000 : ℝ)*(sp2) + (1007679250625209/25000000000000 : ℝ)*(sp4) + (2015352441195087/50000000000000 : ℝ)*(sp5) + (1007677635415409/25000000000000 : ℝ)*(sp6) + (350073752699149/20000000000000 : ℝ)*(sp7) + (350073752699149/20000000000000 : ℝ)*(f.failure) + (1007679478789681/25000000000000 : ℝ)*(f.sum) + (5369075448821/4730000000000000000000000000 : ℝ)*base65 + (736584132180323079/236500000000000000000000000000000 : ℝ)*base67 + (893023321843676921/236500000000000000000000000000000 : ℝ)*base70 + (1233750776126823079/236500000000000000000000000000000 : ℝ)*base71 + (6859941129521/4730000000000000000000000000 : ℝ)*base73 + (1763525711574823079/236500000000000000000000000000000 : ℝ)*base75 + (854716743513323079/236500000000000000000000000000000 : ℝ)*base77 + (1329620046099676921/236500000000000000000000000000000 : ℝ)*base80 + (2476656146081/4730000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (10918241/2000000000000000000000 : ℝ)*base89 + (10918241/2000000000000000000000 : ℝ)*base91 + (10918241/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1534_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165139109/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9051/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4321/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5299/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7959/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1534_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1534_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165139109/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5299/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7959/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1534_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1534_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1534_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165139109/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5299/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7959/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1534_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
