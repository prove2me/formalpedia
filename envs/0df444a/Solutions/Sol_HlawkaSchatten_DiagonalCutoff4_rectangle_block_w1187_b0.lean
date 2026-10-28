-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1187_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:52:06.803989+00:00
-- url     : https://prove2.me/submissions/db657b5b-6197-4245-bc81-bba4ad1d2f8a

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
theorem support_rectangle_w1187_s0_0 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1877649683/10000000000 : ℝ)*x 0 + (377749243/625000000 : ℝ)*x 1 + (1196534253/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1877649683/10000000000 : ℝ)^2095 ≤ (5465690069507/50000000000000 : ℝ)^1583 := by
    have hnat : (1877649683 : ℕ)^2095*50000000000000^1583 ≤ 5465690069507^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1877649683 10000000000 5465690069507 50000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (377749243/625000000 : ℝ)^2095 ≤ (25678263592879/50000000000000 : ℝ)^1583 := by
    have hnat : (377749243 : ℕ)^2095*50000000000000^1583 ≤ 25678263592879^1583*625000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      377749243 625000000 25678263592879 50000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1196534253/2500000000 : ℝ)^2095 ≤ (37712092663551/100000000000000 : ℝ)^1583 := by
    have hnat : (1196534253 : ℕ)^2095*100000000000000^1583 ≤ 37712092663551^1583*2500000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1196534253 2500000000 37712092663551 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1877649683/10000000000 : ℝ), (377749243/625000000 : ℝ), (1196534253/2500000000 : ℝ)] ![(5465690069507/50000000000000 : ℝ), (25678263592879/50000000000000 : ℝ), (37712092663551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1877649683/10000000000 : ℝ)|^2095 ≤ (5465690069507/50000000000000 : ℝ)^1583
        have hw : |(-1877649683/10000000000 : ℝ)|=(1877649683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(377749243/625000000 : ℝ)|^2095 ≤ (25678263592879/50000000000000 : ℝ)^1583
        have hw : |(377749243/625000000 : ℝ)|=(377749243/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1196534253/2500000000 : ℝ)|^2095 ≤ (37712092663551/100000000000000 : ℝ)^1583
        have hw : |(1196534253/2500000000 : ℝ)|=(1196534253/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1187_s0_1 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (68928229/125000000 : ℝ)*x 0 + (-2598248787/10000000000 : ℝ)*x 1 + (1196534251/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (68928229/125000000 : ℝ)^2095 ≤ (45485670240347/100000000000000 : ℝ)^1583 := by
    have hnat : (68928229 : ℕ)^2095*100000000000000^1583 ≤ 45485670240347^1583*125000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68928229 125000000 45485670240347 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2598248787/10000000000 : ℝ)^2095 ≤ (3360447433567/20000000000000 : ℝ)^1583 := by
    have hnat : (2598248787 : ℕ)^2095*20000000000000^1583 ≤ 3360447433567^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598248787 10000000000 3360447433567 20000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1196534251/2500000000 : ℝ)^2095 ≤ (1178502893129/3125000000000 : ℝ)^1583 := by
    have hnat : (1196534251 : ℕ)^2095*3125000000000^1583 ≤ 1178502893129^1583*2500000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1196534251 2500000000 1178502893129 3125000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(68928229/125000000 : ℝ), (-2598248787/10000000000 : ℝ), (1196534251/2500000000 : ℝ)] ![(45485670240347/100000000000000 : ℝ), (3360447433567/20000000000000 : ℝ), (1178502893129/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(68928229/125000000 : ℝ)|^2095 ≤ (45485670240347/100000000000000 : ℝ)^1583
        have hw : |(68928229/125000000 : ℝ)|=(68928229/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2598248787/10000000000 : ℝ)|^2095 ≤ (3360447433567/20000000000000 : ℝ)^1583
        have hw : |(-2598248787/10000000000 : ℝ)|=(2598248787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1196534251/2500000000 : ℝ)|^2095 ≤ (1178502893129/3125000000000 : ℝ)^1583
        have hw : |(1196534251/2500000000 : ℝ)|=(1196534251/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1187_s0_2 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2757129157/5000000000 : ℝ)*x 0 + (1196534253/2500000000 : ℝ)*x 1 + (-519649757/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2757129157/5000000000 : ℝ)^2095 ≤ (45485670174847/100000000000000 : ℝ)^1583 := by
    have hnat : (2757129157 : ℕ)^2095*100000000000000^1583 ≤ 45485670174847^1583*5000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2757129157 5000000000 45485670174847 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1196534253/2500000000 : ℝ)^2095 ≤ (37712092663551/100000000000000 : ℝ)^1583 := by
    have hnat : (1196534253 : ℕ)^2095*100000000000000^1583 ≤ 37712092663551^1583*2500000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1196534253 2500000000 37712092663551 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (519649757/2000000000 : ℝ)^2095 ≤ (16802237150719/100000000000000 : ℝ)^1583 := by
    have hnat : (519649757 : ℕ)^2095*100000000000000^1583 ≤ 16802237150719^1583*2000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519649757 2000000000 16802237150719 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2757129157/5000000000 : ℝ), (1196534253/2500000000 : ℝ), (-519649757/2000000000 : ℝ)] ![(45485670174847/100000000000000 : ℝ), (37712092663551/100000000000000 : ℝ), (16802237150719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2757129157/5000000000 : ℝ)|^2095 ≤ (45485670174847/100000000000000 : ℝ)^1583
        have hw : |(2757129157/5000000000 : ℝ)|=(2757129157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1196534253/2500000000 : ℝ)|^2095 ≤ (37712092663551/100000000000000 : ℝ)^1583
        have hw : |(1196534253/2500000000 : ℝ)|=(1196534253/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-519649757/2000000000 : ℝ)|^2095 ≤ (16802237150719/100000000000000 : ℝ)^1583
        have hw : |(-519649757/2000000000 : ℝ)|=(519649757/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1187_s0_3 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2098687831/5000000000 : ℝ)*x 0 + (779771213/2500000000 : ℝ)*x 1 + (2821826807/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2098687831/5000000000 : ℝ)^2095 ≤ (3169823693043/10000000000000 : ℝ)^1583 := by
    have hnat : (2098687831 : ℕ)^2095*10000000000000^1583 ≤ 3169823693043^1583*5000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098687831 5000000000 3169823693043 10000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (779771213/2500000000 : ℝ)^2095 ≤ (21398193382099/100000000000000 : ℝ)^1583 := by
    have hnat : (779771213 : ℕ)^2095*100000000000000^1583 ≤ 21398193382099^1583*2500000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      779771213 2500000000 21398193382099 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2821826807/5000000000 : ℝ)^2095 ≤ (938071393451/2000000000000 : ℝ)^1583 := by
    have hnat : (2821826807 : ℕ)^2095*2000000000000^1583 ≤ 938071393451^1583*5000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2821826807 5000000000 938071393451 2000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2098687831/5000000000 : ℝ), (779771213/2500000000 : ℝ), (2821826807/5000000000 : ℝ)] ![(3169823693043/10000000000000 : ℝ), (21398193382099/100000000000000 : ℝ), (938071393451/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2098687831/5000000000 : ℝ)|^2095 ≤ (3169823693043/10000000000000 : ℝ)^1583
        have hw : |(2098687831/5000000000 : ℝ)|=(2098687831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(779771213/2500000000 : ℝ)|^2095 ≤ (21398193382099/100000000000000 : ℝ)^1583
        have hw : |(779771213/2500000000 : ℝ)|=(779771213/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2821826807/5000000000 : ℝ)|^2095 ≤ (938071393451/2000000000000 : ℝ)^1583
        have hw : |(2821826807/5000000000 : ℝ)|=(2821826807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1187_s0_4 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-941332097/5000000000 : ℝ)*x 0 + (4818561931/10000000000 : ℝ)*x 1 + (1502604941/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (941332097/5000000000 : ℝ)^2095 ≤ (10970032813007/100000000000000 : ℝ)^1583 := by
    have hnat : (941332097 : ℕ)^2095*100000000000000^1583 ≤ 10970032813007^1583*5000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      941332097 5000000000 10970032813007 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4818561931/10000000000 : ℝ)^2095 ≤ (38050587732917/100000000000000 : ℝ)^1583 := by
    have hnat : (4818561931 : ℕ)^2095*100000000000000^1583 ≤ 38050587732917^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4818561931 10000000000 38050587732917 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1502604941/2500000000 : ℝ)^2095 ≤ (5097937944811/10000000000000 : ℝ)^1583 := by
    have hnat : (1502604941 : ℕ)^2095*10000000000000^1583 ≤ 5097937944811^1583*2500000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1502604941 2500000000 5097937944811 10000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-941332097/5000000000 : ℝ), (4818561931/10000000000 : ℝ), (1502604941/2500000000 : ℝ)] ![(10970032813007/100000000000000 : ℝ), (38050587732917/100000000000000 : ℝ), (5097937944811/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-941332097/5000000000 : ℝ)|^2095 ≤ (10970032813007/100000000000000 : ℝ)^1583
        have hw : |(-941332097/5000000000 : ℝ)|=(941332097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4818561931/10000000000 : ℝ)|^2095 ≤ (38050587732917/100000000000000 : ℝ)^1583
        have hw : |(4818561931/10000000000 : ℝ)|=(4818561931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1502604941/2500000000 : ℝ)|^2095 ≤ (5097937944811/10000000000000 : ℝ)^1583
        have hw : |(1502604941/2500000000 : ℝ)|=(1502604941/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1187_s0_5 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2586129719/5000000000 : ℝ)*x 0 + (-274793257/2000000000 : ℝ)*x 1 + (187825607/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2586129719/5000000000 : ℝ)^2095 ≤ (41790162091021/100000000000000 : ℝ)^1583 := by
    have hnat : (2586129719 : ℕ)^2095*100000000000000^1583 ≤ 41790162091021^1583*5000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586129719 5000000000 41790162091021 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (274793257/2000000000 : ℝ)^2095 ≤ (7230462264039/100000000000000 : ℝ)^1583 := by
    have hnat : (274793257 : ℕ)^2095*100000000000000^1583 ≤ 7230462264039^1583*2000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274793257 2000000000 7230462264039 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (187825607/312500000 : ℝ)^2095 ≤ (50979375631553/100000000000000 : ℝ)^1583 := by
    have hnat : (187825607 : ℕ)^2095*100000000000000^1583 ≤ 50979375631553^1583*312500000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187825607 312500000 50979375631553 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2586129719/5000000000 : ℝ), (-274793257/2000000000 : ℝ), (187825607/312500000 : ℝ)] ![(41790162091021/100000000000000 : ℝ), (7230462264039/100000000000000 : ℝ), (50979375631553/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2586129719/5000000000 : ℝ)|^2095 ≤ (41790162091021/100000000000000 : ℝ)^1583
        have hw : |(2586129719/5000000000 : ℝ)|=(2586129719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-274793257/2000000000 : ℝ)|^2095 ≤ (7230462264039/100000000000000 : ℝ)^1583
        have hw : |(-274793257/2000000000 : ℝ)|=(274793257/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(187825607/312500000 : ℝ)|^2095 ≤ (50979375631553/100000000000000 : ℝ)^1583
        have hw : |(187825607/312500000 : ℝ)|=(187825607/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1187_s0_6 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (517225937/1000000000 : ℝ)*x 0 + (1202083923/2000000000 : ℝ)*x 1 + (-1373966081/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (517225937/1000000000 : ℝ)^2095 ≤ (20895080681951/50000000000000 : ℝ)^1583 := by
    have hnat : (517225937 : ℕ)^2095*50000000000000^1583 ≤ 20895080681951^1583*1000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517225937 1000000000 20895080681951 50000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1202083923/2000000000 : ℝ)^2095 ≤ (1274484444389/2500000000000 : ℝ)^1583 := by
    have hnat : (1202083923 : ℕ)^2095*2500000000000^1583 ≤ 1274484444389^1583*2000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1202083923 2000000000 1274484444389 2500000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1373966081/10000000000 : ℝ)^2095 ≤ (7230460843271/100000000000000 : ℝ)^1583 := by
    have hnat : (1373966081 : ℕ)^2095*100000000000000^1583 ≤ 7230460843271^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1373966081 10000000000 7230460843271 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(517225937/1000000000 : ℝ), (1202083923/2000000000 : ℝ), (-1373966081/10000000000 : ℝ)] ![(20895080681951/50000000000000 : ℝ), (1274484444389/2500000000000 : ℝ), (7230460843271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(517225937/1000000000 : ℝ)|^2095 ≤ (20895080681951/50000000000000 : ℝ)^1583
        have hw : |(517225937/1000000000 : ℝ)|=(517225937/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1202083923/2000000000 : ℝ)|^2095 ≤ (1274484444389/2500000000000 : ℝ)^1583
        have hw : |(1202083923/2000000000 : ℝ)|=(1202083923/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1373966081/10000000000 : ℝ)|^2095 ≤ (7230460843271/100000000000000 : ℝ)^1583
        have hw : |(-1373966081/10000000000 : ℝ)|=(1373966081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1187_s0_7 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4207440051/10000000000 : ℝ)*x 0 + (1394643687/2500000000 : ℝ)*x 1 + (1593229047/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4207440051/10000000000 : ℝ)^2095 ≤ (7949716072363/25000000000000 : ℝ)^1583 := by
    have hnat : (4207440051 : ℕ)^2095*25000000000000^1583 ≤ 7949716072363^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4207440051 10000000000 7949716072363 25000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1394643687/2500000000 : ℝ)^2095 ≤ (11547278259079/25000000000000 : ℝ)^1583 := by
    have hnat : (1394643687 : ℕ)^2095*25000000000000^1583 ≤ 11547278259079^1583*2500000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1394643687 2500000000 11547278259079 25000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1593229047/5000000000 : ℝ)^2095 ≤ (11006011329171/50000000000000 : ℝ)^1583 := by
    have hnat : (1593229047 : ℕ)^2095*50000000000000^1583 ≤ 11006011329171^1583*5000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1593229047 5000000000 11006011329171 50000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4207440051/10000000000 : ℝ), (1394643687/2500000000 : ℝ), (1593229047/5000000000 : ℝ)] ![(7949716072363/25000000000000 : ℝ), (11547278259079/25000000000000 : ℝ), (11006011329171/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4207440051/10000000000 : ℝ)|^2095 ≤ (7949716072363/25000000000000 : ℝ)^1583
        have hw : |(4207440051/10000000000 : ℝ)|=(4207440051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1394643687/2500000000 : ℝ)|^2095 ≤ (11547278259079/25000000000000 : ℝ)^1583
        have hw : |(1394643687/2500000000 : ℝ)|=(1394643687/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1593229047/5000000000 : ℝ)|^2095 ≤ (11006011329171/50000000000000 : ℝ)^1583
        have hw : |(1593229047/5000000000 : ℝ)|=(1593229047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1187_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150352467/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (597/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27643/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8379/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8379 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8379*1^2048 ≤ 0^2048*1^8379 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8379 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8379 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8379/2048 : ℝ) ≤ (2354532138194087039/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8379 ≤ (2354532138194087039/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8379*100000000000000000000^2048 ≤ 2354532138194087039^2048*5^8379 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2354532138194087039 100000000000000000000 8379 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2354532138194087039/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8379 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8379/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8379 := by
      have hnat : (1 : ℕ)^2048*1^8379 ≤ 1^8379*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8379 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8379 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (102354532138194087039/100000000000000000000 : ℝ) ≤ (502852231841643/500000000000000 : ℝ) ^ (8379/2048 : ℝ) := by
    have hpowers : (102354532138194087039/100000000000000000000 : ℝ)^2048 ≤ (502852231841643/500000000000000 : ℝ)^8379 := by
      have hnat : (102354532138194087039 : ℕ)^2048*500000000000000^8379 ≤ 502852231841643^8379*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102354532138194087039 100000000000000000000 502852231841643 500000000000000 2048 8379 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (502852231841643/500000000000000 : ℝ)) (X := (102354532138194087039/100000000000000000000 : ℝ)) (by norm_num) 8379 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (52354532138194087039/50000000000000000000 : ℝ) ≤ (252852231841643/250000000000000 : ℝ) ^ (8379/2048 : ℝ) := by
    have hpowers : (52354532138194087039/50000000000000000000 : ℝ)^2048 ≤ (252852231841643/250000000000000 : ℝ)^8379 := by
      have hnat : (52354532138194087039 : ℕ)^2048*250000000000000^8379 ≤ 252852231841643^8379*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52354532138194087039 50000000000000000000 252852231841643 250000000000000 2048 8379 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (252852231841643/250000000000000 : ℝ)) (X := (52354532138194087039/50000000000000000000 : ℝ)) (by norm_num) 8379 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(2852231841643/200000000000000 : ℝ)*(0 : ℝ))^(8379/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(2852231841643/200000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2354532138194087039/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(2852231841643/200000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8379/2048 : ℝ) := by
    rw [show (1 : ℝ)+(2852231841643/200000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(502852231841643/500000000000000 : ℝ) by norm_num, show 1+(2354532138194087039/100000000000000000000 : ℝ)+(0 : ℝ)=(102354532138194087039/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2354532138194087039/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(2852231841643/200000000000000 : ℝ)*(2/5 : ℝ))^(8379/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(2852231841643/200000000000000 : ℝ)*(2/5 : ℝ)=(252852231841643/250000000000000 : ℝ) by norm_num, show 1+2*(2354532138194087039/100000000000000000000 : ℝ)=(52354532138194087039/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(2852231841643/200000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8379/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2852231841643/200000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(2852231841643/200000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8379/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2852231841643/200000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(2852231841643/200000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8379/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2852231841643/200000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1877649683/10000000000 : ℝ)*X 0 0+(377749243/625000000 : ℝ)*X 0 1+(1196534253/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((68928229/125000000 : ℝ)*X 1 0+(-2598248787/10000000000 : ℝ)*X 1 1+(1196534251/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2757129157/5000000000 : ℝ)*X 2 0+(1196534253/2500000000 : ℝ)*X 2 1+(-519649757/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2098687831/5000000000 : ℝ)*X 0 0+(779771213/2500000000 : ℝ)*X 0 1+(2821826807/5000000000 : ℝ)*X 0 2+(2098687831/5000000000 : ℝ)*X 1 0+(779771213/2500000000 : ℝ)*X 1 1+(2821826807/5000000000 : ℝ)*X 1 2+(2098687831/5000000000 : ℝ)*X 2 0+(779771213/2500000000 : ℝ)*X 2 1+(2821826807/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-941332097/5000000000 : ℝ)*X 0 0+(4818561931/10000000000 : ℝ)*X 0 1+(1502604941/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2586129719/5000000000 : ℝ)*X 1 0+(-274793257/2000000000 : ℝ)*X 1 1+(187825607/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((517225937/1000000000 : ℝ)*X 2 0+(1202083923/2000000000 : ℝ)*X 2 1+(-1373966081/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4207440051/10000000000 : ℝ)*X 0 0+(1394643687/2500000000 : ℝ)*X 0 1+(1593229047/5000000000 : ℝ)*X 0 2+(4207440051/10000000000 : ℝ)*X 1 0+(1394643687/2500000000 : ℝ)*X 1 1+(1593229047/5000000000 : ℝ)*X 1 2+(4207440051/10000000000 : ℝ)*X 2 0+(1394643687/2500000000 : ℝ)*X 2 1+(1593229047/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6509769798281748782229/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (69526943/100000000000000 : ℝ)*(base1) + (159809129/10000000000000 : ℝ)*(base19) + (1487066283/100000000000000 : ℝ)*(base23) + (55079981/50000000000000 : ℝ)*(base24) + (367001153/100000000000000 : ℝ)*(upper3) + (119112763869433/20000000000000 : ℝ)*(major0) + (119112763869433/20000000000000 : ℝ)*(major1) + (119112763869433/20000000000000 : ℝ)*(major2) + (397506094695983/50000000000000 : ℝ)*(sp0) + (397507026447927/50000000000000 : ℝ)*(sp1) + (795014053760899/100000000000000 : ℝ)*(sp2) + (396108895469249/100000000000000 : ℝ)*(sp3) + (3531122121/100000000000000 : ℝ)*(sp4) + (140285933/5000000000000 : ℝ)*(sp7) + (396111770714853/100000000000000 : ℝ)*(f.failure) + (99376956373393/12500000000000 : ℝ)*(f.sum) + (6729609706419/2000000000000000000000000000 : ℝ)*base65 + (15847595050419/4000000000000000000000000000 : ℝ)*base67 + (35106004350419/4000000000000000000000000000 : ℝ)*base69 + (9648085086419/4000000000000000000000000000 : ℝ)*base71 + (8349814738419/2000000000000000000000000000 : ℝ)*base73 + (23971858830419/4000000000000000000000000000 : ℝ)*base75 + (20584649062419/4000000000000000000000000000 : ℝ)*base77 + (32042753734419/4000000000000000000000000000 : ℝ)*base79 + (23713799776419/2000000000000000000000000000 : ℝ)*base81 + (2092351/10000000000000000000000 : ℝ)*base89 + (2092351/10000000000000000000000 : ℝ)*base91 + (2092351/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8672986006451288363397/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19874651/100000000000000 : ℝ)*(base1) + (238284309/50000000000000 : ℝ)*(base19) + (469447017/100000000000000 : ℝ)*(base23) + (3945413/10000000000000 : ℝ)*(upper3) + (32098643/50000000000000 : ℝ)*(upper5) + (314266551498773/50000000000000 : ℝ)*(major0) + (314266551498773/50000000000000 : ℝ)*(major1) + (628533102997547/100000000000000 : ℝ)*(major2) + (7032459/781250000000 : ℝ)*(sp1) + (959274643/100000000000000 : ℝ)*(sp2) + (839026400868929/100000000000000 : ℝ)*(sp4) + (209756251067727/25000000000000 : ℝ)*(sp5) + (419512476136309/50000000000000 : ℝ)*(sp6) + (209019873653127/50000000000000 : ℝ)*(sp7) + (83607953436181/20000000000000 : ℝ)*(f.failure) + (419513190497139/50000000000000 : ℝ)*(f.sum) + (23624203502201/20000000000000000000000000000 : ℝ)*base66 + (40856796370279/20000000000000000000000000000 : ℝ)*base68 + (26113318484039/10000000000000000000000000000 : ℝ)*base69 + (60271384510279/20000000000000000000000000000 : ℝ)*base72 + (6930216702201/20000000000000000000000000000 : ℝ)*base74 + (39714846044039/10000000000000000000000000000 : ℝ)*base75 + (52578770355961/10000000000000000000000000000 : ℝ)*base78 + (11752982975961/10000000000000000000000000000 : ℝ)*base80 + (15494310510961/5000000000000000000000000000 : ℝ)*base82 + (20408527/2000000000000000000000 : ℝ)*base89 + (20408527/2000000000000000000000 : ℝ)*base91 + (408527/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1187_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150352467/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (597/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27643/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1187_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1187_s1_0 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2079062043/10000000000 : ℝ)*x 0 + (5689639551/10000000000 : ℝ)*x 1 + (501155391/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2079062043/10000000000 : ℝ)^2095 ≤ (500381065479/4000000000000 : ℝ)^1583 := by
    have hnat : (2079062043 : ℕ)^2095*4000000000000^1583 ≤ 500381065479^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079062043 10000000000 500381065479 4000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5689639551/10000000000 : ℝ)^2095 ≤ (1481563405541/3125000000000 : ℝ)^1583 := by
    have hnat : (5689639551 : ℕ)^2095*3125000000000^1583 ≤ 1481563405541^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5689639551 10000000000 1481563405541 3125000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (501155391/1000000000 : ℝ)^2095 ≤ (40080444366629/100000000000000 : ℝ)^1583 := by
    have hnat : (501155391 : ℕ)^2095*100000000000000^1583 ≤ 40080444366629^1583*1000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501155391 1000000000 40080444366629 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2079062043/10000000000 : ℝ), (5689639551/10000000000 : ℝ), (501155391/1000000000 : ℝ)] ![(500381065479/4000000000000 : ℝ), (1481563405541/3125000000000 : ℝ), (40080444366629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2079062043/10000000000 : ℝ)|^2095 ≤ (500381065479/4000000000000 : ℝ)^1583
        have hw : |(-2079062043/10000000000 : ℝ)|=(2079062043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5689639551/10000000000 : ℝ)|^2095 ≤ (1481563405541/3125000000000 : ℝ)^1583
        have hw : |(5689639551/10000000000 : ℝ)|=(5689639551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(501155391/1000000000 : ℝ)|^2095 ≤ (40080444366629/100000000000000 : ℝ)^1583
        have hw : |(501155391/1000000000 : ℝ)|=(501155391/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1187_s1_1 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (67708167/125000000 : ℝ)*x 0 + (-305520421/1250000000 : ℝ)*x 1 + (5011554169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67708167/125000000 : ℝ)^2095 ≤ (11105802594819/25000000000000 : ℝ)^1583 := by
    have hnat : (67708167 : ℕ)^2095*25000000000000^1583 ≤ 11105802594819^1583*125000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67708167 125000000 11105802594819 25000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (305520421/1250000000 : ℝ)^2095 ≤ (1937042811109/12500000000000 : ℝ)^1583 := by
    have hnat : (305520421 : ℕ)^2095*12500000000000^1583 ≤ 1937042811109^1583*1250000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      305520421 1250000000 1937042811109 12500000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5011554169/10000000000 : ℝ)^2095 ≤ (4008044710797/10000000000000 : ℝ)^1583 := by
    have hnat : (5011554169 : ℕ)^2095*10000000000000^1583 ≤ 4008044710797^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5011554169 10000000000 4008044710797 10000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(67708167/125000000 : ℝ), (-305520421/1250000000 : ℝ), (5011554169/10000000000 : ℝ)] ![(11105802594819/25000000000000 : ℝ), (1937042811109/12500000000000 : ℝ), (4008044710797/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(67708167/125000000 : ℝ)|^2095 ≤ (11105802594819/25000000000000 : ℝ)^1583
        have hw : |(67708167/125000000 : ℝ)|=(67708167/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-305520421/1250000000 : ℝ)|^2095 ≤ (1937042811109/12500000000000 : ℝ)^1583
        have hw : |(-305520421/1250000000 : ℝ)|=(305520421/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5011554169/10000000000 : ℝ)|^2095 ≤ (4008044710797/10000000000000 : ℝ)^1583
        have hw : |(5011554169/10000000000 : ℝ)|=(5011554169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1187_s1_2 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5416652483/10000000000 : ℝ)*x 0 + (78305543/156250000 : ℝ)*x 1 + (-2444163767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5416652483/10000000000 : ℝ)^2095 ≤ (4442320086049/10000000000000 : ℝ)^1583 := by
    have hnat : (5416652483 : ℕ)^2095*10000000000000^1583 ≤ 4442320086049^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416652483 10000000000 4442320086049 10000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (78305543/156250000 : ℝ)^2095 ≤ (5010056659829/12500000000000 : ℝ)^1583 := by
    have hnat : (78305543 : ℕ)^2095*12500000000000^1583 ≤ 5010056659829^1583*156250000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78305543 156250000 5010056659829 12500000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2444163767/10000000000 : ℝ)^2095 ≤ (15496345836791/100000000000000 : ℝ)^1583 := by
    have hnat : (2444163767 : ℕ)^2095*100000000000000^1583 ≤ 15496345836791^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2444163767 10000000000 15496345836791 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5416652483/10000000000 : ℝ), (78305543/156250000 : ℝ), (-2444163767/10000000000 : ℝ)] ![(4442320086049/10000000000000 : ℝ), (5010056659829/12500000000000 : ℝ), (15496345836791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5416652483/10000000000 : ℝ)|^2095 ≤ (4442320086049/10000000000000 : ℝ)^1583
        have hw : |(5416652483/10000000000 : ℝ)|=(5416652483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(78305543/156250000 : ℝ)|^2095 ≤ (5010056659829/12500000000000 : ℝ)^1583
        have hw : |(78305543/156250000 : ℝ)|=(78305543/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2444163767/10000000000 : ℝ)|^2095 ≤ (15496345836791/100000000000000 : ℝ)^1583
        have hw : |(-2444163767/10000000000 : ℝ)|=(2444163767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1187_s1_3 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (862720787/2000000000 : ℝ)*x 0 + (1842715299/5000000000 : ℝ)*x 1 + (2523191049/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (862720787/2000000000 : ℝ)^2095 ≤ (32865048376441/100000000000000 : ℝ)^1583 := by
    have hnat : (862720787 : ℕ)^2095*100000000000000^1583 ≤ 32865048376441^1583*2000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862720787 2000000000 32865048376441 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1842715299/5000000000 : ℝ)^2095 ≤ (26685460665653/100000000000000 : ℝ)^1583 := by
    have hnat : (1842715299 : ℕ)^2095*100000000000000^1583 ≤ 26685460665653^1583*5000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1842715299 5000000000 26685460665653 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2523191049/5000000000 : ℝ)^2095 ≤ (40449490933933/100000000000000 : ℝ)^1583 := by
    have hnat : (2523191049 : ℕ)^2095*100000000000000^1583 ≤ 40449490933933^1583*5000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2523191049 5000000000 40449490933933 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(862720787/2000000000 : ℝ), (1842715299/5000000000 : ℝ), (2523191049/5000000000 : ℝ)] ![(32865048376441/100000000000000 : ℝ), (26685460665653/100000000000000 : ℝ), (40449490933933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(862720787/2000000000 : ℝ)|^2095 ≤ (32865048376441/100000000000000 : ℝ)^1583
        have hw : |(862720787/2000000000 : ℝ)|=(862720787/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1842715299/5000000000 : ℝ)|^2095 ≤ (26685460665653/100000000000000 : ℝ)^1583
        have hw : |(1842715299/5000000000 : ℝ)|=(1842715299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2523191049/5000000000 : ℝ)|^2095 ≤ (40449490933933/100000000000000 : ℝ)^1583
        have hw : |(2523191049/5000000000 : ℝ)|=(2523191049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1187_s1_4 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-103990383/500000000 : ℝ)*x 0 + (5020654181/10000000000 : ℝ)*x 1 + (5680361793/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (103990383/500000000 : ℝ)^2095 ≤ (12515464327051/100000000000000 : ℝ)^1583 := by
    have hnat : (103990383 : ℕ)^2095*100000000000000^1583 ≤ 12515464327051^1583*500000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103990383 500000000 12515464327051 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5020654181/10000000000 : ℝ)^2095 ≤ (20088396440467/50000000000000 : ℝ)^1583 := by
    have hnat : (5020654181 : ℕ)^2095*50000000000000^1583 ≤ 20088396440467^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5020654181 10000000000 20088396440467 50000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5680361793/10000000000 : ℝ)^2095 ≤ (47307742779119/100000000000000 : ℝ)^1583 := by
    have hnat : (5680361793 : ℕ)^2095*100000000000000^1583 ≤ 47307742779119^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5680361793 10000000000 47307742779119 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-103990383/500000000 : ℝ), (5020654181/10000000000 : ℝ), (5680361793/10000000000 : ℝ)] ![(12515464327051/100000000000000 : ℝ), (20088396440467/50000000000000 : ℝ), (47307742779119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-103990383/500000000 : ℝ)|^2095 ≤ (12515464327051/100000000000000 : ℝ)^1583
        have hw : |(-103990383/500000000 : ℝ)|=(103990383/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5020654181/10000000000 : ℝ)|^2095 ≤ (20088396440467/50000000000000 : ℝ)^1583
        have hw : |(5020654181/10000000000 : ℝ)|=(5020654181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5680361793/10000000000 : ℝ)|^2095 ≤ (47307742779119/100000000000000 : ℝ)^1583
        have hw : |(5680361793/10000000000 : ℝ)|=(5680361793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1187_s1_5 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5242417541/10000000000 : ℝ)*x 0 + (-443838721/2500000000 : ℝ)*x 1 + (2840181437/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5242417541/10000000000 : ℝ)^2095 ≤ (21270999322129/50000000000000 : ℝ)^1583 := by
    have hnat : (5242417541 : ℕ)^2095*50000000000000^1583 ≤ 21270999322129^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242417541 10000000000 21270999322129 50000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (443838721/2500000000 : ℝ)^2095 ≤ (2537561660657/25000000000000 : ℝ)^1583 := by
    have hnat : (443838721 : ℕ)^2095*25000000000000^1583 ≤ 2537561660657^1583*2500000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443838721 2500000000 2537561660657 25000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2840181437/5000000000 : ℝ)^2095 ≤ (2956734668367/6250000000000 : ℝ)^1583 := by
    have hnat : (2840181437 : ℕ)^2095*6250000000000^1583 ≤ 2956734668367^1583*5000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2840181437 5000000000 2956734668367 6250000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5242417541/10000000000 : ℝ), (-443838721/2500000000 : ℝ), (2840181437/5000000000 : ℝ)] ![(21270999322129/50000000000000 : ℝ), (2537561660657/25000000000000 : ℝ), (2956734668367/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5242417541/10000000000 : ℝ)|^2095 ≤ (21270999322129/50000000000000 : ℝ)^1583
        have hw : |(5242417541/10000000000 : ℝ)|=(5242417541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-443838721/2500000000 : ℝ)|^2095 ≤ (2537561660657/25000000000000 : ℝ)^1583
        have hw : |(-443838721/2500000000 : ℝ)|=(443838721/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2840181437/5000000000 : ℝ)|^2095 ≤ (2956734668367/6250000000000 : ℝ)^1583
        have hw : |(2840181437/5000000000 : ℝ)|=(2840181437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1187_s1_6 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5242417327/10000000000 : ℝ)*x 0 + (5680363671/10000000000 : ℝ)*x 1 + (-1775354027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5242417327/10000000000 : ℝ)^2095 ≤ (42541996345977/100000000000000 : ℝ)^1583 := by
    have hnat : (5242417327 : ℕ)^2095*100000000000000^1583 ≤ 42541996345977^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242417327 10000000000 42541996345977 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5680363671/10000000000 : ℝ)^2095 ≤ (9461552695677/20000000000000 : ℝ)^1583 := by
    have hnat : (5680363671 : ℕ)^2095*20000000000000^1583 ≤ 9461552695677^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5680363671 10000000000 9461552695677 20000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1775354027/10000000000 : ℝ)^2095 ≤ (2030048031629/20000000000000 : ℝ)^1583 := by
    have hnat : (1775354027 : ℕ)^2095*20000000000000^1583 ≤ 2030048031629^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1775354027 10000000000 2030048031629 20000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5242417327/10000000000 : ℝ), (5680363671/10000000000 : ℝ), (-1775354027/10000000000 : ℝ)] ![(42541996345977/100000000000000 : ℝ), (9461552695677/20000000000000 : ℝ), (2030048031629/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5242417327/10000000000 : ℝ)|^2095 ≤ (42541996345977/100000000000000 : ℝ)^1583
        have hw : |(5242417327/10000000000 : ℝ)|=(5242417327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5680363671/10000000000 : ℝ)|^2095 ≤ (9461552695677/20000000000000 : ℝ)^1583
        have hw : |(5680363671/10000000000 : ℝ)|=(5680363671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1775354027/10000000000 : ℝ)|^2095 ≤ (2030048031629/20000000000000 : ℝ)^1583
        have hw : |(-1775354027/10000000000 : ℝ)|=(1775354027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1187_s1_7 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (539387311/1250000000 : ℝ)*x 0 + (502811791/1000000000 : ℝ)*x 1 + (3704049273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539387311/1250000000 : ℝ)^2095 ≤ (32880119053849/100000000000000 : ℝ)^1583 := by
    have hnat : (539387311 : ℕ)^2095*100000000000000^1583 ≤ 32880119053849^1583*1250000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539387311 1250000000 32880119053849 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (502811791/1000000000 : ℝ)^2095 ≤ (40255856792039/100000000000000 : ℝ)^1583 := by
    have hnat : (502811791 : ℕ)^2095*100000000000000^1583 ≤ 40255856792039^1583*1000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502811791 1000000000 40255856792039 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3704049273/10000000000 : ℝ)^2095 ≤ (6716006034161/25000000000000 : ℝ)^1583 := by
    have hnat : (3704049273 : ℕ)^2095*25000000000000^1583 ≤ 6716006034161^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3704049273 10000000000 6716006034161 25000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(539387311/1250000000 : ℝ), (502811791/1000000000 : ℝ), (3704049273/10000000000 : ℝ)] ![(32880119053849/100000000000000 : ℝ), (40255856792039/100000000000000 : ℝ), (6716006034161/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(539387311/1250000000 : ℝ)|^2095 ≤ (32880119053849/100000000000000 : ℝ)^1583
        have hw : |(539387311/1250000000 : ℝ)|=(539387311/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(502811791/1000000000 : ℝ)|^2095 ≤ (40255856792039/100000000000000 : ℝ)^1583
        have hw : |(502811791/1000000000 : ℝ)|=(502811791/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3704049273/10000000000 : ℝ)|^2095 ≤ (6716006034161/25000000000000 : ℝ)^1583
        have hw : |(3704049273/10000000000 : ℝ)|=(3704049273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1187_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150352467/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27643/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (597/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2949/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5059/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27643/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (597/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27643/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (597/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27643/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (597/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27643/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (597/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27643/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (597/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27643/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (597/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (597/100000 : ℝ) ^ (8379/2048 : ℝ) ≤ (79583799277/100000000000000000000 : ℝ) := by
    have hpowers : (597/100000 : ℝ)^8379 ≤ (79583799277/100000000000000000000 : ℝ)^2048 := by
      have hnat : (597 : ℕ)^8379*100000000000000000000^2048 ≤ 79583799277^2048*100000^8379 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        597 100000 79583799277 100000000000000000000 8379 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (597/100000 : ℝ)) (X := (79583799277/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8379 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (27643/100000 : ℝ) ^ (8379/2048 : ℝ) ≤ (519221446194205347/100000000000000000000 : ℝ) := by
    have hpowers : (27643/100000 : ℝ)^8379 ≤ (519221446194205347/100000000000000000000 : ℝ)^2048 := by
      have hnat : (27643 : ℕ)^8379*100000000000000000000^2048 ≤ 519221446194205347^2048*100000^8379 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27643 100000 519221446194205347 100000000000000000000 8379 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27643/100000 : ℝ)) (X := (519221446194205347/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8379 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000079583799277/50000000000000000000 : ℝ) ≤ (625000000243149/625000000000000 : ℝ) ^ (8379/2048 : ℝ) := by
    have hpowers : (50000000079583799277/50000000000000000000 : ℝ)^2048 ≤ (625000000243149/625000000000000 : ℝ)^8379 := by
      have hnat : (50000000079583799277 : ℕ)^2048*625000000000000^8379 ≤ 625000000243149^8379*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000079583799277 50000000000000000000 625000000243149 625000000000000 2048 8379 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625000000243149/625000000000000 : ℝ)) (X := (50000000079583799277/50000000000000000000 : ℝ)) (by norm_num) 8379 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (6282451345361125289/6250000000000000000 : ℝ) ≤ (400506640954073/400000000000000 : ℝ) ^ (8379/2048 : ℝ) := by
    have hpowers : (6282451345361125289/6250000000000000000 : ℝ)^2048 ≤ (400506640954073/400000000000000 : ℝ)^8379 := by
      have hnat : (6282451345361125289 : ℕ)^2048*400000000000000^8379 ≤ 400506640954073^8379*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6282451345361125289 6250000000000000000 400506640954073 400000000000000 2048 8379 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400506640954073/400000000000000 : ℝ)) (X := (6282451345361125289/6250000000000000000 : ℝ)) (by norm_num) 8379 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50519221446194205347/50000000000000000000 : ℝ) ≤ (5012666021906633/5000000000000000 : ℝ) ^ (8379/2048 : ℝ) := by
    have hpowers : (50519221446194205347/50000000000000000000 : ℝ)^2048 ≤ (5012666021906633/5000000000000000 : ℝ)^8379 := by
      have hnat : (50519221446194205347 : ℕ)^2048*5000000000000000^8379 ≤ 5012666021906633^8379*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50519221446194205347 50000000000000000000 5012666021906633 5000000000000000 2048 8379 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5012666021906633/5000000000000000 : ℝ)) (X := (50519221446194205347/50000000000000000000 : ℝ)) (by norm_num) 8379 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(79583799277/100000000000000000000 : ℝ) ≤ ((27044487687738536511/27046000000000000000 : ℝ)+2*(12666019961441/2704600000000000 : ℝ)*(597/100000 : ℝ))^(8379/2048 : ℝ) := by
    rw [show (27044487687738536511/27046000000000000000 : ℝ)+2*(12666019961441/2704600000000000 : ℝ)*(597/100000 : ℝ)=(625000000243149/625000000000000 : ℝ) by norm_num, show 1+2*(79583799277/100000000000000000000 : ℝ)=(50000000079583799277/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(519221446194205347/100000000000000000000 : ℝ)+(79583799277/100000000000000000000 : ℝ) ≤ ((27044487687738536511/27046000000000000000 : ℝ)+(12666019961441/2704600000000000 : ℝ)*((27643/100000 : ℝ)+(597/100000 : ℝ)))^(8379/2048 : ℝ) := by
    rw [show (27044487687738536511/27046000000000000000 : ℝ)+(12666019961441/2704600000000000 : ℝ)*((27643/100000 : ℝ)+(597/100000 : ℝ))=(400506640954073/400000000000000 : ℝ) by norm_num, show 1+(519221446194205347/100000000000000000000 : ℝ)+(79583799277/100000000000000000000 : ℝ)=(6282451345361125289/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(519221446194205347/100000000000000000000 : ℝ) ≤ ((27044487687738536511/27046000000000000000 : ℝ)+2*(12666019961441/2704600000000000 : ℝ)*(27643/100000 : ℝ))^(8379/2048 : ℝ) := by
    rw [show (27044487687738536511/27046000000000000000 : ℝ)+2*(12666019961441/2704600000000000 : ℝ)*(27643/100000 : ℝ)=(5012666021906633/5000000000000000 : ℝ) by norm_num, show 1+2*(519221446194205347/100000000000000000000 : ℝ)=(50519221446194205347/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27044487687738536511/27046000000000000000 : ℝ)*(X 1 0+X 2 0)+(12666019961441/2704600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8379/2048 : ℝ)) (lo := (597/100000 : ℝ)) (hi := (27643/100000 : ℝ)) (c := (27044487687738536511/27046000000000000000 : ℝ)) (alpha := (12666019961441/2704600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27044487687738536511/27046000000000000000 : ℝ)*(X 0 1+X 2 1)+(12666019961441/2704600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8379/2048 : ℝ)) (lo := (597/100000 : ℝ)) (hi := (27643/100000 : ℝ)) (c := (27044487687738536511/27046000000000000000 : ℝ)) (alpha := (12666019961441/2704600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27044487687738536511/27046000000000000000 : ℝ)*(X 0 2+X 1 2)+(12666019961441/2704600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8379/2048 : ℝ)) (lo := (597/100000 : ℝ)) (hi := (27643/100000 : ℝ)) (c := (27044487687738536511/27046000000000000000 : ℝ)) (alpha := (12666019961441/2704600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2079062043/10000000000 : ℝ)*X 0 0+(5689639551/10000000000 : ℝ)*X 0 1+(501155391/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((67708167/125000000 : ℝ)*X 1 0+(-305520421/1250000000 : ℝ)*X 1 1+(5011554169/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5416652483/10000000000 : ℝ)*X 2 0+(78305543/156250000 : ℝ)*X 2 1+(-2444163767/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((862720787/2000000000 : ℝ)*X 0 0+(1842715299/5000000000 : ℝ)*X 0 1+(2523191049/5000000000 : ℝ)*X 0 2+(862720787/2000000000 : ℝ)*X 1 0+(1842715299/5000000000 : ℝ)*X 1 1+(2523191049/5000000000 : ℝ)*X 1 2+(862720787/2000000000 : ℝ)*X 2 0+(1842715299/5000000000 : ℝ)*X 2 1+(2523191049/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-103990383/500000000 : ℝ)*X 0 0+(5020654181/10000000000 : ℝ)*X 0 1+(5680361793/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5242417541/10000000000 : ℝ)*X 1 0+(-443838721/2500000000 : ℝ)*X 1 1+(2840181437/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5242417327/10000000000 : ℝ)*X 2 0+(5680363671/10000000000 : ℝ)*X 2 1+(-1775354027/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((539387311/1250000000 : ℝ)*X 0 0+(502811791/1000000000 : ℝ)*X 0 1+(3704049273/10000000000 : ℝ)*X 0 2+(539387311/1250000000 : ℝ)*X 1 0+(502811791/1000000000 : ℝ)*X 1 1+(3704049273/10000000000 : ℝ)*X 1 2+(539387311/1250000000 : ℝ)*X 2 0+(502811791/1000000000 : ℝ)*X 2 1+(3704049273/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (153629862950333456450175357/42259375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (495962051/50000000000000 : ℝ)*(base19) + (148550649/20000000000000 : ℝ)*(base23) + (319513/12500000000000 : ℝ)*(upper2) + (13518631/6250000000000 : ℝ)*(upper3) + (204691/2500000000000 : ℝ)*(upper4) + (4315504323919/390625000000 : ℝ)*(major0) + (4315504323919/390625000000 : ℝ)*(major1) + (4315504323919/390625000000 : ℝ)*(major2) + (1474747205022583/100000000000000 : ℝ)*(sp0) + (73737547429903/5000000000000 : ℝ)*(sp1) + (737375598884459/50000000000000 : ℝ)*(sp2) + (29391307815211/4000000000000 : ℝ)*(sp3) + (236774979/5000000000000 : ℝ)*(sp4) + (1728381991/50000000000000 : ℝ)*(sp7) + (734786152144257/100000000000000 : ℝ)*(f.failure) + (737375970261081/50000000000000 : ℝ)*(f.sum) + (3456761521799/2112968750000000000000000000 : ℝ)*base66 + (37265120734816689/42259375000000000000000000000000 : ℝ)*base68 + (208757535463703657/21129687500000000000000000000000 : ℝ)*base70 + (33353029160235439/42259375000000000000000000000000 : ℝ)*base72 + (43363584708931/33807500000000000000000000000 : ℝ)*base73 + (3099335154546609/10564843750000000000000000000000 : ℝ)*base75 + (234357286598554189/42259375000000000000000000000000 : ℝ)*base78 + (87622556250734907/21129687500000000000000000000000 : ℝ)*base80 + (52910098627619/33807500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (20167981/10000000000000000000000 : ℝ)*base90 + (20167981/10000000000000000000000 : ℝ)*base92 + (20167981/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (461034297104995764636249879/135230000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (59510203/4000000000000 : ℝ)*(base19) + (1864862087/100000000000000 : ℝ)*(base23) + (159771127/100000000000000 : ℝ)*(upper2) + (58791877/20000000000000 : ℝ)*(upper3) + (6020831/4000000000000 : ℝ)*(upper5) + (113553458142163/10000000000000 : ℝ)*(major0) + (113553458142163/10000000000000 : ℝ)*(major1) + (113553458142163/10000000000000 : ℝ)*(major2) + (7663731507/100000000000000 : ℝ)*(sp1) + (2925533153/25000000000000 : ℝ)*(sp2) + (757910331237157/50000000000000 : ℝ)*(sp4) + (378952877746933/25000000000000 : ℝ)*(sp5) + (23684485866869/1562500000000 : ℝ)*(sp6) + (188812096681731/25000000000000 : ℝ)*(sp7) + (188812096681731/25000000000000 : ℝ)*(f.failure) + (757910331237157/50000000000000 : ℝ)*(f.sum) + (78480509685573/13523000000000000000000000000 : ℝ)*base66 + (303444549217196707/270460000000000000000000000000000 : ℝ)*base68 + (633024396216003293/270460000000000000000000000000000 : ℝ)*base69 + (1415601971171396707/270460000000000000000000000000000 : ℝ)*base72 + (3162024062633/2704600000000000000000000000 : ℝ)*base74 + (1218494716439463293/270460000000000000000000000000000 : ℝ)*base75 + (2355926885379556707/270460000000000000000000000000000 : ℝ)*base78 + (1618149453271156707/270460000000000000000000000000000 : ℝ)*base80 + (3670463465383/2704600000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (19680377/2500000000000000000000 : ℝ)*base89 + (19680377/2500000000000000000000 : ℝ)*base91 + (19680377/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1187_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150352467/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27643/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (597/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2949/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5059/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1187_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1187_s2_0 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1064954229/5000000000 : ℝ)*x 0 + (5502447971/10000000000 : ℝ)*x 1 + (2583185349/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1064954229/5000000000 : ℝ)^2095 ≤ (6458004545711/50000000000000 : ℝ)^1583 := by
    have hnat : (1064954229 : ℕ)^2095*50000000000000^1583 ≤ 6458004545711^1583*5000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064954229 5000000000 6458004545711 50000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5502447971/10000000000 : ℝ)^2095 ≤ (45356785110999/100000000000000 : ℝ)^1583 := by
    have hnat : (5502447971 : ℕ)^2095*100000000000000^1583 ≤ 45356785110999^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5502447971 10000000000 45356785110999 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2583185349/5000000000 : ℝ)^2095 ≤ (41727205782233/100000000000000 : ℝ)^1583 := by
    have hnat : (2583185349 : ℕ)^2095*100000000000000^1583 ≤ 41727205782233^1583*5000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2583185349 5000000000 41727205782233 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1064954229/5000000000 : ℝ), (5502447971/10000000000 : ℝ), (2583185349/5000000000 : ℝ)] ![(6458004545711/50000000000000 : ℝ), (45356785110999/100000000000000 : ℝ), (41727205782233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1064954229/5000000000 : ℝ)|^2095 ≤ (6458004545711/50000000000000 : ℝ)^1583
        have hw : |(-1064954229/5000000000 : ℝ)|=(1064954229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5502447971/10000000000 : ℝ)|^2095 ≤ (45356785110999/100000000000000 : ℝ)^1583
        have hw : |(5502447971/10000000000 : ℝ)|=(5502447971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2583185349/5000000000 : ℝ)|^2095 ≤ (41727205782233/100000000000000 : ℝ)^1583
        have hw : |(2583185349/5000000000 : ℝ)|=(2583185349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1187_s2_1 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2685976137/5000000000 : ℝ)*x 0 + (-2304334833/10000000000 : ℝ)*x 1 + (516637453/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685976137/5000000000 : ℝ)^2095 ≤ (10984670558249/25000000000000 : ℝ)^1583 := by
    have hnat : (2685976137 : ℕ)^2095*25000000000000^1583 ≤ 10984670558249^1583*5000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685976137 5000000000 10984670558249 25000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2304334833/10000000000 : ℝ)^2095 ≤ (14334071009437/100000000000000 : ℝ)^1583 := by
    have hnat : (2304334833 : ℕ)^2095*100000000000000^1583 ≤ 14334071009437^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2304334833 10000000000 14334071009437 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (516637453/1000000000 : ℝ)^2095 ≤ (8345449348493/20000000000000 : ℝ)^1583 := by
    have hnat : (516637453 : ℕ)^2095*20000000000000^1583 ≤ 8345449348493^1583*1000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516637453 1000000000 8345449348493 20000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685976137/5000000000 : ℝ), (-2304334833/10000000000 : ℝ), (516637453/1000000000 : ℝ)] ![(10984670558249/25000000000000 : ℝ), (14334071009437/100000000000000 : ℝ), (8345449348493/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685976137/5000000000 : ℝ)|^2095 ≤ (10984670558249/25000000000000 : ℝ)^1583
        have hw : |(2685976137/5000000000 : ℝ)|=(2685976137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2304334833/10000000000 : ℝ)|^2095 ≤ (14334071009437/100000000000000 : ℝ)^1583
        have hw : |(-2304334833/10000000000 : ℝ)|=(2304334833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(516637453/1000000000 : ℝ)|^2095 ≤ (8345449348493/20000000000000 : ℝ)^1583
        have hw : |(516637453/1000000000 : ℝ)|=(516637453/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1187_s2_2 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5371953723/10000000000 : ℝ)*x 0 + (206654899/400000000 : ℝ)*x 1 + (-460867119/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5371953723/10000000000 : ℝ)^2095 ≤ (2746168619879/6250000000000 : ℝ)^1583 := by
    have hnat : (5371953723 : ℕ)^2095*6250000000000^1583 ≤ 2746168619879^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5371953723 10000000000 2746168619879 6250000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (206654899/400000000 : ℝ)^2095 ≤ (41727224776577/100000000000000 : ℝ)^1583 := by
    have hnat : (206654899 : ℕ)^2095*100000000000000^1583 ≤ 41727224776577^1583*400000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206654899 400000000 41727224776577 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (460867119/2000000000 : ℝ)^2095 ≤ (2866815456507/20000000000000 : ℝ)^1583 := by
    have hnat : (460867119 : ℕ)^2095*20000000000000^1583 ≤ 2866815456507^1583*2000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      460867119 2000000000 2866815456507 20000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5371953723/10000000000 : ℝ), (206654899/400000000 : ℝ), (-460867119/2000000000 : ℝ)] ![(2746168619879/6250000000000 : ℝ), (41727224776577/100000000000000 : ℝ), (2866815456507/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5371953723/10000000000 : ℝ)|^2095 ≤ (2746168619879/6250000000000 : ℝ)^1583
        have hw : |(5371953723/10000000000 : ℝ)|=(5371953723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(206654899/400000000 : ℝ)|^2095 ≤ (41727224776577/100000000000000 : ℝ)^1583
        have hw : |(206654899/400000000 : ℝ)|=(206654899/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-460867119/2000000000 : ℝ)|^2095 ≤ (2866815456507/20000000000000 : ℝ)^1583
        have hw : |(-460867119/2000000000 : ℝ)|=(460867119/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1187_s2_3 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2174299463/5000000000 : ℝ)*x 0 + (4024166683/10000000000 : ℝ)*x 1 + (4698686001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2174299463/5000000000 : ℝ)^2095 ≤ (16609185472551/50000000000000 : ℝ)^1583 := by
    have hnat : (2174299463 : ℕ)^2095*50000000000000^1583 ≤ 16609185472551^1583*5000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174299463 5000000000 16609185472551 50000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4024166683/10000000000 : ℝ)^2095 ≤ (29978764636399/100000000000000 : ℝ)^1583 := by
    have hnat : (4024166683 : ℕ)^2095*100000000000000^1583 ≤ 29978764636399^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4024166683 10000000000 29978764636399 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4698686001/10000000000 : ℝ)^2095 ≤ (36802864408909/100000000000000 : ℝ)^1583 := by
    have hnat : (4698686001 : ℕ)^2095*100000000000000^1583 ≤ 36802864408909^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4698686001 10000000000 36802864408909 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2174299463/5000000000 : ℝ), (4024166683/10000000000 : ℝ), (4698686001/10000000000 : ℝ)] ![(16609185472551/50000000000000 : ℝ), (29978764636399/100000000000000 : ℝ), (36802864408909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2174299463/5000000000 : ℝ)|^2095 ≤ (16609185472551/50000000000000 : ℝ)^1583
        have hw : |(2174299463/5000000000 : ℝ)|=(2174299463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4024166683/10000000000 : ℝ)|^2095 ≤ (29978764636399/100000000000000 : ℝ)^1583
        have hw : |(4024166683/10000000000 : ℝ)|=(4024166683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4698686001/10000000000 : ℝ)|^2095 ≤ (36802864408909/100000000000000 : ℝ)^1583
        have hw : |(4698686001/10000000000 : ℝ)|=(4698686001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1187_s2_4 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1064999179/5000000000 : ℝ)*x 0 + (2584308563/5000000000 : ℝ)*x 1 + (1375045107/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1064999179/5000000000 : ℝ)^2095 ≤ (12916730586167/100000000000000 : ℝ)^1583 := by
    have hnat : (1064999179 : ℕ)^2095*100000000000000^1583 ≤ 12916730586167^1583*5000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064999179 5000000000 12916730586167 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2584308563/5000000000 : ℝ)^2095 ≤ (41751219526969/100000000000000 : ℝ)^1583 := by
    have hnat : (2584308563 : ℕ)^2095*100000000000000^1583 ≤ 41751219526969^1583*5000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2584308563 5000000000 41751219526969 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1375045107/2500000000 : ℝ)^2095 ≤ (4533204987737/10000000000000 : ℝ)^1583 := by
    have hnat : (1375045107 : ℕ)^2095*10000000000000^1583 ≤ 4533204987737^1583*2500000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1375045107 2500000000 4533204987737 10000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1064999179/5000000000 : ℝ), (2584308563/5000000000 : ℝ), (1375045107/2500000000 : ℝ)] ![(12916730586167/100000000000000 : ℝ), (41751219526969/100000000000000 : ℝ), (4533204987737/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1064999179/5000000000 : ℝ)|^2095 ≤ (12916730586167/100000000000000 : ℝ)^1583
        have hw : |(-1064999179/5000000000 : ℝ)|=(1064999179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2584308563/5000000000 : ℝ)|^2095 ≤ (41751219526969/100000000000000 : ℝ)^1583
        have hw : |(2584308563/5000000000 : ℝ)|=(2584308563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1375045107/2500000000 : ℝ)|^2095 ≤ (4533204987737/10000000000000 : ℝ)^1583
        have hw : |(1375045107/2500000000 : ℝ)|=(1375045107/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1187_s2_5 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2643214227/5000000000 : ℝ)*x 0 + (-985263703/5000000000 : ℝ)*x 1 + (2750090219/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643214227/5000000000 : ℝ)^2095 ≤ (21507650072163/50000000000000 : ℝ)^1583 := by
    have hnat : (2643214227 : ℕ)^2095*50000000000000^1583 ≤ 21507650072163^1583*5000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643214227 5000000000 21507650072163 50000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (985263703/5000000000 : ℝ)^2095 ≤ (1456581230571/12500000000000 : ℝ)^1583 := by
    have hnat : (985263703 : ℕ)^2095*12500000000000^1583 ≤ 1456581230571^1583*5000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      985263703 5000000000 1456581230571 12500000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2750090219/5000000000 : ℝ)^2095 ≤ (22666024993223/50000000000000 : ℝ)^1583 := by
    have hnat : (2750090219 : ℕ)^2095*50000000000000^1583 ≤ 22666024993223^1583*5000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2750090219 5000000000 22666024993223 50000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643214227/5000000000 : ℝ), (-985263703/5000000000 : ℝ), (2750090219/5000000000 : ℝ)] ![(21507650072163/50000000000000 : ℝ), (1456581230571/12500000000000 : ℝ), (22666024993223/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643214227/5000000000 : ℝ)|^2095 ≤ (21507650072163/50000000000000 : ℝ)^1583
        have hw : |(2643214227/5000000000 : ℝ)|=(2643214227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-985263703/5000000000 : ℝ)|^2095 ≤ (1456581230571/12500000000000 : ℝ)^1583
        have hw : |(-985263703/5000000000 : ℝ)|=(985263703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2750090219/5000000000 : ℝ)|^2095 ≤ (22666024993223/50000000000000 : ℝ)^1583
        have hw : |(2750090219/5000000000 : ℝ)|=(2750090219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1187_s2_6 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1321607153/2500000000 : ℝ)*x 0 + (1100036089/2000000000 : ℝ)*x 1 + (-98526359/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321607153/2500000000 : ℝ)^2095 ≤ (21507650922891/50000000000000 : ℝ)^1583 := by
    have hnat : (1321607153 : ℕ)^2095*50000000000000^1583 ≤ 21507650922891^1583*2500000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321607153 2500000000 21507650922891 50000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1100036089/2000000000 : ℝ)^2095 ≤ (113330125157/250000000000 : ℝ)^1583 := by
    have hnat : (1100036089 : ℕ)^2095*250000000000^1583 ≤ 113330125157^1583*2000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100036089 2000000000 113330125157 250000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (98526359/500000000 : ℝ)^2095 ≤ (11652648075869/100000000000000 : ℝ)^1583 := by
    have hnat : (98526359 : ℕ)^2095*100000000000000^1583 ≤ 11652648075869^1583*500000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98526359 500000000 11652648075869 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321607153/2500000000 : ℝ), (1100036089/2000000000 : ℝ), (-98526359/500000000 : ℝ)] ![(21507650922891/50000000000000 : ℝ), (113330125157/250000000000 : ℝ), (11652648075869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321607153/2500000000 : ℝ)|^2095 ≤ (21507650922891/50000000000000 : ℝ)^1583
        have hw : |(1321607153/2500000000 : ℝ)|=(1321607153/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1100036089/2000000000 : ℝ)|^2095 ≤ (113330125157/250000000000 : ℝ)^1583
        have hw : |(1100036089/2000000000 : ℝ)|=(1100036089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-98526359/500000000 : ℝ)|^2095 ≤ (11652648075869/100000000000000 : ℝ)^1583
        have hw : |(-98526359/500000000 : ℝ)|=(98526359/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1187_s2_7 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4348781447/10000000000 : ℝ)*x 0 + (469417997/1000000000 : ℝ)*x 1 + (2014357797/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4348781447/10000000000 : ℝ)^2095 ≤ (1328808646557/4000000000000 : ℝ)^1583 := by
    have hnat : (4348781447 : ℕ)^2095*4000000000000^1583 ≤ 1328808646557^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4348781447 10000000000 1328808646557 4000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (469417997/1000000000 : ℝ)^2095 ≤ (35894689891/97656250000 : ℝ)^1583 := by
    have hnat : (469417997 : ℕ)^2095*97656250000^1583 ≤ 35894689891^1583*1000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      469417997 1000000000 35894689891 97656250000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2014357797/5000000000 : ℝ)^2095 ≤ (30023621374353/100000000000000 : ℝ)^1583 := by
    have hnat : (2014357797 : ℕ)^2095*100000000000000^1583 ≤ 30023621374353^1583*5000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2014357797 5000000000 30023621374353 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4348781447/10000000000 : ℝ), (469417997/1000000000 : ℝ), (2014357797/5000000000 : ℝ)] ![(1328808646557/4000000000000 : ℝ), (35894689891/97656250000 : ℝ), (30023621374353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4348781447/10000000000 : ℝ)|^2095 ≤ (1328808646557/4000000000000 : ℝ)^1583
        have hw : |(4348781447/10000000000 : ℝ)|=(4348781447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(469417997/1000000000 : ℝ)|^2095 ≤ (35894689891/97656250000 : ℝ)^1583
        have hw : |(469417997/1000000000 : ℝ)|=(469417997/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2014357797/5000000000 : ℝ)|^2095 ≤ (30023621374353/100000000000000 : ℝ)^1583
        have hw : |(2014357797/5000000000 : ℝ)|=(2014357797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1187_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150352467/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5059/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2949/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (9269/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4093/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5059/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2949/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5059/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2949/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5059/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2949/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5059/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2949/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5059/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2949/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5059/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2949/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2949/50000 : ℝ) ^ (8379/2048 : ℝ) ≤ (93448826914257/10000000000000000000 : ℝ) := by
    have hpowers : (2949/50000 : ℝ)^8379 ≤ (93448826914257/10000000000000000000 : ℝ)^2048 := by
      have hnat : (2949 : ℕ)^8379*10000000000000000000^2048 ≤ 93448826914257^2048*50000^8379 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2949 50000 93448826914257 10000000000000000000 8379 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2949/50000 : ℝ)) (X := (93448826914257/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8379 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (5059/25000 : ℝ) ^ (8379/2048 : ℝ) ≤ (144924530598786659/100000000000000000000 : ℝ) := by
    have hpowers : (5059/25000 : ℝ)^8379 ≤ (144924530598786659/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5059 : ℕ)^8379*100000000000000000000^2048 ≤ 144924530598786659^2048*25000^8379 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5059 25000 144924530598786659 100000000000000000000 8379 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5059/25000 : ℝ)) (X := (144924530598786659/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8379 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000093448826914257/5000000000000000000 : ℝ) ≤ (2500011420327379/2500000000000000 : ℝ) ^ (8379/2048 : ℝ) := by
    have hpowers : (5000093448826914257/5000000000000000000 : ℝ)^2048 ≤ (2500011420327379/2500000000000000 : ℝ)^8379 := by
      have hnat : (5000093448826914257 : ℕ)^2048*2500000000000000^8379 ≤ 2500011420327379^8379*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000093448826914257 5000000000000000000 2500011420327379 2500000000000000 2048 8379 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500011420327379/2500000000000000 : ℝ)) (X := (5000093448826914257/5000000000000000000 : ℝ)) (by norm_num) 8379 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100145859018867929229/100000000000000000000 : ℝ) ≤ (5001781565846907/5000000000000000 : ℝ) ^ (8379/2048 : ℝ) := by
    have hpowers : (100145859018867929229/100000000000000000000 : ℝ)^2048 ≤ (5001781565846907/5000000000000000 : ℝ)^8379 := by
      have hnat : (100145859018867929229 : ℕ)^2048*5000000000000000^8379 ≤ 5001781565846907^8379*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100145859018867929229 100000000000000000000 5001781565846907 5000000000000000 2048 8379 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001781565846907/5000000000000000 : ℝ)) (X := (100145859018867929229/100000000000000000000 : ℝ)) (by norm_num) 8379 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50144924530598786659/50000000000000000000 : ℝ) ≤ (312721268189941/312500000000000 : ℝ) ^ (8379/2048 : ℝ) := by
    have hpowers : (50144924530598786659/50000000000000000000 : ℝ)^2048 ≤ (312721268189941/312500000000000 : ℝ)^8379 := by
      have hnat : (50144924530598786659 : ℕ)^2048*312500000000000^8379 ≤ 312721268189941^8379*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50144924530598786659 50000000000000000000 312721268189941 312500000000000 2048 8379 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312721268189941/312500000000000 : ℝ)) (X := (50144924530598786659/50000000000000000000 : ℝ)) (by norm_num) 8379 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(93448826914257/10000000000000000000 : ℝ) ≤ ((358347907834706653/358450000000000000 : ℝ)+2*(1758725192149/716900000000000 : ℝ)*(2949/50000 : ℝ))^(8379/2048 : ℝ) := by
    rw [show (358347907834706653/358450000000000000 : ℝ)+2*(1758725192149/716900000000000 : ℝ)*(2949/50000 : ℝ)=(2500011420327379/2500000000000000 : ℝ) by norm_num, show 1+2*(93448826914257/10000000000000000000 : ℝ)=(5000093448826914257/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(144924530598786659/100000000000000000000 : ℝ)+(93448826914257/10000000000000000000 : ℝ) ≤ ((358347907834706653/358450000000000000 : ℝ)+(1758725192149/716900000000000 : ℝ)*((5059/25000 : ℝ)+(2949/50000 : ℝ)))^(8379/2048 : ℝ) := by
    rw [show (358347907834706653/358450000000000000 : ℝ)+(1758725192149/716900000000000 : ℝ)*((5059/25000 : ℝ)+(2949/50000 : ℝ))=(5001781565846907/5000000000000000 : ℝ) by norm_num, show 1+(144924530598786659/100000000000000000000 : ℝ)+(93448826914257/10000000000000000000 : ℝ)=(100145859018867929229/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(144924530598786659/100000000000000000000 : ℝ) ≤ ((358347907834706653/358450000000000000 : ℝ)+2*(1758725192149/716900000000000 : ℝ)*(5059/25000 : ℝ))^(8379/2048 : ℝ) := by
    rw [show (358347907834706653/358450000000000000 : ℝ)+2*(1758725192149/716900000000000 : ℝ)*(5059/25000 : ℝ)=(312721268189941/312500000000000 : ℝ) by norm_num, show 1+2*(144924530598786659/100000000000000000000 : ℝ)=(50144924530598786659/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (358347907834706653/358450000000000000 : ℝ)*(X 1 0+X 2 0)+(1758725192149/716900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8379/2048 : ℝ)) (lo := (2949/50000 : ℝ)) (hi := (5059/25000 : ℝ)) (c := (358347907834706653/358450000000000000 : ℝ)) (alpha := (1758725192149/716900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (358347907834706653/358450000000000000 : ℝ)*(X 0 1+X 2 1)+(1758725192149/716900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8379/2048 : ℝ)) (lo := (2949/50000 : ℝ)) (hi := (5059/25000 : ℝ)) (c := (358347907834706653/358450000000000000 : ℝ)) (alpha := (1758725192149/716900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (358347907834706653/358450000000000000 : ℝ)*(X 0 2+X 1 2)+(1758725192149/716900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8379/2048 : ℝ)) (lo := (2949/50000 : ℝ)) (hi := (5059/25000 : ℝ)) (c := (358347907834706653/358450000000000000 : ℝ)) (alpha := (1758725192149/716900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1064954229/5000000000 : ℝ)*X 0 0+(5502447971/10000000000 : ℝ)*X 0 1+(2583185349/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2685976137/5000000000 : ℝ)*X 1 0+(-2304334833/10000000000 : ℝ)*X 1 1+(516637453/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5371953723/10000000000 : ℝ)*X 2 0+(206654899/400000000 : ℝ)*X 2 1+(-460867119/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2174299463/5000000000 : ℝ)*X 0 0+(4024166683/10000000000 : ℝ)*X 0 1+(4698686001/10000000000 : ℝ)*X 0 2+(2174299463/5000000000 : ℝ)*X 1 0+(4024166683/10000000000 : ℝ)*X 1 1+(4698686001/10000000000 : ℝ)*X 1 2+(2174299463/5000000000 : ℝ)*X 2 0+(4024166683/10000000000 : ℝ)*X 2 1+(4698686001/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1064999179/5000000000 : ℝ)*X 0 0+(2584308563/5000000000 : ℝ)*X 0 1+(1375045107/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2643214227/5000000000 : ℝ)*X 1 0+(-985263703/5000000000 : ℝ)*X 1 1+(2750090219/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1321607153/2500000000 : ℝ)*X 2 0+(1100036089/2000000000 : ℝ)*X 2 1+(-98526359/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4348781447/10000000000 : ℝ)*X 0 0+(469417997/1000000000 : ℝ)*X 0 1+(2014357797/5000000000 : ℝ)*X 0 2+(4348781447/10000000000 : ℝ)*X 1 0+(469417997/1000000000 : ℝ)*X 1 1+(2014357797/5000000000 : ℝ)*X 1 2+(4348781447/10000000000 : ℝ)*X 2 0+(469417997/1000000000 : ℝ)*X 2 1+(2014357797/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (127862978840006773037476443/17922500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (898679671/100000000000000 : ℝ)*(base19) + (1435971797/100000000000000 : ℝ)*(base23) + (43200321/50000000000000 : ℝ)*(upper2) + (266949611/50000000000000 : ℝ)*(upper3) + (7154071/3125000000000 : ℝ)*(upper4) + (2229067553697511/100000000000000 : ℝ)*(major0) + (2229067553697511/100000000000000 : ℝ)*(major1) + (278633444212189/12500000000000 : ℝ)*(major2) + (743885587370107/25000000000000 : ℝ)*(sp0) + (1487786314050957/50000000000000 : ℝ)*(sp1) + (2975572090809789/100000000000000 : ℝ)*(sp2) + (185318248466409/12500000000000 : ℝ)*(sp3) + (31177301157/100000000000000 : ℝ)*(sp4) + (15355074969/100000000000000 : ℝ)*(sp7) + (741280671403121/50000000000000 : ℝ)*(f.failure) + (1487786763390793/50000000000000 : ℝ)*(f.sum) + (170514664427777/71690000000000000000000000000 : ℝ)*base65 + (51627546313664683/35845000000000000000000000000000 : ℝ)*base67 + (88802255649301709/8961250000000000000000000000000 : ℝ)*base69 + (276262484361789683/35845000000000000000000000000000 : ℝ)*base71 + (208463224023067/71690000000000000000000000000 : ℝ)*base73 + (85244670942901709/8961250000000000000000000000000 : ℝ)*base75 + (28506347381420183/35845000000000000000000000000000 : ℝ)*base77 + (231263479494634817/35845000000000000000000000000000 : ℝ)*base80 + (50795689711401/8961250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (43849507/5000000000000000000000 : ℝ)*base89 + (43849507/5000000000000000000000 : ℝ)*base91 + (6150493/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (72624940094358211262367/14001953125000000000000000000 : ℝ) := by norm_num
    linear_combination (329739317/25000000000000 : ℝ)*(base19) + (376139031/25000000000000 : ℝ)*(base23) + (10237087/50000000000000 : ℝ)*(upper2) + (169852707/100000000000000 : ℝ)*(upper3) + (6865383/6250000000000 : ℝ)*(upper5) + (112968134840491/5000000000000 : ℝ)*(major0) + (112968134840491/5000000000000 : ℝ)*(major1) + (112968134840491/5000000000000 : ℝ)*(major2) + (798874189/6250000000000 : ℝ)*(sp1) + (509005349/3125000000000 : ℝ)*(sp2) + (301601446253939/10000000000000 : ℝ)*(sp4) + (1508000180797549/50000000000000 : ℝ)*(sp5) + (3015996669812097/100000000000000 : ℝ)*(sp6) + (1502710758187839/100000000000000 : ℝ)*(sp7) + (1502710758187839/100000000000000 : ℝ)*(f.failure) + (301601446253939/10000000000000 : ℝ)*(f.sum) + (18694737209161/7169000000000000000000000000 : ℝ)*base66 + (11591202982666377/1792250000000000000000000000000 : ℝ)*base68 + (11686805748517377/1792250000000000000000000000000 : ℝ)*base70 + (20104849533451127/1792250000000000000000000000000 : ℝ)*base72 + (2594244577907/3584500000000000000000000000 : ℝ)*base74 + (22482123823106377/1792250000000000000000000000000 : ℝ)*base76 + (17118901459061127/1792250000000000000000000000000 : ℝ)*base78 + (3492281926227373/1792250000000000000000000000000 : ℝ)*base79 + (14739974823881/3584500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (43048813/10000000000000000000000 : ℝ)*base89 + (43048813/10000000000000000000000 : ℝ)*base91 + (43048813/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1187_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150352467/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5059/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2949/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9269/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4093/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1187_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1187_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150352467/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9269/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4093/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1187_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1187_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1187_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150352467/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9269/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4093/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1187_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
