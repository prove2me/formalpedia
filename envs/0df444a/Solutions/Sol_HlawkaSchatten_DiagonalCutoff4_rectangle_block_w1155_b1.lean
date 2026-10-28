-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1155_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:37:12.531986+00:00
-- url     : https://prove2.me/submissions/aebb92f6-c39a-4d46-9900-d83623572e05

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
theorem support_rectangle_w1155_s3_0 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1078511153/5000000000 : ℝ)*x 0 + (5427849549/10000000000 : ℝ)*x 1 + (2616647249/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078511153/5000000000 : ℝ)^2087 ≤ (818812646419/6250000000000 : ℝ)^1575 := by
    have hnat : (1078511153 : ℕ)^2087*6250000000000^1575 ≤ 818812646419^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078511153 5000000000 818812646419 6250000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5427849549/10000000000 : ℝ)^2087 ≤ (44500078320677/100000000000000 : ℝ)^1575 := by
    have hnat : (5427849549 : ℕ)^2087*100000000000000^1575 ≤ 44500078320677^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427849549 10000000000 44500078320677 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2616647249/5000000000 : ℝ)^2087 ≤ (1059972983043/2500000000000 : ℝ)^1575 := by
    have hnat : (2616647249 : ℕ)^2087*2500000000000^1575 ≤ 1059972983043^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2616647249 5000000000 1059972983043 2500000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1078511153/5000000000 : ℝ), (5427849549/10000000000 : ℝ), (2616647249/5000000000 : ℝ)] ![(818812646419/6250000000000 : ℝ), (44500078320677/100000000000000 : ℝ), (1059972983043/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1078511153/5000000000 : ℝ)|^2087 ≤ (818812646419/6250000000000 : ℝ)^1575
        have hw : |(-1078511153/5000000000 : ℝ)|=(1078511153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5427849549/10000000000 : ℝ)|^2087 ≤ (44500078320677/100000000000000 : ℝ)^1575
        have hw : |(5427849549/10000000000 : ℝ)|=(5427849549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2616647249/5000000000 : ℝ)|^2087 ≤ (1059972983043/2500000000000 : ℝ)^1575
        have hw : |(2616647249/5000000000 : ℝ)|=(2616647249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s3_1 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1070696603/2000000000 : ℝ)*x 0 + (-564111037/2500000000 : ℝ)*x 1 + (654161789/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070696603/2000000000 : ℝ)^2087 ≤ (43693992701657/100000000000000 : ℝ)^1575 := by
    have hnat : (1070696603 : ℕ)^2087*100000000000000^1575 ≤ 43693992701657^1575*2000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070696603 2000000000 43693992701657 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (564111037/2500000000 : ℝ)^2087 ≤ (6953544979151/50000000000000 : ℝ)^1575 := by
    have hnat : (564111037 : ℕ)^2087*50000000000000^1575 ≤ 6953544979151^1575*2500000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564111037 2500000000 6953544979151 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (654161789/1250000000 : ℝ)^2087 ≤ (42398917324921/100000000000000 : ℝ)^1575 := by
    have hnat : (654161789 : ℕ)^2087*100000000000000^1575 ≤ 42398917324921^1575*1250000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654161789 1250000000 42398917324921 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070696603/2000000000 : ℝ), (-564111037/2500000000 : ℝ), (654161789/1250000000 : ℝ)] ![(43693992701657/100000000000000 : ℝ), (6953544979151/50000000000000 : ℝ), (42398917324921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070696603/2000000000 : ℝ)|^2087 ≤ (43693992701657/100000000000000 : ℝ)^1575
        have hw : |(1070696603/2000000000 : ℝ)|=(1070696603/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-564111037/2500000000 : ℝ)|^2087 ≤ (6953544979151/50000000000000 : ℝ)^1575
        have hw : |(-564111037/2500000000 : ℝ)|=(564111037/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(654161789/1250000000 : ℝ)|^2087 ≤ (42398917324921/100000000000000 : ℝ)^1575
        have hw : |(654161789/1250000000 : ℝ)|=(654161789/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s3_2 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1070696619/2000000000 : ℝ)*x 0 + (1308323589/2500000000 : ℝ)*x 1 + (-141027749/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070696619/2000000000 : ℝ)^2087 ≤ (43693993566859/100000000000000 : ℝ)^1575 := by
    have hnat : (1070696619 : ℕ)^2087*100000000000000^1575 ≤ 43693993566859^1575*2000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070696619 2000000000 43693993566859 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1308323589/2500000000 : ℝ)^2087 ≤ (21199458898641/50000000000000 : ℝ)^1575 := by
    have hnat : (1308323589 : ℕ)^2087*50000000000000^1575 ≤ 21199458898641^1575*2500000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1308323589 2500000000 21199458898641 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (141027749/625000000 : ℝ)^2087 ≤ (6953544309471/50000000000000 : ℝ)^1575 := by
    have hnat : (141027749 : ℕ)^2087*50000000000000^1575 ≤ 6953544309471^1575*625000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141027749 625000000 6953544309471 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070696619/2000000000 : ℝ), (1308323589/2500000000 : ℝ), (-141027749/625000000 : ℝ)] ![(43693993566859/100000000000000 : ℝ), (21199458898641/50000000000000 : ℝ), (6953544309471/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070696619/2000000000 : ℝ)|^2087 ≤ (43693993566859/100000000000000 : ℝ)^1575
        have hw : |(1070696619/2000000000 : ℝ)|=(1070696619/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1308323589/2500000000 : ℝ)|^2087 ≤ (21199458898641/50000000000000 : ℝ)^1575
        have hw : |(1308323589/2500000000 : ℝ)|=(1308323589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-141027749/625000000 : ℝ)|^2087 ≤ (6953544309471/50000000000000 : ℝ)^1575
        have hw : |(-141027749/625000000 : ℝ)|=(141027749/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s3_3 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4360669379/10000000000 : ℝ)*x 0 + (4170921237/10000000000 : ℝ)*x 1 + (4558970591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360669379/10000000000 : ℝ)^2087 ≤ (6659004770899/20000000000000 : ℝ)^1575 := by
    have hnat : (4360669379 : ℕ)^2087*20000000000000^1575 ≤ 6659004770899^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360669379 10000000000 6659004770899 20000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4170921237/10000000000 : ℝ)^2087 ≤ (980905718709/3125000000000 : ℝ)^1575 := by
    have hnat : (4170921237 : ℕ)^2087*3125000000000^1575 ≤ 980905718709^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170921237 10000000000 980905718709 3125000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4558970591/10000000000 : ℝ)^2087 ≤ (17657996561037/50000000000000 : ℝ)^1575 := by
    have hnat : (4558970591 : ℕ)^2087*50000000000000^1575 ≤ 17657996561037^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4558970591 10000000000 17657996561037 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360669379/10000000000 : ℝ), (4170921237/10000000000 : ℝ), (4558970591/10000000000 : ℝ)] ![(6659004770899/20000000000000 : ℝ), (980905718709/3125000000000 : ℝ), (17657996561037/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360669379/10000000000 : ℝ)|^2087 ≤ (6659004770899/20000000000000 : ℝ)^1575
        have hw : |(4360669379/10000000000 : ℝ)|=(4360669379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4170921237/10000000000 : ℝ)|^2087 ≤ (980905718709/3125000000000 : ℝ)^1575
        have hw : |(4170921237/10000000000 : ℝ)|=(4170921237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4558970591/10000000000 : ℝ)|^2087 ≤ (17657996561037/50000000000000 : ℝ)^1575
        have hw : |(4558970591/10000000000 : ℝ)|=(4558970591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s3_4 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2157039773/10000000000 : ℝ)*x 0 + (5234042719/10000000000 : ℝ)*x 1 + (271354859/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2157039773/10000000000 : ℝ)^2087 ≤ (6550571459269/50000000000000 : ℝ)^1575 := by
    have hnat : (2157039773 : ℕ)^2087*50000000000000^1575 ≤ 6550571459269^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157039773 10000000000 6550571459269 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5234042719/10000000000 : ℝ)^2087 ≤ (4240695202063/10000000000000 : ℝ)^1575 := by
    have hnat : (5234042719 : ℕ)^2087*10000000000000^1575 ≤ 4240695202063^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234042719 10000000000 4240695202063 10000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271354859/500000000 : ℝ)^2087 ≤ (22245952524143/50000000000000 : ℝ)^1575 := by
    have hnat : (271354859 : ℕ)^2087*50000000000000^1575 ≤ 22245952524143^1575*500000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271354859 500000000 22245952524143 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2157039773/10000000000 : ℝ), (5234042719/10000000000 : ℝ), (271354859/500000000 : ℝ)] ![(6550571459269/50000000000000 : ℝ), (4240695202063/10000000000000 : ℝ), (22245952524143/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2157039773/10000000000 : ℝ)|^2087 ≤ (6550571459269/50000000000000 : ℝ)^1575
        have hw : |(-2157039773/10000000000 : ℝ)|=(2157039773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5234042719/10000000000 : ℝ)|^2087 ≤ (4240695202063/10000000000000 : ℝ)^1575
        have hw : |(5234042719/10000000000 : ℝ)|=(5234042719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(271354859/500000000 : ℝ)|^2087 ≤ (22245952524143/50000000000000 : ℝ)^1575
        have hw : |(271354859/500000000 : ℝ)|=(271354859/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s3_5 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5304146763/10000000000 : ℝ)*x 0 + (-2062641237/10000000000 : ℝ)*x 1 + (5427097231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304146763/10000000000 : ℝ)^2087 ≤ (43161221226517/100000000000000 : ℝ)^1575 := by
    have hnat : (5304146763 : ℕ)^2087*100000000000000^1575 ≤ 43161221226517^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304146763 10000000000 43161221226517 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2062641237/10000000000 : ℝ)^2087 ≤ (12346873154847/100000000000000 : ℝ)^1575 := by
    have hnat : (2062641237 : ℕ)^2087*100000000000000^1575 ≤ 12346873154847^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2062641237 10000000000 12346873154847 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5427097231/10000000000 : ℝ)^2087 ≤ (22245952801153/50000000000000 : ℝ)^1575 := by
    have hnat : (5427097231 : ℕ)^2087*50000000000000^1575 ≤ 22245952801153^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427097231 10000000000 22245952801153 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304146763/10000000000 : ℝ), (-2062641237/10000000000 : ℝ), (5427097231/10000000000 : ℝ)] ![(43161221226517/100000000000000 : ℝ), (12346873154847/100000000000000 : ℝ), (22245952801153/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304146763/10000000000 : ℝ)|^2087 ≤ (43161221226517/100000000000000 : ℝ)^1575
        have hw : |(5304146763/10000000000 : ℝ)|=(5304146763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2062641237/10000000000 : ℝ)|^2087 ≤ (12346873154847/100000000000000 : ℝ)^1575
        have hw : |(-2062641237/10000000000 : ℝ)|=(2062641237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5427097231/10000000000 : ℝ)|^2087 ≤ (22245952801153/50000000000000 : ℝ)^1575
        have hw : |(5427097231/10000000000 : ℝ)|=(5427097231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s3_6 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (66301833/125000000 : ℝ)*x 0 + (2713548721/5000000000 : ℝ)*x 1 + (-515660279/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66301833/125000000 : ℝ)^2087 ≤ (10790304975067/25000000000000 : ℝ)^1575 := by
    have hnat : (66301833 : ℕ)^2087*25000000000000^1575 ≤ 10790304975067^1575*125000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66301833 125000000 10790304975067 25000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2713548721/5000000000 : ℝ)^2087 ≤ (11122976973607/25000000000000 : ℝ)^1575 := by
    have hnat : (2713548721 : ℕ)^2087*25000000000000^1575 ≤ 11122976973607^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713548721 5000000000 11122976973607 25000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (515660279/2500000000 : ℝ)^2087 ≤ (3086718048773/25000000000000 : ℝ)^1575 := by
    have hnat : (515660279 : ℕ)^2087*25000000000000^1575 ≤ 3086718048773^1575*2500000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515660279 2500000000 3086718048773 25000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66301833/125000000 : ℝ), (2713548721/5000000000 : ℝ), (-515660279/2500000000 : ℝ)] ![(10790304975067/25000000000000 : ℝ), (11122976973607/25000000000000 : ℝ), (3086718048773/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66301833/125000000 : ℝ)|^2087 ≤ (10790304975067/25000000000000 : ℝ)^1575
        have hw : |(66301833/125000000 : ℝ)|=(66301833/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2713548721/5000000000 : ℝ)|^2087 ≤ (11122976973607/25000000000000 : ℝ)^1575
        have hw : |(2713548721/5000000000 : ℝ)|=(2713548721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-515660279/2500000000 : ℝ)|^2087 ≤ (3086718048773/25000000000000 : ℝ)^1575
        have hw : |(-515660279/2500000000 : ℝ)|=(515660279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s3_7 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4360704233/10000000000 : ℝ)*x 0 + (4557478311/10000000000 : ℝ)*x 1 + (1043105443/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360704233/10000000000 : ℝ)^2087 ≤ (6659075297223/20000000000000 : ℝ)^1575 := by
    have hnat : (4360704233 : ℕ)^2087*20000000000000^1575 ≤ 6659075297223^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360704233 10000000000 6659075297223 20000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4557478311/10000000000 : ℝ)^2087 ≤ (8825169030329/25000000000000 : ℝ)^1575 := by
    have hnat : (4557478311 : ℕ)^2087*25000000000000^1575 ≤ 8825169030329^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4557478311 10000000000 8825169030329 25000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043105443/2500000000 : ℝ)^2087 ≤ (1256157895067/4000000000000 : ℝ)^1575 := by
    have hnat : (1043105443 : ℕ)^2087*4000000000000^1575 ≤ 1256157895067^1575*2500000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043105443 2500000000 1256157895067 4000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360704233/10000000000 : ℝ), (4557478311/10000000000 : ℝ), (1043105443/2500000000 : ℝ)] ![(6659075297223/20000000000000 : ℝ), (8825169030329/25000000000000 : ℝ), (1256157895067/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360704233/10000000000 : ℝ)|^2087 ≤ (6659075297223/20000000000000 : ℝ)^1575
        have hw : |(4360704233/10000000000 : ℝ)|=(4360704233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4557478311/10000000000 : ℝ)|^2087 ≤ (8825169030329/25000000000000 : ℝ)^1575
        have hw : |(4557478311/10000000000 : ℝ)|=(4557478311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043105443/2500000000 : ℝ)|^2087 ≤ (1256157895067/4000000000000 : ℝ)^1575
        have hw : |(1043105443/2500000000 : ℝ)|=(1043105443/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1155_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149727417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1029/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9129/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10673/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1479/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1029/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9129/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1029/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9129/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1029/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9129/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1029/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9129/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1029/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9129/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1029/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9129/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9129/100000 : ℝ) ^ (8347/2048 : ℝ) ≤ (724309086778971/12500000000000000000 : ℝ) := by
    have hpowers : (9129/100000 : ℝ)^8347 ≤ (724309086778971/12500000000000000000 : ℝ)^2048 := by
      have hnat : (9129 : ℕ)^8347*12500000000000000000^2048 ≤ 724309086778971^2048*100000^8347 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9129 100000 724309086778971 12500000000000000000 8347 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9129/100000 : ℝ)) (X := (724309086778971/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8347 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1029/6250 : ℝ) ^ (8347/2048 : ℝ) ≤ (8012278248418587/12500000000000000000 : ℝ) := by
    have hpowers : (1029/6250 : ℝ)^8347 ≤ (8012278248418587/12500000000000000000 : ℝ)^2048 := by
      have hnat : (1029 : ℕ)^8347*12500000000000000000^2048 ≤ 8012278248418587^2048*6250^8347 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1029 6250 8012278248418587 12500000000000000000 8347 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1029/6250 : ℝ)) (X := (8012278248418587/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8347 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250724309086778971/6250000000000000000 : ℝ) ≤ (10000284331165561/10000000000000000 : ℝ) ^ (8347/2048 : ℝ) := by
    have hpowers : (6250724309086778971/6250000000000000000 : ℝ)^2048 ≤ (10000284331165561/10000000000000000 : ℝ)^8347 := by
      have hnat : (6250724309086778971 : ℕ)^2048*10000000000000000^8347 ≤ 10000284331165561^8347*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250724309086778971 6250000000000000000 10000284331165561 10000000000000000 2048 8347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000284331165561/10000000000000000 : ℝ)) (X := (6250724309086778971/6250000000000000000 : ℝ)) (by norm_num) 8347 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (6254368293667598779/6250000000000000000 : ℝ) ≤ (10001714418514233/10000000000000000 : ℝ) ^ (8347/2048 : ℝ) := by
    have hpowers : (6254368293667598779/6250000000000000000 : ℝ)^2048 ≤ (10001714418514233/10000000000000000 : ℝ)^8347 := by
      have hnat : (6254368293667598779 : ℕ)^2048*10000000000000000^8347 ≤ 10001714418514233^8347*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254368293667598779 6250000000000000000 10001714418514233 10000000000000000 2048 8347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001714418514233/10000000000000000 : ℝ)) (X := (6254368293667598779/6250000000000000000 : ℝ)) (by norm_num) 8347 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6258012278248418587/6250000000000000000 : ℝ) ≤ (2000628901172581/2000000000000000 : ℝ) ^ (8347/2048 : ℝ) := by
    have hpowers : (6258012278248418587/6250000000000000000 : ℝ)^2048 ≤ (2000628901172581/2000000000000000 : ℝ)^8347 := by
      have hnat : (6258012278248418587 : ℕ)^2048*2000000000000000^8347 ≤ 2000628901172581^8347*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6258012278248418587 6250000000000000000 2000628901172581 2000000000000000 2048 8347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000628901172581/2000000000000000 : ℝ)) (X := (6258012278248418587/6250000000000000000 : ℝ)) (by norm_num) 8347 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(724309086778971/12500000000000000000 : ℝ) ≤ ((24441991678095778853/24450000000000000000 : ℝ)+2*(22345114823/11460937500000 : ℝ)*(9129/100000 : ℝ))^(8347/2048 : ℝ) := by
    rw [show (24441991678095778853/24450000000000000000 : ℝ)+2*(22345114823/11460937500000 : ℝ)*(9129/100000 : ℝ)=(10000284331165561/10000000000000000 : ℝ) by norm_num, show 1+2*(724309086778971/12500000000000000000 : ℝ)=(6250724309086778971/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8012278248418587/12500000000000000000 : ℝ)+(724309086778971/12500000000000000000 : ℝ) ≤ ((24441991678095778853/24450000000000000000 : ℝ)+(22345114823/11460937500000 : ℝ)*((1029/6250 : ℝ)+(9129/100000 : ℝ)))^(8347/2048 : ℝ) := by
    rw [show (24441991678095778853/24450000000000000000 : ℝ)+(22345114823/11460937500000 : ℝ)*((1029/6250 : ℝ)+(9129/100000 : ℝ))=(10001714418514233/10000000000000000 : ℝ) by norm_num, show 1+(8012278248418587/12500000000000000000 : ℝ)+(724309086778971/12500000000000000000 : ℝ)=(6254368293667598779/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8012278248418587/12500000000000000000 : ℝ) ≤ ((24441991678095778853/24450000000000000000 : ℝ)+2*(22345114823/11460937500000 : ℝ)*(1029/6250 : ℝ))^(8347/2048 : ℝ) := by
    rw [show (24441991678095778853/24450000000000000000 : ℝ)+2*(22345114823/11460937500000 : ℝ)*(1029/6250 : ℝ)=(2000628901172581/2000000000000000 : ℝ) by norm_num, show 1+2*(8012278248418587/12500000000000000000 : ℝ)=(6258012278248418587/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (24441991678095778853/24450000000000000000 : ℝ)*(X 1 0+X 2 0)+(22345114823/11460937500000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8347/2048 : ℝ)) (lo := (9129/100000 : ℝ)) (hi := (1029/6250 : ℝ)) (c := (24441991678095778853/24450000000000000000 : ℝ)) (alpha := (22345114823/11460937500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (24441991678095778853/24450000000000000000 : ℝ)*(X 0 1+X 2 1)+(22345114823/11460937500000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8347/2048 : ℝ)) (lo := (9129/100000 : ℝ)) (hi := (1029/6250 : ℝ)) (c := (24441991678095778853/24450000000000000000 : ℝ)) (alpha := (22345114823/11460937500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (24441991678095778853/24450000000000000000 : ℝ)*(X 0 2+X 1 2)+(22345114823/11460937500000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8347/2048 : ℝ)) (lo := (9129/100000 : ℝ)) (hi := (1029/6250 : ℝ)) (c := (24441991678095778853/24450000000000000000 : ℝ)) (alpha := (22345114823/11460937500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1078511153/5000000000 : ℝ)*X 0 0+(5427849549/10000000000 : ℝ)*X 0 1+(2616647249/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070696603/2000000000 : ℝ)*X 1 0+(-564111037/2500000000 : ℝ)*X 1 1+(654161789/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070696619/2000000000 : ℝ)*X 2 0+(1308323589/2500000000 : ℝ)*X 2 1+(-141027749/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4360669379/10000000000 : ℝ)*X 0 0+(4170921237/10000000000 : ℝ)*X 0 1+(4558970591/10000000000 : ℝ)*X 0 2+(4360669379/10000000000 : ℝ)*X 1 0+(4170921237/10000000000 : ℝ)*X 1 1+(4558970591/10000000000 : ℝ)*X 1 2+(4360669379/10000000000 : ℝ)*X 2 0+(4170921237/10000000000 : ℝ)*X 2 1+(4558970591/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2157039773/10000000000 : ℝ)*X 0 0+(5234042719/10000000000 : ℝ)*X 0 1+(271354859/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5304146763/10000000000 : ℝ)*X 1 0+(-2062641237/10000000000 : ℝ)*X 1 1+(5427097231/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((66301833/125000000 : ℝ)*X 2 0+(2713548721/5000000000 : ℝ)*X 2 1+(-515660279/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4360704233/10000000000 : ℝ)*X 0 0+(4557478311/10000000000 : ℝ)*X 0 1+(1043105443/2500000000 : ℝ)*X 0 2+(4360704233/10000000000 : ℝ)*X 1 0+(4557478311/10000000000 : ℝ)*X 1 1+(1043105443/2500000000 : ℝ)*X 1 2+(4360704233/10000000000 : ℝ)*X 2 0+(4557478311/10000000000 : ℝ)*X 2 1+(1043105443/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (802898368382143765254275611/101875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1902432621/100000000000000 : ℝ)*(base19) + (113211837/6250000000000 : ℝ)*(base23) + (44929901/50000000000000 : ℝ)*(lower2) + (146814983/100000000000000 : ℝ)*(upper3) + (208075023/100000000000000 : ℝ)*(upper5) + (964627639013113/25000000000000 : ℝ)*(major0) + (964627639013113/25000000000000 : ℝ)*(major1) + (964627639013113/25000000000000 : ℝ)*(major2) + (256998158860153/5000000000000 : ℝ)*(sp0) + (5139995557820383/100000000000000 : ℝ)*(sp1) + (5139995648863611/100000000000000 : ℝ)*(sp2) + (2577007496981059/100000000000000 : ℝ)*(sp3) + (34283049943/100000000000000 : ℝ)*(sp4) + (15892163797/100000000000000 : ℝ)*(sp7) + (322127923643107/12500000000000 : ℝ)*(f.failure) + (1284999365063251/25000000000000 : ℝ)*(f.sum) + (125363664314281/36675000000000000000000000000 : ℝ)*base66 + (7005149676552648167/1833750000000000000000000000000000 : ℝ)*base67 + (25882217840150148167/1833750000000000000000000000000000 : ℝ)*base69 + (29053154781552648167/1833750000000000000000000000000000 : ℝ)*base71 + (82441999472153/18337500000000000000000000000 : ℝ)*base74 + (5457187406214851833/1833750000000000000000000000000000 : ℝ)*base76 + (16880976622677648167/1833750000000000000000000000000000 : ℝ)*base77 + (7087484158513601833/1833750000000000000000000000000000 : ℝ)*base80 + (4581282497669/36675000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (9035381/1250000000000000000000 : ℝ)*base90 + (9035381/1250000000000000000000 : ℝ)*base92 + (9035381/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (67654004533646307602797383/20375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (362726141/50000000000000 : ℝ)*(base19) + (771267127/100000000000000 : ℝ)*(base23) + (23220121/25000000000000 : ℝ)*(upper3) + (61283571/100000000000000 : ℝ)*(lower4) + (2407979/3125000000000 : ℝ)*(upper5) + (388845211835011/10000000000000 : ℝ)*(major0) + (388845211835011/10000000000000 : ℝ)*(major1) + (388845211835011/10000000000000 : ℝ)*(major2) + (855505677/6250000000000 : ℝ)*(sp1) + (19105904859/100000000000000 : ℝ)*(sp2) + (5179883355701171/100000000000000 : ℝ)*(sp4) + (2589934471079029/50000000000000 : ℝ)*(sp5) + (1035972695705837/20000000000000 : ℝ)*(sp6) + (649255192579411/25000000000000 : ℝ)*(sp7) + (649255192579411/25000000000000 : ℝ)*(f.failure) + (5179883355701171/100000000000000 : ℝ)*(f.sum) + (27062765983331/7335000000000000000000000000 : ℝ)*base66 + (2020127806270167149/733500000000000000000000000000000 : ℝ)*base67 + (708125234682332851/733500000000000000000000000000000 : ℝ)*base70 + (3807037187355332851/733500000000000000000000000000000 : ℝ)*base72 + (12311958206057/3667500000000000000000000000 : ℝ)*base73 + (5787089897349332851/733500000000000000000000000000000 : ℝ)*base76 + (5002834563133832851/733500000000000000000000000000000 : ℝ)*base78 + (9349999918167332851/733500000000000000000000000000000 : ℝ)*base80 + (10858151291159/1833750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (26411387/2500000000000000000000 : ℝ)*base89 + (26411387/2500000000000000000000 : ℝ)*base91 + (26411387/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1155_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149727417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1029/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9129/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10673/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1479/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1155_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1155_s4_0 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-539981003/2500000000 : ℝ)*x 0 + (2700637217/5000000000 : ℝ)*x 1 + (2628985359/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539981003/2500000000 : ℝ)^2087 ≤ (820272536391/6250000000000 : ℝ)^1575 := by
    have hnat : (539981003 : ℕ)^2087*6250000000000^1575 ≤ 820272536391^1575*2500000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539981003 2500000000 820272536391 6250000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2700637217/5000000000 : ℝ)^2087 ≤ (11052901543821/25000000000000 : ℝ)^1575 := by
    have hnat : (2700637217 : ℕ)^2087*25000000000000^1575 ≤ 11052901543821^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700637217 5000000000 11052901543821 25000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2628985359/5000000000 : ℝ)^2087 ≤ (42664033226413/100000000000000 : ℝ)^1575 := by
    have hnat : (2628985359 : ℕ)^2087*100000000000000^1575 ≤ 42664033226413^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628985359 5000000000 42664033226413 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-539981003/2500000000 : ℝ), (2700637217/5000000000 : ℝ), (2628985359/5000000000 : ℝ)] ![(820272536391/6250000000000 : ℝ), (11052901543821/25000000000000 : ℝ), (42664033226413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-539981003/2500000000 : ℝ)|^2087 ≤ (820272536391/6250000000000 : ℝ)^1575
        have hw : |(-539981003/2500000000 : ℝ)|=(539981003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2700637217/5000000000 : ℝ)|^2087 ≤ (11052901543821/25000000000000 : ℝ)^1575
        have hw : |(2700637217/5000000000 : ℝ)|=(2700637217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2628985359/5000000000 : ℝ)|^2087 ≤ (42664033226413/100000000000000 : ℝ)^1575
        have hw : |(2628985359/5000000000 : ℝ)|=(2628985359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s4_1 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2673418667/5000000000 : ℝ)*x 0 + (-2232740047/10000000000 : ℝ)*x 1 + (2628985303/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673418667/5000000000 : ℝ)^2087 ≤ (21811067028441/50000000000000 : ℝ)^1575 := by
    have hnat : (2673418667 : ℕ)^2087*50000000000000^1575 ≤ 21811067028441^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673418667 5000000000 21811067028441 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2232740047/10000000000 : ℝ)^2087 ≤ (13713833905621/100000000000000 : ℝ)^1575 := by
    have hnat : (2232740047 : ℕ)^2087*100000000000000^1575 ≤ 13713833905621^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2232740047 10000000000 13713833905621 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2628985303/5000000000 : ℝ)^2087 ≤ (42664032022199/100000000000000 : ℝ)^1575 := by
    have hnat : (2628985303 : ℕ)^2087*100000000000000^1575 ≤ 42664032022199^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628985303 5000000000 42664032022199 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673418667/5000000000 : ℝ), (-2232740047/10000000000 : ℝ), (2628985303/5000000000 : ℝ)] ![(21811067028441/50000000000000 : ℝ), (13713833905621/100000000000000 : ℝ), (42664032022199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673418667/5000000000 : ℝ)|^2087 ≤ (21811067028441/50000000000000 : ℝ)^1575
        have hw : |(2673418667/5000000000 : ℝ)|=(2673418667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2232740047/10000000000 : ℝ)|^2087 ≤ (13713833905621/100000000000000 : ℝ)^1575
        have hw : |(-2232740047/10000000000 : ℝ)|=(2232740047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2628985303/5000000000 : ℝ)|^2087 ≤ (42664032022199/100000000000000 : ℝ)^1575
        have hw : |(2628985303/5000000000 : ℝ)|=(2628985303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s4_2 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2673418727/5000000000 : ℝ)*x 0 + (1314492661/2500000000 : ℝ)*x 1 + (-2232739837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673418727/5000000000 : ℝ)^2087 ≤ (545276691927/1250000000000 : ℝ)^1575 := by
    have hnat : (2673418727 : ℕ)^2087*1250000000000^1575 ≤ 545276691927^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673418727 5000000000 545276691927 1250000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1314492661/2500000000 : ℝ)^2087 ≤ (42664032430771/100000000000000 : ℝ)^1575 := by
    have hnat : (1314492661 : ℕ)^2087*100000000000000^1575 ≤ 42664032430771^1575*2500000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314492661 2500000000 42664032430771 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2232739837/10000000000 : ℝ)^2087 ≤ (857114512279/6250000000000 : ℝ)^1575 := by
    have hnat : (2232739837 : ℕ)^2087*6250000000000^1575 ≤ 857114512279^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2232739837 10000000000 857114512279 6250000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673418727/5000000000 : ℝ), (1314492661/2500000000 : ℝ), (-2232739837/10000000000 : ℝ)] ![(545276691927/1250000000000 : ℝ), (42664032430771/100000000000000 : ℝ), (857114512279/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673418727/5000000000 : ℝ)|^2087 ≤ (545276691927/1250000000000 : ℝ)^1575
        have hw : |(2673418727/5000000000 : ℝ)|=(2673418727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1314492661/2500000000 : ℝ)|^2087 ≤ (42664032430771/100000000000000 : ℝ)^1575
        have hw : |(1314492661/2500000000 : ℝ)|=(1314492661/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2232739837/10000000000 : ℝ)|^2087 ≤ (857114512279/6250000000000 : ℝ)^1575
        have hw : |(-2232739837/10000000000 : ℝ)|=(2232739837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s4_3 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4362400457/10000000000 : ℝ)*x 0 + (2110904541/5000000000 : ℝ)*x 1 + (450763499/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362400457/10000000000 : ℝ)^2087 ≤ (33312538958369/100000000000000 : ℝ)^1575 := by
    have hnat : (4362400457 : ℕ)^2087*100000000000000^1575 ≤ 33312538958369^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362400457 10000000000 33312538958369 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2110904541/5000000000 : ℝ)^2087 ≤ (7974361468711/25000000000000 : ℝ)^1575 := by
    have hnat : (2110904541 : ℕ)^2087*25000000000000^1575 ≤ 7974361468711^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110904541 5000000000 7974361468711 25000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (450763499/1000000000 : ℝ)^2087 ≤ (1739500757857/5000000000000 : ℝ)^1575 := by
    have hnat : (450763499 : ℕ)^2087*5000000000000^1575 ≤ 1739500757857^1575*1000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450763499 1000000000 1739500757857 5000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362400457/10000000000 : ℝ), (2110904541/5000000000 : ℝ), (450763499/1000000000 : ℝ)] ![(33312538958369/100000000000000 : ℝ), (7974361468711/25000000000000 : ℝ), (1739500757857/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362400457/10000000000 : ℝ)|^2087 ≤ (33312538958369/100000000000000 : ℝ)^1575
        have hw : |(4362400457/10000000000 : ℝ)|=(4362400457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2110904541/5000000000 : ℝ)|^2087 ≤ (7974361468711/25000000000000 : ℝ)^1575
        have hw : |(2110904541/5000000000 : ℝ)|=(2110904541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(450763499/1000000000 : ℝ)|^2087 ≤ (1739500757857/5000000000000 : ℝ)^1575
        have hw : |(450763499/1000000000 : ℝ)|=(450763499/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s4_4 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2159931249/10000000000 : ℝ)*x 0 + (2629188619/5000000000 : ℝ)*x 1 + (5400866069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2159931249/10000000000 : ℝ)^2087 ≤ (6562209425817/50000000000000 : ℝ)^1575 := by
    have hnat : (2159931249 : ℕ)^2087*50000000000000^1575 ≤ 6562209425817^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159931249 10000000000 6562209425817 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2629188619/5000000000 : ℝ)^2087 ≤ (10667101036989/25000000000000 : ℝ)^1575 := by
    have hnat : (2629188619 : ℕ)^2087*25000000000000^1575 ≤ 10667101036989^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629188619 5000000000 10667101036989 25000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5400866069/10000000000 : ℝ)^2087 ≤ (44207176977079/100000000000000 : ℝ)^1575 := by
    have hnat : (5400866069 : ℕ)^2087*100000000000000^1575 ≤ 44207176977079^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400866069 10000000000 44207176977079 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2159931249/10000000000 : ℝ), (2629188619/5000000000 : ℝ), (5400866069/10000000000 : ℝ)] ![(6562209425817/50000000000000 : ℝ), (10667101036989/25000000000000 : ℝ), (44207176977079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2159931249/10000000000 : ℝ)|^2087 ≤ (6562209425817/50000000000000 : ℝ)^1575
        have hw : |(-2159931249/10000000000 : ℝ)|=(2159931249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2629188619/5000000000 : ℝ)|^2087 ≤ (10667101036989/25000000000000 : ℝ)^1575
        have hw : |(2629188619/5000000000 : ℝ)|=(2629188619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5400866069/10000000000 : ℝ)|^2087 ≤ (44207176977079/100000000000000 : ℝ)^1575
        have hw : |(5400866069/10000000000 : ℝ)|=(5400866069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s4_5 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5310498123/10000000000 : ℝ)*x 0 + (-2089844351/10000000000 : ℝ)*x 1 + (5400865989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310498123/10000000000 : ℝ)^2087 ≤ (10807429547073/25000000000000 : ℝ)^1575 := by
    have hnat : (5310498123 : ℕ)^2087*25000000000000^1575 ≤ 10807429547073^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310498123 10000000000 10807429547073 25000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2089844351/10000000000 : ℝ)^2087 ≤ (12563105690713/100000000000000 : ℝ)^1575 := by
    have hnat : (2089844351 : ℕ)^2087*100000000000000^1575 ≤ 12563105690713^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2089844351 10000000000 12563105690713 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5400865989/10000000000 : ℝ)^2087 ≤ (8841435221879/20000000000000 : ℝ)^1575 := by
    have hnat : (5400865989 : ℕ)^2087*20000000000000^1575 ≤ 8841435221879^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400865989 10000000000 8841435221879 20000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310498123/10000000000 : ℝ), (-2089844351/10000000000 : ℝ), (5400865989/10000000000 : ℝ)] ![(10807429547073/25000000000000 : ℝ), (12563105690713/100000000000000 : ℝ), (8841435221879/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310498123/10000000000 : ℝ)|^2087 ≤ (10807429547073/25000000000000 : ℝ)^1575
        have hw : |(5310498123/10000000000 : ℝ)|=(5310498123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2089844351/10000000000 : ℝ)|^2087 ≤ (12563105690713/100000000000000 : ℝ)^1575
        have hw : |(-2089844351/10000000000 : ℝ)|=(2089844351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5400865989/10000000000 : ℝ)|^2087 ≤ (8841435221879/20000000000000 : ℝ)^1575
        have hw : |(5400865989/10000000000 : ℝ)|=(5400865989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s4_6 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5310497977/10000000000 : ℝ)*x 0 + (2700433003/5000000000 : ℝ)*x 1 + (-1044922263/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310497977/10000000000 : ℝ)^2087 ≤ (5403714576679/12500000000000 : ℝ)^1575 := by
    have hnat : (5310497977 : ℕ)^2087*12500000000000^1575 ≤ 5403714576679^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310497977 10000000000 5403714576679 12500000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2700433003/5000000000 : ℝ)^2087 ≤ (22103588146889/50000000000000 : ℝ)^1575 := by
    have hnat : (2700433003 : ℕ)^2087*50000000000000^1575 ≤ 22103588146889^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700433003 5000000000 22103588146889 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1044922263/5000000000 : ℝ)^2087 ≤ (6281553542357/50000000000000 : ℝ)^1575 := by
    have hnat : (1044922263 : ℕ)^2087*50000000000000^1575 ≤ 6281553542357^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044922263 5000000000 6281553542357 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310497977/10000000000 : ℝ), (2700433003/5000000000 : ℝ), (-1044922263/5000000000 : ℝ)] ![(5403714576679/12500000000000 : ℝ), (22103588146889/50000000000000 : ℝ), (6281553542357/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310497977/10000000000 : ℝ)|^2087 ≤ (5403714576679/12500000000000 : ℝ)^1575
        have hw : |(5310497977/10000000000 : ℝ)|=(5310497977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2700433003/5000000000 : ℝ)|^2087 ≤ (22103588146889/50000000000000 : ℝ)^1575
        have hw : |(2700433003/5000000000 : ℝ)|=(2700433003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1044922263/5000000000 : ℝ)|^2087 ≤ (6281553542357/50000000000000 : ℝ)^1575
        have hw : |(-1044922263/5000000000 : ℝ)|=(1044922263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s4_7 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2181207151/5000000000 : ℝ)*x 0 + (563352989/1250000000 : ℝ)*x 1 + (2111311787/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2181207151/5000000000 : ℝ)^2087 ≤ (33312679051641/100000000000000 : ℝ)^1575 := by
    have hnat : (2181207151 : ℕ)^2087*100000000000000^1575 ≤ 33312679051641^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181207151 5000000000 33312679051641 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (563352989/1250000000 : ℝ)^2087 ≤ (34781720514369/100000000000000 : ℝ)^1575 := by
    have hnat : (563352989 : ℕ)^2087*100000000000000^1575 ≤ 34781720514369^1575*1250000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563352989 1250000000 34781720514369 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2111311787/5000000000 : ℝ)^2087 ≤ (7976400104573/25000000000000 : ℝ)^1575 := by
    have hnat : (2111311787 : ℕ)^2087*25000000000000^1575 ≤ 7976400104573^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111311787 5000000000 7976400104573 25000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2181207151/5000000000 : ℝ), (563352989/1250000000 : ℝ), (2111311787/5000000000 : ℝ)] ![(33312679051641/100000000000000 : ℝ), (34781720514369/100000000000000 : ℝ), (7976400104573/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2181207151/5000000000 : ℝ)|^2087 ≤ (33312679051641/100000000000000 : ℝ)^1575
        have hw : |(2181207151/5000000000 : ℝ)|=(2181207151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(563352989/1250000000 : ℝ)|^2087 ≤ (34781720514369/100000000000000 : ℝ)^1575
        have hw : |(563352989/1250000000 : ℝ)|=(563352989/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2111311787/5000000000 : ℝ)|^2087 ≤ (7976400104573/25000000000000 : ℝ)^1575
        have hw : |(2111311787/5000000000 : ℝ)|=(2111311787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1155_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149727417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1479/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10673/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (14/125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2847/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1479/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10673/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1479/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10673/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1479/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10673/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1479/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10673/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1479/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10673/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1479/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10673/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10673/100000 : ℝ) ^ (8347/2048 : ℝ) ≤ (547738506111663/5000000000000000000 : ℝ) := by
    have hpowers : (10673/100000 : ℝ)^8347 ≤ (547738506111663/5000000000000000000 : ℝ)^2048 := by
      have hnat : (10673 : ℕ)^8347*5000000000000000000^2048 ≤ 547738506111663^2048*100000^8347 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10673 100000 547738506111663 5000000000000000000 8347 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10673/100000 : ℝ)) (X := (547738506111663/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8347 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1479/10000 : ℝ) ^ (8347/2048 : ℝ) ≤ (41405011010703679/100000000000000000000 : ℝ) := by
    have hpowers : (1479/10000 : ℝ)^8347 ≤ (41405011010703679/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1479 : ℕ)^8347*100000000000000000000^2048 ≤ 41405011010703679^2048*10000^8347 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1479 10000 41405011010703679 100000000000000000000 8347 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1479/10000 : ℝ)) (X := (41405011010703679/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8347 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500547738506111663/2500000000000000000 : ℝ) ≤ (5000268761408061/5000000000000000 : ℝ) ^ (8347/2048 : ℝ) := by
    have hpowers : (2500547738506111663/2500000000000000000 : ℝ)^2048 ≤ (5000268761408061/5000000000000000 : ℝ)^8347 := by
      have hnat : (2500547738506111663 : ℕ)^2048*5000000000000000^8347 ≤ 5000268761408061^8347*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500547738506111663 2500000000000000000 5000268761408061 5000000000000000 2048 8347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000268761408061/5000000000000000 : ℝ)) (X := (2500547738506111663/2500000000000000000 : ℝ)) (by norm_num) 8347 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100052359781132936939/100000000000000000000 : ℝ) ≤ (10001284433363359/10000000000000000 : ℝ) ^ (8347/2048 : ℝ) := by
    have hpowers : (100052359781132936939/100000000000000000000 : ℝ)^2048 ≤ (10001284433363359/10000000000000000 : ℝ)^8347 := by
      have hnat : (100052359781132936939 : ℕ)^2048*10000000000000000^8347 ≤ 10001284433363359^8347*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100052359781132936939 100000000000000000000 10001284433363359 10000000000000000 2048 8347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001284433363359/10000000000000000 : ℝ)) (X := (100052359781132936939/100000000000000000000 : ℝ)) (by norm_num) 8347 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50041405011010703679/50000000000000000000 : ℝ) ≤ (2500507835977649/2500000000000000 : ℝ) ^ (8347/2048 : ℝ) := by
    have hpowers : (50041405011010703679/50000000000000000000 : ℝ)^2048 ≤ (2500507835977649/2500000000000000 : ℝ)^8347 := by
      have hnat : (50041405011010703679 : ℕ)^2048*2500000000000000^8347 ≤ 2500507835977649^8347*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50041405011010703679 50000000000000000000 2500507835977649 2500000000000000 2048 8347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500507835977649/2500000000000000 : ℝ)) (X := (50041405011010703679/50000000000000000000 : ℝ)) (by norm_num) 8347 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(547738506111663/5000000000000000000 : ℝ) ≤ ((223675377330938333/223750000000000000 : ℝ)+2*(32474371619/17900000000000 : ℝ)*(10673/100000 : ℝ))^(8347/2048 : ℝ) := by
    rw [show (223675377330938333/223750000000000000 : ℝ)+2*(32474371619/17900000000000 : ℝ)*(10673/100000 : ℝ)=(5000268761408061/5000000000000000 : ℝ) by norm_num, show 1+2*(547738506111663/5000000000000000000 : ℝ)=(2500547738506111663/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(41405011010703679/100000000000000000000 : ℝ)+(547738506111663/5000000000000000000 : ℝ) ≤ ((223675377330938333/223750000000000000 : ℝ)+(32474371619/17900000000000 : ℝ)*((1479/10000 : ℝ)+(10673/100000 : ℝ)))^(8347/2048 : ℝ) := by
    rw [show (223675377330938333/223750000000000000 : ℝ)+(32474371619/17900000000000 : ℝ)*((1479/10000 : ℝ)+(10673/100000 : ℝ))=(10001284433363359/10000000000000000 : ℝ) by norm_num, show 1+(41405011010703679/100000000000000000000 : ℝ)+(547738506111663/5000000000000000000 : ℝ)=(100052359781132936939/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(41405011010703679/100000000000000000000 : ℝ) ≤ ((223675377330938333/223750000000000000 : ℝ)+2*(32474371619/17900000000000 : ℝ)*(1479/10000 : ℝ))^(8347/2048 : ℝ) := by
    rw [show (223675377330938333/223750000000000000 : ℝ)+2*(32474371619/17900000000000 : ℝ)*(1479/10000 : ℝ)=(2500507835977649/2500000000000000 : ℝ) by norm_num, show 1+2*(41405011010703679/100000000000000000000 : ℝ)=(50041405011010703679/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (223675377330938333/223750000000000000 : ℝ)*(X 1 0+X 2 0)+(32474371619/17900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8347/2048 : ℝ)) (lo := (10673/100000 : ℝ)) (hi := (1479/10000 : ℝ)) (c := (223675377330938333/223750000000000000 : ℝ)) (alpha := (32474371619/17900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (223675377330938333/223750000000000000 : ℝ)*(X 0 1+X 2 1)+(32474371619/17900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8347/2048 : ℝ)) (lo := (10673/100000 : ℝ)) (hi := (1479/10000 : ℝ)) (c := (223675377330938333/223750000000000000 : ℝ)) (alpha := (32474371619/17900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (223675377330938333/223750000000000000 : ℝ)*(X 0 2+X 1 2)+(32474371619/17900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8347/2048 : ℝ)) (lo := (10673/100000 : ℝ)) (hi := (1479/10000 : ℝ)) (c := (223675377330938333/223750000000000000 : ℝ)) (alpha := (32474371619/17900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-539981003/2500000000 : ℝ)*X 0 0+(2700637217/5000000000 : ℝ)*X 0 1+(2628985359/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673418667/5000000000 : ℝ)*X 1 0+(-2232740047/10000000000 : ℝ)*X 1 1+(2628985303/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673418727/5000000000 : ℝ)*X 2 0+(1314492661/2500000000 : ℝ)*X 2 1+(-2232739837/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4362400457/10000000000 : ℝ)*X 0 0+(2110904541/5000000000 : ℝ)*X 0 1+(450763499/1000000000 : ℝ)*X 0 2+(4362400457/10000000000 : ℝ)*X 1 0+(2110904541/5000000000 : ℝ)*X 1 1+(450763499/1000000000 : ℝ)*X 1 2+(4362400457/10000000000 : ℝ)*X 2 0+(2110904541/5000000000 : ℝ)*X 2 1+(450763499/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2159931249/10000000000 : ℝ)*X 0 0+(2629188619/5000000000 : ℝ)*X 0 1+(5400866069/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5310498123/10000000000 : ℝ)*X 1 0+(-2089844351/10000000000 : ℝ)*X 1 1+(5400865989/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310497977/10000000000 : ℝ)*X 2 0+(2700433003/5000000000 : ℝ)*X 2 1+(-1044922263/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2181207151/5000000000 : ℝ)*X 0 0+(563352989/1250000000 : ℝ)*X 0 1+(2111311787/5000000000 : ℝ)*X 0 2+(2181207151/5000000000 : ℝ)*X 1 0+(563352989/1250000000 : ℝ)*X 1 1+(2111311787/5000000000 : ℝ)*X 1 2+(2181207151/5000000000 : ℝ)*X 2 0+(563352989/1250000000 : ℝ)*X 2 1+(2111311787/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5461523915724853344612843/1118750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1012263421/100000000000000 : ℝ)*(base19) + (493526971/50000000000000 : ℝ)*(base23) + (50420419/50000000000000 : ℝ)*(lower2) + (161655901/100000000000000 : ℝ)*(upper5) + (1047688636107843/20000000000000 : ℝ)*(major0) + (1047688636107843/20000000000000 : ℝ)*(major1) + (1047688636107843/20000000000000 : ℝ)*(major2) + (6978203802145077/100000000000000 : ℝ)*(sp0) + (1395646182541177/20000000000000 : ℝ)*(sp1) + (3489115967448879/50000000000000 : ℝ)*(sp2) + (3498643803812911/100000000000000 : ℝ)*(sp3) + (14559903311/50000000000000 : ℝ)*(sp4) + (996982393/100000000000000 : ℝ)*(sp5) + (4736293419/50000000000000 : ℝ)*(sp7) + (3498653276399749/100000000000000 : ℝ)*(f.failure) + (69782329219517/1000000000000 : ℝ)*(f.sum) + (33679011381/89500000000000000000000000 : ℝ)*base66 + (60169259649658219/4475000000000000000000000000000 : ℝ)*base67 + (103630550519008219/4475000000000000000000000000000 : ℝ)*base69 + (3065319932658219/4475000000000000000000000000000 : ℝ)*base71 + (370887351637/179000000000000000000000000 : ℝ)*base73 + (93859013090083219/4475000000000000000000000000000 : ℝ)*base75 + (27387082749233219/4475000000000000000000000000000 : ℝ)*base77 + (55553724373891781/4475000000000000000000000000000 : ℝ)*base80 + (680871904807/179000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (22781667/10000000000000000000000 : ℝ)*base90 + (22781667/10000000000000000000000 : ℝ)*base92 + (22781667/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24981004192115708667445623/2796875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (103073579/4000000000000 : ℝ)*(base19) + (76391541/3125000000000 : ℝ)*(base23) + (77057189/100000000000000 : ℝ)*(upper2) + (74883099/50000000000000 : ℝ)*(upper3) + (158208673/50000000000000 : ℝ)*(upper5) + (164636510630469/3125000000000 : ℝ)*(major0) + (164636510630469/3125000000000 : ℝ)*(major1) + (164636510630469/3125000000000 : ℝ)*(major2) + (68526499261/100000000000000 : ℝ)*(sp1) + (56182314397/100000000000000 : ℝ)*(sp2) + (3509048340033933/50000000000000 : ℝ)*(sp4) + (701802557672913/10000000000000 : ℝ)*(sp5) + (7018038053224157/100000000000000 : ℝ)*(sp6) + (439829962819619/12500000000000 : ℝ)*(sp7) + (439829962819619/12500000000000 : ℝ)*(f.failure) + (3509048340033933/50000000000000 : ℝ)*(f.sum) + (1896962314651/447500000000000000000000000 : ℝ)*base65 + (252972499524681/87402343750000000000000000000 : ℝ)*base68 + (4947251568410521/1398437500000000000000000000000 : ℝ)*base70 + (596991443073597/43701171875000000000000000000 : ℝ)*base71 + (248793464713/895000000000000000000000000 : ℝ)*base74 + (1358122244275573/699218750000000000000000000000 : ℝ)*base76 + (10304645780507083/2796875000000000000000000000000 : ℝ)*base77 + (10724028553785521/1398437500000000000000000000000 : ℝ)*base80 + (4478907771537/895000000000000000000000000 : ℝ)*base81 + (10205877/1250000000000000000000 : ℝ)*base90 + (10205877/1250000000000000000000 : ℝ)*base92 + (10205877/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1155_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149727417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1479/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10673/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (14/125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1155_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1155_s5_0 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-432105847/2000000000 : ℝ)*x 0 + (5394577217/10000000000 : ℝ)*x 1 + (5264270903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (432105847/2000000000 : ℝ)^2087 ≤ (6564616905371/50000000000000 : ℝ)^1575 := by
    have hnat : (432105847 : ℕ)^2087*50000000000000^1575 ≤ 6564616905371^1575*2000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432105847 2000000000 6564616905371 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394577217/10000000000 : ℝ)^2087 ≤ (44138980739641/100000000000000 : ℝ)^1575 := by
    have hnat : (5394577217 : ℕ)^2087*100000000000000^1575 ≤ 44138980739641^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394577217 10000000000 44138980739641 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264270903/10000000000 : ℝ)^2087 ≤ (667684147503/1562500000000 : ℝ)^1575 := by
    have hnat : (5264270903 : ℕ)^2087*1562500000000^1575 ≤ 667684147503^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264270903 10000000000 667684147503 1562500000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-432105847/2000000000 : ℝ), (5394577217/10000000000 : ℝ), (5264270903/10000000000 : ℝ)] ![(6564616905371/50000000000000 : ℝ), (44138980739641/100000000000000 : ℝ), (667684147503/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-432105847/2000000000 : ℝ)|^2087 ≤ (6564616905371/50000000000000 : ℝ)^1575
        have hw : |(-432105847/2000000000 : ℝ)|=(432105847/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394577217/10000000000 : ℝ)|^2087 ≤ (44138980739641/100000000000000 : ℝ)^1575
        have hw : |(5394577217/10000000000 : ℝ)|=(5394577217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264270903/10000000000 : ℝ)|^2087 ≤ (667684147503/1562500000000 : ℝ)^1575
        have hw : |(5264270903/10000000000 : ℝ)|=(5264270903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s5_1 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5345156461/10000000000 : ℝ)*x 0 + (-1113322749/5000000000 : ℝ)*x 1 + (2632135337/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345156461/10000000000 : ℝ)^2087 ≤ (21801981827457/50000000000000 : ℝ)^1575 := by
    have hnat : (5345156461 : ℕ)^2087*50000000000000^1575 ≤ 21801981827457^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345156461 10000000000 21801981827457 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1113322749/5000000000 : ℝ)^2087 ≤ (13664253355487/100000000000000 : ℝ)^1575 := by
    have hnat : (1113322749 : ℕ)^2087*100000000000000^1575 ≤ 13664253355487^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1113322749 5000000000 13664253355487 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632135337/5000000000 : ℝ)^2087 ≤ (21365891488523/50000000000000 : ℝ)^1575 := by
    have hnat : (2632135337 : ℕ)^2087*50000000000000^1575 ≤ 21365891488523^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632135337 5000000000 21365891488523 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345156461/10000000000 : ℝ), (-1113322749/5000000000 : ℝ), (2632135337/5000000000 : ℝ)] ![(21801981827457/50000000000000 : ℝ), (13664253355487/100000000000000 : ℝ), (21365891488523/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345156461/10000000000 : ℝ)|^2087 ≤ (21801981827457/50000000000000 : ℝ)^1575
        have hw : |(5345156461/10000000000 : ℝ)|=(5345156461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1113322749/5000000000 : ℝ)|^2087 ≤ (13664253355487/100000000000000 : ℝ)^1575
        have hw : |(-1113322749/5000000000 : ℝ)|=(1113322749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632135337/5000000000 : ℝ)|^2087 ≤ (21365891488523/50000000000000 : ℝ)^1575
        have hw : |(2632135337/5000000000 : ℝ)|=(2632135337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s5_2 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (106903129/200000000 : ℝ)*x 0 + (5264270751/10000000000 : ℝ)*x 1 + (-222664541/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106903129/200000000 : ℝ)^2087 ≤ (43603963536009/100000000000000 : ℝ)^1575 := by
    have hnat : (106903129 : ℕ)^2087*100000000000000^1575 ≤ 43603963536009^1575*200000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106903129 200000000 43603963536009 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264270751/10000000000 : ℝ)^2087 ≤ (8546356761053/20000000000000 : ℝ)^1575 := by
    have hnat : (5264270751 : ℕ)^2087*20000000000000^1575 ≤ 8546356761053^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264270751 10000000000 8546356761053 20000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (222664541/1000000000 : ℝ)^2087 ≤ (2732850527981/20000000000000 : ℝ)^1575 := by
    have hnat : (222664541 : ℕ)^2087*20000000000000^1575 ≤ 2732850527981^1575*1000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222664541 1000000000 2732850527981 20000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106903129/200000000 : ℝ), (5264270751/10000000000 : ℝ), (-222664541/1000000000 : ℝ)] ![(43603963536009/100000000000000 : ℝ), (8546356761053/20000000000000 : ℝ), (2732850527981/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106903129/200000000 : ℝ)|^2087 ≤ (43603963536009/100000000000000 : ℝ)^1575
        have hw : |(106903129/200000000 : ℝ)|=(106903129/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264270751/10000000000 : ℝ)|^2087 ≤ (8546356761053/20000000000000 : ℝ)^1575
        have hw : |(5264270751/10000000000 : ℝ)|=(5264270751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-222664541/1000000000 : ℝ)|^2087 ≤ (2732850527981/20000000000000 : ℝ)^1575
        have hw : |(-222664541/1000000000 : ℝ)|=(222664541/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s5_3 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1090688903/2500000000 : ℝ)*x 0 + (2117362497/5000000000 : ℝ)*x 1 + (898925487/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1090688903/2500000000 : ℝ)^2087 ≤ (33316132707649/100000000000000 : ℝ)^1575 := by
    have hnat : (1090688903 : ℕ)^2087*100000000000000^1575 ≤ 33316132707649^1575*2500000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090688903 2500000000 33316132707649 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2117362497/5000000000 : ℝ)^2087 ≤ (32026817800963/100000000000000 : ℝ)^1575 := by
    have hnat : (2117362497 : ℕ)^2087*100000000000000^1575 ≤ 32026817800963^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117362497 5000000000 32026817800963 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (898925487/2000000000 : ℝ)^2087 ≤ (34657049477323/100000000000000 : ℝ)^1575 := by
    have hnat : (898925487 : ℕ)^2087*100000000000000^1575 ≤ 34657049477323^1575*2000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898925487 2000000000 34657049477323 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1090688903/2500000000 : ℝ), (2117362497/5000000000 : ℝ), (898925487/2000000000 : ℝ)] ![(33316132707649/100000000000000 : ℝ), (32026817800963/100000000000000 : ℝ), (34657049477323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1090688903/2500000000 : ℝ)|^2087 ≤ (33316132707649/100000000000000 : ℝ)^1575
        have hw : |(1090688903/2500000000 : ℝ)|=(1090688903/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2117362497/5000000000 : ℝ)|^2087 ≤ (32026817800963/100000000000000 : ℝ)^1575
        have hw : |(2117362497/5000000000 : ℝ)|=(2117362497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(898925487/2000000000 : ℝ)|^2087 ≤ (34657049477323/100000000000000 : ℝ)^1575
        have hw : |(898925487/2000000000 : ℝ)|=(898925487/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s5_4 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-432106823/2000000000 : ℝ)*x 0 + (2632303779/5000000000 : ℝ)*x 1 + (1078847919/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (432106823/2000000000 : ℝ)^2087 ≤ (13129273106087/100000000000000 : ℝ)^1575 := by
    have hnat : (432106823 : ℕ)^2087*100000000000000^1575 ≤ 13129273106087^1575*2000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432106823 2000000000 13129273106087 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632303779/5000000000 : ℝ)^2087 ≤ (2136770328579/5000000000000 : ℝ)^1575 := by
    have hnat : (2632303779 : ℕ)^2087*5000000000000^1575 ≤ 2136770328579^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632303779 5000000000 2136770328579 5000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078847919/2000000000 : ℝ)^2087 ≤ (8827064060257/20000000000000 : ℝ)^1575 := by
    have hnat : (1078847919 : ℕ)^2087*20000000000000^1575 ≤ 8827064060257^1575*2000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078847919 2000000000 8827064060257 20000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-432106823/2000000000 : ℝ), (2632303779/5000000000 : ℝ), (1078847919/2000000000 : ℝ)] ![(13129273106087/100000000000000 : ℝ), (2136770328579/5000000000000 : ℝ), (8827064060257/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-432106823/2000000000 : ℝ)|^2087 ≤ (13129273106087/100000000000000 : ℝ)^1575
        have hw : |(-432106823/2000000000 : ℝ)|=(432106823/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632303779/5000000000 : ℝ)|^2087 ≤ (2136770328579/5000000000000 : ℝ)^1575
        have hw : |(2632303779/5000000000 : ℝ)|=(2632303779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078847919/2000000000 : ℝ)|^2087 ≤ (8827064060257/20000000000000 : ℝ)^1575
        have hw : |(1078847919/2000000000 : ℝ)|=(1078847919/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s5_5 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (132802799/250000000 : ℝ)*x 0 + (-419335141/2000000000 : ℝ)*x 1 + (2697119863/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132802799/250000000 : ℝ)^2087 ≤ (21623563520561/50000000000000 : ℝ)^1575 := by
    have hnat : (132802799 : ℕ)^2087*50000000000000^1575 ≤ 21623563520561^1575*250000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132802799 250000000 21623563520561 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (419335141/2000000000 : ℝ)^2087 ≤ (63087756129/500000000000 : ℝ)^1575 := by
    have hnat : (419335141 : ℕ)^2087*500000000000^1575 ≤ 63087756129^1575*2000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419335141 2000000000 63087756129 500000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697119863/5000000000 : ℝ)^2087 ≤ (882706434431/2000000000000 : ℝ)^1575 := by
    have hnat : (2697119863 : ℕ)^2087*2000000000000^1575 ≤ 882706434431^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697119863 5000000000 882706434431 2000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132802799/250000000 : ℝ), (-419335141/2000000000 : ℝ), (2697119863/5000000000 : ℝ)] ![(21623563520561/50000000000000 : ℝ), (63087756129/500000000000 : ℝ), (882706434431/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132802799/250000000 : ℝ)|^2087 ≤ (21623563520561/50000000000000 : ℝ)^1575
        have hw : |(132802799/250000000 : ℝ)|=(132802799/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-419335141/2000000000 : ℝ)|^2087 ≤ (63087756129/500000000000 : ℝ)^1575
        have hw : |(-419335141/2000000000 : ℝ)|=(419335141/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697119863/5000000000 : ℝ)|^2087 ≤ (882706434431/2000000000000 : ℝ)^1575
        have hw : |(2697119863/5000000000 : ℝ)|=(2697119863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s5_6 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (212484463/400000000 : ℝ)*x 0 + (269712001/500000000 : ℝ)*x 1 + (-1048337913/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212484463/400000000 : ℝ)^2087 ≤ (10811780721957/25000000000000 : ℝ)^1575 := by
    have hnat : (212484463 : ℕ)^2087*25000000000000^1575 ≤ 10811780721957^1575*400000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212484463 400000000 10811780721957 25000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269712001/500000000 : ℝ)^2087 ≤ (22067662454507/50000000000000 : ℝ)^1575 := by
    have hnat : (269712001 : ℕ)^2087*50000000000000^1575 ≤ 22067662454507^1575*500000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269712001 500000000 22067662454507 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048337913/5000000000 : ℝ)^2087 ≤ (504702087627/4000000000000 : ℝ)^1575 := by
    have hnat : (1048337913 : ℕ)^2087*4000000000000^1575 ≤ 504702087627^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048337913 5000000000 504702087627 4000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212484463/400000000 : ℝ), (269712001/500000000 : ℝ), (-1048337913/5000000000 : ℝ)] ![(10811780721957/25000000000000 : ℝ), (22067662454507/50000000000000 : ℝ), (504702087627/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212484463/400000000 : ℝ)|^2087 ≤ (10811780721957/25000000000000 : ℝ)^1575
        have hw : |(212484463/400000000 : ℝ)|=(212484463/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269712001/500000000 : ℝ)|^2087 ≤ (22067662454507/50000000000000 : ℝ)^1575
        have hw : |(269712001/500000000 : ℝ)|=(269712001/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1048337913/5000000000 : ℝ)|^2087 ≤ (504702087627/4000000000000 : ℝ)^1575
        have hw : |(-1048337913/5000000000 : ℝ)|=(1048337913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s5_7 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4362766723/10000000000 : ℝ)*x 0 + (1123489071/2500000000 : ℝ)*x 1 + (2117699007/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362766723/10000000000 : ℝ)^2087 ≤ (6663249027877/20000000000000 : ℝ)^1575 := by
    have hnat : (4362766723 : ℕ)^2087*20000000000000^1575 ≤ 6663249027877^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362766723 10000000000 6663249027877 20000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1123489071/2500000000 : ℝ)^2087 ≤ (17325096117639/50000000000000 : ℝ)^1575 := by
    have hnat : (1123489071 : ℕ)^2087*50000000000000^1575 ≤ 17325096117639^1575*2500000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123489071 2500000000 17325096117639 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2117699007/5000000000 : ℝ)^2087 ≤ (8008390652493/25000000000000 : ℝ)^1575 := by
    have hnat : (2117699007 : ℕ)^2087*25000000000000^1575 ≤ 8008390652493^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117699007 5000000000 8008390652493 25000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362766723/10000000000 : ℝ), (1123489071/2500000000 : ℝ), (2117699007/5000000000 : ℝ)] ![(6663249027877/20000000000000 : ℝ), (17325096117639/50000000000000 : ℝ), (8008390652493/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362766723/10000000000 : ℝ)|^2087 ≤ (6663249027877/20000000000000 : ℝ)^1575
        have hw : |(4362766723/10000000000 : ℝ)|=(4362766723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1123489071/2500000000 : ℝ)|^2087 ≤ (17325096117639/50000000000000 : ℝ)^1575
        have hw : |(1123489071/2500000000 : ℝ)|=(1123489071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2117699007/5000000000 : ℝ)|^2087 ≤ (8008390652493/25000000000000 : ℝ)^1575
        have hw : |(2117699007/5000000000 : ℝ)|=(2117699007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1155_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149727417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (14/125 : ℝ)*pair X i i ≤ pair X i h) :
    (5667/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7047/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (14/125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (14/125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (14/125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (14/125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (14/125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (14/125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (14/125 : ℝ) ^ (8347/2048 : ℝ) ≤ (13332558371885553/100000000000000000000 : ℝ) := by
    have hpowers : (14/125 : ℝ)^8347 ≤ (13332558371885553/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14 : ℕ)^8347*100000000000000000000^2048 ≤ 13332558371885553^2048*125^8347 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14 125 13332558371885553 100000000000000000000 8347 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14/125 : ℝ)) (X := (13332558371885553/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8347 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2847/20000 : ℝ) ^ (8347/2048 : ℝ) ≤ (3542851399331859/10000000000000000000 : ℝ) := by
    have hpowers : (2847/20000 : ℝ)^8347 ≤ (3542851399331859/10000000000000000000 : ℝ)^2048 := by
      have hnat : (2847 : ℕ)^8347*10000000000000000000^2048 ≤ 3542851399331859^2048*20000^8347 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 20000 3542851399331859 10000000000000000000 8347 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/20000 : ℝ)) (X := (3542851399331859/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8347 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013332558371885553/50000000000000000000 : ℝ) ≤ (10000654183125059/10000000000000000 : ℝ) ^ (8347/2048 : ℝ) := by
    have hpowers : (50013332558371885553/50000000000000000000 : ℝ)^2048 ≤ (10000654183125059/10000000000000000 : ℝ)^8347 := by
      have hnat : (50013332558371885553 : ℕ)^2048*10000000000000000^8347 ≤ 10000654183125059^8347*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013332558371885553 50000000000000000000 10000654183125059 10000000000000000 2048 8347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000654183125059/10000000000000000 : ℝ)) (X := (50013332558371885553/50000000000000000000 : ℝ)) (by norm_num) 8347 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048761072365204143/100000000000000000000 : ℝ) ≤ (10001196169978697/10000000000000000 : ℝ) ^ (8347/2048 : ℝ) := by
    have hpowers : (100048761072365204143/100000000000000000000 : ℝ)^2048 ≤ (10001196169978697/10000000000000000 : ℝ)^8347 := by
      have hnat : (100048761072365204143 : ℕ)^2048*10000000000000000^8347 ≤ 10001196169978697^8347*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048761072365204143 100000000000000000000 10001196169978697 10000000000000000 2048 8347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001196169978697/10000000000000000 : ℝ)) (X := (100048761072365204143/100000000000000000000 : ℝ)) (by norm_num) 8347 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003542851399331859/5000000000000000000 : ℝ) ≤ (2000347631366467/2000000000000000 : ℝ) ^ (8347/2048 : ℝ) := by
    have hpowers : (5003542851399331859/5000000000000000000 : ℝ)^2048 ≤ (2000347631366467/2000000000000000 : ℝ)^8347 := by
      have hnat : (5003542851399331859 : ℕ)^2048*2000000000000000^8347 ≤ 2000347631366467^8347*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003542851399331859 5000000000000000000 2000347631366467 2000000000000000 2048 8347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000347631366467/2000000000000000 : ℝ)) (X := (5003542851399331859/5000000000000000000 : ℝ)) (by norm_num) 8347 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13332558371885553/100000000000000000000 : ℝ) ≤ ((6067968988052612573/6070000000000000000 : ℝ)+2*(270993426819/151750000000000 : ℝ)*(14/125 : ℝ))^(8347/2048 : ℝ) := by
    rw [show (6067968988052612573/6070000000000000000 : ℝ)+2*(270993426819/151750000000000 : ℝ)*(14/125 : ℝ)=(10000654183125059/10000000000000000 : ℝ) by norm_num, show 1+2*(13332558371885553/100000000000000000000 : ℝ)=(50013332558371885553/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3542851399331859/10000000000000000000 : ℝ)+(13332558371885553/100000000000000000000 : ℝ) ≤ ((6067968988052612573/6070000000000000000 : ℝ)+(270993426819/151750000000000 : ℝ)*((2847/20000 : ℝ)+(14/125 : ℝ)))^(8347/2048 : ℝ) := by
    rw [show (6067968988052612573/6070000000000000000 : ℝ)+(270993426819/151750000000000 : ℝ)*((2847/20000 : ℝ)+(14/125 : ℝ))=(10001196169978697/10000000000000000 : ℝ) by norm_num, show 1+(3542851399331859/10000000000000000000 : ℝ)+(13332558371885553/100000000000000000000 : ℝ)=(100048761072365204143/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3542851399331859/10000000000000000000 : ℝ) ≤ ((6067968988052612573/6070000000000000000 : ℝ)+2*(270993426819/151750000000000 : ℝ)*(2847/20000 : ℝ))^(8347/2048 : ℝ) := by
    rw [show (6067968988052612573/6070000000000000000 : ℝ)+2*(270993426819/151750000000000 : ℝ)*(2847/20000 : ℝ)=(2000347631366467/2000000000000000 : ℝ) by norm_num, show 1+2*(3542851399331859/10000000000000000000 : ℝ)=(5003542851399331859/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6067968988052612573/6070000000000000000 : ℝ)*(X 1 0+X 2 0)+(270993426819/151750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8347/2048 : ℝ)) (lo := (14/125 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (6067968988052612573/6070000000000000000 : ℝ)) (alpha := (270993426819/151750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6067968988052612573/6070000000000000000 : ℝ)*(X 0 1+X 2 1)+(270993426819/151750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8347/2048 : ℝ)) (lo := (14/125 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (6067968988052612573/6070000000000000000 : ℝ)) (alpha := (270993426819/151750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6067968988052612573/6070000000000000000 : ℝ)*(X 0 2+X 1 2)+(270993426819/151750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8347/2048 : ℝ)) (lo := (14/125 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (6067968988052612573/6070000000000000000 : ℝ)) (alpha := (270993426819/151750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-432105847/2000000000 : ℝ)*X 0 0+(5394577217/10000000000 : ℝ)*X 0 1+(5264270903/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345156461/10000000000 : ℝ)*X 1 0+(-1113322749/5000000000 : ℝ)*X 1 1+(2632135337/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((106903129/200000000 : ℝ)*X 2 0+(5264270751/10000000000 : ℝ)*X 2 1+(-222664541/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1090688903/2500000000 : ℝ)*X 0 0+(2117362497/5000000000 : ℝ)*X 0 1+(898925487/2000000000 : ℝ)*X 0 2+(1090688903/2500000000 : ℝ)*X 1 0+(2117362497/5000000000 : ℝ)*X 1 1+(898925487/2000000000 : ℝ)*X 1 2+(1090688903/2500000000 : ℝ)*X 2 0+(2117362497/5000000000 : ℝ)*X 2 1+(898925487/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-432106823/2000000000 : ℝ)*X 0 0+(2632303779/5000000000 : ℝ)*X 0 1+(1078847919/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((132802799/250000000 : ℝ)*X 1 0+(-419335141/2000000000 : ℝ)*X 1 1+(2697119863/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((212484463/400000000 : ℝ)*X 2 0+(269712001/500000000 : ℝ)*X 2 1+(-1048337913/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4362766723/10000000000 : ℝ)*X 0 0+(1123489071/2500000000 : ℝ)*X 0 1+(2117699007/5000000000 : ℝ)*X 0 2+(4362766723/10000000000 : ℝ)*X 1 0+(1123489071/2500000000 : ℝ)*X 1 1+(2117699007/5000000000 : ℝ)*X 1 2+(4362766723/10000000000 : ℝ)*X 2 0+(1123489071/2500000000 : ℝ)*X 2 1+(2117699007/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (385703038909374421834255323/37937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (29111/3125000000 : ℝ)*(base19) + (138763973/25000000000000 : ℝ)*(base23) + (115857067/50000000000000 : ℝ)*(upper3) + (192801409/100000000000000 : ℝ)*(upper4) + (105717957/100000000000000 : ℝ)*(upper5) + (720114673655361/12500000000000 : ℝ)*(major0) + (720114673655361/12500000000000 : ℝ)*(major1) + (720114673655361/12500000000000 : ℝ)*(major2) + (767422831144419/10000000000000 : ℝ)*(sp0) + (153484599462321/2000000000000 : ℝ)*(sp1) + (3837115174806079/50000000000000 : ℝ)*(sp2) + (961899607020197/25000000000000 : ℝ)*(sp3) + (129661193/5000000000000 : ℝ)*(sp4) + (2553421769/50000000000000 : ℝ)*(sp7) + (3847603534924327/100000000000000 : ℝ)*(f.failure) + (153484618093361/2000000000000 : ℝ)*(f.sum) + (136629282163/29638671875000000000000000 : ℝ)*base66 + (829628786346563853/75875000000000000000000000000000 : ℝ)*base67 + (328730003264563853/75875000000000000000000000000000 : ℝ)*base69 + (69209073053813853/75875000000000000000000000000000 : ℝ)*base71 + (16017186140711/3793750000000000000000000000 : ℝ)*base73 + (724981315763313853/75875000000000000000000000000000 : ℝ)*base75 + (1558497226760063853/75875000000000000000000000000000 : ℝ)*base77 + (1067084337392063853/75875000000000000000000000000000 : ℝ)*base79 + (7783254905389/3793750000000000000000000000 : ℝ)*base82 + (27826641/10000000000000000000000 : ℝ)*base90 + (27826641/10000000000000000000000 : ℝ)*base92 + (27826641/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (51604049667801081818816319/12140000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (121697699/12500000000000 : ℝ)*(base19) + (505846319/50000000000000 : ℝ)*(base23) + (48029743/100000000000000 : ℝ)*(upper3) + (296002539/100000000000000 : ℝ)*(lower4) + (231634643229401/4000000000000 : ℝ)*(major0) + (231634643229401/4000000000000 : ℝ)*(major1) + (231634643229401/4000000000000 : ℝ)*(major2) + (2411312753/6250000000000 : ℝ)*(sp1) + (22503535501/50000000000000 : ℝ)*(sp2) + (2547366501/50000000000000 : ℝ)*(sp3) + (7714126342232491/100000000000000 : ℝ)*(sp4) + (154281735752937/2000000000000 : ℝ)*(sp5) + (1928520080867213/25000000000000 : ℝ)*(sp6) + (483450072851629/12500000000000 : ℝ)*(sp7) + (1933802838773017/50000000000000 : ℝ)*(f.failure) + (7714126342232491/100000000000000 : ℝ)*(f.sum) + (1487394702427/607000000000000000000000000 : ℝ)*base66 + (354798784638501227/24280000000000000000000000000000 : ℝ)*base68 + (34844290270978773/24280000000000000000000000000000 : ℝ)*base69 + (67617142303978773/24280000000000000000000000000000 : ℝ)*base71 + (699998633977/75875000000000000000000000 : ℝ)*base74 + (306114172782981227/24280000000000000000000000000000 : ℝ)*base76 + (263410178332181227/24280000000000000000000000000000 : ℝ)*base78 + (451407752892421227/24280000000000000000000000000000 : ℝ)*base80 + (236377028373/75875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (34707089/5000000000000000000000 : ℝ)*base89 + (34707089/5000000000000000000000 : ℝ)*base91 + (34707089/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1155_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149727417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (14/125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5667/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7047/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1155_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1155_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149727417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1029/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9129/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5667/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7047/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1155_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1155_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1155_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149727417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1029/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9129/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5667/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7047/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1155_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
