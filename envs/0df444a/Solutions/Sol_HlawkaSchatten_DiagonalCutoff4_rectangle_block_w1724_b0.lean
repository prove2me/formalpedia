-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1724_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:00:50.317722+00:00
-- url     : https://prove2.me/submissions/797337b7-b3fd-4d38-8b4d-3b46ccb82372

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
theorem support_rectangle_w1724_s0_0 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1296372369/10000000000 : ℝ)*x 0 + (2835356643/5000000000 : ℝ)*x 1 + (621806279/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1296372369/10000000000 : ℝ)^5415 ≤ (8050346035131/100000000000000 : ℝ)^4391 := by
    have hnat : (1296372369 : ℕ)^5415*100000000000000^4391 ≤ 8050346035131^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296372369 10000000000 8050346035131 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2835356643/5000000000 : ℝ)^5415 ≤ (49680384014133/100000000000000 : ℝ)^4391 := by
    have hnat : (2835356643 : ℕ)^5415*100000000000000^4391 ≤ 49680384014133^4391*5000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2835356643 5000000000 49680384014133 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (621806279/1250000000 : ℝ)^5415 ≤ (2641829371097/6250000000000 : ℝ)^4391 := by
    have hnat : (621806279 : ℕ)^5415*6250000000000^4391 ≤ 2641829371097^4391*1250000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      621806279 1250000000 2641829371097 6250000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1296372369/10000000000 : ℝ), (2835356643/5000000000 : ℝ), (621806279/1250000000 : ℝ)] ![(8050346035131/100000000000000 : ℝ), (49680384014133/100000000000000 : ℝ), (2641829371097/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1296372369/10000000000 : ℝ)|^5415 ≤ (8050346035131/100000000000000 : ℝ)^4391
        have hw : |(-1296372369/10000000000 : ℝ)|=(1296372369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2835356643/5000000000 : ℝ)|^5415 ≤ (49680384014133/100000000000000 : ℝ)^4391
        have hw : |(2835356643/5000000000 : ℝ)|=(2835356643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(621806279/1250000000 : ℝ)|^5415 ≤ (2641829371097/6250000000000 : ℝ)^4391
        have hw : |(621806279/1250000000 : ℝ)|=(621806279/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_s0_1 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1078933659/2000000000 : ℝ)*x 0 + (-835868653/5000000000 : ℝ)*x 1 + (497444963/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078933659/2000000000 : ℝ)^5415 ≤ (46715153189999/100000000000000 : ℝ)^4391 := by
    have hnat : (1078933659 : ℕ)^5415*100000000000000^4391 ≤ 46715153189999^4391*2000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078933659 2000000000 46715153189999 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (835868653/5000000000 : ℝ)^5415 ≤ (344236973971/3125000000000 : ℝ)^4391 := by
    have hnat : (835868653 : ℕ)^5415*3125000000000^4391 ≤ 344236973971^4391*5000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      835868653 5000000000 344236973971 3125000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (497444963/1000000000 : ℝ)^5415 ≤ (42269263629269/100000000000000 : ℝ)^4391 := by
    have hnat : (497444963 : ℕ)^5415*100000000000000^4391 ≤ 42269263629269^4391*1000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      497444963 1000000000 42269263629269 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1078933659/2000000000 : ℝ), (-835868653/5000000000 : ℝ), (497444963/1000000000 : ℝ)] ![(46715153189999/100000000000000 : ℝ), (344236973971/3125000000000 : ℝ), (42269263629269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1078933659/2000000000 : ℝ)|^5415 ≤ (46715153189999/100000000000000 : ℝ)^4391
        have hw : |(1078933659/2000000000 : ℝ)|=(1078933659/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-835868653/5000000000 : ℝ)|^5415 ≤ (344236973971/3125000000000 : ℝ)^4391
        have hw : |(-835868653/5000000000 : ℝ)|=(835868653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(497444963/1000000000 : ℝ)|^5415 ≤ (42269263629269/100000000000000 : ℝ)^4391
        have hw : |(497444963/1000000000 : ℝ)|=(497444963/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_s0_2 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2697333557/5000000000 : ℝ)*x 0 + (4974450341/10000000000 : ℝ)*x 1 + (-1671737941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2697333557/5000000000 : ℝ)^5415 ≤ (23357570289087/50000000000000 : ℝ)^4391 := by
    have hnat : (2697333557 : ℕ)^5415*50000000000000^4391 ≤ 23357570289087^4391*5000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697333557 5000000000 23357570289087 50000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4974450341/10000000000 : ℝ)^5415 ≤ (169077084319/400000000000 : ℝ)^4391 := by
    have hnat : (4974450341 : ℕ)^5415*400000000000^4391 ≤ 169077084319^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4974450341 10000000000 169077084319 400000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1671737941/10000000000 : ℝ)^5415 ≤ (2203117665411/20000000000000 : ℝ)^4391 := by
    have hnat : (1671737941 : ℕ)^5415*20000000000000^4391 ≤ 2203117665411^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1671737941 10000000000 2203117665411 20000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2697333557/5000000000 : ℝ), (4974450341/10000000000 : ℝ), (-1671737941/10000000000 : ℝ)] ![(23357570289087/50000000000000 : ℝ), (169077084319/400000000000 : ℝ), (2203117665411/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2697333557/5000000000 : ℝ)|^5415 ≤ (23357570289087/50000000000000 : ℝ)^4391
        have hw : |(2697333557/5000000000 : ℝ)|=(2697333557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4974450341/10000000000 : ℝ)|^5415 ≤ (169077084319/400000000000 : ℝ)^4391
        have hw : |(4974450341/10000000000 : ℝ)|=(4974450341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1671737941/10000000000 : ℝ)|^5415 ≤ (2203117665411/20000000000000 : ℝ)^4391
        have hw : |(-1671737941/10000000000 : ℝ)|=(1671737941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_s0_3 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4027970109/10000000000 : ℝ)*x 0 + (1533921733/5000000000 : ℝ)*x 1 + (1287764481/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4027970109/10000000000 : ℝ)^5415 ≤ (4072871162189/12500000000000 : ℝ)^4391 := by
    have hnat : (4027970109 : ℕ)^5415*12500000000000^4391 ≤ 4072871162189^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4027970109 10000000000 4072871162189 12500000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1533921733/5000000000 : ℝ)^5415 ≤ (23289518008409/100000000000000 : ℝ)^4391 := by
    have hnat : (1533921733 : ℕ)^5415*100000000000000^4391 ≤ 23289518008409^4391*5000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1533921733 5000000000 23289518008409 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1287764481/2500000000 : ℝ)^5415 ≤ (1378984771143/3125000000000 : ℝ)^4391 := by
    have hnat : (1287764481 : ℕ)^5415*3125000000000^4391 ≤ 1378984771143^4391*2500000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1287764481 2500000000 1378984771143 3125000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4027970109/10000000000 : ℝ), (1533921733/5000000000 : ℝ), (1287764481/2500000000 : ℝ)] ![(4072871162189/12500000000000 : ℝ), (23289518008409/100000000000000 : ℝ), (1378984771143/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4027970109/10000000000 : ℝ)|^5415 ≤ (4072871162189/12500000000000 : ℝ)^4391
        have hw : |(4027970109/10000000000 : ℝ)|=(4027970109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1533921733/5000000000 : ℝ)|^5415 ≤ (23289518008409/100000000000000 : ℝ)^4391
        have hw : |(1533921733/5000000000 : ℝ)|=(1533921733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1287764481/2500000000 : ℝ)|^5415 ≤ (1378984771143/3125000000000 : ℝ)^4391
        have hw : |(1287764481/2500000000 : ℝ)|=(1287764481/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_s0_4 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1297839073/10000000000 : ℝ)*x 0 + (311956033/625000000 : ℝ)*x 1 + (2826660709/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1297839073/10000000000 : ℝ)^5415 ≤ (2015394912663/25000000000000 : ℝ)^4391 := by
    have hnat : (1297839073 : ℕ)^5415*25000000000000^4391 ≤ 2015394912663^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1297839073 10000000000 2015394912663 25000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (311956033/625000000 : ℝ)^5415 ≤ (424458698241/1000000000000 : ℝ)^4391 := by
    have hnat : (311956033 : ℕ)^5415*1000000000000^4391 ≤ 424458698241^4391*625000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      311956033 625000000 424458698241 1000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2826660709/5000000000 : ℝ)^5415 ≤ (24746275257471/50000000000000 : ℝ)^4391 := by
    have hnat : (2826660709 : ℕ)^5415*50000000000000^4391 ≤ 24746275257471^4391*5000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2826660709 5000000000 24746275257471 50000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1297839073/10000000000 : ℝ), (311956033/625000000 : ℝ), (2826660709/5000000000 : ℝ)] ![(2015394912663/25000000000000 : ℝ), (424458698241/1000000000000 : ℝ), (24746275257471/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1297839073/10000000000 : ℝ)|^5415 ≤ (2015394912663/25000000000000 : ℝ)^4391
        have hw : |(-1297839073/10000000000 : ℝ)|=(1297839073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(311956033/625000000 : ℝ)|^5415 ≤ (424458698241/1000000000000 : ℝ)^4391
        have hw : |(311956033/625000000 : ℝ)|=(311956033/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2826660709/5000000000 : ℝ)|^5415 ≤ (24746275257471/50000000000000 : ℝ)^4391
        have hw : |(2826660709/5000000000 : ℝ)|=(2826660709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_s0_5 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5206473297/10000000000 : ℝ)*x 0 + (-124108233/1250000000 : ℝ)*x 1 + (1130664303/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5206473297/10000000000 : ℝ)^5415 ≤ (44713679526059/100000000000000 : ℝ)^4391 := by
    have hnat : (5206473297 : ℕ)^5415*100000000000000^4391 ≤ 44713679526059^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5206473297 10000000000 44713679526059 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (124108233/1250000000 : ℝ)^5415 ≤ (5793768892597/100000000000000 : ℝ)^4391 := by
    have hnat : (124108233 : ℕ)^5415*100000000000000^4391 ≤ 5793768892597^4391*1250000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124108233 1250000000 5793768892597 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1130664303/2000000000 : ℝ)^5415 ≤ (24746275781087/50000000000000 : ℝ)^4391 := by
    have hnat : (1130664303 : ℕ)^5415*50000000000000^4391 ≤ 24746275781087^4391*2000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130664303 2000000000 24746275781087 50000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5206473297/10000000000 : ℝ), (-124108233/1250000000 : ℝ), (1130664303/2000000000 : ℝ)] ![(44713679526059/100000000000000 : ℝ), (5793768892597/100000000000000 : ℝ), (24746275781087/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5206473297/10000000000 : ℝ)|^5415 ≤ (44713679526059/100000000000000 : ℝ)^4391
        have hw : |(5206473297/10000000000 : ℝ)|=(5206473297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-124108233/1250000000 : ℝ)|^5415 ≤ (5793768892597/100000000000000 : ℝ)^4391
        have hw : |(-124108233/1250000000 : ℝ)|=(124108233/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1130664303/2000000000 : ℝ)|^5415 ≤ (24746275781087/50000000000000 : ℝ)^4391
        have hw : |(1130664303/2000000000 : ℝ)|=(1130664303/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_s0_6 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (650809121/1250000000 : ℝ)*x 0 + (226132859/400000000 : ℝ)*x 1 + (-992866409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (650809121/1250000000 : ℝ)^5415 ≤ (22356838020831/50000000000000 : ℝ)^4391 := by
    have hnat : (650809121 : ℕ)^5415*50000000000000^4391 ≤ 22356838020831^4391*1250000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      650809121 1250000000 22356838020831 50000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (226132859/400000000 : ℝ)^5415 ≤ (24746275565163/50000000000000 : ℝ)^4391 := by
    have hnat : (226132859 : ℕ)^5415*50000000000000^4391 ≤ 24746275565163^4391*400000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226132859 400000000 24746275565163 50000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (992866409/10000000000 : ℝ)^5415 ≤ (5793772814547/100000000000000 : ℝ)^4391 := by
    have hnat : (992866409 : ℕ)^5415*100000000000000^4391 ≤ 5793772814547^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      992866409 10000000000 5793772814547 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(650809121/1250000000 : ℝ), (226132859/400000000 : ℝ), (-992866409/10000000000 : ℝ)] ![(22356838020831/50000000000000 : ℝ), (24746275565163/50000000000000 : ℝ), (5793772814547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(650809121/1250000000 : ℝ)|^5415 ≤ (22356838020831/50000000000000 : ℝ)^4391
        have hw : |(650809121/1250000000 : ℝ)|=(650809121/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(226132859/400000000 : ℝ)|^5415 ≤ (24746275565163/50000000000000 : ℝ)^4391
        have hw : |(226132859/400000000 : ℝ)|=(226132859/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-992866409/10000000000 : ℝ)|^5415 ≤ (5793772814547/100000000000000 : ℝ)^4391
        have hw : |(-992866409/10000000000 : ℝ)|=(992866409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_s0_7 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4032356193/10000000000 : ℝ)*x 0 + (5100655371/10000000000 : ℝ)*x 1 + (779969731/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4032356193/10000000000 : ℝ)^5415 ≤ (652534574259/2000000000000 : ℝ)^4391 := by
    have hnat : (4032356193 : ℕ)^5415*2000000000000^4391 ≤ 652534574259^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4032356193 10000000000 652534574259 2000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5100655371/10000000000 : ℝ)^5415 ≤ (43595645069339/100000000000000 : ℝ)^4391 := by
    have hnat : (5100655371 : ℕ)^5415*100000000000000^4391 ≤ 43595645069339^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5100655371 10000000000 43595645069339 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (779969731/2500000000 : ℝ)^5415 ≤ (23777626205391/100000000000000 : ℝ)^4391 := by
    have hnat : (779969731 : ℕ)^5415*100000000000000^4391 ≤ 23777626205391^4391*2500000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      779969731 2500000000 23777626205391 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4032356193/10000000000 : ℝ), (5100655371/10000000000 : ℝ), (779969731/2500000000 : ℝ)] ![(652534574259/2000000000000 : ℝ), (43595645069339/100000000000000 : ℝ), (23777626205391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4032356193/10000000000 : ℝ)|^5415 ≤ (652534574259/2000000000000 : ℝ)^4391
        have hw : |(4032356193/10000000000 : ℝ)|=(4032356193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5100655371/10000000000 : ℝ)|^5415 ≤ (43595645069339/100000000000000 : ℝ)^4391
        have hw : |(5100655371/10000000000 : ℝ)|=(5100655371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(779969731/2500000000 : ℝ)|^5415 ≤ (23777626205391/100000000000000 : ℝ)^4391
        have hw : |(779969731/2500000000 : ℝ)|=(779969731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1724_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39919953/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (6441/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (21431/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (5407/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5407 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5407*1^1024 ≤ 0^1024*1^5407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5407 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5407 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5407/1024 : ℝ) ≤ (792077984644852427/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5407 ≤ (792077984644852427/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5407*100000000000000000000^1024 ≤ 792077984644852427^1024*5^5407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 792077984644852427 100000000000000000000 5407 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (792077984644852427/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5407 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5407/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5407 := by
      have hnat : (1 : ℕ)^1024*1^5407 ≤ 1^5407*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5407 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100792077984644852427/100000000000000000000 : ℝ) ≤ (10014952771506647/10000000000000000 : ℝ) ^ (5407/1024 : ℝ) := by
    have hpowers : (100792077984644852427/100000000000000000000 : ℝ)^1024 ≤ (10014952771506647/10000000000000000 : ℝ)^5407 := by
      have hnat : (100792077984644852427 : ℕ)^1024*10000000000000000^5407 ≤ 10014952771506647^5407*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100792077984644852427 100000000000000000000 10014952771506647 10000000000000000 1024 5407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10014952771506647/10000000000000000 : ℝ)) (X := (100792077984644852427/100000000000000000000 : ℝ)) (by norm_num) 5407 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50792077984644852427/50000000000000000000 : ℝ) ≤ (5014952771506647/5000000000000000 : ℝ) ^ (5407/1024 : ℝ) := by
    have hpowers : (50792077984644852427/50000000000000000000 : ℝ)^1024 ≤ (5014952771506647/5000000000000000 : ℝ)^5407 := by
      have hnat : (50792077984644852427 : ℕ)^1024*5000000000000000^5407 ≤ 5014952771506647^5407*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50792077984644852427 50000000000000000000 5014952771506647 5000000000000000 1024 5407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5014952771506647/5000000000000000 : ℝ)) (X := (50792077984644852427/50000000000000000000 : ℝ)) (by norm_num) 5407 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(14952771506647/4000000000000000 : ℝ)*(0 : ℝ))^(5407/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(14952771506647/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(792077984644852427/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(14952771506647/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5407/1024 : ℝ) := by
    rw [show (1 : ℝ)+(14952771506647/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10014952771506647/10000000000000000 : ℝ) by norm_num, show 1+(792077984644852427/100000000000000000000 : ℝ)+(0 : ℝ)=(100792077984644852427/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(792077984644852427/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(14952771506647/4000000000000000 : ℝ)*(2/5 : ℝ))^(5407/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(14952771506647/4000000000000000 : ℝ)*(2/5 : ℝ)=(5014952771506647/5000000000000000 : ℝ) by norm_num, show 1+2*(792077984644852427/100000000000000000000 : ℝ)=(50792077984644852427/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(14952771506647/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5407/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14952771506647/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(14952771506647/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5407/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14952771506647/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(14952771506647/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5407/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14952771506647/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1296372369/10000000000 : ℝ)*X 0 0+(2835356643/5000000000 : ℝ)*X 0 1+(621806279/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1078933659/2000000000 : ℝ)*X 1 0+(-835868653/5000000000 : ℝ)*X 1 1+(497444963/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2697333557/5000000000 : ℝ)*X 2 0+(4974450341/10000000000 : ℝ)*X 2 1+(-1671737941/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4027970109/10000000000 : ℝ)*X 0 0+(1533921733/5000000000 : ℝ)*X 0 1+(1287764481/2500000000 : ℝ)*X 0 2+(4027970109/10000000000 : ℝ)*X 1 0+(1533921733/5000000000 : ℝ)*X 1 1+(1287764481/2500000000 : ℝ)*X 1 2+(4027970109/10000000000 : ℝ)*X 2 0+(1533921733/5000000000 : ℝ)*X 2 1+(1287764481/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1297839073/10000000000 : ℝ)*X 0 0+(311956033/625000000 : ℝ)*X 0 1+(2826660709/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5206473297/10000000000 : ℝ)*X 1 0+(-124108233/1250000000 : ℝ)*X 1 1+(1130664303/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((650809121/1250000000 : ℝ)*X 2 0+(226132859/400000000 : ℝ)*X 2 1+(-992866409/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4032356193/10000000000 : ℝ)*X 0 0+(5100655371/10000000000 : ℝ)*X 0 1+(779969731/2500000000 : ℝ)*X 0 2+(4032356193/10000000000 : ℝ)*X 1 0+(5100655371/10000000000 : ℝ)*X 1 1+(779969731/2500000000 : ℝ)*X 1 2+(4032356193/10000000000 : ℝ)*X 2 0+(5100655371/10000000000 : ℝ)*X 2 1+(779969731/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (306346708030548139435131/40000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (41247929/20000000000000 : ℝ)*(base1) + (40126997/2500000000000 : ℝ)*(base19) + (161332087/12500000000000 : ℝ)*(base23) + (193123659/50000000000000 : ℝ)*(upper3) + (53476039/100000000000000 : ℝ)*(upper5) + (191628010649409/20000000000000 : ℝ)*(major0) + (191628010649409/20000000000000 : ℝ)*(major1) + (191628010649409/20000000000000 : ℝ)*(major2) + (17953074972333/1250000000000 : ℝ)*(sp0) + (1436247594161813/100000000000000 : ℝ)*(sp1) + (359061977146249/25000000000000 : ℝ)*(sp2) + (480028414500169/100000000000000 : ℝ)*(sp3) + (3407694697/100000000000000 : ℝ)*(sp4) + (2031223651/100000000000000 : ℝ)*(sp7) + (96006130392693/20000000000000 : ℝ)*(f.failure) + (359062299810423/25000000000000 : ℝ)*(f.sum) + (49647090798377/40000000000000000000000000000 : ℝ)*base66 + (974026923641623/80000000000000000000000000000 : ℝ)*base67 + (2642509641623/80000000000000000000000000000 : ℝ)*base69 + (244678798201623/80000000000000000000000000000 : ℝ)*base71 + (22564650241623/40000000000000000000000000000 : ℝ)*base73 + (113226159478377/80000000000000000000000000000 : ℝ)*base76 + (524342581481623/80000000000000000000000000000 : ℝ)*base77 + (612565117241623/80000000000000000000000000000 : ℝ)*base79 + (200245667638377/40000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (3896571/400000000000000000000 : ℝ)*base90 + (3896571/400000000000000000000 : ℝ)*base92 + (3896571/400000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (392501044017806604141207/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (898539541/100000000000000 : ℝ)*(base19) + (805895617/100000000000000 : ℝ)*(base23) + (284907/1562500000000 : ℝ)*(upper2) + (155873357/100000000000000 : ℝ)*(upper3) + (115675121/100000000000000 : ℝ)*(upper5) + (1007684555349173/100000000000000 : ℝ)*(major0) + (1007684555349173/100000000000000 : ℝ)*(major1) + (1007684555349173/100000000000000 : ℝ)*(major2) + (3672930149/100000000000000 : ℝ)*(sp1) + (2781691813/100000000000000 : ℝ)*(sp2) + (18881455047953/1250000000000 : ℝ)*(sp4) + (30210236647331/2000000000000 : ℝ)*(sp5) + (1510512816248811/100000000000000 : ℝ)*(sp6) + (25242628801421/5000000000000 : ℝ)*(sp7) + (25242628801421/5000000000000 : ℝ)*(f.failure) + (18881455047953/1250000000000 : ℝ)*(f.sum) + (692702467452931/200000000000000000000000000000 : ℝ)*base65 + (2600134959452931/400000000000000000000000000000 : ℝ)*base67 + (290020984547069/400000000000000000000000000000 : ℝ)*base70 + (1293043829452931/400000000000000000000000000000 : ℝ)*base71 + (150671170252931/200000000000000000000000000000 : ℝ)*base73 + (416527095452931/400000000000000000000000000000 : ℝ)*base75 + (70308859452931/400000000000000000000000000000 : ℝ)*base77 + (1124544935747069/400000000000000000000000000000 : ℝ)*base80 + (112928294147069/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (346787/100000000000000000000 : ℝ)*base90 + (346787/100000000000000000000 : ℝ)*base92 + (346787/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1724_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39919953/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6441/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (21431/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1724_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1724_s1_0 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-340097709/2500000000 : ℝ)*x 0 + (218890993/400000000 : ℝ)*x 1 + (5130583727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (340097709/2500000000 : ℝ)^5415 ≤ (4271696286269/50000000000000 : ℝ)^4391 := by
    have hnat : (340097709 : ℕ)^5415*50000000000000^4391 ≤ 4271696286269^4391*2500000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340097709 2500000000 4271696286269 50000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (218890993/400000000 : ℝ)^5415 ≤ (47545293578799/100000000000000 : ℝ)^4391 := by
    have hnat : (218890993 : ℕ)^5415*100000000000000^4391 ≤ 47545293578799^4391*400000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218890993 400000000 47545293578799 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5130583727/10000000000 : ℝ)^5415 ≤ (43911313824131/100000000000000 : ℝ)^4391 := by
    have hnat : (5130583727 : ℕ)^5415*100000000000000^4391 ≤ 43911313824131^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5130583727 10000000000 43911313824131 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-340097709/2500000000 : ℝ), (218890993/400000000 : ℝ), (5130583727/10000000000 : ℝ)] ![(4271696286269/50000000000000 : ℝ), (47545293578799/100000000000000 : ℝ), (43911313824131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-340097709/2500000000 : ℝ)|^5415 ≤ (4271696286269/50000000000000 : ℝ)^4391
        have hw : |(-340097709/2500000000 : ℝ)|=(340097709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(218890993/400000000 : ℝ)|^5415 ≤ (47545293578799/100000000000000 : ℝ)^4391
        have hw : |(218890993/400000000 : ℝ)|=(218890993/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5130583727/10000000000 : ℝ)|^5415 ≤ (43911313824131/100000000000000 : ℝ)^4391
        have hw : |(5130583727/10000000000 : ℝ)|=(5130583727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_s1_1 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5341821677/10000000000 : ℝ)*x 0 + (-153775541/1000000000 : ℝ)*x 1 + (320661423/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5341821677/10000000000 : ℝ)^5415 ≤ (369211629501/800000000000 : ℝ)^4391 := by
    have hnat : (5341821677 : ℕ)^5415*800000000000^4391 ≤ 369211629501^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5341821677 10000000000 369211629501 800000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (153775541/1000000000 : ℝ)^5415 ≤ (993724259233/10000000000000 : ℝ)^4391 := by
    have hnat : (153775541 : ℕ)^5415*10000000000000^4391 ≤ 993724259233^4391*1000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153775541 1000000000 993724259233 10000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (320661423/625000000 : ℝ)^5415 ≤ (21955651851101/50000000000000 : ℝ)^4391 := by
    have hnat : (320661423 : ℕ)^5415*50000000000000^4391 ≤ 21955651851101^4391*625000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      320661423 625000000 21955651851101 50000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5341821677/10000000000 : ℝ), (-153775541/1000000000 : ℝ), (320661423/625000000 : ℝ)] ![(369211629501/800000000000 : ℝ), (993724259233/10000000000000 : ℝ), (21955651851101/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5341821677/10000000000 : ℝ)|^5415 ≤ (369211629501/800000000000 : ℝ)^4391
        have hw : |(5341821677/10000000000 : ℝ)|=(5341821677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-153775541/1000000000 : ℝ)|^5415 ≤ (993724259233/10000000000000 : ℝ)^4391
        have hw : |(-153775541/1000000000 : ℝ)|=(153775541/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(320661423/625000000 : ℝ)|^5415 ≤ (21955651851101/50000000000000 : ℝ)^4391
        have hw : |(320661423/625000000 : ℝ)|=(320661423/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_s1_2 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2670910231/5000000000 : ℝ)*x 0 + (2565291791/5000000000 : ℝ)*x 1 + (-384438989/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2670910231/5000000000 : ℝ)^5415 ≤ (46151440742469/100000000000000 : ℝ)^4391 := by
    have hnat : (2670910231 : ℕ)^5415*100000000000000^4391 ≤ 46151440742469^4391*5000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2670910231 5000000000 46151440742469 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2565291791/5000000000 : ℝ)^5415 ≤ (5488914036713/12500000000000 : ℝ)^4391 := by
    have hnat : (2565291791 : ℕ)^5415*12500000000000^4391 ≤ 5488914036713^4391*5000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2565291791 5000000000 5488914036713 12500000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (384438989/2500000000 : ℝ)^5415 ≤ (4968623471751/50000000000000 : ℝ)^4391 := by
    have hnat : (384438989 : ℕ)^5415*50000000000000^4391 ≤ 4968623471751^4391*2500000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      384438989 2500000000 4968623471751 50000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2670910231/5000000000 : ℝ), (2565291791/5000000000 : ℝ), (-384438989/2500000000 : ℝ)] ![(46151440742469/100000000000000 : ℝ), (5488914036713/12500000000000 : ℝ), (4968623471751/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2670910231/5000000000 : ℝ)|^5415 ≤ (46151440742469/100000000000000 : ℝ)^4391
        have hw : |(2670910231/5000000000 : ℝ)|=(2670910231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2565291791/5000000000 : ℝ)|^5415 ≤ (5488914036713/12500000000000 : ℝ)^4391
        have hw : |(2565291791/5000000000 : ℝ)|=(2565291791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-384438989/2500000000 : ℝ)|^5415 ≤ (4968623471751/50000000000000 : ℝ)^4391
        have hw : |(-384438989/2500000000 : ℝ)|=(384438989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_s1_3 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4085064961/10000000000 : ℝ)*x 0 + (3593401329/10000000000 : ℝ)*x 1 + (4615734479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4085064961/10000000000 : ℝ)^5415 ≤ (8288365804163/25000000000000 : ℝ)^4391 := by
    have hnat : (4085064961 : ℕ)^5415*25000000000000^4391 ≤ 8288365804163^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4085064961 10000000000 8288365804163 25000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3593401329/10000000000 : ℝ)^5415 ≤ (14151998054143/50000000000000 : ℝ)^4391 := by
    have hnat : (3593401329 : ℕ)^5415*50000000000000^4391 ≤ 14151998054143^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3593401329 10000000000 14151998054143 50000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4615734479/10000000000 : ℝ)^5415 ≤ (770850813149/2000000000000 : ℝ)^4391 := by
    have hnat : (4615734479 : ℕ)^5415*2000000000000^4391 ≤ 770850813149^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4615734479 10000000000 770850813149 2000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4085064961/10000000000 : ℝ), (3593401329/10000000000 : ℝ), (4615734479/10000000000 : ℝ)] ![(8288365804163/25000000000000 : ℝ), (14151998054143/50000000000000 : ℝ), (770850813149/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4085064961/10000000000 : ℝ)|^5415 ≤ (8288365804163/25000000000000 : ℝ)^4391
        have hw : |(4085064961/10000000000 : ℝ)|=(4085064961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3593401329/10000000000 : ℝ)|^5415 ≤ (14151998054143/50000000000000 : ℝ)^4391
        have hw : |(3593401329/10000000000 : ℝ)|=(3593401329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4615734479/10000000000 : ℝ)|^5415 ≤ (770850813149/2000000000000 : ℝ)^4391
        have hw : |(4615734479/10000000000 : ℝ)|=(4615734479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_s1_4 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-340140881/2500000000 : ℝ)*x 0 + (641831763/1250000000 : ℝ)*x 1 + (1093627927/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (340140881/2500000000 : ℝ)^5415 ≤ (2136182500031/25000000000000 : ℝ)^4391 := by
    have hnat : (340140881 : ℕ)^5415*25000000000000^4391 ≤ 2136182500031^4391*2500000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340140881 2500000000 2136182500031 25000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (641831763/1250000000 : ℝ)^5415 ≤ (43954279285213/100000000000000 : ℝ)^4391 := by
    have hnat : (641831763 : ℕ)^5415*100000000000000^4391 ≤ 43954279285213^4391*1250000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      641831763 1250000000 43954279285213 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1093627927/2000000000 : ℝ)^5415 ≤ (23750495354951/50000000000000 : ℝ)^4391 := by
    have hnat : (1093627927 : ℕ)^5415*50000000000000^4391 ≤ 23750495354951^4391*2000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093627927 2000000000 23750495354951 50000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-340140881/2500000000 : ℝ), (641831763/1250000000 : ℝ), (1093627927/2000000000 : ℝ)] ![(2136182500031/25000000000000 : ℝ), (43954279285213/100000000000000 : ℝ), (23750495354951/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-340140881/2500000000 : ℝ)|^5415 ≤ (2136182500031/25000000000000 : ℝ)^4391
        have hw : |(-340140881/2500000000 : ℝ)|=(340140881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(641831763/1250000000 : ℝ)|^5415 ≤ (43954279285213/100000000000000 : ℝ)^4391
        have hw : |(641831763/1250000000 : ℝ)|=(641831763/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1093627927/2000000000 : ℝ)|^5415 ≤ (23750495354951/50000000000000 : ℝ)^4391
        have hw : |(1093627927/2000000000 : ℝ)|=(1093627927/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_s1_5 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5250334741/10000000000 : ℝ)*x 0 + (-1200199339/10000000000 : ℝ)*x 1 + (5468139831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5250334741/10000000000 : ℝ)^5415 ≤ (45178665870741/100000000000000 : ℝ)^4391 := by
    have hnat : (5250334741 : ℕ)^5415*100000000000000^4391 ≤ 45178665870741^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5250334741 10000000000 45178665870741 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1200199339/10000000000 : ℝ)^5415 ≤ (1464068260651/20000000000000 : ℝ)^4391 := by
    have hnat : (1200199339 : ℕ)^5415*20000000000000^4391 ≤ 1464068260651^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1200199339 10000000000 1464068260651 20000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5468139831/10000000000 : ℝ)^5415 ≤ (11875248202397/25000000000000 : ℝ)^4391 := by
    have hnat : (5468139831 : ℕ)^5415*25000000000000^4391 ≤ 11875248202397^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5468139831 10000000000 11875248202397 25000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5250334741/10000000000 : ℝ), (-1200199339/10000000000 : ℝ), (5468139831/10000000000 : ℝ)] ![(45178665870741/100000000000000 : ℝ), (1464068260651/20000000000000 : ℝ), (11875248202397/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5250334741/10000000000 : ℝ)|^5415 ≤ (45178665870741/100000000000000 : ℝ)^4391
        have hw : |(5250334741/10000000000 : ℝ)|=(5250334741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1200199339/10000000000 : ℝ)|^5415 ≤ (1464068260651/20000000000000 : ℝ)^4391
        have hw : |(-1200199339/10000000000 : ℝ)|=(1200199339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5468139831/10000000000 : ℝ)|^5415 ≤ (11875248202397/25000000000000 : ℝ)^4391
        have hw : |(5468139831/10000000000 : ℝ)|=(5468139831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_s1_6 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2625167243/5000000000 : ℝ)*x 0 + (2734070023/5000000000 : ℝ)*x 1 + (-600099697/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2625167243/5000000000 : ℝ)^5415 ≤ (45178663164779/100000000000000 : ℝ)^4391 := by
    have hnat : (2625167243 : ℕ)^5415*100000000000000^4391 ≤ 45178663164779^4391*5000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625167243 5000000000 45178663164779 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2734070023/5000000000 : ℝ)^5415 ≤ (23750497556407/50000000000000 : ℝ)^4391 := by
    have hnat : (2734070023 : ℕ)^5415*50000000000000^4391 ≤ 23750497556407^4391*5000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734070023 5000000000 23750497556407 50000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (600099697/5000000000 : ℝ)^5415 ≤ (1464068343389/20000000000000 : ℝ)^4391 := by
    have hnat : (600099697 : ℕ)^5415*20000000000000^4391 ≤ 1464068343389^4391*5000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      600099697 5000000000 1464068343389 20000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2625167243/5000000000 : ℝ), (2734070023/5000000000 : ℝ), (-600099697/5000000000 : ℝ)] ![(45178663164779/100000000000000 : ℝ), (23750497556407/50000000000000 : ℝ), (1464068343389/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2625167243/5000000000 : ℝ)|^5415 ≤ (45178663164779/100000000000000 : ℝ)^4391
        have hw : |(2625167243/5000000000 : ℝ)|=(2625167243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2734070023/5000000000 : ℝ)|^5415 ≤ (23750497556407/50000000000000 : ℝ)^4391
        have hw : |(2734070023/5000000000 : ℝ)|=(2734070023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-600099697/5000000000 : ℝ)|^5415 ≤ (1464068343389/20000000000000 : ℝ)^4391
        have hw : |(-600099697/5000000000 : ℝ)|=(600099697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_s1_7 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2042790063/5000000000 : ℝ)*x 0 + (575444801/1250000000 : ℝ)*x 1 + (1802884877/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2042790063/5000000000 : ℝ)^5415 ≤ (16579309636731/50000000000000 : ℝ)^4391 := by
    have hnat : (2042790063 : ℕ)^5415*50000000000000^4391 ≤ 16579309636731^4391*5000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2042790063 5000000000 16579309636731 50000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (575444801/1250000000 : ℝ)^5415 ≤ (19208597683457/50000000000000 : ℝ)^4391 := by
    have hnat : (575444801 : ℕ)^5415*50000000000000^4391 ≤ 19208597683457^4391*1250000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      575444801 1250000000 19208597683457 50000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1802884877/5000000000 : ℝ)^5415 ≤ (3553023167823/12500000000000 : ℝ)^4391 := by
    have hnat : (1802884877 : ℕ)^5415*12500000000000^4391 ≤ 3553023167823^4391*5000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1802884877 5000000000 3553023167823 12500000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2042790063/5000000000 : ℝ), (575444801/1250000000 : ℝ), (1802884877/5000000000 : ℝ)] ![(16579309636731/50000000000000 : ℝ), (19208597683457/50000000000000 : ℝ), (3553023167823/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2042790063/5000000000 : ℝ)|^5415 ≤ (16579309636731/50000000000000 : ℝ)^4391
        have hw : |(2042790063/5000000000 : ℝ)|=(2042790063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(575444801/1250000000 : ℝ)|^5415 ≤ (19208597683457/50000000000000 : ℝ)^4391
        have hw : |(575444801/1250000000 : ℝ)|=(575444801/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1802884877/5000000000 : ℝ)|^5415 ≤ (3553023167823/12500000000000 : ℝ)^4391
        have hw : |(1802884877/5000000000 : ℝ)|=(1802884877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1724_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39919953/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (21431/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6441/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9913/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (689/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (21431/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6441/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (21431/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6441/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (21431/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6441/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (21431/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6441/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (21431/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6441/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (21431/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6441/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6441/100000 : ℝ) ^ (5407/1024 : ℝ) ≤ (25699090102389/50000000000000000000 : ℝ) := by
    have hpowers : (6441/100000 : ℝ)^5407 ≤ (25699090102389/50000000000000000000 : ℝ)^1024 := by
      have hnat : (6441 : ℕ)^5407*50000000000000000000^1024 ≤ 25699090102389^1024*100000^5407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6441 100000 25699090102389 50000000000000000000 5407 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6441/100000 : ℝ)) (X := (25699090102389/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5407 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (21431/100000 : ℝ) ^ (5407/1024 : ℝ) ≤ (14678820166829083/50000000000000000000 : ℝ) := by
    have hpowers : (21431/100000 : ℝ)^5407 ≤ (14678820166829083/50000000000000000000 : ℝ)^1024 := by
      have hnat : (21431 : ℕ)^5407*50000000000000000000^1024 ≤ 14678820166829083^1024*100000^5407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21431 100000 14678820166829083 50000000000000000000 5407 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21431/100000 : ℝ)) (X := (14678820166829083/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5407 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000025699090102389/25000000000000000000 : ℝ) ≤ (2000000389359827/2000000000000000 : ℝ) ^ (5407/1024 : ℝ) := by
    have hpowers : (25000025699090102389/25000000000000000000 : ℝ)^1024 ≤ (2000000389359827/2000000000000000 : ℝ)^5407 := by
      have hnat : (25000025699090102389 : ℕ)^1024*2000000000000000^5407 ≤ 2000000389359827^5407*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000025699090102389 25000000000000000000 2000000389359827 2000000000000000 1024 5407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000389359827/2000000000000000 : ℝ)) (X := (25000025699090102389/25000000000000000000 : ℝ)) (by norm_num) 5407 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3125919032453558217/3125000000000000000 : ℝ) ≤ (5000278447072959/5000000000000000 : ℝ) ^ (5407/1024 : ℝ) := by
    have hpowers : (3125919032453558217/3125000000000000000 : ℝ)^1024 ≤ (5000278447072959/5000000000000000 : ℝ)^5407 := by
      have hnat : (3125919032453558217 : ℕ)^1024*5000000000000000^5407 ≤ 5000278447072959^5407*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125919032453558217 3125000000000000000 5000278447072959 5000000000000000 1024 5407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000278447072959/5000000000000000 : ℝ)) (X := (3125919032453558217/3125000000000000000 : ℝ)) (by norm_num) 5407 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014678820166829083/25000000000000000000 : ℝ) ≤ (10001111841492701/10000000000000000 : ℝ) ^ (5407/1024 : ℝ) := by
    have hpowers : (25014678820166829083/25000000000000000000 : ℝ)^1024 ≤ (10001111841492701/10000000000000000 : ℝ)^5407 := by
      have hnat : (25014678820166829083 : ℕ)^1024*10000000000000000^5407 ≤ 10001111841492701^5407*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014678820166829083 25000000000000000000 10001111841492701 10000000000000000 1024 5407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001111841492701/10000000000000000 : ℝ)) (X := (25014678820166829083/25000000000000000000 : ℝ)) (by norm_num) 5407 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(25699090102389/50000000000000000000 : ℝ) ≤ ((37473220087699443761/37475000000000000000 : ℝ)+2*(554947346783/1499000000000000 : ℝ)*(6441/100000 : ℝ))^(5407/1024 : ℝ) := by
    rw [show (37473220087699443761/37475000000000000000 : ℝ)+2*(554947346783/1499000000000000 : ℝ)*(6441/100000 : ℝ)=(2000000389359827/2000000000000000 : ℝ) by norm_num, show 1+2*(25699090102389/50000000000000000000 : ℝ)=(25000025699090102389/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14678820166829083/50000000000000000000 : ℝ)+(25699090102389/50000000000000000000 : ℝ) ≤ ((37473220087699443761/37475000000000000000 : ℝ)+(554947346783/1499000000000000 : ℝ)*((21431/100000 : ℝ)+(6441/100000 : ℝ)))^(5407/1024 : ℝ) := by
    rw [show (37473220087699443761/37475000000000000000 : ℝ)+(554947346783/1499000000000000 : ℝ)*((21431/100000 : ℝ)+(6441/100000 : ℝ))=(5000278447072959/5000000000000000 : ℝ) by norm_num, show 1+(14678820166829083/50000000000000000000 : ℝ)+(25699090102389/50000000000000000000 : ℝ)=(3125919032453558217/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14678820166829083/50000000000000000000 : ℝ) ≤ ((37473220087699443761/37475000000000000000 : ℝ)+2*(554947346783/1499000000000000 : ℝ)*(21431/100000 : ℝ))^(5407/1024 : ℝ) := by
    rw [show (37473220087699443761/37475000000000000000 : ℝ)+2*(554947346783/1499000000000000 : ℝ)*(21431/100000 : ℝ)=(10001111841492701/10000000000000000 : ℝ) by norm_num, show 1+2*(14678820166829083/50000000000000000000 : ℝ)=(25014678820166829083/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (37473220087699443761/37475000000000000000 : ℝ)*(X 1 0+X 2 0)+(554947346783/1499000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5407/1024 : ℝ)) (lo := (6441/100000 : ℝ)) (hi := (21431/100000 : ℝ)) (c := (37473220087699443761/37475000000000000000 : ℝ)) (alpha := (554947346783/1499000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (37473220087699443761/37475000000000000000 : ℝ)*(X 0 1+X 2 1)+(554947346783/1499000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5407/1024 : ℝ)) (lo := (6441/100000 : ℝ)) (hi := (21431/100000 : ℝ)) (c := (37473220087699443761/37475000000000000000 : ℝ)) (alpha := (554947346783/1499000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (37473220087699443761/37475000000000000000 : ℝ)*(X 0 2+X 1 2)+(554947346783/1499000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5407/1024 : ℝ)) (lo := (6441/100000 : ℝ)) (hi := (21431/100000 : ℝ)) (c := (37473220087699443761/37475000000000000000 : ℝ)) (alpha := (554947346783/1499000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-340097709/2500000000 : ℝ)*X 0 0+(218890993/400000000 : ℝ)*X 0 1+(5130583727/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5341821677/10000000000 : ℝ)*X 1 0+(-153775541/1000000000 : ℝ)*X 1 1+(320661423/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2670910231/5000000000 : ℝ)*X 2 0+(2565291791/5000000000 : ℝ)*X 2 1+(-384438989/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4085064961/10000000000 : ℝ)*X 0 0+(3593401329/10000000000 : ℝ)*X 0 1+(4615734479/10000000000 : ℝ)*X 0 2+(4085064961/10000000000 : ℝ)*X 1 0+(3593401329/10000000000 : ℝ)*X 1 1+(4615734479/10000000000 : ℝ)*X 1 2+(4085064961/10000000000 : ℝ)*X 2 0+(3593401329/10000000000 : ℝ)*X 2 1+(4615734479/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-340140881/2500000000 : ℝ)*X 0 0+(641831763/1250000000 : ℝ)*X 0 1+(1093627927/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5250334741/10000000000 : ℝ)*X 1 0+(-1200199339/10000000000 : ℝ)*X 1 1+(5468139831/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2625167243/5000000000 : ℝ)*X 2 0+(2734070023/5000000000 : ℝ)*X 2 1+(-600099697/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2042790063/5000000000 : ℝ)*X 0 0+(575444801/1250000000 : ℝ)*X 0 1+(1802884877/5000000000 : ℝ)*X 0 2+(2042790063/5000000000 : ℝ)*X 1 0+(575444801/1250000000 : ℝ)*X 1 1+(1802884877/5000000000 : ℝ)*X 1 2+(2042790063/5000000000 : ℝ)*X 2 0+(575444801/1250000000 : ℝ)*X 2 1+(1802884877/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3693569559906594868629438699/468437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1034661403/100000000000000 : ℝ)*(base19) + (9702287/6250000000000 : ℝ)*(base23) + (99052369/50000000000000 : ℝ)*(lower2) + (14464111/10000000000000 : ℝ)*(lower4) + (4473509/12500000000000 : ℝ)*(lower5) + (976197608564547/50000000000000 : ℝ)*(major0) + (976197608564547/50000000000000 : ℝ)*(major1) + (976197608564547/50000000000000 : ℝ)*(major2) + (1463314246238303/50000000000000 : ℝ)*(sp0) + (365829258591863/12500000000000 : ℝ)*(sp1) + (1463314155359351/50000000000000 : ℝ)*(sp2) + (978155068032817/100000000000000 : ℝ)*(sp3) + (6610919701/100000000000000 : ℝ)*(sp4) + (1659360253/25000000000000 : ℝ)*(sp6) + (978155068032817/100000000000000 : ℝ)*(f.failure) + (1463317551698153/50000000000000 : ℝ)*(f.sum) + (73980176159863/18737500000000000000000000000 : ℝ)*base65 + (328137376806216267/1873750000000000000000000000000000 : ℝ)*base67 + (1957781985422466267/1873750000000000000000000000000000 : ℝ)*base69 + (16367477666178716267/1873750000000000000000000000000000 : ℝ)*base71 + (24567009821813/18737500000000000000000000000 : ℝ)*base73 + (4749117525516216267/1873750000000000000000000000000000 : ℝ)*base75 + (12225916521363716267/1873750000000000000000000000000000 : ℝ)*base77 + (1381041651616283733/1873750000000000000000000000000000 : ℝ)*base80 + (378806375707/1171093750000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (22902399/2000000000000000000000 : ℝ)*base90 + (22902399/2000000000000000000000 : ℝ)*base92 + (22902399/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (535510590409220984996237127/46843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (454120667/50000000000000 : ℝ)*(base19) + (1256641411/100000000000000 : ℝ)*(base23) + (1105057/500000000000 : ℝ)*(upper3) + (26812571/12500000000000 : ℝ)*(lower4) + (9708087/10000000000000 : ℝ)*(upper5) + (100021047309269/5000000000000 : ℝ)*(major0) + (100021047309269/5000000000000 : ℝ)*(major1) + (100021047309269/5000000000000 : ℝ)*(major2) + (738731189/10000000000000 : ℝ)*(sp1) + (2458744173/20000000000000 : ℝ)*(sp2) + (374828178555859/12500000000000 : ℝ)*(sp4) + (187413570805853/6250000000000 : ℝ)*(sp5) + (749652969521149/25000000000000 : ℝ)*(sp6) + (125277010357789/12500000000000 : ℝ)*(sp7) + (125277010357789/12500000000000 : ℝ)*(f.failure) + (374828178555859/12500000000000 : ℝ)*(f.sum) + (17841080577587/3747500000000000000000000000 : ℝ)*base65 + (225658148921804291/187375000000000000000000000000000 : ℝ)*base68 + (890502308298804291/187375000000000000000000000000000 : ℝ)*base70 + (827128145456445709/187375000000000000000000000000000 : ℝ)*base71 + (16583114755937/3747500000000000000000000000 : ℝ)*base73 + (1699256520637804291/187375000000000000000000000000000 : ℝ)*base76 + (1058436333220054291/187375000000000000000000000000000 : ℝ)*base78 + (443464190152054291/187375000000000000000000000000000 : ℝ)*base80 + (11416216302837/3747500000000000000000000000 : ℝ)*base81 + (63917/250000000000000000000 : ℝ)*base89 + (63917/250000000000000000000 : ℝ)*base91 + (63917/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1724_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39919953/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (21431/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6441/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9913/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (689/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1724_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1724_s2_0 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1362975913/10000000000 : ℝ)*x 0 + (2730780533/5000000000 : ℝ)*x 1 + (2569779111/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1362975913/10000000000 : ℝ)^5415 ≤ (8563417518053/100000000000000 : ℝ)^4391 := by
    have hnat : (1362975913 : ℕ)^5415*100000000000000^4391 ≤ 8563417518053^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1362975913 10000000000 8563417518053 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2730780533/5000000000 : ℝ)^5415 ≤ (9486105300111/20000000000000 : ℝ)^4391 := by
    have hnat : (2730780533 : ℕ)^5415*20000000000000^4391 ≤ 9486105300111^4391*5000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2730780533 5000000000 9486105300111 20000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2569779111/5000000000 : ℝ)^5415 ≤ (2200302798607/5000000000000 : ℝ)^4391 := by
    have hnat : (2569779111 : ℕ)^5415*5000000000000^4391 ≤ 2200302798607^4391*5000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2569779111 5000000000 2200302798607 5000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1362975913/10000000000 : ℝ), (2730780533/5000000000 : ℝ), (2569779111/5000000000 : ℝ)] ![(8563417518053/100000000000000 : ℝ), (9486105300111/20000000000000 : ℝ), (2200302798607/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1362975913/10000000000 : ℝ)|^5415 ≤ (8563417518053/100000000000000 : ℝ)^4391
        have hw : |(-1362975913/10000000000 : ℝ)|=(1362975913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2730780533/5000000000 : ℝ)|^5415 ≤ (9486105300111/20000000000000 : ℝ)^4391
        have hw : |(2730780533/5000000000 : ℝ)|=(2730780533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2569779111/5000000000 : ℝ)|^5415 ≤ (2200302798607/5000000000000 : ℝ)^4391
        have hw : |(2569779111/5000000000 : ℝ)|=(2569779111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_s2_1 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (533890021/1000000000 : ℝ)*x 0 + (-305953327/2000000000 : ℝ)*x 1 + (642444751/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (533890021/1000000000 : ℝ)^5415 ≤ (46120329049697/100000000000000 : ℝ)^4391 := by
    have hnat : (533890021 : ℕ)^5415*100000000000000^4391 ≤ 46120329049697^4391*1000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533890021 1000000000 46120329049697 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (305953327/2000000000 : ℝ)^5415 ≤ (4936808610173/50000000000000 : ℝ)^4391 := by
    have hnat : (305953327 : ℕ)^5415*50000000000000^4391 ≤ 4936808610173^4391*2000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      305953327 2000000000 4936808610173 50000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (642444751/1250000000 : ℝ)^5415 ≤ (44006053712519/100000000000000 : ℝ)^4391 := by
    have hnat : (642444751 : ℕ)^5415*100000000000000^4391 ≤ 44006053712519^4391*1250000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      642444751 1250000000 44006053712519 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(533890021/1000000000 : ℝ), (-305953327/2000000000 : ℝ), (642444751/1250000000 : ℝ)] ![(46120329049697/100000000000000 : ℝ), (4936808610173/50000000000000 : ℝ), (44006053712519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(533890021/1000000000 : ℝ)|^5415 ≤ (46120329049697/100000000000000 : ℝ)^4391
        have hw : |(533890021/1000000000 : ℝ)|=(533890021/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-305953327/2000000000 : ℝ)|^5415 ≤ (4936808610173/50000000000000 : ℝ)^4391
        have hw : |(-305953327/2000000000 : ℝ)|=(305953327/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(642444751/1250000000 : ℝ)|^5415 ≤ (44006053712519/100000000000000 : ℝ)^4391
        have hw : |(642444751/1250000000 : ℝ)|=(642444751/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_s2_2 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5338899867/10000000000 : ℝ)*x 0 + (1027911691/2000000000 : ℝ)*x 1 + (-764883251/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5338899867/10000000000 : ℝ)^5415 ≤ (46120325395687/100000000000000 : ℝ)^4391 := by
    have hnat : (5338899867 : ℕ)^5415*100000000000000^4391 ≤ 46120325395687^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5338899867 10000000000 46120325395687 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1027911691/2000000000 : ℝ)^5415 ≤ (2200302921619/5000000000000 : ℝ)^4391 := by
    have hnat : (1027911691 : ℕ)^5415*5000000000000^4391 ≤ 2200302921619^4391*2000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027911691 2000000000 2200302921619 5000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (764883251/5000000000 : ℝ)^5415 ≤ (2468404040433/25000000000000 : ℝ)^4391 := by
    have hnat : (764883251 : ℕ)^5415*25000000000000^4391 ≤ 2468404040433^4391*5000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      764883251 5000000000 2468404040433 25000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5338899867/10000000000 : ℝ), (1027911691/2000000000 : ℝ), (-764883251/5000000000 : ℝ)] ![(46120325395687/100000000000000 : ℝ), (2200302921619/5000000000000 : ℝ), (2468404040433/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5338899867/10000000000 : ℝ)|^5415 ≤ (46120325395687/100000000000000 : ℝ)^4391
        have hw : |(5338899867/10000000000 : ℝ)|=(5338899867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1027911691/2000000000 : ℝ)|^5415 ≤ (2200302921619/5000000000000 : ℝ)^4391
        have hw : |(1027911691/2000000000 : ℝ)|=(1027911691/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-764883251/5000000000 : ℝ)|^5415 ≤ (2468404040433/25000000000000 : ℝ)^4391
        have hw : |(-764883251/5000000000 : ℝ)|=(764883251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_s2_3 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2043538339/5000000000 : ℝ)*x 0 + (3622680391/10000000000 : ℝ)*x 1 + (2293056139/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2043538339/5000000000 : ℝ)^5415 ≤ (33173598455157/100000000000000 : ℝ)^4391 := by
    have hnat : (2043538339 : ℕ)^5415*100000000000000^4391 ≤ 33173598455157^4391*5000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2043538339 5000000000 33173598455157 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3622680391/10000000000 : ℝ)^5415 ≤ (28588668779149/100000000000000 : ℝ)^4391 := by
    have hnat : (3622680391 : ℕ)^5415*100000000000000^4391 ≤ 28588668779149^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3622680391 10000000000 28588668779149 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2293056139/5000000000 : ℝ)^5415 ≤ (38237732753209/100000000000000 : ℝ)^4391 := by
    have hnat : (2293056139 : ℕ)^5415*100000000000000^4391 ≤ 38237732753209^4391*5000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2293056139 5000000000 38237732753209 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2043538339/5000000000 : ℝ), (3622680391/10000000000 : ℝ), (2293056139/5000000000 : ℝ)] ![(33173598455157/100000000000000 : ℝ), (28588668779149/100000000000000 : ℝ), (38237732753209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2043538339/5000000000 : ℝ)|^5415 ≤ (33173598455157/100000000000000 : ℝ)^4391
        have hw : |(2043538339/5000000000 : ℝ)|=(2043538339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3622680391/10000000000 : ℝ)|^5415 ≤ (28588668779149/100000000000000 : ℝ)^4391
        have hw : |(3622680391/10000000000 : ℝ)|=(3622680391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2293056139/5000000000 : ℝ)|^5415 ≤ (38237732753209/100000000000000 : ℝ)^4391
        have hw : |(2293056139/5000000000 : ℝ)|=(2293056139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_s2_4 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-85195021/625000000 : ℝ)*x 0 + (642896791/1250000000 : ℝ)*x 1 + (682236347/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (85195021/625000000 : ℝ)^5415 ≤ (856453653249/10000000000000 : ℝ)^4391 := by
    have hnat : (85195021 : ℕ)^5415*10000000000000^4391 ≤ 856453653249^4391*625000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85195021 625000000 856453653249 10000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (642896791/1250000000 : ℝ)^5415 ≤ (44044241469747/100000000000000 : ℝ)^4391 := by
    have hnat : (642896791 : ℕ)^5415*100000000000000^4391 ≤ 44044241469747^4391*1250000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      642896791 1250000000 44044241469747 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (682236347/1250000000 : ℝ)^5415 ≤ (23695610989331/50000000000000 : ℝ)^4391 := by
    have hnat : (682236347 : ℕ)^5415*50000000000000^4391 ≤ 23695610989331^4391*1250000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682236347 1250000000 23695610989331 50000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-85195021/625000000 : ℝ), (642896791/1250000000 : ℝ), (682236347/1250000000 : ℝ)] ![(856453653249/10000000000000 : ℝ), (44044241469747/100000000000000 : ℝ), (23695610989331/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-85195021/625000000 : ℝ)|^5415 ≤ (856453653249/10000000000000 : ℝ)^4391
        have hw : |(-85195021/625000000 : ℝ)|=(85195021/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(642896791/1250000000 : ℝ)|^5415 ≤ (44044241469747/100000000000000 : ℝ)^4391
        have hw : |(642896791/1250000000 : ℝ)|=(642896791/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(682236347/1250000000 : ℝ)|^5415 ≤ (23695610989331/50000000000000 : ℝ)^4391
        have hw : |(682236347/1250000000 : ℝ)|=(682236347/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_s2_5 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2626353713/5000000000 : ℝ)*x 0 + (-242286691/2000000000 : ℝ)*x 1 + (10659943/19531250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2626353713/5000000000 : ℝ)^5415 ≤ (22601922607009/50000000000000 : ℝ)^4391 := by
    have hnat : (2626353713 : ℕ)^5415*50000000000000^4391 ≤ 22601922607009^4391*5000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626353713 5000000000 22601922607009 50000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (242286691/2000000000 : ℝ)^5415 ≤ (740493236691/10000000000000 : ℝ)^4391 := by
    have hnat : (242286691 : ℕ)^5415*10000000000000^4391 ≤ 740493236691^4391*2000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      242286691 2000000000 740493236691 10000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10659943/19531250 : ℝ)^5415 ≤ (23695611203491/50000000000000 : ℝ)^4391 := by
    have hnat : (10659943 : ℕ)^5415*50000000000000^4391 ≤ 23695611203491^4391*19531250^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10659943 19531250 23695611203491 50000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2626353713/5000000000 : ℝ), (-242286691/2000000000 : ℝ), (10659943/19531250 : ℝ)] ![(22601922607009/50000000000000 : ℝ), (740493236691/10000000000000 : ℝ), (23695611203491/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2626353713/5000000000 : ℝ)|^5415 ≤ (22601922607009/50000000000000 : ℝ)^4391
        have hw : |(2626353713/5000000000 : ℝ)|=(2626353713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-242286691/2000000000 : ℝ)|^5415 ≤ (740493236691/10000000000000 : ℝ)^4391
        have hw : |(-242286691/2000000000 : ℝ)|=(242286691/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(10659943/19531250 : ℝ)|^5415 ≤ (23695611203491/50000000000000 : ℝ)^4391
        have hw : |(10659943/19531250 : ℝ)|=(10659943/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_s2_6 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050541483/2000000000 : ℝ)*x 0 + (5457890833/10000000000 : ℝ)*x 1 + (-605716723/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050541483/2000000000 : ℝ)^5415 ≤ (22601922548639/50000000000000 : ℝ)^4391 := by
    have hnat : (1050541483 : ℕ)^5415*50000000000000^4391 ≤ 22601922548639^4391*2000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050541483 2000000000 22601922548639 50000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5457890833/10000000000 : ℝ)^5415 ≤ (23695611294509/50000000000000 : ℝ)^4391 := by
    have hnat : (5457890833 : ℕ)^5415*50000000000000^4391 ≤ 23695611294509^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457890833 10000000000 23695611294509 50000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (605716723/5000000000 : ℝ)^5415 ≤ (1851233074767/25000000000000 : ℝ)^4391 := by
    have hnat : (605716723 : ℕ)^5415*25000000000000^4391 ≤ 1851233074767^4391*5000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      605716723 5000000000 1851233074767 25000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050541483/2000000000 : ℝ), (5457890833/10000000000 : ℝ), (-605716723/5000000000 : ℝ)] ![(22601922548639/50000000000000 : ℝ), (23695611294509/50000000000000 : ℝ), (1851233074767/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050541483/2000000000 : ℝ)|^5415 ≤ (22601922548639/50000000000000 : ℝ)^4391
        have hw : |(1050541483/2000000000 : ℝ)|=(1050541483/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5457890833/10000000000 : ℝ)|^5415 ≤ (23695611294509/50000000000000 : ℝ)^4391
        have hw : |(5457890833/10000000000 : ℝ)|=(5457890833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-605716723/5000000000 : ℝ)|^5415 ≤ (1851233074767/25000000000000 : ℝ)^4391
        have hw : |(-605716723/5000000000 : ℝ)|=(605716723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_s2_7 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4087507997/10000000000 : ℝ)*x 0 + (71488939/156250000 : ℝ)*x 1 + (3633661629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4087507997/10000000000 : ℝ)^5415 ≤ (16588957910023/50000000000000 : ℝ)^4391 := by
    have hnat : (4087507997 : ℕ)^5415*50000000000000^4391 ≤ 16588957910023^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4087507997 10000000000 16588957910023 50000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (71488939/156250000 : ℝ)^5415 ≤ (19063254509021/50000000000000 : ℝ)^4391 := by
    have hnat : (71488939 : ℕ)^5415*50000000000000^4391 ≤ 19063254509021^4391*156250000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71488939 156250000 19063254509021 50000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3633661629/10000000000 : ℝ)^5415 ≤ (28695575152341/100000000000000 : ℝ)^4391 := by
    have hnat : (3633661629 : ℕ)^5415*100000000000000^4391 ≤ 28695575152341^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3633661629 10000000000 28695575152341 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4087507997/10000000000 : ℝ), (71488939/156250000 : ℝ), (3633661629/10000000000 : ℝ)] ![(16588957910023/50000000000000 : ℝ), (19063254509021/50000000000000 : ℝ), (28695575152341/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4087507997/10000000000 : ℝ)|^5415 ≤ (16588957910023/50000000000000 : ℝ)^4391
        have hw : |(4087507997/10000000000 : ℝ)|=(4087507997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(71488939/156250000 : ℝ)|^5415 ≤ (19063254509021/50000000000000 : ℝ)^4391
        have hw : |(71488939/156250000 : ℝ)|=(71488939/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3633661629/10000000000 : ℝ)|^5415 ≤ (28695575152341/100000000000000 : ℝ)^4391
        have hw : |(3633661629/10000000000 : ℝ)|=(3633661629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1724_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39919953/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (689/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9913/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10109/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16999/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (689/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9913/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (689/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9913/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (689/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9913/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (689/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9913/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (689/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9913/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (689/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9913/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9913/100000 : ℝ) ^ (5407/1024 : ℝ) ≤ (250413933282433/50000000000000000000 : ℝ) := by
    have hpowers : (9913/100000 : ℝ)^5407 ≤ (250413933282433/50000000000000000000 : ℝ)^1024 := by
      have hnat : (9913 : ℕ)^5407*50000000000000000000^1024 ≤ 250413933282433^1024*100000^5407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9913 100000 250413933282433 50000000000000000000 5407 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9913/100000 : ℝ)) (X := (250413933282433/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5407 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (689/4000 : ℝ) ^ (5407/1024 : ℝ) ≤ (1157768922376241/12500000000000000000 : ℝ) := by
    have hpowers : (689/4000 : ℝ)^5407 ≤ (1157768922376241/12500000000000000000 : ℝ)^1024 := by
      have hnat : (689 : ℕ)^5407*12500000000000000000^1024 ≤ 1157768922376241^1024*4000^5407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        689 4000 1157768922376241 12500000000000000000 5407 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (689/4000 : ℝ)) (X := (1157768922376241/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 5407 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000250413933282433/25000000000000000000 : ℝ) ≤ (5000009484846557/5000000000000000 : ℝ) ^ (5407/1024 : ℝ) := by
    have hpowers : (25000250413933282433/25000000000000000000 : ℝ)^1024 ≤ (5000009484846557/5000000000000000 : ℝ)^5407 := by
      have hnat : (25000250413933282433 : ℕ)^1024*5000000000000000^5407 ≤ 5000009484846557^5407*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000250413933282433 25000000000000000000 5000009484846557 5000000000000000 1024 5407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000009484846557/5000000000000000 : ℝ)) (X := (25000250413933282433/25000000000000000000 : ℝ)) (by norm_num) 5407 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50004881489622787397/50000000000000000000 : ℝ) ≤ (2500046222004701/2500000000000000 : ℝ) ^ (5407/1024 : ℝ) := by
    have hpowers : (50004881489622787397/50000000000000000000 : ℝ)^1024 ≤ (2500046222004701/2500000000000000 : ℝ)^5407 := by
      have hnat : (50004881489622787397 : ℕ)^1024*2500000000000000^5407 ≤ 2500046222004701^5407*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004881489622787397 50000000000000000000 2500046222004701 2500000000000000 1024 5407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500046222004701/2500000000000000 : ℝ)) (X := (50004881489622787397/50000000000000000000 : ℝ)) (by norm_num) 5407 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6251157768922376241/6250000000000000000 : ℝ) ≤ (5000175403172247/5000000000000000 : ℝ) ^ (5407/1024 : ℝ) := by
    have hpowers : (6251157768922376241/6250000000000000000 : ℝ)^1024 ≤ (5000175403172247/5000000000000000 : ℝ)^5407 := by
      have hnat : (6251157768922376241 : ℕ)^1024*5000000000000000^5407 ≤ 5000175403172247^5407*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251157768922376241 6250000000000000000 5000175403172247 5000000000000000 1024 5407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000175403172247/5000000000000000 : ℝ)) (X := (6251157768922376241/6250000000000000000 : ℝ)) (by norm_num) 5407 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(250413933282433/50000000000000000000 : ℝ) ≤ ((18279212302417729907/18280000000000000000 : ℝ)+2*(16591832569/73120000000000 : ℝ)*(9913/100000 : ℝ))^(5407/1024 : ℝ) := by
    rw [show (18279212302417729907/18280000000000000000 : ℝ)+2*(16591832569/73120000000000 : ℝ)*(9913/100000 : ℝ)=(5000009484846557/5000000000000000 : ℝ) by norm_num, show 1+2*(250413933282433/50000000000000000000 : ℝ)=(25000250413933282433/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1157768922376241/12500000000000000000 : ℝ)+(250413933282433/50000000000000000000 : ℝ) ≤ ((18279212302417729907/18280000000000000000 : ℝ)+(16591832569/73120000000000 : ℝ)*((689/4000 : ℝ)+(9913/100000 : ℝ)))^(5407/1024 : ℝ) := by
    rw [show (18279212302417729907/18280000000000000000 : ℝ)+(16591832569/73120000000000 : ℝ)*((689/4000 : ℝ)+(9913/100000 : ℝ))=(2500046222004701/2500000000000000 : ℝ) by norm_num, show 1+(1157768922376241/12500000000000000000 : ℝ)+(250413933282433/50000000000000000000 : ℝ)=(50004881489622787397/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1157768922376241/12500000000000000000 : ℝ) ≤ ((18279212302417729907/18280000000000000000 : ℝ)+2*(16591832569/73120000000000 : ℝ)*(689/4000 : ℝ))^(5407/1024 : ℝ) := by
    rw [show (18279212302417729907/18280000000000000000 : ℝ)+2*(16591832569/73120000000000 : ℝ)*(689/4000 : ℝ)=(5000175403172247/5000000000000000 : ℝ) by norm_num, show 1+2*(1157768922376241/12500000000000000000 : ℝ)=(6251157768922376241/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18279212302417729907/18280000000000000000 : ℝ)*(X 1 0+X 2 0)+(16591832569/73120000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5407/1024 : ℝ)) (lo := (9913/100000 : ℝ)) (hi := (689/4000 : ℝ)) (c := (18279212302417729907/18280000000000000000 : ℝ)) (alpha := (16591832569/73120000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18279212302417729907/18280000000000000000 : ℝ)*(X 0 1+X 2 1)+(16591832569/73120000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5407/1024 : ℝ)) (lo := (9913/100000 : ℝ)) (hi := (689/4000 : ℝ)) (c := (18279212302417729907/18280000000000000000 : ℝ)) (alpha := (16591832569/73120000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18279212302417729907/18280000000000000000 : ℝ)*(X 0 2+X 1 2)+(16591832569/73120000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5407/1024 : ℝ)) (lo := (9913/100000 : ℝ)) (hi := (689/4000 : ℝ)) (c := (18279212302417729907/18280000000000000000 : ℝ)) (alpha := (16591832569/73120000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1362975913/10000000000 : ℝ)*X 0 0+(2730780533/5000000000 : ℝ)*X 0 1+(2569779111/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((533890021/1000000000 : ℝ)*X 1 0+(-305953327/2000000000 : ℝ)*X 1 1+(642444751/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5338899867/10000000000 : ℝ)*X 2 0+(1027911691/2000000000 : ℝ)*X 2 1+(-764883251/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2043538339/5000000000 : ℝ)*X 0 0+(3622680391/10000000000 : ℝ)*X 0 1+(2293056139/5000000000 : ℝ)*X 0 2+(2043538339/5000000000 : ℝ)*X 1 0+(3622680391/10000000000 : ℝ)*X 1 1+(2293056139/5000000000 : ℝ)*X 1 2+(2043538339/5000000000 : ℝ)*X 2 0+(3622680391/10000000000 : ℝ)*X 2 1+(2293056139/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-85195021/625000000 : ℝ)*X 0 0+(642896791/1250000000 : ℝ)*X 0 1+(682236347/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2626353713/5000000000 : ℝ)*X 1 0+(-242286691/2000000000 : ℝ)*X 1 1+(10659943/19531250 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1050541483/2000000000 : ℝ)*X 2 0+(5457890833/10000000000 : ℝ)*X 2 1+(-605716723/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4087507997/10000000000 : ℝ)*X 0 0+(71488939/156250000 : ℝ)*X 0 1+(3633661629/10000000000 : ℝ)*X 0 2+(4087507997/10000000000 : ℝ)*X 1 0+(71488939/156250000 : ℝ)*X 1 1+(3633661629/10000000000 : ℝ)*X 1 2+(4087507997/10000000000 : ℝ)*X 2 0+(71488939/156250000 : ℝ)*X 2 1+(3633661629/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2018354837401033396033636839/457000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (79147647/50000000000000 : ℝ)*(base19) + (41640959/100000000000000 : ℝ)*(lower2) + (3962323/100000000000000 : ℝ)*(upper3) + (3182473/5000000000000 : ℝ)*(lower4) + (96728137/100000000000000 : ℝ)*(upper5) + (1035879786387359/50000000000000 : ℝ)*(major0) + (1035879786387359/50000000000000 : ℝ)*(major1) + (1035879786387359/50000000000000 : ℝ)*(major2) + (1552780936888677/50000000000000 : ℝ)*(sp0) + (1552780960105013/50000000000000 : ℝ)*(sp1) + (77639051962633/2500000000000 : ℝ)*(sp2) + (259489225085391/25000000000000 : ℝ)*(sp3) + (40945593/20000000000000 : ℝ)*(sp4) + (19484829/100000000000000 : ℝ)*(sp7) + (129744614978299/12500000000000 : ℝ)*(f.failure) + (77639051962633/2500000000000 : ℝ)*(f.sum) + (8603222379093/1828000000000000000000000000 : ℝ)*base66 + (1060947289529204387/914000000000000000000000000000000 : ℝ)*base68 + (9281017853004795613/914000000000000000000000000000000 : ℝ)*base69 + (5257269698451204387/914000000000000000000000000000000 : ℝ)*base72 + (9889310197873/1828000000000000000000000000 : ℝ)*base74 + (1549187692084795613/914000000000000000000000000000000 : ℝ)*base75 + (1099745998171204387/914000000000000000000000000000000 : ℝ)*base78 + (5080626715953204387/914000000000000000000000000000000 : ℝ)*base80 + (3782561387267/1828000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (2900053/250000000000000000000 : ℝ)*base90 + (2900053/250000000000000000000 : ℝ)*base92 + (2900053/250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3060638338726706646002955753/457000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (559607777/50000000000000 : ℝ)*(base19) + (597870297/50000000000000 : ℝ)*(base23) + (187314879/100000000000000 : ℝ)*(upper3) + (6663123/20000000000000 : ℝ)*(lower4) + (76951457/50000000000000 : ℝ)*(upper5) + (2119725161892793/100000000000000 : ℝ)*(major0) + (2119725161892793/100000000000000 : ℝ)*(major1) + (2119725161892793/100000000000000 : ℝ)*(major2) + (10484464259/100000000000000 : ℝ)*(sp1) + (2922079339/25000000000000 : ℝ)*(sp2) + (1588731148076711/50000000000000 : ℝ)*(sp4) + (317745069247361/10000000000000 : ℝ)*(sp5) + (198590588255967/6250000000000 : ℝ)*(sp6) + (16593559443607/1562500000000 : ℝ)*(sp7) + (16593559443607/1562500000000 : ℝ)*(f.failure) + (1588731148076711/50000000000000 : ℝ)*(f.sum) + (6086661828367/3656000000000000000000000000 : ℝ)*base66 + (2498308476103889749/1828000000000000000000000000000000 : ℝ)*base68 + (750958081223889749/1828000000000000000000000000000000 : ℝ)*base70 + (12608694748399889749/1828000000000000000000000000000000 : ℝ)*base72 + (12146195042409/3656000000000000000000000000 : ℝ)*base73 + (11828576587303889749/1828000000000000000000000000000000 : ℝ)*base76 + (5654789495895889749/1828000000000000000000000000000000 : ℝ)*base78 + (7513825315176110251/1828000000000000000000000000000000 : ℝ)*base79 + (9974202825009/3656000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (222029/31250000000000000000 : ℝ)*base90 + (222029/31250000000000000000 : ℝ)*base92 + (222029/31250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1724_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39919953/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (689/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9913/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10109/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16999/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1724_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1724_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39919953/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10109/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16999/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1724_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1724_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1724_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39919953/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10109/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16999/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1724_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
