-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1426_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:52:53.900791+00:00
-- url     : https://prove2.me/submissions/d21dc4f9-824d-4058-90a6-5a9738c57e09

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
theorem support_rectangle_w1426_s0_0 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1760513519/10000000000 : ℝ)*x 0 + (596141997/1000000000 : ℝ)*x 1 + (603818931/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1760513519/10000000000 : ℝ)^2193 ≤ (2074463223159/20000000000000 : ℝ)^1681 := by
    have hnat : (1760513519 : ℕ)^2193*20000000000000^1681 ≤ 2074463223159^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1760513519 10000000000 2074463223159 20000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (596141997/1000000000 : ℝ)^2193 ≤ (3182772641099/6250000000000 : ℝ)^1681 := by
    have hnat : (596141997 : ℕ)^2193*6250000000000^1681 ≤ 3182772641099^1681*1000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      596141997 1000000000 3182772641099 6250000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (603818931/1250000000 : ℝ)^2193 ≤ (7740664320749/20000000000000 : ℝ)^1681 := by
    have hnat : (603818931 : ℕ)^2193*20000000000000^1681 ≤ 7740664320749^1681*1250000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      603818931 1250000000 7740664320749 20000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1760513519/10000000000 : ℝ), (596141997/1000000000 : ℝ), (603818931/1250000000 : ℝ)] ![(2074463223159/20000000000000 : ℝ), (3182772641099/6250000000000 : ℝ), (7740664320749/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1760513519/10000000000 : ℝ)|^2193 ≤ (2074463223159/20000000000000 : ℝ)^1681
        have hw : |(-1760513519/10000000000 : ℝ)|=(1760513519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(596141997/1000000000 : ℝ)|^2193 ≤ (3182772641099/6250000000000 : ℝ)^1681
        have hw : |(596141997/1000000000 : ℝ)|=(596141997/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(603818931/1250000000 : ℝ)|^2193 ≤ (7740664320749/20000000000000 : ℝ)^1681
        have hw : |(603818931/1250000000 : ℝ)|=(603818931/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s0_1 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5492432901/10000000000 : ℝ)*x 0 + (-2399470197/10000000000 : ℝ)*x 1 + (4830551873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5492432901/10000000000 : ℝ)^2193 ≤ (2860106269973/6250000000000 : ℝ)^1681 := by
    have hnat : (5492432901 : ℕ)^2193*6250000000000^1681 ≤ 2860106269973^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5492432901 10000000000 2860106269973 6250000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2399470197/10000000000 : ℝ)^2193 ≤ (15534973627229/100000000000000 : ℝ)^1681 := by
    have hnat : (2399470197 : ℕ)^2193*100000000000000^1681 ≤ 15534973627229^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2399470197 10000000000 15534973627229 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4830551873/10000000000 : ℝ)^2193 ≤ (38703326046081/100000000000000 : ℝ)^1681 := by
    have hnat : (4830551873 : ℕ)^2193*100000000000000^1681 ≤ 38703326046081^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4830551873 10000000000 38703326046081 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5492432901/10000000000 : ℝ), (-2399470197/10000000000 : ℝ), (4830551873/10000000000 : ℝ)] ![(2860106269973/6250000000000 : ℝ), (15534973627229/100000000000000 : ℝ), (38703326046081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5492432901/10000000000 : ℝ)|^2193 ≤ (2860106269973/6250000000000 : ℝ)^1681
        have hw : |(5492432901/10000000000 : ℝ)|=(5492432901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2399470197/10000000000 : ℝ)|^2193 ≤ (15534973627229/100000000000000 : ℝ)^1681
        have hw : |(-2399470197/10000000000 : ℝ)|=(2399470197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4830551873/10000000000 : ℝ)|^2193 ≤ (38703326046081/100000000000000 : ℝ)^1681
        have hw : |(4830551873/10000000000 : ℝ)|=(4830551873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s0_2 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2746216671/5000000000 : ℝ)*x 0 + (301909481/625000000 : ℝ)*x 1 + (-2399469849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2746216671/5000000000 : ℝ)^2193 ≤ (45761705113003/100000000000000 : ℝ)^1681 := by
    have hnat : (2746216671 : ℕ)^2193*100000000000000^1681 ≤ 45761705113003^1681*5000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2746216671 5000000000 45761705113003 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (301909481/625000000 : ℝ)^2193 ≤ (38703324195979/100000000000000 : ℝ)^1681 := by
    have hnat : (301909481 : ℕ)^2193*100000000000000^1681 ≤ 38703324195979^1681*625000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      301909481 625000000 38703324195979 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2399469849/10000000000 : ℝ)^2193 ≤ (194187133599/1250000000000 : ℝ)^1681 := by
    have hnat : (2399469849 : ℕ)^2193*1250000000000^1681 ≤ 194187133599^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2399469849 10000000000 194187133599 1250000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2746216671/5000000000 : ℝ), (301909481/625000000 : ℝ), (-2399469849/10000000000 : ℝ)] ![(45761705113003/100000000000000 : ℝ), (38703324195979/100000000000000 : ℝ), (194187133599/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2746216671/5000000000 : ℝ)|^2193 ≤ (45761705113003/100000000000000 : ℝ)^1681
        have hw : |(2746216671/5000000000 : ℝ)|=(2746216671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(301909481/625000000 : ℝ)|^2193 ≤ (38703324195979/100000000000000 : ℝ)^1681
        have hw : |(301909481/625000000 : ℝ)|=(301909481/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2399469849/10000000000 : ℝ)|^2193 ≤ (194187133599/1250000000000 : ℝ)^1681
        have hw : |(-2399469849/10000000000 : ℝ)|=(2399469849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s0_3 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4166431221/10000000000 : ℝ)*x 0 + (3103432007/10000000000 : ℝ)*x 1 + (5547190673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4166431221/10000000000 : ℝ)^2193 ≤ (15955917265521/50000000000000 : ℝ)^1681 := by
    have hnat : (4166431221 : ℕ)^2193*50000000000000^1681 ≤ 15955917265521^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4166431221 10000000000 15955917265521 50000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3103432007/10000000000 : ℝ)^2193 ≤ (2716296959163/12500000000000 : ℝ)^1681 := by
    have hnat : (3103432007 : ℕ)^2193*12500000000000^1681 ≤ 2716296959163^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3103432007 10000000000 2716296959163 12500000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5547190673/10000000000 : ℝ)^2193 ≤ (46357789786211/100000000000000 : ℝ)^1681 := by
    have hnat : (5547190673 : ℕ)^2193*100000000000000^1681 ≤ 46357789786211^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5547190673 10000000000 46357789786211 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4166431221/10000000000 : ℝ), (3103432007/10000000000 : ℝ), (5547190673/10000000000 : ℝ)] ![(15955917265521/50000000000000 : ℝ), (2716296959163/12500000000000 : ℝ), (46357789786211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4166431221/10000000000 : ℝ)|^2193 ≤ (15955917265521/50000000000000 : ℝ)^1681
        have hw : |(4166431221/10000000000 : ℝ)|=(4166431221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3103432007/10000000000 : ℝ)|^2193 ≤ (2716296959163/12500000000000 : ℝ)^1681
        have hw : |(3103432007/10000000000 : ℝ)|=(3103432007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5547190673/10000000000 : ℝ)|^2193 ≤ (46357789786211/100000000000000 : ℝ)^1681
        have hw : |(5547190673/10000000000 : ℝ)|=(5547190673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s0_4 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1764545209/10000000000 : ℝ)*x 0 + (1214873107/2500000000 : ℝ)*x 1 + (1482861423/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1764545209/10000000000 : ℝ)^2193 ≤ (10403314980247/100000000000000 : ℝ)^1681 := by
    have hnat : (1764545209 : ℕ)^2193*100000000000000^1681 ≤ 10403314980247^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1764545209 10000000000 10403314980247 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1214873107/2500000000 : ℝ)^2193 ≤ (39006104404929/100000000000000 : ℝ)^1681 := by
    have hnat : (1214873107 : ℕ)^2193*100000000000000^1681 ≤ 39006104404929^1681*2500000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1214873107 2500000000 39006104404929 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1482861423/2500000000 : ℝ)^2193 ≤ (50590580601659/100000000000000 : ℝ)^1681 := by
    have hnat : (1482861423 : ℕ)^2193*100000000000000^1681 ≤ 50590580601659^1681*2500000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1482861423 2500000000 50590580601659 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1764545209/10000000000 : ℝ), (1214873107/2500000000 : ℝ), (1482861423/2500000000 : ℝ)] ![(10403314980247/100000000000000 : ℝ), (39006104404929/100000000000000 : ℝ), (50590580601659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1764545209/10000000000 : ℝ)|^2193 ≤ (10403314980247/100000000000000 : ℝ)^1681
        have hw : |(-1764545209/10000000000 : ℝ)|=(1764545209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1214873107/2500000000 : ℝ)|^2193 ≤ (39006104404929/100000000000000 : ℝ)^1681
        have hw : |(1214873107/2500000000 : ℝ)|=(1214873107/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1482861423/2500000000 : ℝ)|^2193 ≤ (50590580601659/100000000000000 : ℝ)^1681
        have hw : |(1482861423/2500000000 : ℝ)|=(1482861423/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s0_5 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2591893921/5000000000 : ℝ)*x 0 + (-649287873/5000000000 : ℝ)*x 1 + (5931445769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2591893921/5000000000 : ℝ)^2193 ≤ (8487197161807/20000000000000 : ℝ)^1681 := by
    have hnat : (2591893921 : ℕ)^2193*20000000000000^1681 ≤ 8487197161807^1681*5000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591893921 5000000000 8487197161807 20000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (649287873/5000000000 : ℝ)^2193 ≤ (6973432725499/100000000000000 : ℝ)^1681 := by
    have hnat : (649287873 : ℕ)^2193*100000000000000^1681 ≤ 6973432725499^1681*5000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649287873 5000000000 6973432725499 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5931445769/10000000000 : ℝ)^2193 ≤ (25295290729221/50000000000000 : ℝ)^1681 := by
    have hnat : (5931445769 : ℕ)^2193*50000000000000^1681 ≤ 25295290729221^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5931445769 10000000000 25295290729221 50000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2591893921/5000000000 : ℝ), (-649287873/5000000000 : ℝ), (5931445769/10000000000 : ℝ)] ![(8487197161807/20000000000000 : ℝ), (6973432725499/100000000000000 : ℝ), (25295290729221/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2591893921/5000000000 : ℝ)|^2193 ≤ (8487197161807/20000000000000 : ℝ)^1681
        have hw : |(2591893921/5000000000 : ℝ)|=(2591893921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-649287873/5000000000 : ℝ)|^2193 ≤ (6973432725499/100000000000000 : ℝ)^1681
        have hw : |(-649287873/5000000000 : ℝ)|=(649287873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5931445769/10000000000 : ℝ)|^2193 ≤ (25295290729221/50000000000000 : ℝ)^1681
        have hw : |(5931445769/10000000000 : ℝ)|=(5931445769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s0_6 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5183787861/10000000000 : ℝ)*x 0 + (1482861401/2500000000 : ℝ)*x 1 + (-649287989/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5183787861/10000000000 : ℝ)^2193 ≤ (42435986011949/100000000000000 : ℝ)^1681 := by
    have hnat : (5183787861 : ℕ)^2193*100000000000000^1681 ≤ 42435986011949^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183787861 10000000000 42435986011949 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1482861401/2500000000 : ℝ)^2193 ≤ (25295289811239/50000000000000 : ℝ)^1681 := by
    have hnat : (1482861401 : ℕ)^2193*50000000000000^1681 ≤ 25295289811239^1681*2500000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1482861401 2500000000 25295289811239 50000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (649287989/5000000000 : ℝ)^2193 ≤ (6973434350817/100000000000000 : ℝ)^1681 := by
    have hnat : (649287989 : ℕ)^2193*100000000000000^1681 ≤ 6973434350817^1681*5000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649287989 5000000000 6973434350817 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5183787861/10000000000 : ℝ), (1482861401/2500000000 : ℝ), (-649287989/5000000000 : ℝ)] ![(42435986011949/100000000000000 : ℝ), (25295289811239/50000000000000 : ℝ), (6973434350817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5183787861/10000000000 : ℝ)|^2193 ≤ (42435986011949/100000000000000 : ℝ)^1681
        have hw : |(5183787861/10000000000 : ℝ)|=(5183787861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1482861401/2500000000 : ℝ)|^2193 ≤ (25295289811239/50000000000000 : ℝ)^1681
        have hw : |(1482861401/2500000000 : ℝ)|=(1482861401/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-649287989/5000000000 : ℝ)|^2193 ≤ (6973434350817/100000000000000 : ℝ)^1681
        have hw : |(-649287989/5000000000 : ℝ)|=(649287989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s0_7 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (835029127/2000000000 : ℝ)*x 0 + (5484650237/10000000000 : ℝ)*x 1 + (1584102801/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (835029127/2000000000 : ℝ)^2193 ≤ (31998937890713/100000000000000 : ℝ)^1681 := by
    have hnat : (835029127 : ℕ)^2193*100000000000000^1681 ≤ 31998937890713^1681*2000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      835029127 2000000000 31998937890713 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5484650237/10000000000 : ℝ)^2193 ≤ (45677125158459/100000000000000 : ℝ)^1681 := by
    have hnat : (5484650237 : ℕ)^2193*100000000000000^1681 ≤ 45677125158459^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5484650237 10000000000 45677125158459 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1584102801/5000000000 : ℝ)^2193 ≤ (1116196847081/5000000000000 : ℝ)^1681 := by
    have hnat : (1584102801 : ℕ)^2193*5000000000000^1681 ≤ 1116196847081^1681*5000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1584102801 5000000000 1116196847081 5000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(835029127/2000000000 : ℝ), (5484650237/10000000000 : ℝ), (1584102801/5000000000 : ℝ)] ![(31998937890713/100000000000000 : ℝ), (45677125158459/100000000000000 : ℝ), (1116196847081/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(835029127/2000000000 : ℝ)|^2193 ≤ (31998937890713/100000000000000 : ℝ)^1681
        have hw : |(835029127/2000000000 : ℝ)|=(835029127/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5484650237/10000000000 : ℝ)|^2193 ≤ (45677125158459/100000000000000 : ℝ)^1681
        have hw : |(5484650237/10000000000 : ℝ)|=(5484650237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1584102801/5000000000 : ℝ)|^2193 ≤ (1116196847081/5000000000000 : ℝ)^1681
        have hw : |(1584102801/5000000000 : ℝ)|=(1584102801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1426_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79023921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1013/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26279/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4385/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4385 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4385*1^1024 ≤ 0^1024*1^4385 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4385 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4385 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4385/1024 : ℝ) ≤ (395330862761719341/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4385 ≤ (395330862761719341/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4385*20000000000000000000^1024 ≤ 395330862761719341^1024*5^4385 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 395330862761719341 20000000000000000000 4385 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (395330862761719341/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4385 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4385/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4385 := by
      have hnat : (1 : ℕ)^1024*1^4385 ≤ 1^4385*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4385 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20395330862761719341/20000000000000000000 : ℝ) ≤ (10045813841814203/10000000000000000 : ℝ) ^ (4385/1024 : ℝ) := by
    have hpowers : (20395330862761719341/20000000000000000000 : ℝ)^1024 ≤ (10045813841814203/10000000000000000 : ℝ)^4385 := by
      have hnat : (20395330862761719341 : ℕ)^1024*10000000000000000^4385 ≤ 10045813841814203^4385*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20395330862761719341 20000000000000000000 10045813841814203 10000000000000000 1024 4385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10045813841814203/10000000000000000 : ℝ)) (X := (20395330862761719341/20000000000000000000 : ℝ)) (by norm_num) 4385 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10395330862761719341/10000000000000000000 : ℝ) ≤ (5045813841814203/5000000000000000 : ℝ) ^ (4385/1024 : ℝ) := by
    have hpowers : (10395330862761719341/10000000000000000000 : ℝ)^1024 ≤ (5045813841814203/5000000000000000 : ℝ)^4385 := by
      have hnat : (10395330862761719341 : ℕ)^1024*5000000000000000^4385 ≤ 5045813841814203^4385*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10395330862761719341 10000000000000000000 5045813841814203 5000000000000000 1024 4385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5045813841814203/5000000000000000 : ℝ)) (X := (10395330862761719341/10000000000000000000 : ℝ)) (by norm_num) 4385 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(45813841814203/4000000000000000 : ℝ)*(0 : ℝ))^(4385/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(45813841814203/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(395330862761719341/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(45813841814203/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4385/1024 : ℝ) := by
    rw [show (1 : ℝ)+(45813841814203/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10045813841814203/10000000000000000 : ℝ) by norm_num, show 1+(395330862761719341/20000000000000000000 : ℝ)+(0 : ℝ)=(20395330862761719341/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(395330862761719341/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(45813841814203/4000000000000000 : ℝ)*(2/5 : ℝ))^(4385/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(45813841814203/4000000000000000 : ℝ)*(2/5 : ℝ)=(5045813841814203/5000000000000000 : ℝ) by norm_num, show 1+2*(395330862761719341/20000000000000000000 : ℝ)=(10395330862761719341/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(45813841814203/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4385/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (45813841814203/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(45813841814203/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4385/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (45813841814203/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(45813841814203/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4385/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (45813841814203/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1760513519/10000000000 : ℝ)*X 0 0+(596141997/1000000000 : ℝ)*X 0 1+(603818931/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5492432901/10000000000 : ℝ)*X 1 0+(-2399470197/10000000000 : ℝ)*X 1 1+(4830551873/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2746216671/5000000000 : ℝ)*X 2 0+(301909481/625000000 : ℝ)*X 2 1+(-2399469849/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4166431221/10000000000 : ℝ)*X 0 0+(3103432007/10000000000 : ℝ)*X 0 1+(5547190673/10000000000 : ℝ)*X 0 2+(4166431221/10000000000 : ℝ)*X 1 0+(3103432007/10000000000 : ℝ)*X 1 1+(5547190673/10000000000 : ℝ)*X 1 2+(4166431221/10000000000 : ℝ)*X 2 0+(3103432007/10000000000 : ℝ)*X 2 1+(5547190673/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1764545209/10000000000 : ℝ)*X 0 0+(1214873107/2500000000 : ℝ)*X 0 1+(1482861423/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2591893921/5000000000 : ℝ)*X 1 0+(-649287873/5000000000 : ℝ)*X 1 1+(5931445769/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5183787861/10000000000 : ℝ)*X 2 0+(1482861401/2500000000 : ℝ)*X 2 1+(-649287989/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((835029127/2000000000 : ℝ)*X 0 0+(5484650237/10000000000 : ℝ)*X 0 1+(1584102801/5000000000 : ℝ)*X 0 2+(835029127/2000000000 : ℝ)*X 1 0+(5484650237/10000000000 : ℝ)*X 1 1+(1584102801/5000000000 : ℝ)*X 1 2+(835029127/2000000000 : ℝ)*X 2 0+(5484650237/10000000000 : ℝ)*X 2 1+(1584102801/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (786820397348347458096003/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (74805159/4000000000000 : ℝ)*(base19) + (958395317/50000000000000 : ℝ)*(base23) + (200990459/100000000000000 : ℝ)*(upper3) + (6684241/50000000000000 : ℝ)*(upper4) + (293968027/100000000000000 : ℝ)*(upper5) + (323375496802289/50000000000000 : ℝ)*(major0) + (323375496802289/50000000000000 : ℝ)*(major1) + (323375496802289/50000000000000 : ℝ)*(major2) + (88428226423417/10000000000000 : ℝ)*(sp0) + (221071922828051/25000000000000 : ℝ)*(sp1) + (176857528930109/20000000000000 : ℝ)*(sp2) + (4092089576037/1000000000000 : ℝ)*(sp3) + (228037719/3125000000000 : ℝ)*(sp4) + (1602945403/50000000000000 : ℝ)*(sp7) + (204606081747253/50000000000000 : ℝ)*(f.failure) + (442144780720589/50000000000000 : ℝ)*(f.sum) + (70523097689333/100000000000000000000000000000 : ℝ)*base66 + (672606486089333/200000000000000000000000000000 : ℝ)*base68 + (1020670361510667/200000000000000000000000000000 : ℝ)*base69 + (42709699689333/200000000000000000000000000000 : ℝ)*base72 + (444221310289333/100000000000000000000000000000 : ℝ)*base74 + (1603643717689333/200000000000000000000000000000 : ℝ)*base76 + (79519216889333/200000000000000000000000000000 : ℝ)*base78 + (2024239285289333/200000000000000000000000000000 : ℝ)*base80 + (459218202410667/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (13039013/2500000000000000000000 : ℝ)*base89 + (13039013/2500000000000000000000 : ℝ)*base91 + (13039013/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (379895706667427550009393/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13857313/800000000000 : ℝ)*(base19) + (1745725613/100000000000000 : ℝ)*(base23) + (43677513/25000000000000 : ℝ)*(base32) + (131411669/50000000000000 : ℝ)*(upper3) + (150722183/100000000000000 : ℝ)*(upper5) + (682285877086577/100000000000000 : ℝ)*(major0) + (682285877086577/100000000000000 : ℝ)*(major1) + (682285877086577/100000000000000 : ℝ)*(major2) + (4079413783/100000000000000 : ℝ)*(sp1) + (4249750159/100000000000000 : ℝ)*(sp2) + (932875712815903/100000000000000 : ℝ)*(sp4) + (186573980247599/20000000000000 : ℝ)*(sp5) + (932869717340131/100000000000000 : ℝ)*(sp6) + (43169561338339/10000000000000 : ℝ)*(sp7) + (215847894046721/50000000000000 : ℝ)*(f.failure) + (932875712815903/100000000000000 : ℝ)*(f.sum) + (170575005346869/200000000000000000000000000000 : ℝ)*base66 + (3418844586346869/400000000000000000000000000000 : ℝ)*base68 + (1774182483146869/400000000000000000000000000000 : ℝ)*base70 + (1254719789946869/400000000000000000000000000000 : ℝ)*base72 + (1033140002546869/200000000000000000000000000000 : ℝ)*base74 + (365790018346869/400000000000000000000000000000 : ℝ)*base76 + (2445047748346869/400000000000000000000000000000 : ℝ)*base78 + (2434833107946869/400000000000000000000000000000 : ℝ)*base80 + (10629445053131/200000000000000000000000000000 : ℝ)*base81 + (25613041/2500000000000000000000 : ℝ)*base89 + (25613041/2500000000000000000000 : ℝ)*base91 + (25613041/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1426_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79023921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1013/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26279/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1426_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1426_s1_0 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-966646899/5000000000 : ℝ)*x 0 + (5606437047/10000000000 : ℝ)*x 1 + (2537386767/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (966646899/5000000000 : ℝ)^2193 ≤ (11719741325533/100000000000000 : ℝ)^1681 := by
    have hnat : (966646899 : ℕ)^2193*100000000000000^1681 ≤ 11719741325533^1681*5000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      966646899 5000000000 11719741325533 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5606437047/10000000000 : ℝ)^2193 ≤ (2350238157493/5000000000000 : ℝ)^1681 := by
    have hnat : (5606437047 : ℕ)^2193*5000000000000^1681 ≤ 2350238157493^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5606437047 10000000000 2350238157493 5000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2537386767/5000000000 : ℝ)^2193 ≤ (10318873879411/25000000000000 : ℝ)^1681 := by
    have hnat : (2537386767 : ℕ)^2193*25000000000000^1681 ≤ 10318873879411^1681*5000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2537386767 5000000000 10318873879411 25000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-966646899/5000000000 : ℝ), (5606437047/10000000000 : ℝ), (2537386767/5000000000 : ℝ)] ![(11719741325533/100000000000000 : ℝ), (2350238157493/5000000000000 : ℝ), (10318873879411/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-966646899/5000000000 : ℝ)|^2193 ≤ (11719741325533/100000000000000 : ℝ)^1681
        have hw : |(-966646899/5000000000 : ℝ)|=(966646899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5606437047/10000000000 : ℝ)|^2193 ≤ (2350238157493/5000000000000 : ℝ)^1681
        have hw : |(5606437047/10000000000 : ℝ)|=(5606437047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2537386767/5000000000 : ℝ)|^2193 ≤ (10318873879411/25000000000000 : ℝ)^1681
        have hw : |(2537386767/5000000000 : ℝ)|=(2537386767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s1_1 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5397112403/10000000000 : ℝ)*x 0 + (-55377007/250000000 : ℝ)*x 1 + (5074774789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5397112403/10000000000 : ℝ)^2193 ≤ (8945673321493/20000000000000 : ℝ)^1681 := by
    have hnat : (5397112403 : ℕ)^2193*20000000000000^1681 ≤ 8945673321493^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397112403 10000000000 8945673321493 20000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (55377007/250000000 : ℝ)^2193 ≤ (69980622747/500000000000 : ℝ)^1681 := by
    have hnat : (55377007 : ℕ)^2193*500000000000^1681 ≤ 69980622747^1681*250000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55377007 250000000 69980622747 500000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5074774789/10000000000 : ℝ)^2193 ≤ (825510176683/2000000000000 : ℝ)^1681 := by
    have hnat : (5074774789 : ℕ)^2193*2000000000000^1681 ≤ 825510176683^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5074774789 10000000000 825510176683 2000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5397112403/10000000000 : ℝ), (-55377007/250000000 : ℝ), (5074774789/10000000000 : ℝ)] ![(8945673321493/20000000000000 : ℝ), (69980622747/500000000000 : ℝ), (825510176683/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5397112403/10000000000 : ℝ)|^2193 ≤ (8945673321493/20000000000000 : ℝ)^1681
        have hw : |(5397112403/10000000000 : ℝ)|=(5397112403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-55377007/250000000 : ℝ)|^2193 ≤ (69980622747/500000000000 : ℝ)^1681
        have hw : |(-55377007/250000000 : ℝ)|=(55377007/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5074774789/10000000000 : ℝ)|^2193 ≤ (825510176683/2000000000000 : ℝ)^1681
        have hw : |(5074774789/10000000000 : ℝ)|=(5074774789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s1_2 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2698556693/5000000000 : ℝ)*x 0 + (5074773687/10000000000 : ℝ)*x 1 + (-276885051/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2698556693/5000000000 : ℝ)^2193 ≤ (4472837723533/10000000000000 : ℝ)^1681 := by
    have hnat : (2698556693 : ℕ)^2193*10000000000000^1681 ≤ 4472837723533^1681*5000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698556693 5000000000 4472837723533 10000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5074773687/10000000000 : ℝ)^2193 ≤ (4127549714109/10000000000000 : ℝ)^1681 := by
    have hnat : (5074773687 : ℕ)^2193*10000000000000^1681 ≤ 4127549714109^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5074773687 10000000000 4127549714109 10000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (276885051/1250000000 : ℝ)^2193 ≤ (13996125604513/100000000000000 : ℝ)^1681 := by
    have hnat : (276885051 : ℕ)^2193*100000000000000^1681 ≤ 13996125604513^1681*1250000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276885051 1250000000 13996125604513 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2698556693/5000000000 : ℝ), (5074773687/10000000000 : ℝ), (-276885051/1250000000 : ℝ)] ![(4472837723533/10000000000000 : ℝ), (4127549714109/10000000000000 : ℝ), (13996125604513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2698556693/5000000000 : ℝ)|^2193 ≤ (4472837723533/10000000000000 : ℝ)^1681
        have hw : |(2698556693/5000000000 : ℝ)|=(2698556693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5074773687/10000000000 : ℝ)|^2193 ≤ (4127549714109/10000000000000 : ℝ)^1681
        have hw : |(5074773687/10000000000 : ℝ)|=(5074773687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-276885051/1250000000 : ℝ)|^2193 ≤ (13996125604513/100000000000000 : ℝ)^1681
        have hw : |(-276885051/1250000000 : ℝ)|=(276885051/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s1_3 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (171087287/400000000 : ℝ)*x 0 + (1868606223/5000000000 : ℝ)*x 1 + (4886112029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (171087287/400000000 : ℝ)^2193 ≤ (6604585200939/20000000000000 : ℝ)^1681 := by
    have hnat : (171087287 : ℕ)^2193*20000000000000^1681 ≤ 6604585200939^1681*400000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171087287 400000000 6604585200939 20000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1868606223/5000000000 : ℝ)^2193 ≤ (2769198782177/10000000000000 : ℝ)^1681 := by
    have hnat : (1868606223 : ℕ)^2193*10000000000000^1681 ≤ 2769198782177^1681*5000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1868606223 5000000000 2769198782177 10000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4886112029/10000000000 : ℝ)^2193 ≤ (39285086170441/100000000000000 : ℝ)^1681 := by
    have hnat : (4886112029 : ℕ)^2193*100000000000000^1681 ≤ 39285086170441^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4886112029 10000000000 39285086170441 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(171087287/400000000 : ℝ), (1868606223/5000000000 : ℝ), (4886112029/10000000000 : ℝ)] ![(6604585200939/20000000000000 : ℝ), (2769198782177/10000000000000 : ℝ), (39285086170441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(171087287/400000000 : ℝ)|^2193 ≤ (6604585200939/20000000000000 : ℝ)^1681
        have hw : |(171087287/400000000 : ℝ)|=(171087287/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1868606223/5000000000 : ℝ)|^2193 ≤ (2769198782177/10000000000000 : ℝ)^1681
        have hw : |(1868606223/5000000000 : ℝ)|=(1868606223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4886112029/10000000000 : ℝ)|^2193 ≤ (39285086170441/100000000000000 : ℝ)^1681
        have hw : |(4886112029/10000000000 : ℝ)|=(4886112029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s1_4 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1933695937/10000000000 : ℝ)*x 0 + (5081022829/10000000000 : ℝ)*x 1 + (5600081539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1933695937/10000000000 : ℝ)^2193 ≤ (2930730430087/25000000000000 : ℝ)^1681 := by
    have hnat : (1933695937 : ℕ)^2193*25000000000000^1681 ≤ 2930730430087^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1933695937 10000000000 2930730430087 25000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5081022829/10000000000 : ℝ)^2193 ≤ (41341817727613/100000000000000 : ℝ)^1681 := by
    have hnat : (5081022829 : ℕ)^2193*100000000000000^1681 ≤ 41341817727613^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5081022829 10000000000 41341817727613 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5600081539/10000000000 : ℝ)^2193 ≤ (11733815135319/25000000000000 : ℝ)^1681 := by
    have hnat : (5600081539 : ℕ)^2193*25000000000000^1681 ≤ 11733815135319^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5600081539 10000000000 11733815135319 25000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1933695937/10000000000 : ℝ), (5081022829/10000000000 : ℝ), (5600081539/10000000000 : ℝ)] ![(2930730430087/25000000000000 : ℝ), (41341817727613/100000000000000 : ℝ), (11733815135319/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1933695937/10000000000 : ℝ)|^2193 ≤ (2930730430087/25000000000000 : ℝ)^1681
        have hw : |(-1933695937/10000000000 : ℝ)|=(1933695937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5081022829/10000000000 : ℝ)|^2193 ≤ (41341817727613/100000000000000 : ℝ)^1681
        have hw : |(5081022829/10000000000 : ℝ)|=(5081022829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5600081539/10000000000 : ℝ)|^2193 ≤ (11733815135319/25000000000000 : ℝ)^1681
        have hw : |(5600081539/10000000000 : ℝ)|=(5600081539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s1_5 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2629117253/5000000000 : ℝ)*x 0 + (-844886481/5000000000 : ℝ)*x 1 + (350005097/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2629117253/5000000000 : ℝ)^2193 ≤ (43232785050861/100000000000000 : ℝ)^1681 := by
    have hnat : (2629117253 : ℕ)^2193*100000000000000^1681 ≤ 43232785050861^1681*5000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629117253 5000000000 43232785050861 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (844886481/5000000000 : ℝ)^2193 ≤ (9831954250401/100000000000000 : ℝ)^1681 := by
    have hnat : (844886481 : ℕ)^2193*100000000000000^1681 ≤ 9831954250401^1681*5000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844886481 5000000000 9831954250401 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (350005097/625000000 : ℝ)^2193 ≤ (5866907585427/12500000000000 : ℝ)^1681 := by
    have hnat : (350005097 : ℕ)^2193*12500000000000^1681 ≤ 5866907585427^1681*625000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      350005097 625000000 5866907585427 12500000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2629117253/5000000000 : ℝ), (-844886481/5000000000 : ℝ), (350005097/625000000 : ℝ)] ![(43232785050861/100000000000000 : ℝ), (9831954250401/100000000000000 : ℝ), (5866907585427/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2629117253/5000000000 : ℝ)|^2193 ≤ (43232785050861/100000000000000 : ℝ)^1681
        have hw : |(2629117253/5000000000 : ℝ)|=(2629117253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-844886481/5000000000 : ℝ)|^2193 ≤ (9831954250401/100000000000000 : ℝ)^1681
        have hw : |(-844886481/5000000000 : ℝ)|=(844886481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(350005097/625000000 : ℝ)|^2193 ≤ (5866907585427/12500000000000 : ℝ)^1681
        have hw : |(350005097/625000000 : ℝ)|=(350005097/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s1_6 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1051646893/2000000000 : ℝ)*x 0 + (1120016303/2000000000 : ℝ)*x 1 + (-844886537/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051646893/2000000000 : ℝ)^2193 ≤ (2702049038193/6250000000000 : ℝ)^1681 := by
    have hnat : (1051646893 : ℕ)^2193*6250000000000^1681 ≤ 2702049038193^1681*2000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051646893 2000000000 2702049038193 6250000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1120016303/2000000000 : ℝ)^2193 ≤ (46935260278861/100000000000000 : ℝ)^1681 := by
    have hnat : (1120016303 : ℕ)^2193*100000000000000^1681 ≤ 46935260278861^1681*2000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120016303 2000000000 46935260278861 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (844886537/5000000000 : ℝ)^2193 ≤ (9831955100561/100000000000000 : ℝ)^1681 := by
    have hnat : (844886537 : ℕ)^2193*100000000000000^1681 ≤ 9831955100561^1681*5000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844886537 5000000000 9831955100561 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051646893/2000000000 : ℝ), (1120016303/2000000000 : ℝ), (-844886537/5000000000 : ℝ)] ![(2702049038193/6250000000000 : ℝ), (46935260278861/100000000000000 : ℝ), (9831955100561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051646893/2000000000 : ℝ)|^2193 ≤ (2702049038193/6250000000000 : ℝ)^1681
        have hw : |(1051646893/2000000000 : ℝ)|=(1051646893/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1120016303/2000000000 : ℝ)|^2193 ≤ (46935260278861/100000000000000 : ℝ)^1681
        have hw : |(1120016303/2000000000 : ℝ)|=(1120016303/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-844886537/5000000000 : ℝ)|^2193 ≤ (9831955100561/100000000000000 : ℝ)^1681
        have hw : |(-844886537/5000000000 : ℝ)|=(844886537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s1_7 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2139025781/5000000000 : ℝ)*x 0 + (487260859/1000000000 : ℝ)*x 1 + (937736221/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2139025781/5000000000 : ℝ)^2193 ≤ (8257920750953/25000000000000 : ℝ)^1681 := by
    have hnat : (2139025781 : ℕ)^2193*25000000000000^1681 ≤ 8257920750953^1681*5000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139025781 5000000000 8257920750953 25000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (487260859/1000000000 : ℝ)^2193 ≤ (152904327667/390625000000 : ℝ)^1681 := by
    have hnat : (487260859 : ℕ)^2193*390625000000^1681 ≤ 152904327667^1681*1000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      487260859 1000000000 152904327667 390625000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (937736221/2500000000 : ℝ)^2193 ≤ (27824809102657/100000000000000 : ℝ)^1681 := by
    have hnat : (937736221 : ℕ)^2193*100000000000000^1681 ≤ 27824809102657^1681*2500000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      937736221 2500000000 27824809102657 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2139025781/5000000000 : ℝ), (487260859/1000000000 : ℝ), (937736221/2500000000 : ℝ)] ![(8257920750953/25000000000000 : ℝ), (152904327667/390625000000 : ℝ), (27824809102657/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2139025781/5000000000 : ℝ)|^2193 ≤ (8257920750953/25000000000000 : ℝ)^1681
        have hw : |(2139025781/5000000000 : ℝ)|=(2139025781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(487260859/1000000000 : ℝ)|^2193 ≤ (152904327667/390625000000 : ℝ)^1681
        have hw : |(487260859/1000000000 : ℝ)|=(487260859/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(937736221/2500000000 : ℝ)|^2193 ≤ (27824809102657/100000000000000 : ℝ)^1681
        have hw : |(937736221/2500000000 : ℝ)|=(937736221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1426_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79023921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26279/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1013/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (7627/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9433/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26279/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1013/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26279/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1013/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26279/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1013/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26279/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1013/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26279/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1013/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26279/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1013/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1013/50000 : ℝ) ^ (4385/1024 : ℝ) ≤ (5605914044859/100000000000000000000 : ℝ) := by
    have hpowers : (1013/50000 : ℝ)^4385 ≤ (5605914044859/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1013 : ℕ)^4385*100000000000000000000^1024 ≤ 5605914044859^1024*50000^4385 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1013 50000 5605914044859 100000000000000000000 4385 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1013/50000 : ℝ)) (X := (5605914044859/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4385 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (26279/100000 : ℝ) ^ (4385/1024 : ℝ) ≤ (327064596697086611/100000000000000000000 : ℝ) := by
    have hpowers : (26279/100000 : ℝ)^4385 ≤ (327064596697086611/100000000000000000000 : ℝ)^1024 := by
      have hnat : (26279 : ℕ)^4385*100000000000000000000^1024 ≤ 327064596697086611^1024*100000^4385 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26279 100000 327064596697086611 100000000000000000000 4385 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26279/100000 : ℝ)) (X := (327064596697086611/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4385 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000005605914044859/50000000000000000000 : ℝ) ≤ (10000000261822383/10000000000000000 : ℝ) ^ (4385/1024 : ℝ) := by
    have hpowers : (50000005605914044859/50000000000000000000 : ℝ)^1024 ≤ (10000000261822383/10000000000000000 : ℝ)^4385 := by
      have hnat : (50000005605914044859 : ℕ)^1024*10000000000000000^4385 ≤ 10000000261822383^4385*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000005605914044859 50000000000000000000 10000000261822383 10000000000000000 1024 4385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000261822383/10000000000000000 : ℝ)) (X := (50000005605914044859/50000000000000000000 : ℝ)) (by norm_num) 4385 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10032707020261113147/10000000000000000000 : ℝ) ≤ (1250953537303379/1250000000000000 : ℝ) ^ (4385/1024 : ℝ) := by
    have hpowers : (10032707020261113147/10000000000000000000 : ℝ)^1024 ≤ (1250953537303379/1250000000000000 : ℝ)^4385 := by
      have hnat : (10032707020261113147 : ℕ)^1024*1250000000000000^4385 ≤ 1250953537303379^4385*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10032707020261113147 10000000000000000000 1250953537303379 1250000000000000 1024 4385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250953537303379/1250000000000000 : ℝ)) (X := (10032707020261113147/10000000000000000000 : ℝ)) (by norm_num) 4385 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50327064596697086611/50000000000000000000 : ℝ) ≤ (10015256335031681/10000000000000000 : ℝ) ^ (4385/1024 : ℝ) := by
    have hpowers : (50327064596697086611/50000000000000000000 : ℝ)^1024 ≤ (10015256335031681/10000000000000000 : ℝ)^4385 := by
      have hnat : (50327064596697086611 : ℕ)^1024*10000000000000000^4385 ≤ 10015256335031681^4385*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50327064596697086611 50000000000000000000 10015256335031681 10000000000000000 1024 4385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10015256335031681/10000000000000000 : ℝ)) (X := (50327064596697086611/50000000000000000000 : ℝ)) (by norm_num) 4385 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5605914044859/100000000000000000000 : ℝ) ≤ ((242499097545656217151/242530000000000000000 : ℝ)+2*(7628036604649/2425300000000000 : ℝ)*(1013/50000 : ℝ))^(4385/1024 : ℝ) := by
    rw [show (242499097545656217151/242530000000000000000 : ℝ)+2*(7628036604649/2425300000000000 : ℝ)*(1013/50000 : ℝ)=(10000000261822383/10000000000000000 : ℝ) by norm_num, show 1+2*(5605914044859/100000000000000000000 : ℝ)=(50000005605914044859/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(327064596697086611/100000000000000000000 : ℝ)+(5605914044859/100000000000000000000 : ℝ) ≤ ((242499097545656217151/242530000000000000000 : ℝ)+(7628036604649/2425300000000000 : ℝ)*((26279/100000 : ℝ)+(1013/50000 : ℝ)))^(4385/1024 : ℝ) := by
    rw [show (242499097545656217151/242530000000000000000 : ℝ)+(7628036604649/2425300000000000 : ℝ)*((26279/100000 : ℝ)+(1013/50000 : ℝ))=(1250953537303379/1250000000000000 : ℝ) by norm_num, show 1+(327064596697086611/100000000000000000000 : ℝ)+(5605914044859/100000000000000000000 : ℝ)=(10032707020261113147/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(327064596697086611/100000000000000000000 : ℝ) ≤ ((242499097545656217151/242530000000000000000 : ℝ)+2*(7628036604649/2425300000000000 : ℝ)*(26279/100000 : ℝ))^(4385/1024 : ℝ) := by
    rw [show (242499097545656217151/242530000000000000000 : ℝ)+2*(7628036604649/2425300000000000 : ℝ)*(26279/100000 : ℝ)=(10015256335031681/10000000000000000 : ℝ) by norm_num, show 1+2*(327064596697086611/100000000000000000000 : ℝ)=(50327064596697086611/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (242499097545656217151/242530000000000000000 : ℝ)*(X 1 0+X 2 0)+(7628036604649/2425300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4385/1024 : ℝ)) (lo := (1013/50000 : ℝ)) (hi := (26279/100000 : ℝ)) (c := (242499097545656217151/242530000000000000000 : ℝ)) (alpha := (7628036604649/2425300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (242499097545656217151/242530000000000000000 : ℝ)*(X 0 1+X 2 1)+(7628036604649/2425300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4385/1024 : ℝ)) (lo := (1013/50000 : ℝ)) (hi := (26279/100000 : ℝ)) (c := (242499097545656217151/242530000000000000000 : ℝ)) (alpha := (7628036604649/2425300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (242499097545656217151/242530000000000000000 : ℝ)*(X 0 2+X 1 2)+(7628036604649/2425300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4385/1024 : ℝ)) (lo := (1013/50000 : ℝ)) (hi := (26279/100000 : ℝ)) (c := (242499097545656217151/242530000000000000000 : ℝ)) (alpha := (7628036604649/2425300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-966646899/5000000000 : ℝ)*X 0 0+(5606437047/10000000000 : ℝ)*X 0 1+(2537386767/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5397112403/10000000000 : ℝ)*X 1 0+(-55377007/250000000 : ℝ)*X 1 1+(5074774789/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2698556693/5000000000 : ℝ)*X 2 0+(5074773687/10000000000 : ℝ)*X 2 1+(-276885051/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((171087287/400000000 : ℝ)*X 0 0+(1868606223/5000000000 : ℝ)*X 0 1+(4886112029/10000000000 : ℝ)*X 0 2+(171087287/400000000 : ℝ)*X 1 0+(1868606223/5000000000 : ℝ)*X 1 1+(4886112029/10000000000 : ℝ)*X 1 2+(171087287/400000000 : ℝ)*X 2 0+(1868606223/5000000000 : ℝ)*X 2 1+(4886112029/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1933695937/10000000000 : ℝ)*X 0 0+(5081022829/10000000000 : ℝ)*X 0 1+(5600081539/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2629117253/5000000000 : ℝ)*X 1 0+(-844886481/5000000000 : ℝ)*X 1 1+(350005097/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1051646893/2000000000 : ℝ)*X 2 0+(1120016303/2000000000 : ℝ)*X 2 1+(-844886537/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2139025781/5000000000 : ℝ)*X 0 0+(487260859/1000000000 : ℝ)*X 0 1+(937736221/2500000000 : ℝ)*X 0 2+(2139025781/5000000000 : ℝ)*X 1 0+(487260859/1000000000 : ℝ)*X 1 1+(937736221/2500000000 : ℝ)*X 1 2+(2139025781/5000000000 : ℝ)*X 2 0+(487260859/1000000000 : ℝ)*X 2 1+(937736221/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5370692622244719827135819217/1515812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (495999923/100000000000000 : ℝ)*(base19) + (402066899/50000000000000 : ℝ)*(base23) + (61171701/100000000000000 : ℝ)*(upper3) + (2323681/12500000000000 : ℝ)*(upper4) + (6552991/12500000000000 : ℝ)*(upper5) + (343913397756611/25000000000000 : ℝ)*(major0) + (343913397756611/25000000000000 : ℝ)*(major1) + (343913397756611/25000000000000 : ℝ)*(major2) + (940447905264939/50000000000000 : ℝ)*(sp0) + (940451647046721/50000000000000 : ℝ)*(sp1) + (117556436622473/6250000000000 : ℝ)*(sp2) + (870400416574433/100000000000000 : ℝ)*(sp3) + (249361359/3125000000000 : ℝ)*(sp4) + (357160171/12500000000000 : ℝ)*(sp7) + (870403273855801/100000000000000 : ℝ)*(f.failure) + (940451895046683/50000000000000 : ℝ)*(f.sum) + (330334150049041/121265000000000000000000000000 : ℝ)*base65 + (38367830185473735261/6063250000000000000000000000000000 : ℝ)*base67 + (18805408018111514739/6063250000000000000000000000000000 : ℝ)*base70 + (25076654674915485261/6063250000000000000000000000000000 : ℝ)*base71 + (3466264463257/60632500000000000000000000000 : ℝ)*base74 + (40287409351872985261/6063250000000000000000000000000000 : ℝ)*base75 + (12656595623198985261/6063250000000000000000000000000000 : ℝ)*base77 + (53951417088050235261/6063250000000000000000000000000000 : ℝ)*base79 + (24461567200031/121265000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (16384279/5000000000000000000000 : ℝ)*base90 + (16384279/5000000000000000000000 : ℝ)*base92 + (16384279/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12672661658606892176996268771/6063250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1665479/20000000000000 : ℝ)*(base1) + (504223289/100000000000000 : ℝ)*(base19) + (482005639/100000000000000 : ℝ)*(base23) + (5727981/10000000000000 : ℝ)*(upper3) + (3881779/10000000000000 : ℝ)*(upper5) + (1409048491043793/100000000000000 : ℝ)*(major0) + (1409048491043793/100000000000000 : ℝ)*(major1) + (1409048491043793/100000000000000 : ℝ)*(major2) + (3091821001/100000000000000 : ℝ)*(sp1) + (352419473/12500000000000 : ℝ)*(sp2) + (481641008053637/25000000000000 : ℝ)*(sp4) + (963280213921431/50000000000000 : ℝ)*(sp5) + (192656072252573/10000000000000 : ℝ)*(sp6) + (891532880203783/100000000000000 : ℝ)*(sp7) + (445766444265589/50000000000000 : ℝ)*(f.failure) + (1926564023887153/100000000000000 : ℝ)*(f.sum) + (13889195017607/121265000000000000000000000000 : ℝ)*base65 + (109804139440938393743/24253000000000000000000000000000000 : ℝ)*base67 + (235650209012592393743/24253000000000000000000000000000000 : ℝ)*base69 + (252959451980111393743/24253000000000000000000000000000000 : ℝ)*base71 + (111919710760533/121265000000000000000000000000 : ℝ)*base74 + (112576026379619393743/24253000000000000000000000000000000 : ℝ)*base75 + (141613019516864393743/24253000000000000000000000000000000 : ℝ)*base77 + (176512718270359606257/24253000000000000000000000000000000 : ℝ)*base80 + (448787356609457/121265000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (16845531/2500000000000000000000 : ℝ)*base90 + (16845531/2500000000000000000000 : ℝ)*base92 + (16845531/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1426_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79023921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26279/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1013/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7627/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9433/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1426_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1426_s2_0 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-196665127/1000000000 : ℝ)*x 0 + (218353751/400000000 : ℝ)*x 1 + (5200898853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (196665127/1000000000 : ℝ)^2193 ≤ (11984237487637/100000000000000 : ℝ)^1681 := by
    have hnat : (196665127 : ℕ)^2193*100000000000000^1681 ≤ 11984237487637^1681*1000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196665127 1000000000 11984237487637 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (218353751/400000000 : ℝ)^2193 ≤ (45396944880469/100000000000000 : ℝ)^1681 := by
    have hnat : (218353751 : ℕ)^2193*100000000000000^1681 ≤ 45396944880469^1681*400000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218353751 400000000 45396944880469 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5200898853/10000000000 : ℝ)^2193 ≤ (4261881761941/10000000000000 : ℝ)^1681 := by
    have hnat : (5200898853 : ℕ)^2193*10000000000000^1681 ≤ 4261881761941^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5200898853 10000000000 4261881761941 10000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-196665127/1000000000 : ℝ), (218353751/400000000 : ℝ), (5200898853/10000000000 : ℝ)] ![(11984237487637/100000000000000 : ℝ), (45396944880469/100000000000000 : ℝ), (4261881761941/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-196665127/1000000000 : ℝ)|^2193 ≤ (11984237487637/100000000000000 : ℝ)^1681
        have hw : |(-196665127/1000000000 : ℝ)|=(196665127/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(218353751/400000000 : ℝ)|^2193 ≤ (45396944880469/100000000000000 : ℝ)^1681
        have hw : |(218353751/400000000 : ℝ)|=(218353751/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5200898853/10000000000 : ℝ)|^2193 ≤ (4261881761941/10000000000000 : ℝ)^1681
        have hw : |(5200898853/10000000000 : ℝ)|=(5200898853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s2_1 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5360330097/10000000000 : ℝ)*x 0 + (-1049690143/5000000000 : ℝ)*x 1 + (5200898761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5360330097/10000000000 : ℝ)^2193 ≤ (44331102114599/100000000000000 : ℝ)^1681 := by
    have hnat : (5360330097 : ℕ)^2193*100000000000000^1681 ≤ 44331102114599^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5360330097 10000000000 44331102114599 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049690143/5000000000 : ℝ)^2193 ≤ (3262520308401/25000000000000 : ℝ)^1681 := by
    have hnat : (1049690143 : ℕ)^2193*25000000000000^1681 ≤ 3262520308401^1681*5000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049690143 5000000000 3262520308401 25000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5200898761/10000000000 : ℝ)^2193 ≤ (42618816635893/100000000000000 : ℝ)^1681 := by
    have hnat : (5200898761 : ℕ)^2193*100000000000000^1681 ≤ 42618816635893^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5200898761 10000000000 42618816635893 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5360330097/10000000000 : ℝ), (-1049690143/5000000000 : ℝ), (5200898761/10000000000 : ℝ)] ![(44331102114599/100000000000000 : ℝ), (3262520308401/25000000000000 : ℝ), (42618816635893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5360330097/10000000000 : ℝ)|^2193 ≤ (44331102114599/100000000000000 : ℝ)^1681
        have hw : |(5360330097/10000000000 : ℝ)|=(5360330097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1049690143/5000000000 : ℝ)|^2193 ≤ (3262520308401/25000000000000 : ℝ)^1681
        have hw : |(-1049690143/5000000000 : ℝ)|=(1049690143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5200898761/10000000000 : ℝ)|^2193 ≤ (42618816635893/100000000000000 : ℝ)^1681
        have hw : |(5200898761/10000000000 : ℝ)|=(5200898761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s2_2 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (536032973/1000000000 : ℝ)*x 0 + (650112397/1250000000 : ℝ)*x 1 + (-1049690113/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536032973/1000000000 : ℝ)^2193 ≤ (1773243926199/4000000000000 : ℝ)^1681 := by
    have hnat : (536032973 : ℕ)^2193*4000000000000^1681 ≤ 1773243926199^1681*1000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536032973 1000000000 1773243926199 4000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (650112397/1250000000 : ℝ)^2193 ≤ (42618821072409/100000000000000 : ℝ)^1681 := by
    have hnat : (650112397 : ℕ)^2193*100000000000000^1681 ≤ 42618821072409^1681*1250000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      650112397 1250000000 42618821072409 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049690113/5000000000 : ℝ)^2193 ≤ (3262520186759/25000000000000 : ℝ)^1681 := by
    have hnat : (1049690113 : ℕ)^2193*25000000000000^1681 ≤ 3262520186759^1681*5000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049690113 5000000000 3262520186759 25000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536032973/1000000000 : ℝ), (650112397/1250000000 : ℝ), (-1049690113/5000000000 : ℝ)] ![(1773243926199/4000000000000 : ℝ), (42618821072409/100000000000000 : ℝ), (3262520186759/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536032973/1000000000 : ℝ)|^2193 ≤ (1773243926199/4000000000000 : ℝ)^1681
        have hw : |(536032973/1000000000 : ℝ)|=(536032973/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(650112397/1250000000 : ℝ)|^2193 ≤ (42618821072409/100000000000000 : ℝ)^1681
        have hw : |(650112397/1250000000 : ℝ)|=(650112397/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1049690113/5000000000 : ℝ)|^2193 ≤ (3262520186759/25000000000000 : ℝ)^1681
        have hw : |(-1049690113/5000000000 : ℝ)|=(1049690113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s2_3 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2150361717/5000000000 : ℝ)*x 0 + (1007534087/2500000000 : ℝ)*x 1 + (2293772107/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2150361717/5000000000 : ℝ)^2193 ≤ (16630119580109/50000000000000 : ℝ)^1681 := by
    have hnat : (2150361717 : ℕ)^2193*50000000000000^1681 ≤ 16630119580109^1681*5000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150361717 5000000000 16630119580109 50000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1007534087/2500000000 : ℝ)^2193 ≤ (15278396995437/50000000000000 : ℝ)^1681 := by
    have hnat : (1007534087 : ℕ)^2193*50000000000000^1681 ≤ 15278396995437^1681*2500000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007534087 2500000000 15278396995437 50000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2293772107/5000000000 : ℝ)^2193 ≤ (36182966832261/100000000000000 : ℝ)^1681 := by
    have hnat : (2293772107 : ℕ)^2193*100000000000000^1681 ≤ 36182966832261^1681*5000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2293772107 5000000000 36182966832261 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2150361717/5000000000 : ℝ), (1007534087/2500000000 : ℝ), (2293772107/5000000000 : ℝ)] ![(16630119580109/50000000000000 : ℝ), (15278396995437/50000000000000 : ℝ), (36182966832261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2150361717/5000000000 : ℝ)|^2193 ≤ (16630119580109/50000000000000 : ℝ)^1681
        have hw : |(2150361717/5000000000 : ℝ)|=(2150361717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1007534087/2500000000 : ℝ)|^2193 ≤ (15278396995437/50000000000000 : ℝ)^1681
        have hw : |(1007534087/2500000000 : ℝ)|=(1007534087/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2293772107/5000000000 : ℝ)|^2193 ≤ (36182966832261/100000000000000 : ℝ)^1681
        have hw : |(2293772107/5000000000 : ℝ)|=(2293772107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s2_4 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1966697439/10000000000 : ℝ)*x 0 + (5202378873/10000000000 : ℝ)*x 1 + (5457351459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1966697439/10000000000 : ℝ)^2193 ≤ (11984604521377/100000000000000 : ℝ)^1681 := by
    have hnat : (1966697439 : ℕ)^2193*100000000000000^1681 ≤ 11984604521377^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1966697439 10000000000 11984604521377 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5202378873/10000000000 : ℝ)^2193 ≤ (8526928061821/20000000000000 : ℝ)^1681 := by
    have hnat : (5202378873 : ℕ)^2193*20000000000000^1681 ≤ 8526928061821^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5202378873 10000000000 8526928061821 20000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5457351459/10000000000 : ℝ)^2193 ≤ (45380755150973/100000000000000 : ℝ)^1681 := by
    have hnat : (5457351459 : ℕ)^2193*100000000000000^1681 ≤ 45380755150973^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457351459 10000000000 45380755150973 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1966697439/10000000000 : ℝ), (5202378873/10000000000 : ℝ), (5457351459/10000000000 : ℝ)] ![(11984604521377/100000000000000 : ℝ), (8526928061821/20000000000000 : ℝ), (45380755150973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1966697439/10000000000 : ℝ)|^2193 ≤ (11984604521377/100000000000000 : ℝ)^1681
        have hw : |(-1966697439/10000000000 : ℝ)|=(1966697439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5202378873/10000000000 : ℝ)|^2193 ≤ (8526928061821/20000000000000 : ℝ)^1681
        have hw : |(5202378873/10000000000 : ℝ)|=(5202378873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5457351459/10000000000 : ℝ)|^2193 ≤ (45380755150973/100000000000000 : ℝ)^1681
        have hw : |(5457351459/10000000000 : ℝ)|=(5457351459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s2_5 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5293274833/10000000000 : ℝ)*x 0 + (-1842927373/10000000000 : ℝ)*x 1 + (2728675913/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293274833/10000000000 : ℝ)^2193 ≤ (21804506983779/50000000000000 : ℝ)^1681 := by
    have hnat : (5293274833 : ℕ)^2193*50000000000000^1681 ≤ 21804506983779^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293274833 10000000000 21804506983779 50000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1842927373/10000000000 : ℝ)^2193 ≤ (11010226894491/100000000000000 : ℝ)^1681 := by
    have hnat : (1842927373 : ℕ)^2193*100000000000000^1681 ≤ 11010226894491^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1842927373 10000000000 11010226894491 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2728675913/5000000000 : ℝ)^2193 ≤ (4538075913229/10000000000000 : ℝ)^1681 := by
    have hnat : (2728675913 : ℕ)^2193*10000000000000^1681 ≤ 4538075913229^1681*5000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728675913 5000000000 4538075913229 10000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293274833/10000000000 : ℝ), (-1842927373/10000000000 : ℝ), (2728675913/5000000000 : ℝ)] ![(21804506983779/50000000000000 : ℝ), (11010226894491/100000000000000 : ℝ), (4538075913229/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293274833/10000000000 : ℝ)|^2193 ≤ (21804506983779/50000000000000 : ℝ)^1681
        have hw : |(5293274833/10000000000 : ℝ)|=(5293274833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1842927373/10000000000 : ℝ)|^2193 ≤ (11010226894491/100000000000000 : ℝ)^1681
        have hw : |(-1842927373/10000000000 : ℝ)|=(1842927373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2728675913/5000000000 : ℝ)|^2193 ≤ (4538075913229/10000000000000 : ℝ)^1681
        have hw : |(2728675913/5000000000 : ℝ)|=(2728675913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s2_6 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5293274763/10000000000 : ℝ)*x 0 + (27286759/50000000 : ℝ)*x 1 + (-921463753/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293274763/10000000000 : ℝ)^2193 ≤ (21804506607603/50000000000000 : ℝ)^1681 := by
    have hnat : (5293274763 : ℕ)^2193*50000000000000^1681 ≤ 21804506607603^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293274763 10000000000 21804506607603 50000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27286759/50000000 : ℝ)^2193 ≤ (9076151770047/20000000000000 : ℝ)^1681 := by
    have hnat : (27286759 : ℕ)^2193*20000000000000^1681 ≤ 9076151770047^1681*50000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27286759 50000000 9076151770047 20000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (921463753/5000000000 : ℝ)^2193 ≤ (11010227931089/100000000000000 : ℝ)^1681 := by
    have hnat : (921463753 : ℕ)^2193*100000000000000^1681 ≤ 11010227931089^1681*5000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      921463753 5000000000 11010227931089 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293274763/10000000000 : ℝ), (27286759/50000000 : ℝ), (-921463753/5000000000 : ℝ)] ![(21804506607603/50000000000000 : ℝ), (9076151770047/20000000000000 : ℝ), (11010227931089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293274763/10000000000 : ℝ)|^2193 ≤ (21804506607603/50000000000000 : ℝ)^1681
        have hw : |(5293274763/10000000000 : ℝ)|=(5293274763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(27286759/50000000 : ℝ)|^2193 ≤ (9076151770047/20000000000000 : ℝ)^1681
        have hw : |(27286759/50000000 : ℝ)|=(27286759/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-921463753/5000000000 : ℝ)|^2193 ≤ (11010227931089/100000000000000 : ℝ)^1681
        have hw : |(-921463753/5000000000 : ℝ)|=(921463753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s2_7 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4300822971/10000000000 : ℝ)*x 0 + (229217309/500000000 : ℝ)*x 1 + (252085051/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4300822971/10000000000 : ℝ)^2193 ≤ (1330449736317/4000000000000 : ℝ)^1681 := by
    have hnat : (4300822971 : ℕ)^2193*4000000000000^1681 ≤ 1330449736317^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4300822971 10000000000 1330449736317 4000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (229217309/500000000 : ℝ)^2193 ≤ (36150064113151/100000000000000 : ℝ)^1681 := by
    have hnat : (229217309 : ℕ)^2193*100000000000000^1681 ≤ 36150064113151^1681*500000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229217309 500000000 36150064113151 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (252085051/625000000 : ℝ)^2193 ≤ (30588692467299/100000000000000 : ℝ)^1681 := by
    have hnat : (252085051 : ℕ)^2193*100000000000000^1681 ≤ 30588692467299^1681*625000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252085051 625000000 30588692467299 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4300822971/10000000000 : ℝ), (229217309/500000000 : ℝ), (252085051/625000000 : ℝ)] ![(1330449736317/4000000000000 : ℝ), (36150064113151/100000000000000 : ℝ), (30588692467299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4300822971/10000000000 : ℝ)|^2193 ≤ (1330449736317/4000000000000 : ℝ)^1681
        have hw : |(4300822971/10000000000 : ℝ)|=(4300822971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(229217309/500000000 : ℝ)|^2193 ≤ (36150064113151/100000000000000 : ℝ)^1681
        have hw : |(229217309/500000000 : ℝ)|=(229217309/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(252085051/625000000 : ℝ)|^2193 ≤ (30588692467299/100000000000000 : ℝ)^1681
        have hw : |(252085051/625000000 : ℝ)|=(252085051/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1426_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79023921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9433/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7627/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10351/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15809/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9433/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7627/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9433/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7627/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9433/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7627/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9433/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7627/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9433/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7627/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9433/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7627/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (7627/100000 : ℝ) ^ (4385/1024 : ℝ) ≤ (818380984266029/50000000000000000000 : ℝ) := by
    have hpowers : (7627/100000 : ℝ)^4385 ≤ (818380984266029/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7627 : ℕ)^4385*50000000000000000000^1024 ≤ 818380984266029^1024*100000^4385 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7627 100000 818380984266029 50000000000000000000 4385 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7627/100000 : ℝ)) (X := (818380984266029/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4385 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9433/50000 : ℝ) ^ (4385/1024 : ℝ) ≤ (15824388053743453/20000000000000000000 : ℝ) := by
    have hpowers : (9433/50000 : ℝ)^4385 ≤ (15824388053743453/20000000000000000000 : ℝ)^1024 := by
      have hnat : (9433 : ℕ)^4385*20000000000000000000^1024 ≤ 15824388053743453^1024*50000^4385 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9433 50000 15824388053743453 20000000000000000000 4385 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9433/50000 : ℝ)) (X := (15824388053743453/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4385 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000818380984266029/25000000000000000000 : ℝ) ≤ (312502388858651/312500000000000 : ℝ) ^ (4385/1024 : ℝ) := by
    have hpowers : (25000818380984266029/25000000000000000000 : ℝ)^1024 ≤ (312502388858651/312500000000000 : ℝ)^4385 := by
      have hnat : (25000818380984266029 : ℕ)^1024*312500000000000^4385 ≤ 312502388858651^4385*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000818380984266029 25000000000000000000 312502388858651 312500000000000 1024 4385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312502388858651/312500000000000 : ℝ)) (X := (25000818380984266029/25000000000000000000 : ℝ)) (by norm_num) 4385 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100080758702237249323/100000000000000000000 : ℝ) ≤ (312558916283283/312500000000000 : ℝ) ^ (4385/1024 : ℝ) := by
    have hpowers : (100080758702237249323/100000000000000000000 : ℝ)^1024 ≤ (312558916283283/312500000000000 : ℝ)^4385 := by
      have hnat : (100080758702237249323 : ℕ)^1024*312500000000000^4385 ≤ 312558916283283^4385*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100080758702237249323 100000000000000000000 312558916283283 312500000000000 1024 4385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312558916283283/312500000000000 : ℝ)) (X := (100080758702237249323/100000000000000000000 : ℝ)) (by norm_num) 4385 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10015824388053743453/10000000000000000000 : ℝ) ≤ (62523088741583/62500000000000 : ℝ) ^ (4385/1024 : ℝ) := by
    have hpowers : (10015824388053743453/10000000000000000000 : ℝ)^1024 ≤ (62523088741583/62500000000000 : ℝ)^4385 := by
      have hnat : (10015824388053743453 : ℕ)^1024*62500000000000^4385 ≤ 62523088741583^4385*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10015824388053743453 10000000000000000000 62523088741583 62500000000000 1024 4385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (62523088741583/62500000000000 : ℝ)) (X := (10015824388053743453/10000000000000000000 : ℝ)) (by norm_num) 4385 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(818380984266029/50000000000000000000 : ℝ) ≤ ((3511352079047042061/3512187500000000000 : ℝ)+2*(7065928079/4390234375000 : ℝ)*(7627/100000 : ℝ))^(4385/1024 : ℝ) := by
    rw [show (3511352079047042061/3512187500000000000 : ℝ)+2*(7065928079/4390234375000 : ℝ)*(7627/100000 : ℝ)=(312502388858651/312500000000000 : ℝ) by norm_num, show 1+2*(818380984266029/50000000000000000000 : ℝ)=(25000818380984266029/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15824388053743453/20000000000000000000 : ℝ)+(818380984266029/50000000000000000000 : ℝ) ≤ ((3511352079047042061/3512187500000000000 : ℝ)+(7065928079/4390234375000 : ℝ)*((9433/50000 : ℝ)+(7627/100000 : ℝ)))^(4385/1024 : ℝ) := by
    rw [show (3511352079047042061/3512187500000000000 : ℝ)+(7065928079/4390234375000 : ℝ)*((9433/50000 : ℝ)+(7627/100000 : ℝ))=(312558916283283/312500000000000 : ℝ) by norm_num, show 1+(15824388053743453/20000000000000000000 : ℝ)+(818380984266029/50000000000000000000 : ℝ)=(100080758702237249323/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15824388053743453/20000000000000000000 : ℝ) ≤ ((3511352079047042061/3512187500000000000 : ℝ)+2*(7065928079/4390234375000 : ℝ)*(9433/50000 : ℝ))^(4385/1024 : ℝ) := by
    rw [show (3511352079047042061/3512187500000000000 : ℝ)+2*(7065928079/4390234375000 : ℝ)*(9433/50000 : ℝ)=(62523088741583/62500000000000 : ℝ) by norm_num, show 1+2*(15824388053743453/20000000000000000000 : ℝ)=(10015824388053743453/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3511352079047042061/3512187500000000000 : ℝ)*(X 1 0+X 2 0)+(7065928079/4390234375000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4385/1024 : ℝ)) (lo := (7627/100000 : ℝ)) (hi := (9433/50000 : ℝ)) (c := (3511352079047042061/3512187500000000000 : ℝ)) (alpha := (7065928079/4390234375000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3511352079047042061/3512187500000000000 : ℝ)*(X 0 1+X 2 1)+(7065928079/4390234375000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4385/1024 : ℝ)) (lo := (7627/100000 : ℝ)) (hi := (9433/50000 : ℝ)) (c := (3511352079047042061/3512187500000000000 : ℝ)) (alpha := (7065928079/4390234375000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3511352079047042061/3512187500000000000 : ℝ)*(X 0 2+X 1 2)+(7065928079/4390234375000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4385/1024 : ℝ)) (lo := (7627/100000 : ℝ)) (hi := (9433/50000 : ℝ)) (c := (3511352079047042061/3512187500000000000 : ℝ)) (alpha := (7065928079/4390234375000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-196665127/1000000000 : ℝ)*X 0 0+(218353751/400000000 : ℝ)*X 0 1+(5200898853/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5360330097/10000000000 : ℝ)*X 1 0+(-1049690143/5000000000 : ℝ)*X 1 1+(5200898761/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((536032973/1000000000 : ℝ)*X 2 0+(650112397/1250000000 : ℝ)*X 2 1+(-1049690113/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2150361717/5000000000 : ℝ)*X 0 0+(1007534087/2500000000 : ℝ)*X 0 1+(2293772107/5000000000 : ℝ)*X 0 2+(2150361717/5000000000 : ℝ)*X 1 0+(1007534087/2500000000 : ℝ)*X 1 1+(2293772107/5000000000 : ℝ)*X 1 2+(2150361717/5000000000 : ℝ)*X 2 0+(1007534087/2500000000 : ℝ)*X 2 1+(2293772107/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1966697439/10000000000 : ℝ)*X 0 0+(5202378873/10000000000 : ℝ)*X 0 1+(5457351459/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5293274833/10000000000 : ℝ)*X 1 0+(-1842927373/10000000000 : ℝ)*X 1 1+(2728675913/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293274763/10000000000 : ℝ)*X 2 0+(27286759/50000000 : ℝ)*X 2 1+(-921463753/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4300822971/10000000000 : ℝ)*X 0 0+(229217309/500000000 : ℝ)*X 0 1+(252085051/625000000 : ℝ)*X 0 2+(4300822971/10000000000 : ℝ)*X 1 0+(229217309/500000000 : ℝ)*X 1 1+(252085051/625000000 : ℝ)*X 1 2+(4300822971/10000000000 : ℝ)*X 2 0+(229217309/500000000 : ℝ)*X 2 1+(252085051/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (83524423957197282769670787/7024375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (928816309/50000000000000 : ℝ)*(base19) + (1302915317/100000000000000 : ℝ)*(base23) + (6202671/4000000000000 : ℝ)*(lower2) + (348633957/100000000000000 : ℝ)*(upper3) + (59264173/50000000000000 : ℝ)*(upper5) + (3544300202827/125000000000 : ℝ)*(major0) + (3544300202827/125000000000 : ℝ)*(major1) + (3544300202827/125000000000 : ℝ)*(major2) + (969205250033177/25000000000000 : ℝ)*(sp0) + (3876838919870113/100000000000000 : ℝ)*(sp1) + (1938419737293707/50000000000000 : ℝ)*(sp2) + (358805501790307/20000000000000 : ℝ)*(sp3) + (9888685011/50000000000000 : ℝ)*(sp4) + (11641713743/100000000000000 : ℝ)*(sp7) + (897019575332639/50000000000000 : ℝ)*(f.failure) + (387684077750273/10000000000000 : ℝ)*(f.sum) + (553649852899/2247800000000000000000000000 : ℝ)*base66 + (15407258799327799/3512187500000000000000000000000 : ℝ)*base68 + (1313348911743553/439023437500000000000000000000 : ℝ)*base70 + (1202454882220163/1756093750000000000000000000000 : ℝ)*base71 + (11143961823401/5619500000000000000000000000 : ℝ)*base73 + (23493776806689973/7024375000000000000000000000000 : ℝ)*base76 + (42276864886057473/7024375000000000000000000000000 : ℝ)*base78 + (965120272015411/219511718750000000000000000000 : ℝ)*base79 + (15618018840767/5619500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (13057519/2500000000000000000000 : ℝ)*base89 + (13057519/2500000000000000000000 : ℝ)*base91 + (13057519/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (458979796260655850434669347/43902343750000000000000000000000 : ℝ) := by norm_num
    linear_combination (1262952403/100000000000000 : ℝ)*(base19) + (1437228357/100000000000000 : ℝ)*(base23) + (266609569/100000000000000 : ℝ)*(upper3) + (52190793/50000000000000 : ℝ)*(lower4) + (172651539/100000000000000 : ℝ)*(upper5) + (717114630131197/25000000000000 : ℝ)*(major0) + (717114630131197/25000000000000 : ℝ)*(major1) + (717114630131197/25000000000000 : ℝ)*(major2) + (17587708157/100000000000000 : ℝ)*(sp1) + (19872681613/100000000000000 : ℝ)*(sp2) + (1960993086324657/50000000000000 : ℝ)*(sp4) + (1960983660994377/50000000000000 : ℝ)*(sp5) + (245122803921209/6250000000000 : ℝ)*(sp6) + (907465259957421/50000000000000 : ℝ)*(sp7) + (907465259957421/50000000000000 : ℝ)*(f.failure) + (1960993086324657/50000000000000 : ℝ)*(f.sum) + (2452864893031/1756093750000000000000000000 : ℝ)*base65 + (234869641770252571/43902343750000000000000000000000 : ℝ)*base67 + (15723330286837223/21951171875000000000000000000000 : ℝ)*base69 + (1439962087808682159/175609375000000000000000000000000 : ℝ)*base71 + (3025716955701/7024375000000000000000000000 : ℝ)*base74 + (211658018965869659/175609375000000000000000000000000 : ℝ)*base75 + (425492845337239517/87804687500000000000000000000000 : ℝ)*base77 + (796396694705552017/87804687500000000000000000000000 : ℝ)*base79 + (133248134632569/28097500000000000000000000000 : ℝ)*base82 + (467741/2500000000000000000000 : ℝ)*base89 + (467741/2500000000000000000000 : ℝ)*base91 + (467741/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1426_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79023921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9433/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7627/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10351/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15809/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1426_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1426_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79023921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10351/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15809/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1426_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1426_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1426_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79023921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10351/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15809/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1426_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
