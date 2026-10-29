-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1477_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:12:26.699956+00:00
-- url     : https://prove2.me/submissions/af6a0a15-ea8c-46d3-b036-9c943ca36838

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
theorem support_rectangle_w1477_s0_0 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-344718739/2000000000 : ℝ)*x 0 + (594029027/1000000000 : ℝ)*x 1 + (2420031703/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (344718739/2000000000 : ℝ)^4451 ≤ (2548114209771/25000000000000 : ℝ)^3427 := by
    have hnat : (344718739 : ℕ)^4451*25000000000000^3427 ≤ 2548114209771^3427*2000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344718739 2000000000 2548114209771 25000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (594029027/1000000000 : ℝ)^4451 ≤ (50841760401299/100000000000000 : ℝ)^3427 := by
    have hnat : (594029027 : ℕ)^4451*100000000000000^3427 ≤ 50841760401299^3427*1000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      594029027 1000000000 50841760401299 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2420031703/5000000000 : ℝ)^4451 ≤ (19482891372979/50000000000000 : ℝ)^3427 := by
    have hnat : (2420031703 : ℕ)^4451*50000000000000^3427 ≤ 19482891372979^3427*5000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2420031703 5000000000 19482891372979 50000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-344718739/2000000000 : ℝ), (594029027/1000000000 : ℝ), (2420031703/5000000000 : ℝ)] ![(2548114209771/25000000000000 : ℝ), (50841760401299/100000000000000 : ℝ), (19482891372979/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-344718739/2000000000 : ℝ)|^4451 ≤ (2548114209771/25000000000000 : ℝ)^3427
        have hw : |(-344718739/2000000000 : ℝ)|=(344718739/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(594029027/1000000000 : ℝ)|^4451 ≤ (50841760401299/100000000000000 : ℝ)^3427
        have hw : |(594029027/1000000000 : ℝ)|=(594029027/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2420031703/5000000000 : ℝ)|^4451 ≤ (19482891372979/50000000000000 : ℝ)^3427
        have hw : |(2420031703/5000000000 : ℝ)|=(2420031703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1477_s0_1 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1097126921/2000000000 : ℝ)*x 0 + (-292891771/1250000000 : ℝ)*x 1 + (2420031723/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1097126921/2000000000 : ℝ)^4451 ≤ (22923288882817/50000000000000 : ℝ)^3427 := by
    have hnat : (1097126921 : ℕ)^4451*50000000000000^3427 ≤ 22923288882817^3427*2000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097126921 2000000000 22923288882817 50000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (292891771/1250000000 : ℝ)^4451 ≤ (3796909763801/25000000000000 : ℝ)^3427 := by
    have hnat : (292891771 : ℕ)^4451*25000000000000^3427 ≤ 3796909763801^3427*1250000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      292891771 1250000000 3796909763801 25000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2420031723/5000000000 : ℝ)^4451 ≤ (2435361447763/6250000000000 : ℝ)^3427 := by
    have hnat : (2420031723 : ℕ)^4451*6250000000000^3427 ≤ 2435361447763^3427*5000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2420031723 5000000000 2435361447763 6250000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1097126921/2000000000 : ℝ), (-292891771/1250000000 : ℝ), (2420031723/5000000000 : ℝ)] ![(22923288882817/50000000000000 : ℝ), (3796909763801/25000000000000 : ℝ), (2435361447763/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1097126921/2000000000 : ℝ)|^4451 ≤ (22923288882817/50000000000000 : ℝ)^3427
        have hw : |(1097126921/2000000000 : ℝ)|=(1097126921/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-292891771/1250000000 : ℝ)|^4451 ≤ (3796909763801/25000000000000 : ℝ)^3427
        have hw : |(-292891771/1250000000 : ℝ)|=(292891771/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2420031723/5000000000 : ℝ)|^4451 ≤ (2435361447763/6250000000000 : ℝ)^3427
        have hw : |(2420031723/5000000000 : ℝ)|=(2420031723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1477_s0_2 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (685704319/1250000000 : ℝ)*x 0 + (2420031731/5000000000 : ℝ)*x 1 + (-292891777/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (685704319/1250000000 : ℝ)^4451 ≤ (45846577190327/100000000000000 : ℝ)^3427 := by
    have hnat : (685704319 : ℕ)^4451*100000000000000^3427 ≤ 45846577190327^3427*1250000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685704319 1250000000 45846577190327 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2420031731/5000000000 : ℝ)^4451 ≤ (9741445832877/25000000000000 : ℝ)^3427 := by
    have hnat : (2420031731 : ℕ)^4451*25000000000000^3427 ≤ 9741445832877^3427*5000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2420031731 5000000000 9741445832877 25000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (292891777/1250000000 : ℝ)^4451 ≤ (7593819729647/50000000000000 : ℝ)^3427 := by
    have hnat : (292891777 : ℕ)^4451*50000000000000^3427 ≤ 7593819729647^3427*1250000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      292891777 1250000000 7593819729647 50000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(685704319/1250000000 : ℝ), (2420031731/5000000000 : ℝ), (-292891777/1250000000 : ℝ)] ![(45846577190327/100000000000000 : ℝ), (9741445832877/25000000000000 : ℝ), (7593819729647/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(685704319/1250000000 : ℝ)|^4451 ≤ (45846577190327/100000000000000 : ℝ)^3427
        have hw : |(685704319/1250000000 : ℝ)|=(685704319/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2420031731/5000000000 : ℝ)|^4451 ≤ (9741445832877/25000000000000 : ℝ)^3427
        have hw : |(2420031731/5000000000 : ℝ)|=(2420031731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-292891777/1250000000 : ℝ)|^4451 ≤ (7593819729647/50000000000000 : ℝ)^3427
        have hw : |(-292891777/1250000000 : ℝ)|=(292891777/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1477_s0_3 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4154719137/10000000000 : ℝ)*x 0 + (3091549551/10000000000 : ℝ)*x 1 + (1381250793/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4154719137/10000000000 : ℝ)^4451 ≤ (31956598132253/100000000000000 : ℝ)^3427 := by
    have hnat : (4154719137 : ℕ)^4451*100000000000000^3427 ≤ 31956598132253^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4154719137 10000000000 31956598132253 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3091549551/10000000000 : ℝ)^4451 ≤ (21769027052441/100000000000000 : ℝ)^3427 := by
    have hnat : (3091549551 : ℕ)^4451*100000000000000^3427 ≤ 21769027052441^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3091549551 10000000000 21769027052441 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1381250793/2500000000 : ℝ)^4451 ≤ (1446074212513/3125000000000 : ℝ)^3427 := by
    have hnat : (1381250793 : ℕ)^4451*3125000000000^3427 ≤ 1446074212513^3427*2500000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1381250793 2500000000 1446074212513 3125000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4154719137/10000000000 : ℝ), (3091549551/10000000000 : ℝ), (1381250793/2500000000 : ℝ)] ![(31956598132253/100000000000000 : ℝ), (21769027052441/100000000000000 : ℝ), (1446074212513/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4154719137/10000000000 : ℝ)|^4451 ≤ (31956598132253/100000000000000 : ℝ)^3427
        have hw : |(4154719137/10000000000 : ℝ)|=(4154719137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3091549551/10000000000 : ℝ)|^4451 ≤ (21769027052441/100000000000000 : ℝ)^3427
        have hw : |(3091549551/10000000000 : ℝ)|=(3091549551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1381250793/2500000000 : ℝ)|^4451 ≤ (1446074212513/3125000000000 : ℝ)^3427
        have hw : |(1381250793/2500000000 : ℝ)|=(1381250793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1477_s0_4 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1727424643/10000000000 : ℝ)*x 0 + (2434151699/5000000000 : ℝ)*x 1 + (5911034397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1727424643/10000000000 : ℝ)^4451 ≤ (1277736257989/12500000000000 : ℝ)^3427 := by
    have hnat : (1727424643 : ℕ)^4451*12500000000000^3427 ≤ 1277736257989^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1727424643 10000000000 1277736257989 12500000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2434151699/5000000000 : ℝ)^4451 ≤ (39261324134891/100000000000000 : ℝ)^3427 := by
    have hnat : (2434151699 : ℕ)^4451*100000000000000^3427 ≤ 39261324134891^3427*5000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2434151699 5000000000 39261324134891 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5911034397/10000000000 : ℝ)^4451 ≤ (25258392898753/50000000000000 : ℝ)^3427 := by
    have hnat : (5911034397 : ℕ)^4451*50000000000000^3427 ≤ 25258392898753^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5911034397 10000000000 25258392898753 50000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1727424643/10000000000 : ℝ), (2434151699/5000000000 : ℝ), (5911034397/10000000000 : ℝ)] ![(1277736257989/12500000000000 : ℝ), (39261324134891/100000000000000 : ℝ), (25258392898753/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1727424643/10000000000 : ℝ)|^4451 ≤ (1277736257989/12500000000000 : ℝ)^3427
        have hw : |(-1727424643/10000000000 : ℝ)|=(1727424643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2434151699/5000000000 : ℝ)|^4451 ≤ (39261324134891/100000000000000 : ℝ)^3427
        have hw : |(2434151699/5000000000 : ℝ)|=(2434151699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5911034397/10000000000 : ℝ)|^4451 ≤ (25258392898753/50000000000000 : ℝ)^3427
        have hw : |(5911034397/10000000000 : ℝ)|=(5911034397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1477_s0_5 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2592621237/5000000000 : ℝ)*x 0 + (-1272162891/10000000000 : ℝ)*x 1 + (5911034527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2592621237/5000000000 : ℝ)^4451 ≤ (10653223648893/25000000000000 : ℝ)^3427 := by
    have hnat : (2592621237 : ℕ)^4451*25000000000000^3427 ≤ 10653223648893^3427*5000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592621237 5000000000 10653223648893 25000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1272162891/10000000000 : ℝ)^4451 ≤ (68703181477/1000000000000 : ℝ)^3427 := by
    have hnat : (1272162891 : ℕ)^4451*1000000000000^3427 ≤ 68703181477^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1272162891 10000000000 68703181477 1000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5911034527/10000000000 : ℝ)^4451 ≤ (25258393620241/50000000000000 : ℝ)^3427 := by
    have hnat : (5911034527 : ℕ)^4451*50000000000000^3427 ≤ 25258393620241^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5911034527 10000000000 25258393620241 50000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2592621237/5000000000 : ℝ), (-1272162891/10000000000 : ℝ), (5911034527/10000000000 : ℝ)] ![(10653223648893/25000000000000 : ℝ), (68703181477/1000000000000 : ℝ), (25258393620241/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2592621237/5000000000 : ℝ)|^4451 ≤ (10653223648893/25000000000000 : ℝ)^3427
        have hw : |(2592621237/5000000000 : ℝ)|=(2592621237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1272162891/10000000000 : ℝ)|^4451 ≤ (68703181477/1000000000000 : ℝ)^3427
        have hw : |(-1272162891/10000000000 : ℝ)|=(1272162891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5911034527/10000000000 : ℝ)|^4451 ≤ (25258393620241/50000000000000 : ℝ)^3427
        have hw : |(5911034527/10000000000 : ℝ)|=(5911034527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1477_s0_6 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2592621213/5000000000 : ℝ)*x 0 + (591103437/1000000000 : ℝ)*x 1 + (-318040803/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2592621213/5000000000 : ℝ)^4451 ≤ (21306447041617/50000000000000 : ℝ)^3427 := by
    have hnat : (2592621213 : ℕ)^4451*50000000000000^3427 ≤ 21306447041617^3427*5000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592621213 5000000000 21306447041617 50000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (591103437/1000000000 : ℝ)^4451 ≤ (50516785497811/100000000000000 : ℝ)^3427 := by
    have hnat : (591103437 : ℕ)^4451*100000000000000^3427 ≤ 50516785497811^3427*1000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      591103437 1000000000 50516785497811 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (318040803/2500000000 : ℝ)^4451 ≤ (858790049907/12500000000000 : ℝ)^3427 := by
    have hnat : (318040803 : ℕ)^4451*12500000000000^3427 ≤ 858790049907^3427*2500000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      318040803 2500000000 858790049907 12500000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2592621213/5000000000 : ℝ), (591103437/1000000000 : ℝ), (-318040803/2500000000 : ℝ)] ![(21306447041617/50000000000000 : ℝ), (50516785497811/100000000000000 : ℝ), (858790049907/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2592621213/5000000000 : ℝ)|^4451 ≤ (21306447041617/50000000000000 : ℝ)^3427
        have hw : |(2592621213/5000000000 : ℝ)|=(2592621213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(591103437/1000000000 : ℝ)|^4451 ≤ (50516785497811/100000000000000 : ℝ)^3427
        have hw : |(591103437/1000000000 : ℝ)|=(591103437/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-318040803/2500000000 : ℝ)|^4451 ≤ (858790049907/12500000000000 : ℝ)^3427
        have hw : |(-318040803/2500000000 : ℝ)|=(318040803/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1477_s0_7 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4163192979/10000000000 : ℝ)*x 0 + (5462542481/10000000000 : ℝ)*x 1 + (157812849/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4163192979/10000000000 : ℝ)^4451 ≤ (4005159623379/12500000000000 : ℝ)^3427 := by
    have hnat : (4163192979 : ℕ)^4451*12500000000000^3427 ≤ 4005159623379^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4163192979 10000000000 4005159623379 12500000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5462542481/10000000000 : ℝ)^4451 ≤ (45596074190977/100000000000000 : ℝ)^3427 := by
    have hnat : (5462542481 : ℕ)^4451*100000000000000^3427 ≤ 45596074190977^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462542481 10000000000 45596074190977 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (157812849/500000000 : ℝ)^4451 ≤ (22362648816611/100000000000000 : ℝ)^3427 := by
    have hnat : (157812849 : ℕ)^4451*100000000000000^3427 ≤ 22362648816611^3427*500000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157812849 500000000 22362648816611 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4163192979/10000000000 : ℝ), (5462542481/10000000000 : ℝ), (157812849/500000000 : ℝ)] ![(4005159623379/12500000000000 : ℝ), (45596074190977/100000000000000 : ℝ), (22362648816611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4163192979/10000000000 : ℝ)|^4451 ≤ (4005159623379/12500000000000 : ℝ)^3427
        have hw : |(4163192979/10000000000 : ℝ)|=(4163192979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5462542481/10000000000 : ℝ)|^4451 ≤ (45596074190977/100000000000000 : ℝ)^3427
        have hw : |(5462542481/10000000000 : ℝ)|=(5462542481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(157812849/500000000 : ℝ)|^4451 ≤ (22362648816611/100000000000000 : ℝ)^3427
        have hw : |(157812849/500000000 : ℝ)|=(157812849/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1477_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160588719/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (473/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5189/20000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4449/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4449 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4449*1^1024 ≤ 0^1024*1^4449 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4449 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4449 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4449/1024 : ℝ) ≤ (93331764895608491/5000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4449 ≤ (93331764895608491/5000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4449*5000000000000000000^1024 ≤ 93331764895608491^1024*5^4449 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 93331764895608491 5000000000000000000 4449 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (93331764895608491/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4449 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4449/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4449 := by
      have hnat : (1 : ℕ)^1024*1^4449 ≤ 1^4449*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4449 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4449 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5093331764895608491/5000000000000000000 : ℝ) ≤ (1004265790446187/1000000000000000 : ℝ) ^ (4449/1024 : ℝ) := by
    have hpowers : (5093331764895608491/5000000000000000000 : ℝ)^1024 ≤ (1004265790446187/1000000000000000 : ℝ)^4449 := by
      have hnat : (5093331764895608491 : ℕ)^1024*1000000000000000^4449 ≤ 1004265790446187^4449*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5093331764895608491 5000000000000000000 1004265790446187 1000000000000000 1024 4449 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1004265790446187/1000000000000000 : ℝ)) (X := (5093331764895608491/5000000000000000000 : ℝ)) (by norm_num) 4449 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2593331764895608491/2500000000000000000 : ℝ) ≤ (504265790446187/500000000000000 : ℝ) ^ (4449/1024 : ℝ) := by
    have hpowers : (2593331764895608491/2500000000000000000 : ℝ)^1024 ≤ (504265790446187/500000000000000 : ℝ)^4449 := by
      have hnat : (2593331764895608491 : ℕ)^1024*500000000000000^4449 ≤ 504265790446187^4449*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2593331764895608491 2500000000000000000 504265790446187 500000000000000 1024 4449 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (504265790446187/500000000000000 : ℝ)) (X := (2593331764895608491/2500000000000000000 : ℝ)) (by norm_num) 4449 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(4265790446187/400000000000000 : ℝ)*(0 : ℝ))^(4449/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(4265790446187/400000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(93331764895608491/5000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(4265790446187/400000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4449/1024 : ℝ) := by
    rw [show (1 : ℝ)+(4265790446187/400000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1004265790446187/1000000000000000 : ℝ) by norm_num, show 1+(93331764895608491/5000000000000000000 : ℝ)+(0 : ℝ)=(5093331764895608491/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(93331764895608491/5000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(4265790446187/400000000000000 : ℝ)*(2/5 : ℝ))^(4449/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(4265790446187/400000000000000 : ℝ)*(2/5 : ℝ)=(504265790446187/500000000000000 : ℝ) by norm_num, show 1+2*(93331764895608491/5000000000000000000 : ℝ)=(2593331764895608491/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(4265790446187/400000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4449/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4265790446187/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(4265790446187/400000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4449/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4265790446187/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(4265790446187/400000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4449/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4265790446187/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-344718739/2000000000 : ℝ)*X 0 0+(594029027/1000000000 : ℝ)*X 0 1+(2420031703/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1097126921/2000000000 : ℝ)*X 1 0+(-292891771/1250000000 : ℝ)*X 1 1+(2420031723/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((685704319/1250000000 : ℝ)*X 2 0+(2420031731/5000000000 : ℝ)*X 2 1+(-292891777/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4154719137/10000000000 : ℝ)*X 0 0+(3091549551/10000000000 : ℝ)*X 0 1+(1381250793/2500000000 : ℝ)*X 0 2+(4154719137/10000000000 : ℝ)*X 1 0+(3091549551/10000000000 : ℝ)*X 1 1+(1381250793/2500000000 : ℝ)*X 1 2+(4154719137/10000000000 : ℝ)*X 2 0+(3091549551/10000000000 : ℝ)*X 2 1+(1381250793/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1727424643/10000000000 : ℝ)*X 0 0+(2434151699/5000000000 : ℝ)*X 0 1+(5911034397/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2592621237/5000000000 : ℝ)*X 1 0+(-1272162891/10000000000 : ℝ)*X 1 1+(5911034527/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2592621213/5000000000 : ℝ)*X 2 0+(591103437/1000000000 : ℝ)*X 2 1+(-318040803/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4163192979/10000000000 : ℝ)*X 0 0+(5462542481/10000000000 : ℝ)*X 0 1+(157812849/500000000 : ℝ)*X 0 2+(4163192979/10000000000 : ℝ)*X 1 0+(5462542481/10000000000 : ℝ)*X 1 1+(157812849/500000000 : ℝ)*X 1 2+(4163192979/10000000000 : ℝ)*X 2 0+(5462542481/10000000000 : ℝ)*X 2 1+(157812849/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (33300618952359723536481/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (27320737/50000000000000 : ℝ)*(base1) + (372054027/25000000000000 : ℝ)*(base19) + (295886913/20000000000000 : ℝ)*(base23) + (194775827/100000000000000 : ℝ)*(upper3) + (178946873/100000000000000 : ℝ)*(upper5) + (164982124645279/25000000000000 : ℝ)*(major0) + (164982124645279/25000000000000 : ℝ)*(major1) + (164982124645279/25000000000000 : ℝ)*(major2) + (908908442757563/100000000000000 : ℝ)*(sp0) + (908912038443243/100000000000000 : ℝ)*(sp1) + (454456023612393/50000000000000 : ℝ)*(sp2) + (102735202587497/25000000000000 : ℝ)*(sp3) + (2569271631/50000000000000 : ℝ)*(sp4) + (2383507281/100000000000000 : ℝ)*(sp7) + (410943248498741/100000000000000 : ℝ)*(f.failure) + (113614190832419/12500000000000 : ℝ)*(f.sum) + (18871135418827/5000000000000000000000000000 : ℝ)*base66 + (165245248827/10000000000000000000000000000 : ℝ)*base68 + (31675954021173/10000000000000000000000000000 : ℝ)*base69 + (18003268401173/10000000000000000000000000000 : ℝ)*base71 + (13983150523827/5000000000000000000000000000 : ℝ)*base74 + (45382226161173/10000000000000000000000000000 : ℝ)*base75 + (41371449831173/10000000000000000000000000000 : ℝ)*base77 + (13865226291173/10000000000000000000000000000 : ℝ)*base79 + (217735401173/5000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (109697221/10000000000000000000000 : ℝ)*base90 + (109697221/10000000000000000000000 : ℝ)*base92 + (109697221/10000000000000000000000 : ℝ)*base94 + (1/50000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (93979930363545501639741/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1090531397/100000000000000 : ℝ)*(base19) + (539417529/50000000000000 : ℝ)*(base23) + (58460087/50000000000000 : ℝ)*(base32) + (82478891/50000000000000 : ℝ)*(upper3) + (95474459/100000000000000 : ℝ)*(upper5) + (696308599248381/100000000000000 : ℝ)*(major0) + (696308599248381/100000000000000 : ℝ)*(major1) + (696308599248381/100000000000000 : ℝ)*(major2) + (1369896909/50000000000000 : ℝ)*(sp1) + (672784813/25000000000000 : ℝ)*(sp2) + (95901958646047/10000000000000 : ℝ)*(sp4) + (191803151227051/20000000000000 : ℝ)*(sp5) + (11987697706077/1250000000000 : ℝ)*(sp6) + (433597338482893/100000000000000 : ℝ)*(sp7) + (216798727701533/50000000000000 : ℝ)*(f.failure) + (95901958646047/10000000000000 : ℝ)*(f.sum) + (36358093366753/20000000000000000000000000000 : ℝ)*base66 + (83759356346753/40000000000000000000000000000 : ℝ)*base68 + (344453638173247/40000000000000000000000000000 : ℝ)*base69 + (174162787093247/40000000000000000000000000000 : ℝ)*base71 + (81550810706753/20000000000000000000000000000 : ℝ)*base74 + (8135946746753/40000000000000000000000000000 : ℝ)*base76 + (46652126933247/40000000000000000000000000000 : ℝ)*base77 + (13953458906753/40000000000000000000000000000 : ℝ)*base80 + (68141811613247/20000000000000000000000000000 : ℝ)*base81 + (51193773/5000000000000000000000 : ℝ)*base90 + (51193773/5000000000000000000000 : ℝ)*base92 + (51193773/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1477_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160588719/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (473/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5189/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1477_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1477_s1_0 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-943413379/5000000000 : ℝ)*x 0 + (223796919/400000000 : ℝ)*x 1 + (1016133593/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (943413379/5000000000 : ℝ)^4451 ≤ (11463523759921/100000000000000 : ℝ)^3427 := by
    have hnat : (943413379 : ℕ)^4451*100000000000000^3427 ≤ 11463523759921^3427*5000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      943413379 5000000000 11463523759921 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (223796919/400000000 : ℝ)^4451 ≤ (47036400555093/100000000000000 : ℝ)^3427 := by
    have hnat : (223796919 : ℕ)^4451*100000000000000^3427 ≤ 47036400555093^3427*400000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223796919 400000000 47036400555093 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1016133593/2000000000 : ℝ)^4451 ≤ (10375018916907/25000000000000 : ℝ)^3427 := by
    have hnat : (1016133593 : ℕ)^4451*25000000000000^3427 ≤ 10375018916907^3427*2000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016133593 2000000000 10375018916907 25000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-943413379/5000000000 : ℝ), (223796919/400000000 : ℝ), (1016133593/2000000000 : ℝ)] ![(11463523759921/100000000000000 : ℝ), (47036400555093/100000000000000 : ℝ), (10375018916907/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-943413379/5000000000 : ℝ)|^4451 ≤ (11463523759921/100000000000000 : ℝ)^3427
        have hw : |(-943413379/5000000000 : ℝ)|=(943413379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(223796919/400000000 : ℝ)|^4451 ≤ (47036400555093/100000000000000 : ℝ)^3427
        have hw : |(223796919/400000000 : ℝ)|=(223796919/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1016133593/2000000000 : ℝ)|^4451 ≤ (10375018916907/25000000000000 : ℝ)^3427
        have hw : |(1016133593/2000000000 : ℝ)|=(1016133593/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1477_s1_1 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5393131461/10000000000 : ℝ)*x 0 + (-431771887/2000000000 : ℝ)*x 1 + (1270167561/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5393131461/10000000000 : ℝ)^4451 ≤ (44845010404583/100000000000000 : ℝ)^3427 := by
    have hnat : (5393131461 : ℕ)^4451*100000000000000^3427 ≤ 44845010404583^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393131461 10000000000 44845010404583 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (431771887/2000000000 : ℝ)^4451 ≤ (853430608577/6250000000000 : ℝ)^3427 := by
    have hnat : (431771887 : ℕ)^4451*6250000000000^3427 ≤ 853430608577^3427*2000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431771887 2000000000 853430608577 6250000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1270167561/2500000000 : ℝ)^4451 ≤ (2075004992269/5000000000000 : ℝ)^3427 := by
    have hnat : (1270167561 : ℕ)^4451*5000000000000^3427 ≤ 2075004992269^3427*2500000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1270167561 2500000000 2075004992269 5000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5393131461/10000000000 : ℝ), (-431771887/2000000000 : ℝ), (1270167561/2500000000 : ℝ)] ![(44845010404583/100000000000000 : ℝ), (853430608577/6250000000000 : ℝ), (2075004992269/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5393131461/10000000000 : ℝ)|^4451 ≤ (44845010404583/100000000000000 : ℝ)^3427
        have hw : |(5393131461/10000000000 : ℝ)|=(5393131461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-431771887/2000000000 : ℝ)|^4451 ≤ (853430608577/6250000000000 : ℝ)^3427
        have hw : |(-431771887/2000000000 : ℝ)|=(431771887/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1270167561/2500000000 : ℝ)|^4451 ≤ (2075004992269/5000000000000 : ℝ)^3427
        have hw : |(1270167561/2500000000 : ℝ)|=(1270167561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1477_s1_2 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (674141651/1250000000 : ℝ)*x 0 + (1016133671/2000000000 : ℝ)*x 1 + (-1079429789/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (674141651/1250000000 : ℝ)^4451 ≤ (44845029271873/100000000000000 : ℝ)^3427 := by
    have hnat : (674141651 : ℕ)^4451*100000000000000^3427 ≤ 44845029271873^3427*1250000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674141651 1250000000 44845029271873 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1016133671/2000000000 : ℝ)^4451 ≤ (41500079805111/100000000000000 : ℝ)^3427 := by
    have hnat : (1016133671 : ℕ)^4451*100000000000000^3427 ≤ 41500079805111^3427*2000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016133671 2000000000 41500079805111 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1079429789/5000000000 : ℝ)^4451 ≤ (1706861363997/12500000000000 : ℝ)^3427 := by
    have hnat : (1079429789 : ℕ)^4451*12500000000000^3427 ≤ 1706861363997^3427*5000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079429789 5000000000 1706861363997 12500000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(674141651/1250000000 : ℝ), (1016133671/2000000000 : ℝ), (-1079429789/5000000000 : ℝ)] ![(44845029271873/100000000000000 : ℝ), (41500079805111/100000000000000 : ℝ), (1706861363997/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(674141651/1250000000 : ℝ)|^4451 ≤ (44845029271873/100000000000000 : ℝ)^3427
        have hw : |(674141651/1250000000 : ℝ)|=(674141651/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1016133671/2000000000 : ℝ)|^4451 ≤ (41500079805111/100000000000000 : ℝ)^3427
        have hw : |(1016133671/2000000000 : ℝ)|=(1016133671/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1079429789/5000000000 : ℝ)|^4451 ≤ (1706861363997/12500000000000 : ℝ)^3427
        have hw : |(-1079429789/5000000000 : ℝ)|=(1079429789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1477_s1_3 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (852470729/2000000000 : ℝ)*x 0 + (1863310273/5000000000 : ℝ)*x 1 + (2432015771/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (852470729/2000000000 : ℝ)^4451 ≤ (4129499497739/12500000000000 : ℝ)^3427 := by
    have hnat : (852470729 : ℕ)^4451*12500000000000^3427 ≤ 4129499497739^3427*2000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      852470729 2000000000 4129499497739 12500000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1863310273/5000000000 : ℝ)^4451 ≤ (27747419296063/100000000000000 : ℝ)^3427 := by
    have hnat : (1863310273 : ℕ)^4451*100000000000000^3427 ≤ 27747419296063^3427*5000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1863310273 5000000000 27747419296063 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2432015771/5000000000 : ℝ)^4451 ≤ (39216584704489/100000000000000 : ℝ)^3427 := by
    have hnat : (2432015771 : ℕ)^4451*100000000000000^3427 ≤ 39216584704489^3427*5000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2432015771 5000000000 39216584704489 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(852470729/2000000000 : ℝ), (1863310273/5000000000 : ℝ), (2432015771/5000000000 : ℝ)] ![(4129499497739/12500000000000 : ℝ), (27747419296063/100000000000000 : ℝ), (39216584704489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(852470729/2000000000 : ℝ)|^4451 ≤ (4129499497739/12500000000000 : ℝ)^3427
        have hw : |(852470729/2000000000 : ℝ)|=(852470729/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1863310273/5000000000 : ℝ)|^4451 ≤ (27747419296063/100000000000000 : ℝ)^3427
        have hw : |(1863310273/5000000000 : ℝ)|=(1863310273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2432015771/5000000000 : ℝ)|^4451 ≤ (39216584704489/100000000000000 : ℝ)^3427
        have hw : |(2432015771/5000000000 : ℝ)|=(2432015771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1477_s1_4 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-943601677/5000000000 : ℝ)*x 0 + (158959747/312500000 : ℝ)*x 1 + (5588776457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (943601677/5000000000 : ℝ)^4451 ≤ (286662388771/2500000000000 : ℝ)^3427 := by
    have hnat : (943601677 : ℕ)^4451*2500000000000^3427 ≤ 286662388771^3427*5000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      943601677 5000000000 286662388771 2500000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (158959747/312500000 : ℝ)^4451 ≤ (10391051695821/25000000000000 : ℝ)^3427 := by
    have hnat : (158959747 : ℕ)^4451*25000000000000^3427 ≤ 10391051695821^3427*312500000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      158959747 312500000 10391051695821 25000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5588776457/10000000000 : ℝ)^4451 ≤ (11742324412971/25000000000000 : ℝ)^3427 := by
    have hnat : (5588776457 : ℕ)^4451*25000000000000^3427 ≤ 11742324412971^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5588776457 10000000000 11742324412971 25000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-943601677/5000000000 : ℝ), (158959747/312500000 : ℝ), (5588776457/10000000000 : ℝ)] ![(286662388771/2500000000000 : ℝ), (10391051695821/25000000000000 : ℝ), (11742324412971/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-943601677/5000000000 : ℝ)|^4451 ≤ (286662388771/2500000000000 : ℝ)^3427
        have hw : |(-943601677/5000000000 : ℝ)|=(943601677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(158959747/312500000 : ℝ)|^4451 ≤ (10391051695821/25000000000000 : ℝ)^3427
        have hw : |(158959747/312500000 : ℝ)|=(158959747/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5588776457/10000000000 : ℝ)|^4451 ≤ (11742324412971/25000000000000 : ℝ)^3427
        have hw : |(5588776457/10000000000 : ℝ)|=(5588776457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1477_s1_5 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1314570453/2500000000 : ℝ)*x 0 + (-825376301/5000000000 : ℝ)*x 1 + (5588776489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314570453/2500000000 : ℝ)^4451 ≤ (21697065345163/50000000000000 : ℝ)^3427 := by
    have hnat : (1314570453 : ℕ)^4451*50000000000000^3427 ≤ 21697065345163^3427*2500000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314570453 2500000000 21697065345163 50000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (825376301/5000000000 : ℝ)^4451 ≤ (4818285644809/50000000000000 : ℝ)^3427 := by
    have hnat : (825376301 : ℕ)^4451*50000000000000^3427 ≤ 4818285644809^3427*5000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      825376301 5000000000 4818285644809 50000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5588776489/10000000000 : ℝ)^4451 ≤ (23484649000589/50000000000000 : ℝ)^3427 := by
    have hnat : (5588776489 : ℕ)^4451*50000000000000^3427 ≤ 23484649000589^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5588776489 10000000000 23484649000589 50000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314570453/2500000000 : ℝ), (-825376301/5000000000 : ℝ), (5588776489/10000000000 : ℝ)] ![(21697065345163/50000000000000 : ℝ), (4818285644809/50000000000000 : ℝ), (23484649000589/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314570453/2500000000 : ℝ)|^4451 ≤ (21697065345163/50000000000000 : ℝ)^3427
        have hw : |(1314570453/2500000000 : ℝ)|=(1314570453/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-825376301/5000000000 : ℝ)|^4451 ≤ (4818285644809/50000000000000 : ℝ)^3427
        have hw : |(-825376301/5000000000 : ℝ)|=(825376301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5588776489/10000000000 : ℝ)|^4451 ≤ (23484649000589/50000000000000 : ℝ)^3427
        have hw : |(5588776489/10000000000 : ℝ)|=(5588776489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1477_s1_6 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (657285231/1250000000 : ℝ)*x 0 + (1117755291/2000000000 : ℝ)*x 1 + (-8253763/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (657285231/1250000000 : ℝ)^4451 ≤ (43394131076189/100000000000000 : ℝ)^3427 := by
    have hnat : (657285231 : ℕ)^4451*100000000000000^3427 ≤ 43394131076189^3427*1250000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657285231 1250000000 43394131076189 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1117755291/2000000000 : ℝ)^4451 ≤ (46969297630053/100000000000000 : ℝ)^3427 := by
    have hnat : (1117755291 : ℕ)^4451*100000000000000^3427 ≤ 46969297630053^3427*2000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1117755291 2000000000 46969297630053 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8253763/50000000 : ℝ)^4451 ≤ (4818285637227/50000000000000 : ℝ)^3427 := by
    have hnat : (8253763 : ℕ)^4451*50000000000000^3427 ≤ 4818285637227^3427*50000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8253763 50000000 4818285637227 50000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(657285231/1250000000 : ℝ), (1117755291/2000000000 : ℝ), (-8253763/50000000 : ℝ)] ![(43394131076189/100000000000000 : ℝ), (46969297630053/100000000000000 : ℝ), (4818285637227/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(657285231/1250000000 : ℝ)|^4451 ≤ (43394131076189/100000000000000 : ℝ)^3427
        have hw : |(657285231/1250000000 : ℝ)|=(657285231/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1117755291/2000000000 : ℝ)|^4451 ≤ (46969297630053/100000000000000 : ℝ)^3427
        have hw : |(1117755291/2000000000 : ℝ)|=(1117755291/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8253763/50000000 : ℝ)|^4451 ≤ (4818285637227/50000000000000 : ℝ)^3427
        have hw : |(-8253763/50000000 : ℝ)|=(8253763/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1477_s1_7 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4263187659/10000000000 : ℝ)*x 0 + (4850665871/10000000000 : ℝ)*x 1 + (3740211947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4263187659/10000000000 : ℝ)^4451 ≤ (2065274492853/6250000000000 : ℝ)^3427 := by
    have hnat : (4263187659 : ℕ)^4451*6250000000000^3427 ≤ 2065274492853^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4263187659 10000000000 2065274492853 6250000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4850665871/10000000000 : ℝ)^4451 ≤ (39076681005033/100000000000000 : ℝ)^3427 := by
    have hnat : (4850665871 : ℕ)^4451*100000000000000^3427 ≤ 39076681005033^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4850665871 10000000000 39076681005033 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3740211947/10000000000 : ℝ)^4451 ≤ (13939463548203/50000000000000 : ℝ)^3427 := by
    have hnat : (3740211947 : ℕ)^4451*50000000000000^3427 ≤ 13939463548203^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3740211947 10000000000 13939463548203 50000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4263187659/10000000000 : ℝ), (4850665871/10000000000 : ℝ), (3740211947/10000000000 : ℝ)] ![(2065274492853/6250000000000 : ℝ), (39076681005033/100000000000000 : ℝ), (13939463548203/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4263187659/10000000000 : ℝ)|^4451 ≤ (2065274492853/6250000000000 : ℝ)^3427
        have hw : |(4263187659/10000000000 : ℝ)|=(4263187659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4850665871/10000000000 : ℝ)|^4451 ≤ (39076681005033/100000000000000 : ℝ)^3427
        have hw : |(4850665871/10000000000 : ℝ)|=(4850665871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3740211947/10000000000 : ℝ)|^4451 ≤ (13939463548203/50000000000000 : ℝ)^3427
        have hw : |(3740211947/10000000000 : ℝ)|=(3740211947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1477_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160588719/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5189/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (473/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (7861/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4683/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5189/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (473/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5189/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (473/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5189/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (473/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5189/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (473/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5189/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (473/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5189/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (473/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (473/20000 : ℝ) ^ (4449/1024 : ℝ) ≤ (860480396957/10000000000000000000 : ℝ) := by
    have hpowers : (473/20000 : ℝ)^4449 ≤ (860480396957/10000000000000000000 : ℝ)^1024 := by
      have hnat : (473 : ℕ)^4449*10000000000000000000^1024 ≤ 860480396957^1024*20000^4449 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        473 20000 860480396957 10000000000000000000 4449 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (473/20000 : ℝ)) (X := (860480396957/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4449 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (5189/20000 : ℝ) ^ (4449/1024 : ℝ) ≤ (35574061433121501/12500000000000000000 : ℝ) := by
    have hpowers : (5189/20000 : ℝ)^4449 ≤ (35574061433121501/12500000000000000000 : ℝ)^1024 := by
      have hnat : (5189 : ℕ)^4449*12500000000000000000^1024 ≤ 35574061433121501^1024*20000^4449 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5189 20000 35574061433121501 12500000000000000000 4449 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5189/20000 : ℝ)) (X := (35574061433121501/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4449 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000000860480396957/5000000000000000000 : ℝ) ≤ (2000000079220667/2000000000000000 : ℝ) ^ (4449/1024 : ℝ) := by
    have hpowers : (5000000860480396957/5000000000000000000 : ℝ)^1024 ≤ (2000000079220667/2000000000000000 : ℝ)^4449 := by
      have hnat : (5000000860480396957 : ℕ)^1024*2000000000000000^4449 ≤ 2000000079220667^4449*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000000860480396957 5000000000000000000 2000000079220667 2000000000000000 1024 4449 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000079220667/2000000000000000 : ℝ)) (X := (5000000860480396957/5000000000000000000 : ℝ)) (by norm_num) 4449 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50142300548134470789/50000000000000000000 : ℝ) ≤ (10006543331084253/10000000000000000 : ℝ) ^ (4449/1024 : ℝ) := by
    have hpowers : (50142300548134470789/50000000000000000000 : ℝ)^1024 ≤ (10006543331084253/10000000000000000 : ℝ)^4449 := by
      have hnat : (50142300548134470789 : ℕ)^1024*10000000000000000^4449 ≤ 10006543331084253^4449*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50142300548134470789 50000000000000000000 10006543331084253 10000000000000000 1024 4449 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006543331084253/10000000000000000 : ℝ)) (X := (50142300548134470789/50000000000000000000 : ℝ)) (by norm_num) 4449 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6285574061433121501/6250000000000000000 : ℝ) ≤ (10013086266065171/10000000000000000 : ℝ) ^ (4449/1024 : ℝ) := by
    have hpowers : (6285574061433121501/6250000000000000000 : ℝ)^1024 ≤ (10013086266065171/10000000000000000 : ℝ)^4449 := by
      have hnat : (6285574061433121501 : ℕ)^1024*10000000000000000^4449 ≤ 10013086266065171^4449*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6285574061433121501 6250000000000000000 10013086266065171 10000000000000000 1024 4449 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10013086266065171/10000000000000000 : ℝ)) (X := (6285574061433121501/6250000000000000000 : ℝ)) (by norm_num) 4449 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(860480396957/10000000000000000000 : ℝ) ≤ ((5894226531441422429/5895000000000000000 : ℝ)+2*(3271467490459/1179000000000000 : ℝ)*(473/20000 : ℝ))^(4449/1024 : ℝ) := by
    rw [show (5894226531441422429/5895000000000000000 : ℝ)+2*(3271467490459/1179000000000000 : ℝ)*(473/20000 : ℝ)=(2000000079220667/2000000000000000 : ℝ) by norm_num, show 1+2*(860480396957/10000000000000000000 : ℝ)=(5000000860480396957/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35574061433121501/12500000000000000000 : ℝ)+(860480396957/10000000000000000000 : ℝ) ≤ ((5894226531441422429/5895000000000000000 : ℝ)+(3271467490459/1179000000000000 : ℝ)*((5189/20000 : ℝ)+(473/20000 : ℝ)))^(4449/1024 : ℝ) := by
    rw [show (5894226531441422429/5895000000000000000 : ℝ)+(3271467490459/1179000000000000 : ℝ)*((5189/20000 : ℝ)+(473/20000 : ℝ))=(10006543331084253/10000000000000000 : ℝ) by norm_num, show 1+(35574061433121501/12500000000000000000 : ℝ)+(860480396957/10000000000000000000 : ℝ)=(50142300548134470789/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35574061433121501/12500000000000000000 : ℝ) ≤ ((5894226531441422429/5895000000000000000 : ℝ)+2*(3271467490459/1179000000000000 : ℝ)*(5189/20000 : ℝ))^(4449/1024 : ℝ) := by
    rw [show (5894226531441422429/5895000000000000000 : ℝ)+2*(3271467490459/1179000000000000 : ℝ)*(5189/20000 : ℝ)=(10013086266065171/10000000000000000 : ℝ) by norm_num, show 1+2*(35574061433121501/12500000000000000000 : ℝ)=(6285574061433121501/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5894226531441422429/5895000000000000000 : ℝ)*(X 1 0+X 2 0)+(3271467490459/1179000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4449/1024 : ℝ)) (lo := (473/20000 : ℝ)) (hi := (5189/20000 : ℝ)) (c := (5894226531441422429/5895000000000000000 : ℝ)) (alpha := (3271467490459/1179000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5894226531441422429/5895000000000000000 : ℝ)*(X 0 1+X 2 1)+(3271467490459/1179000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4449/1024 : ℝ)) (lo := (473/20000 : ℝ)) (hi := (5189/20000 : ℝ)) (c := (5894226531441422429/5895000000000000000 : ℝ)) (alpha := (3271467490459/1179000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5894226531441422429/5895000000000000000 : ℝ)*(X 0 2+X 1 2)+(3271467490459/1179000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4449/1024 : ℝ)) (lo := (473/20000 : ℝ)) (hi := (5189/20000 : ℝ)) (c := (5894226531441422429/5895000000000000000 : ℝ)) (alpha := (3271467490459/1179000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-943413379/5000000000 : ℝ)*X 0 0+(223796919/400000000 : ℝ)*X 0 1+(1016133593/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5393131461/10000000000 : ℝ)*X 1 0+(-431771887/2000000000 : ℝ)*X 1 1+(1270167561/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((674141651/1250000000 : ℝ)*X 2 0+(1016133671/2000000000 : ℝ)*X 2 1+(-1079429789/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((852470729/2000000000 : ℝ)*X 0 0+(1863310273/5000000000 : ℝ)*X 0 1+(2432015771/5000000000 : ℝ)*X 0 2+(852470729/2000000000 : ℝ)*X 1 0+(1863310273/5000000000 : ℝ)*X 1 1+(2432015771/5000000000 : ℝ)*X 1 2+(852470729/2000000000 : ℝ)*X 2 0+(1863310273/5000000000 : ℝ)*X 2 1+(2432015771/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-943601677/5000000000 : ℝ)*X 0 0+(158959747/312500000 : ℝ)*X 0 1+(5588776457/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1314570453/2500000000 : ℝ)*X 1 0+(-825376301/5000000000 : ℝ)*X 1 1+(5588776489/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((657285231/1250000000 : ℝ)*X 2 0+(1117755291/2000000000 : ℝ)*X 2 1+(-8253763/50000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4263187659/10000000000 : ℝ)*X 0 0+(4850665871/10000000000 : ℝ)*X 0 1+(3740211947/10000000000 : ℝ)*X 0 2+(4263187659/10000000000 : ℝ)*X 1 0+(4850665871/10000000000 : ℝ)*X 1 1+(3740211947/10000000000 : ℝ)*X 1 2+(4263187659/10000000000 : ℝ)*X 2 0+(4850665871/10000000000 : ℝ)*X 2 1+(3740211947/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (371654772319394973677164793/49125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (147945759/12500000000000 : ℝ)*(base19) + (855993887/50000000000000 : ℝ)*(base23) + (62793899/50000000000000 : ℝ)*(upper3) + (27367719/50000000000000 : ℝ)*(upper4) + (58126361/50000000000000 : ℝ)*(upper5) + (1411897360215983/100000000000000 : ℝ)*(major0) + (1411897360215983/100000000000000 : ℝ)*(major1) + (1411897360215983/100000000000000 : ℝ)*(major2) + (1944575922880197/100000000000000 : ℝ)*(sp0) + (972296224264733/50000000000000 : ℝ)*(sp1) + (388918384021553/20000000000000 : ℝ)*(sp2) + (879194761591053/100000000000000 : ℝ)*(sp3) + (8854607671/50000000000000 : ℝ)*(sp4) + (1214912463/20000000000000 : ℝ)*(sp7) + (109900104519171/12500000000000 : ℝ)*(f.failure) + (1944593632095539/100000000000000 : ℝ)*(f.sum) + (172272141640997/58950000000000000000000000000 : ℝ)*base65 + (1019188691155532293/589500000000000000000000000000000 : ℝ)*base68 + (2883843717226467707/589500000000000000000000000000000 : ℝ)*base69 + (5666887856869467707/589500000000000000000000000000000 : ℝ)*base71 + (252956268451153/58950000000000000000000000000 : ℝ)*base74 + (4817511415928967707/589500000000000000000000000000000 : ℝ)*base75 + (3255814998556467707/589500000000000000000000000000000 : ℝ)*base77 + (863309212630467707/589500000000000000000000000000000 : ℝ)*base79 + (150831585400247/58950000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (5668051/1250000000000000000000 : ℝ)*base90 + (5668051/1250000000000000000000 : ℝ)*base92 + (5668051/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (33729617588208150795971713/6550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (246391521/25000000000000 : ℝ)*(base19) + (106131919/10000000000000 : ℝ)*(base23) + (69492183/50000000000000 : ℝ)*(upper3) + (11995101/50000000000000 : ℝ)*(lower4) + (103378667/100000000000000 : ℝ)*(upper5) + (289230810859003/20000000000000 : ℝ)*(major0) + (289230810859003/20000000000000 : ℝ)*(major1) + (289230810859003/20000000000000 : ℝ)*(major2) + (5946483547/100000000000000 : ℝ)*(sp1) + (6589525751/100000000000000 : ℝ)*(sp2) + (995887578868193/50000000000000 : ℝ)*(sp4) + (398353645137351/20000000000000 : ℝ)*(sp5) + (398353501378289/20000000000000 : ℝ)*(sp6) + (450266389600821/50000000000000 : ℝ)*(sp7) + (450266389600821/50000000000000 : ℝ)*(f.failure) + (995887578868193/50000000000000 : ℝ)*(f.sum) + (44726893994483/11790000000000000000000000000 : ℝ)*base66 + (24392570487263287/117900000000000000000000000000000 : ℝ)*base67 + (848362393212263287/117900000000000000000000000000000 : ℝ)*base69 + (205061448283163287/117900000000000000000000000000000 : ℝ)*base71 + (86820262848953/11790000000000000000000000000 : ℝ)*base74 + (799774121840363287/117900000000000000000000000000000 : ℝ)*base75 + (420953167779263287/117900000000000000000000000000000 : ℝ)*base77 + (819027000252863287/117900000000000000000000000000000 : ℝ)*base79 + (2459973451463/11790000000000000000000000000 : ℝ)*base82 + (15738299/5000000000000000000000 : ℝ)*base89 + (15738299/5000000000000000000000 : ℝ)*base91 + (15738299/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1477_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160588719/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5189/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (473/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7861/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4683/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1477_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1477_s2_0 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-191566483/1000000000 : ℝ)*x 0 + (2735015513/5000000000 : ℝ)*x 1 + (1037390037/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (191566483/1000000000 : ℝ)^4451 ≤ (5845800740433/50000000000000 : ℝ)^3427 := by
    have hnat : (191566483 : ℕ)^4451*50000000000000^3427 ≤ 5845800740433^3427*1000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191566483 1000000000 5845800740433 50000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2735015513/5000000000 : ℝ)^4451 ≤ (22838637697583/50000000000000 : ℝ)^3427 := by
    have hnat : (2735015513 : ℕ)^4451*50000000000000^3427 ≤ 22838637697583^3427*5000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2735015513 5000000000 22838637697583 50000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1037390037/2000000000 : ℝ)^4451 ≤ (42631123106739/100000000000000 : ℝ)^3427 := by
    have hnat : (1037390037 : ℕ)^4451*100000000000000^3427 ≤ 42631123106739^3427*2000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037390037 2000000000 42631123106739 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-191566483/1000000000 : ℝ), (2735015513/5000000000 : ℝ), (1037390037/2000000000 : ℝ)] ![(5845800740433/50000000000000 : ℝ), (22838637697583/50000000000000 : ℝ), (42631123106739/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-191566483/1000000000 : ℝ)|^4451 ≤ (5845800740433/50000000000000 : ℝ)^3427
        have hw : |(-191566483/1000000000 : ℝ)|=(191566483/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2735015513/5000000000 : ℝ)|^4451 ≤ (22838637697583/50000000000000 : ℝ)^3427
        have hw : |(2735015513/5000000000 : ℝ)|=(2735015513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1037390037/2000000000 : ℝ)|^4451 ≤ (42631123106739/100000000000000 : ℝ)^3427
        have hw : |(1037390037/2000000000 : ℝ)|=(1037390037/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1477_s2_1 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (670220601/1250000000 : ℝ)*x 0 + (-1030861159/5000000000 : ℝ)*x 1 + (5186949759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (670220601/1250000000 : ℝ)^4451 ≤ (11126637719413/25000000000000 : ℝ)^3427 := by
    have hnat : (670220601 : ℕ)^4451*25000000000000^3427 ≤ 11126637719413^3427*1250000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      670220601 1250000000 11126637719413 25000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1030861159/5000000000 : ℝ)^4451 ≤ (1607791318401/12500000000000 : ℝ)^3427 := by
    have hnat : (1030861159 : ℕ)^4451*12500000000000^3427 ≤ 1607791318401^3427*5000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030861159 5000000000 1607791318401 12500000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5186949759/10000000000 : ℝ)^4451 ≤ (4263111855929/10000000000000 : ℝ)^3427 := by
    have hnat : (5186949759 : ℕ)^4451*10000000000000^3427 ≤ 4263111855929^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5186949759 10000000000 4263111855929 10000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(670220601/1250000000 : ℝ), (-1030861159/5000000000 : ℝ), (5186949759/10000000000 : ℝ)] ![(11126637719413/25000000000000 : ℝ), (1607791318401/12500000000000 : ℝ), (4263111855929/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(670220601/1250000000 : ℝ)|^4451 ≤ (11126637719413/25000000000000 : ℝ)^3427
        have hw : |(670220601/1250000000 : ℝ)|=(670220601/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1030861159/5000000000 : ℝ)|^4451 ≤ (1607791318401/12500000000000 : ℝ)^3427
        have hw : |(-1030861159/5000000000 : ℝ)|=(1030861159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5186949759/10000000000 : ℝ)|^4451 ≤ (4263111855929/10000000000000 : ℝ)^3427
        have hw : |(5186949759/10000000000 : ℝ)|=(5186949759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1477_s2_2 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1072352941/2000000000 : ℝ)*x 0 + (5186949681/10000000000 : ℝ)*x 1 + (-1030861279/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072352941/2000000000 : ℝ)^4451 ≤ (5563318720901/12500000000000 : ℝ)^3427 := by
    have hnat : (1072352941 : ℕ)^4451*12500000000000^3427 ≤ 5563318720901^3427*2000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072352941 2000000000 5563318720901 12500000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5186949681/10000000000 : ℝ)^4451 ≤ (42631117726659/100000000000000 : ℝ)^3427 := by
    have hnat : (5186949681 : ℕ)^4451*100000000000000^3427 ≤ 42631117726659^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5186949681 10000000000 42631117726659 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1030861279/5000000000 : ℝ)^4451 ≤ (1286233249187/10000000000000 : ℝ)^3427 := by
    have hnat : (1030861279 : ℕ)^4451*10000000000000^3427 ≤ 1286233249187^3427*5000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030861279 5000000000 1286233249187 10000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072352941/2000000000 : ℝ), (5186949681/10000000000 : ℝ), (-1030861279/5000000000 : ℝ)] ![(5563318720901/12500000000000 : ℝ), (42631117726659/100000000000000 : ℝ), (1286233249187/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072352941/2000000000 : ℝ)|^4451 ≤ (5563318720901/12500000000000 : ℝ)^3427
        have hw : |(1072352941/2000000000 : ℝ)|=(1072352941/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5186949681/10000000000 : ℝ)|^4451 ≤ (42631117726659/100000000000000 : ℝ)^3427
        have hw : |(5186949681/10000000000 : ℝ)|=(5186949681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1030861279/5000000000 : ℝ)|^4451 ≤ (1286233249187/10000000000000 : ℝ)^3427
        have hw : |(-1030861279/5000000000 : ℝ)|=(1030861279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1477_s2_3 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4282923793/10000000000 : ℝ)*x 0 + (3979858293/10000000000 : ℝ)*x 1 + (921194069/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4282923793/10000000000 : ℝ)^4451 ≤ (6648643180053/20000000000000 : ℝ)^3427 := by
    have hnat : (4282923793 : ℕ)^4451*20000000000000^3427 ≤ 6648643180053^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4282923793 10000000000 6648643180053 20000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3979858293/10000000000 : ℝ)^4451 ≤ (30220844940583/100000000000000 : ℝ)^3427 := by
    have hnat : (3979858293 : ℕ)^4451*100000000000000^3427 ≤ 30220844940583^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3979858293 10000000000 30220844940583 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (921194069/2000000000 : ℝ)^4451 ≤ (114174809807/312500000000 : ℝ)^3427 := by
    have hnat : (921194069 : ℕ)^4451*312500000000^3427 ≤ 114174809807^3427*2000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      921194069 2000000000 114174809807 312500000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4282923793/10000000000 : ℝ), (3979858293/10000000000 : ℝ), (921194069/2000000000 : ℝ)] ![(6648643180053/20000000000000 : ℝ), (30220844940583/100000000000000 : ℝ), (114174809807/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4282923793/10000000000 : ℝ)|^4451 ≤ (6648643180053/20000000000000 : ℝ)^3427
        have hw : |(4282923793/10000000000 : ℝ)|=(4282923793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3979858293/10000000000 : ℝ)|^4451 ≤ (30220844940583/100000000000000 : ℝ)^3427
        have hw : |(3979858293/10000000000 : ℝ)|=(3979858293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(921194069/2000000000 : ℝ)|^4451 ≤ (114174809807/312500000000 : ℝ)^3427
        have hw : |(921194069/2000000000 : ℝ)|=(921194069/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1477_s2_4 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-957863849/5000000000 : ℝ)*x 0 + (518879041/1000000000 : ℝ)*x 1 + (5468173651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (957863849/5000000000 : ℝ)^4451 ≤ (1461512478181/12500000000000 : ℝ)^3427 := by
    have hnat : (957863849 : ℕ)^4451*12500000000000^3427 ≤ 1461512478181^3427*5000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      957863849 5000000000 1461512478181 12500000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (518879041/1000000000 : ℝ)^4451 ≤ (42650768111143/100000000000000 : ℝ)^3427 := by
    have hnat : (518879041 : ℕ)^4451*100000000000000^3427 ≤ 42650768111143^3427*1000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518879041 1000000000 42650768111143 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5468173651/10000000000 : ℝ)^4451 ≤ (4565713205659/10000000000000 : ℝ)^3427 := by
    have hnat : (5468173651 : ℕ)^4451*10000000000000^3427 ≤ 4565713205659^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5468173651 10000000000 4565713205659 10000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-957863849/5000000000 : ℝ), (518879041/1000000000 : ℝ), (5468173651/10000000000 : ℝ)] ![(1461512478181/12500000000000 : ℝ), (42650768111143/100000000000000 : ℝ), (4565713205659/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-957863849/5000000000 : ℝ)|^4451 ≤ (1461512478181/12500000000000 : ℝ)^3427
        have hw : |(-957863849/5000000000 : ℝ)|=(957863849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(518879041/1000000000 : ℝ)|^4451 ≤ (42650768111143/100000000000000 : ℝ)^3427
        have hw : |(518879041/1000000000 : ℝ)|=(518879041/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5468173651/10000000000 : ℝ)|^4451 ≤ (4565713205659/10000000000000 : ℝ)^3427
        have hw : |(5468173651/10000000000 : ℝ)|=(5468173651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1477_s2_5 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165244989/312500000 : ℝ)*x 0 + (-1780499319/10000000000 : ℝ)*x 1 + (5468173691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165244989/312500000 : ℝ)^4451 ≤ (43711209600499/100000000000000 : ℝ)^3427 := by
    have hnat : (165244989 : ℕ)^4451*100000000000000^3427 ≤ 43711209600499^3427*312500000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165244989 312500000 43711209600499 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1780499319/10000000000 : ℝ)^4451 ≤ (10631657896573/100000000000000 : ℝ)^3427 := by
    have hnat : (1780499319 : ℕ)^4451*100000000000000^3427 ≤ 10631657896573^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1780499319 10000000000 10631657896573 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5468173691/10000000000 : ℝ)^4451 ≤ (4565713249037/10000000000000 : ℝ)^3427 := by
    have hnat : (5468173691 : ℕ)^4451*10000000000000^3427 ≤ 4565713249037^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5468173691 10000000000 4565713249037 10000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165244989/312500000 : ℝ), (-1780499319/10000000000 : ℝ), (5468173691/10000000000 : ℝ)] ![(43711209600499/100000000000000 : ℝ), (10631657896573/100000000000000 : ℝ), (4565713249037/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165244989/312500000 : ℝ)|^4451 ≤ (43711209600499/100000000000000 : ℝ)^3427
        have hw : |(165244989/312500000 : ℝ)|=(165244989/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1780499319/10000000000 : ℝ)|^4451 ≤ (10631657896573/100000000000000 : ℝ)^3427
        have hw : |(-1780499319/10000000000 : ℝ)|=(1780499319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5468173691/10000000000 : ℝ)|^4451 ≤ (4565713249037/10000000000000 : ℝ)^3427
        have hw : |(5468173691/10000000000 : ℝ)|=(5468173691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1477_s2_6 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5287839993/10000000000 : ℝ)*x 0 + (5468173731/10000000000 : ℝ)*x 1 + (-890249393/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287839993/10000000000 : ℝ)^4451 ≤ (5463901663069/12500000000000 : ℝ)^3427 := by
    have hnat : (5287839993 : ℕ)^4451*12500000000000^3427 ≤ 5463901663069^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287839993 10000000000 5463901663069 12500000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5468173731/10000000000 : ℝ)^4451 ≤ (913142658483/2000000000000 : ℝ)^3427 := by
    have hnat : (5468173731 : ℕ)^4451*2000000000000^3427 ≤ 913142658483^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5468173731 10000000000 913142658483 2000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (890249393/5000000000 : ℝ)^4451 ≤ (132895672037/1250000000000 : ℝ)^3427 := by
    have hnat : (890249393 : ℕ)^4451*1250000000000^3427 ≤ 132895672037^3427*5000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      890249393 5000000000 132895672037 1250000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287839993/10000000000 : ℝ), (5468173731/10000000000 : ℝ), (-890249393/5000000000 : ℝ)] ![(5463901663069/12500000000000 : ℝ), (913142658483/2000000000000 : ℝ), (132895672037/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287839993/10000000000 : ℝ)|^4451 ≤ (5463901663069/12500000000000 : ℝ)^3427
        have hw : |(5287839993/10000000000 : ℝ)|=(5287839993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5468173731/10000000000 : ℝ)|^4451 ≤ (913142658483/2000000000000 : ℝ)^3427
        have hw : |(5468173731/10000000000 : ℝ)|=(5468173731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-890249393/5000000000 : ℝ)|^4451 ≤ (132895672037/1250000000000 : ℝ)^3427
        have hw : |(-890249393/5000000000 : ℝ)|=(890249393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1477_s2_7 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2141531451/5000000000 : ℝ)*x 0 + (4601899499/10000000000 : ℝ)*x 1 + (398396741/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2141531451/5000000000 : ℝ)^4451 ≤ (831115456829/2500000000000 : ℝ)^3427 := by
    have hnat : (2141531451 : ℕ)^4451*2500000000000^3427 ≤ 831115456829^3427*5000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141531451 5000000000 831115456829 2500000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4601899499/10000000000 : ℝ)^4451 ≤ (9123501196493/25000000000000 : ℝ)^3427 := by
    have hnat : (4601899499 : ℕ)^4451*25000000000000^3427 ≤ 9123501196493^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4601899499 10000000000 9123501196493 25000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (398396741/1000000000 : ℝ)^4451 ≤ (7565344233447/25000000000000 : ℝ)^3427 := by
    have hnat : (398396741 : ℕ)^4451*25000000000000^3427 ≤ 7565344233447^3427*1000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398396741 1000000000 7565344233447 25000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2141531451/5000000000 : ℝ), (4601899499/10000000000 : ℝ), (398396741/1000000000 : ℝ)] ![(831115456829/2500000000000 : ℝ), (9123501196493/25000000000000 : ℝ), (7565344233447/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2141531451/5000000000 : ℝ)|^4451 ≤ (831115456829/2500000000000 : ℝ)^3427
        have hw : |(2141531451/5000000000 : ℝ)|=(2141531451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4601899499/10000000000 : ℝ)|^4451 ≤ (9123501196493/25000000000000 : ℝ)^3427
        have hw : |(4601899499/10000000000 : ℝ)|=(4601899499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(398396741/1000000000 : ℝ)|^4451 ≤ (7565344233447/25000000000000 : ℝ)^3427
        have hw : |(398396741/1000000000 : ℝ)|=(398396741/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1477_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160588719/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4683/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7861/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5079/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3229/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4683/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7861/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4683/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7861/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4683/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7861/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4683/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7861/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4683/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7861/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4683/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7861/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (7861/100000 : ℝ) ^ (4449/1024 : ℝ) ≤ (1589106640995091/100000000000000000000 : ℝ) := by
    have hpowers : (7861/100000 : ℝ)^4449 ≤ (1589106640995091/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7861 : ℕ)^4449*100000000000000000000^1024 ≤ 1589106640995091^1024*100000^4449 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7861 100000 1589106640995091 100000000000000000000 4449 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7861/100000 : ℝ)) (X := (1589106640995091/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4449 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4683/25000 : ℝ) ^ (4449/1024 : ℝ) ≤ (13823150177810953/20000000000000000000 : ℝ) := by
    have hpowers : (4683/25000 : ℝ)^4449 ≤ (13823150177810953/20000000000000000000 : ℝ)^1024 := by
      have hnat : (4683 : ℕ)^4449*20000000000000000000^1024 ≤ 13823150177810953^1024*25000^4449 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4683 25000 13823150177810953 20000000000000000000 4449 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4683/25000 : ℝ)) (X := (13823150177810953/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4449 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001589106640995091/50000000000000000000 : ℝ) ≤ (10000073150159309/10000000000000000 : ℝ) ^ (4449/1024 : ℝ) := by
    have hpowers : (50001589106640995091/50000000000000000000 : ℝ)^1024 ≤ (10000073150159309/10000000000000000 : ℝ)^4449 := by
      have hnat : (50001589106640995091 : ℕ)^1024*10000000000000000^4449 ≤ 10000073150159309^4449*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001589106640995091 50000000000000000000 10000073150159309 10000000000000000 1024 4449 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000073150159309/10000000000000000 : ℝ)) (X := (50001589106640995091/50000000000000000000 : ℝ)) (by norm_num) 4449 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (1563604763398907029/1562500000000000000 : ℝ) ≤ (10001626929147467/10000000000000000 : ℝ) ^ (4449/1024 : ℝ) := by
    have hpowers : (1563604763398907029/1562500000000000000 : ℝ)^1024 ≤ (10001626929147467/10000000000000000 : ℝ)^4449 := by
      have hnat : (1563604763398907029 : ℕ)^1024*10000000000000000^4449 ≤ 10001626929147467^4449*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563604763398907029 1562500000000000000 10001626929147467 10000000000000000 1024 4449 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001626929147467/10000000000000000 : ℝ)) (X := (1563604763398907029/1562500000000000000 : ℝ)) (by norm_num) 4449 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10013823150177810953/10000000000000000000 : ℝ) ≤ (16005089133017/16000000000000 : ℝ) ^ (4449/1024 : ℝ) := by
    have hpowers : (10013823150177810953/10000000000000000000 : ℝ)^1024 ≤ (16005089133017/16000000000000 : ℝ)^4449 := by
      have hnat : (10013823150177810953 : ℕ)^1024*16000000000000^4449 ≤ 16005089133017^4449*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10013823150177810953 10000000000000000000 16005089133017 16000000000000 1024 4449 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (16005089133017/16000000000000 : ℝ)) (X := (10013823150177810953/10000000000000000000 : ℝ)) (by norm_num) 4449 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1589106640995091/100000000000000000000 : ℝ) ≤ ((15526623814590004009/15530000000000000000 : ℝ)+2*(776889494079/543550000000000 : ℝ)*(7861/100000 : ℝ))^(4449/1024 : ℝ) := by
    rw [show (15526623814590004009/15530000000000000000 : ℝ)+2*(776889494079/543550000000000 : ℝ)*(7861/100000 : ℝ)=(10000073150159309/10000000000000000 : ℝ) by norm_num, show 1+2*(1589106640995091/100000000000000000000 : ℝ)=(50001589106640995091/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13823150177810953/20000000000000000000 : ℝ)+(1589106640995091/100000000000000000000 : ℝ) ≤ ((15526623814590004009/15530000000000000000 : ℝ)+(776889494079/543550000000000 : ℝ)*((4683/25000 : ℝ)+(7861/100000 : ℝ)))^(4449/1024 : ℝ) := by
    rw [show (15526623814590004009/15530000000000000000 : ℝ)+(776889494079/543550000000000 : ℝ)*((4683/25000 : ℝ)+(7861/100000 : ℝ))=(10001626929147467/10000000000000000 : ℝ) by norm_num, show 1+(13823150177810953/20000000000000000000 : ℝ)+(1589106640995091/100000000000000000000 : ℝ)=(1563604763398907029/1562500000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13823150177810953/20000000000000000000 : ℝ) ≤ ((15526623814590004009/15530000000000000000 : ℝ)+2*(776889494079/543550000000000 : ℝ)*(4683/25000 : ℝ))^(4449/1024 : ℝ) := by
    rw [show (15526623814590004009/15530000000000000000 : ℝ)+2*(776889494079/543550000000000 : ℝ)*(4683/25000 : ℝ)=(16005089133017/16000000000000 : ℝ) by norm_num, show 1+2*(13823150177810953/20000000000000000000 : ℝ)=(10013823150177810953/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15526623814590004009/15530000000000000000 : ℝ)*(X 1 0+X 2 0)+(776889494079/543550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4449/1024 : ℝ)) (lo := (7861/100000 : ℝ)) (hi := (4683/25000 : ℝ)) (c := (15526623814590004009/15530000000000000000 : ℝ)) (alpha := (776889494079/543550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15526623814590004009/15530000000000000000 : ℝ)*(X 0 1+X 2 1)+(776889494079/543550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4449/1024 : ℝ)) (lo := (7861/100000 : ℝ)) (hi := (4683/25000 : ℝ)) (c := (15526623814590004009/15530000000000000000 : ℝ)) (alpha := (776889494079/543550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15526623814590004009/15530000000000000000 : ℝ)*(X 0 2+X 1 2)+(776889494079/543550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4449/1024 : ℝ)) (lo := (7861/100000 : ℝ)) (hi := (4683/25000 : ℝ)) (c := (15526623814590004009/15530000000000000000 : ℝ)) (alpha := (776889494079/543550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-191566483/1000000000 : ℝ)*X 0 0+(2735015513/5000000000 : ℝ)*X 0 1+(1037390037/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((670220601/1250000000 : ℝ)*X 1 0+(-1030861159/5000000000 : ℝ)*X 1 1+(5186949759/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1072352941/2000000000 : ℝ)*X 2 0+(5186949681/10000000000 : ℝ)*X 2 1+(-1030861279/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4282923793/10000000000 : ℝ)*X 0 0+(3979858293/10000000000 : ℝ)*X 0 1+(921194069/2000000000 : ℝ)*X 0 2+(4282923793/10000000000 : ℝ)*X 1 0+(3979858293/10000000000 : ℝ)*X 1 1+(921194069/2000000000 : ℝ)*X 1 2+(4282923793/10000000000 : ℝ)*X 2 0+(3979858293/10000000000 : ℝ)*X 2 1+(921194069/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-957863849/5000000000 : ℝ)*X 0 0+(518879041/1000000000 : ℝ)*X 0 1+(5468173651/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((165244989/312500000 : ℝ)*X 1 0+(-1780499319/10000000000 : ℝ)*X 1 1+(5468173691/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5287839993/10000000000 : ℝ)*X 2 0+(5468173731/10000000000 : ℝ)*X 2 1+(-890249393/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2141531451/5000000000 : ℝ)*X 0 0+(4601899499/10000000000 : ℝ)*X 0 1+(398396741/1000000000 : ℝ)*X 0 2+(2141531451/5000000000 : ℝ)*X 1 0+(4601899499/10000000000 : ℝ)*X 1 1+(398396741/1000000000 : ℝ)*X 1 2+(2141531451/5000000000 : ℝ)*X 2 0+(4601899499/10000000000 : ℝ)*X 2 1+(398396741/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (189950077014362331016233/54355000000000000000000000000 : ℝ) := by norm_num
    linear_combination (587357637/50000000000000 : ℝ)*(base19) + (219258821/20000000000000 : ℝ)*(base23) + (5662033/100000000000000 : ℝ)*(lower2) + (6595867/3125000000000 : ℝ)*(upper3) + (7046903/100000000000000 : ℝ)*(upper5) + (641218626545671/25000000000000 : ℝ)*(major0) + (641218626545671/25000000000000 : ℝ)*(major1) + (641218626545671/25000000000000 : ℝ)*(major2) + (1766285928709663/50000000000000 : ℝ)*(sp0) + (70651558621179/2000000000000 : ℝ)*(sp1) + (3532578009480119/100000000000000 : ℝ)*(sp2) + (1597163130065753/100000000000000 : ℝ)*(sp3) + (7248354897/100000000000000 : ℝ)*(sp4) + (6660038049/100000000000000 : ℝ)*(sp7) + (798584895051901/50000000000000 : ℝ)*(f.failure) + (220786194110889/6250000000000 : ℝ)*(f.sum) + (2295690020483/54355000000000000000000000000 : ℝ)*base66 + (10471373668146465273/2717750000000000000000000000000000 : ℝ)*base67 + (9286573800639965273/2717750000000000000000000000000000 : ℝ)*base69 + (10979630319471284727/2717750000000000000000000000000000 : ℝ)*base72 + (12485186690457/13588750000000000000000000000 : ℝ)*base74 + (22855708619035784727/2717750000000000000000000000000000 : ℝ)*base76 + (8723811653207534727/2717750000000000000000000000000000 : ℝ)*base78 + (13513226789220715273/2717750000000000000000000000000000 : ℝ)*base79 + (75026801868843/54355000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (20104819/5000000000000000000000 : ℝ)*base89 + (20104819/5000000000000000000000 : ℝ)*base91 + (20104819/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4820267654812730311366974999/679437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (651744101/100000000000000 : ℝ)*(base19) + (1054411657/100000000000000 : ℝ)*(base23) + (11310859/10000000000000 : ℝ)*(upper3) + (37957897/100000000000000 : ℝ)*(lower4) + (192605707/100000000000000 : ℝ)*(upper5) + (649702051396791/25000000000000 : ℝ)*(major0) + (649702051396791/25000000000000 : ℝ)*(major1) + (649702051396791/25000000000000 : ℝ)*(major2) + (3494862203/50000000000000 : ℝ)*(sp1) + (13953595021/100000000000000 : ℝ)*(sp2) + (1789657786574047/50000000000000 : ℝ)*(sp4) + (3579307931679587/100000000000000 : ℝ)*(sp5) + (447412570642677/12500000000000 : ℝ)*(sp6) + (1618300601542979/100000000000000 : ℝ)*(sp7) + (1618300601542979/100000000000000 : ℝ)*(f.failure) + (1789657786574047/50000000000000 : ℝ)*(f.sum) + (37044616586709/27177500000000000000000000000 : ℝ)*base66 + (6779184170993195833/2717750000000000000000000000000000 : ℝ)*base67 + (22314980542640054167/2717750000000000000000000000000000 : ℝ)*base70 + (3650965310179554167/2717750000000000000000000000000000 : ℝ)*base72 + (4181334199507/3397187500000000000000000000 : ℝ)*base73 + (37321288768781804167/2717750000000000000000000000000000 : ℝ)*base76 + (29759341783304304167/2717750000000000000000000000000000 : ℝ)*base78 + (5704808218618554167/2717750000000000000000000000000000 : ℝ)*base80 + (11775427902771/6794375000000000000000000000 : ℝ)*base82 + (21053901/10000000000000000000000 : ℝ)*base89 + (21053901/10000000000000000000000 : ℝ)*base91 + (21053901/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1477_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160588719/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4683/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7861/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5079/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3229/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1477_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1477_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160588719/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5079/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3229/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1477_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1477_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1477_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160588719/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5079/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3229/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1477_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
