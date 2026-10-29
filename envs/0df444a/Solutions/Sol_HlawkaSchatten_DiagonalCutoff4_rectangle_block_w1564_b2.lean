-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1564_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:25:19.744097+00:00
-- url     : https://prove2.me/submissions/994b36d2-8b6c-45a7-9130-17d5191f636e

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
theorem support_rectangle_w1564_s6_0 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-224230701/1250000000 : ℝ)*x 0 + (5426547103/10000000000 : ℝ)*x 1 + (5219858153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (224230701/1250000000 : ℝ)^4625 ≤ (5502465347457/50000000000000 : ℝ)^3601 := by
    have hnat : (224230701 : ℕ)^4625*50000000000000^3601 ≤ 5502465347457^3601*1250000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224230701 1250000000 5502465347457 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5426547103/10000000000 : ℝ)^4625 ≤ (4560697353483/10000000000000 : ℝ)^3601 := by
    have hnat : (5426547103 : ℕ)^4625*10000000000000^3601 ≤ 4560697353483^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426547103 10000000000 4560697353483 10000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219858153/10000000000 : ℝ)^4625 ≤ (21694047873479/50000000000000 : ℝ)^3601 := by
    have hnat : (5219858153 : ℕ)^4625*50000000000000^3601 ≤ 21694047873479^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219858153 10000000000 21694047873479 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-224230701/1250000000 : ℝ), (5426547103/10000000000 : ℝ), (5219858153/10000000000 : ℝ)] ![(5502465347457/50000000000000 : ℝ), (4560697353483/10000000000000 : ℝ), (21694047873479/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-224230701/1250000000 : ℝ)|^4625 ≤ (5502465347457/50000000000000 : ℝ)^3601
        have hw : |(-224230701/1250000000 : ℝ)|=(224230701/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5426547103/10000000000 : ℝ)|^4625 ≤ (4560697353483/10000000000000 : ℝ)^3601
        have hw : |(5426547103/10000000000 : ℝ)|=(5426547103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219858153/10000000000 : ℝ)|^4625 ≤ (21694047873479/50000000000000 : ℝ)^3601
        have hw : |(5219858153/10000000000 : ℝ)|=(5219858153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_s6_1 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348556211/10000000000 : ℝ)*x 0 + (-379919201/2000000000 : ℝ)*x 1 + (2609929107/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348556211/10000000000 : ℝ)^4625 ≤ (44766839191267/100000000000000 : ℝ)^3601 := by
    have hnat : (5348556211 : ℕ)^4625*100000000000000^3601 ≤ 44766839191267^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348556211 10000000000 44766839191267 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (379919201/2000000000 : ℝ)^4625 ≤ (473802575383/4000000000000 : ℝ)^3601 := by
    have hnat : (379919201 : ℕ)^4625*4000000000000^3601 ≤ 473802575383^3601*2000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      379919201 2000000000 473802575383 4000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609929107/5000000000 : ℝ)^4625 ≤ (21694048199091/50000000000000 : ℝ)^3601 := by
    have hnat : (2609929107 : ℕ)^4625*50000000000000^3601 ≤ 21694048199091^3601*5000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609929107 5000000000 21694048199091 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348556211/10000000000 : ℝ), (-379919201/2000000000 : ℝ), (2609929107/5000000000 : ℝ)] ![(44766839191267/100000000000000 : ℝ), (473802575383/4000000000000 : ℝ), (21694048199091/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348556211/10000000000 : ℝ)|^4625 ≤ (44766839191267/100000000000000 : ℝ)^3601
        have hw : |(5348556211/10000000000 : ℝ)|=(5348556211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-379919201/2000000000 : ℝ)|^4625 ≤ (473802575383/4000000000000 : ℝ)^3601
        have hw : |(-379919201/2000000000 : ℝ)|=(379919201/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609929107/5000000000 : ℝ)|^4625 ≤ (21694048199091/50000000000000 : ℝ)^3601
        have hw : |(2609929107/5000000000 : ℝ)|=(2609929107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_s6_2 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674278117/5000000000 : ℝ)*x 0 + (2609929101/5000000000 : ℝ)*x 1 + (-1899595991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674278117/5000000000 : ℝ)^4625 ≤ (44766839438517/100000000000000 : ℝ)^3601 := by
    have hnat : (2674278117 : ℕ)^4625*100000000000000^3601 ≤ 44766839438517^3601*5000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674278117 5000000000 44766839438517 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609929101/5000000000 : ℝ)^4625 ≤ (43388096270073/100000000000000 : ℝ)^3601 := by
    have hnat : (2609929101 : ℕ)^4625*100000000000000^3601 ≤ 43388096270073^3601*5000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609929101 5000000000 43388096270073 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1899595991/10000000000 : ℝ)^4625 ≤ (2961266068113/25000000000000 : ℝ)^3601 := by
    have hnat : (1899595991 : ℕ)^4625*25000000000000^3601 ≤ 2961266068113^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1899595991 10000000000 2961266068113 25000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674278117/5000000000 : ℝ), (2609929101/5000000000 : ℝ), (-1899595991/10000000000 : ℝ)] ![(44766839438517/100000000000000 : ℝ), (43388096270073/100000000000000 : ℝ), (2961266068113/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674278117/5000000000 : ℝ)|^4625 ≤ (44766839438517/100000000000000 : ℝ)^3601
        have hw : |(2674278117/5000000000 : ℝ)|=(2674278117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609929101/5000000000 : ℝ)|^4625 ≤ (43388096270073/100000000000000 : ℝ)^3601
        have hw : |(2609929101/5000000000 : ℝ)|=(2609929101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1899595991/10000000000 : ℝ)|^4625 ≤ (2961266068113/25000000000000 : ℝ)^3601
        have hw : |(-1899595991/10000000000 : ℝ)|=(1899595991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_s6_3 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4246155793/10000000000 : ℝ)*x 0 + (4008858157/10000000000 : ℝ)*x 1 + (4494766113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4246155793/10000000000 : ℝ)^4625 ≤ (33282107323957/100000000000000 : ℝ)^3601 := by
    have hnat : (4246155793 : ℕ)^4625*100000000000000^3601 ≤ 33282107323957^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4246155793 10000000000 33282107323957 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4008858157/10000000000 : ℝ)^4625 ≤ (1545622719019/5000000000000 : ℝ)^3601 := by
    have hnat : (4008858157 : ℕ)^4625*5000000000000^3601 ≤ 1545622719019^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4008858157 10000000000 1545622719019 5000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4494766113/10000000000 : ℝ)^4625 ≤ (17902719143051/50000000000000 : ℝ)^3601 := by
    have hnat : (4494766113 : ℕ)^4625*50000000000000^3601 ≤ 17902719143051^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4494766113 10000000000 17902719143051 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4246155793/10000000000 : ℝ), (4008858157/10000000000 : ℝ), (4494766113/10000000000 : ℝ)] ![(33282107323957/100000000000000 : ℝ), (1545622719019/5000000000000 : ℝ), (17902719143051/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4246155793/10000000000 : ℝ)|^4625 ≤ (33282107323957/100000000000000 : ℝ)^3601
        have hw : |(4246155793/10000000000 : ℝ)|=(4246155793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4008858157/10000000000 : ℝ)|^4625 ≤ (1545622719019/5000000000000 : ℝ)^3601
        have hw : |(4008858157/10000000000 : ℝ)|=(4008858157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4494766113/10000000000 : ℝ)|^4625 ≤ (17902719143051/50000000000000 : ℝ)^3601
        have hw : |(4494766113/10000000000 : ℝ)|=(4494766113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_s6_4 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-448468143/2500000000 : ℝ)*x 0 + (1044186687/2000000000 : ℝ)*x 1 + (1085092777/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (448468143/2500000000 : ℝ)^4625 ≤ (11005143154393/100000000000000 : ℝ)^3601 := by
    have hnat : (448468143 : ℕ)^4625*100000000000000^3601 ≤ 11005143154393^3601*2500000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448468143 2500000000 11005143154393 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1044186687/2000000000 : ℝ)^4625 ≤ (5424946947591/12500000000000 : ℝ)^3601 := by
    have hnat : (1044186687 : ℕ)^4625*12500000000000^3601 ≤ 5424946947591^3601*2000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044186687 2000000000 5424946947591 12500000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1085092777/2000000000 : ℝ)^4625 ≤ (11398820309491/25000000000000 : ℝ)^3601 := by
    have hnat : (1085092777 : ℕ)^4625*25000000000000^3601 ≤ 11398820309491^3601*2000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085092777 2000000000 11398820309491 25000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-448468143/2500000000 : ℝ), (1044186687/2000000000 : ℝ), (1085092777/2000000000 : ℝ)] ![(11005143154393/100000000000000 : ℝ), (5424946947591/12500000000000 : ℝ), (11398820309491/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-448468143/2500000000 : ℝ)|^4625 ≤ (11005143154393/100000000000000 : ℝ)^3601
        have hw : |(-448468143/2500000000 : ℝ)|=(448468143/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1044186687/2000000000 : ℝ)|^4625 ≤ (5424946947591/12500000000000 : ℝ)^3601
        have hw : |(1044186687/2000000000 : ℝ)|=(1044186687/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1085092777/2000000000 : ℝ)|^4625 ≤ (11398820309491/25000000000000 : ℝ)^3601
        have hw : |(1085092777/2000000000 : ℝ)|=(1085092777/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_s6_5 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (849243857/2000000000 : ℝ)*x 0 + (898447721/2000000000 : ℝ)*x 1 + (4011404267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (849243857/2000000000 : ℝ)^4625 ≤ (16641373252171/50000000000000 : ℝ)^3601 := by
    have hnat : (849243857 : ℕ)^4625*50000000000000^3601 ≤ 16641373252171^3601*2000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849243857 2000000000 16641373252171 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (898447721/2000000000 : ℝ)^4625 ≤ (35779580679619/100000000000000 : ℝ)^3601 := by
    have hnat : (898447721 : ℕ)^4625*100000000000000^3601 ≤ 35779580679619^3601*2000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898447721 2000000000 35779580679619 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4011404267/10000000000 : ℝ)^4625 ≤ (30937672795369/100000000000000 : ℝ)^3601 := by
    have hnat : (4011404267 : ℕ)^4625*100000000000000^3601 ≤ 30937672795369^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4011404267 10000000000 30937672795369 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(849243857/2000000000 : ℝ), (898447721/2000000000 : ℝ), (4011404267/10000000000 : ℝ)] ![(16641373252171/50000000000000 : ℝ), (35779580679619/100000000000000 : ℝ), (30937672795369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(849243857/2000000000 : ℝ)|^4625 ≤ (16641373252171/50000000000000 : ℝ)^3601
        have hw : |(849243857/2000000000 : ℝ)|=(849243857/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(898447721/2000000000 : ℝ)|^4625 ≤ (35779580679619/100000000000000 : ℝ)^3601
        have hw : |(898447721/2000000000 : ℝ)|=(898447721/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4011404267/10000000000 : ℝ)|^4625 ≤ (30937672795369/100000000000000 : ℝ)^3601
        have hw : |(4011404267/10000000000 : ℝ)|=(4011404267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1564_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5235807/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11101/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5551/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3097/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11101/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11101/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11101/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11101/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11101/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11101/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11101/100000 : ℝ) ^ (4623/1024 : ℝ) ≤ (612428681248773/12500000000000000000 : ℝ) := by
    have hpowers : (11101/100000 : ℝ)^4623 ≤ (612428681248773/12500000000000000000 : ℝ)^1024 := by
      have hnat : (11101 : ℕ)^4623*12500000000000000000^1024 ≤ 612428681248773^1024*100000^4623 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11101 100000 612428681248773 12500000000000000000 4623 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11101/100000 : ℝ)) (X := (612428681248773/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4623 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3097/20000 : ℝ) ^ (4623/1024 : ℝ) ≤ (5503942869089091/25000000000000000000 : ℝ) := by
    have hpowers : (3097/20000 : ℝ)^4623 ≤ (5503942869089091/25000000000000000000 : ℝ)^1024 := by
      have hnat : (3097 : ℕ)^4623*25000000000000000000^1024 ≤ 5503942869089091^1024*20000^4623 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3097 20000 5503942869089091 25000000000000000000 4623 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3097/20000 : ℝ)) (X := (5503942869089091/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4623 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250612428681248773/6250000000000000000 : ℝ) ≤ (400008681504493/400000000000000 : ℝ) ^ (4623/1024 : ℝ) := by
    have hpowers : (6250612428681248773/6250000000000000000 : ℝ)^1024 ≤ (400008681504493/400000000000000 : ℝ)^4623 := by
      have hnat : (6250612428681248773 : ℕ)^1024*400000000000000^4623 ≤ 400008681504493^4623*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250612428681248773 6250000000000000000 400008681504493 400000000000000 1024 4623 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400008681504493/400000000000000 : ℝ)) (X := (6250612428681248773/6250000000000000000 : ℝ)) (by norm_num) 4623 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25006728800231586637/25000000000000000000 : ℝ) ≤ (1250074514056623/1250000000000000 : ℝ) ^ (4623/1024 : ℝ) := by
    have hpowers : (25006728800231586637/25000000000000000000 : ℝ)^1024 ≤ (1250074514056623/1250000000000000 : ℝ)^4623 := by
      have hnat : (25006728800231586637 : ℕ)^1024*1250000000000000^4623 ≤ 1250074514056623^4623*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006728800231586637 25000000000000000000 1250074514056623 1250000000000000 1024 4623 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250074514056623/1250000000000000 : ℝ)) (X := (25006728800231586637/25000000000000000000 : ℝ)) (by norm_num) 4623 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12505503942869089091/12500000000000000000 : ℝ) ≤ (10000975187293643/10000000000000000 : ℝ) ^ (4623/1024 : ℝ) := by
    have hpowers : (12505503942869089091/12500000000000000000 : ℝ)^1024 ≤ (10000975187293643/10000000000000000 : ℝ)^4623 := by
      have hnat : (12505503942869089091 : ℕ)^1024*10000000000000000^4623 ≤ 10000975187293643^4623*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505503942869089091 12500000000000000000 10000975187293643 10000000000000000 1024 4623 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000975187293643/10000000000000000 : ℝ)) (X := (12505503942869089091/12500000000000000000 : ℝ)) (by norm_num) 4623 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(612428681248773/12500000000000000000 : ℝ) ≤ ((21916267636640060841/21920000000000000000 : ℝ)+2*(379074840659/438400000000000 : ℝ)*(11101/100000 : ℝ))^(4623/1024 : ℝ) := by
    rw [show (21916267636640060841/21920000000000000000 : ℝ)+2*(379074840659/438400000000000 : ℝ)*(11101/100000 : ℝ)=(400008681504493/400000000000000 : ℝ) by norm_num, show 1+2*(612428681248773/12500000000000000000 : ℝ)=(6250612428681248773/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5503942869089091/25000000000000000000 : ℝ)+(612428681248773/12500000000000000000 : ℝ) ≤ ((21916267636640060841/21920000000000000000 : ℝ)+(379074840659/438400000000000 : ℝ)*((3097/20000 : ℝ)+(11101/100000 : ℝ)))^(4623/1024 : ℝ) := by
    rw [show (21916267636640060841/21920000000000000000 : ℝ)+(379074840659/438400000000000 : ℝ)*((3097/20000 : ℝ)+(11101/100000 : ℝ))=(1250074514056623/1250000000000000 : ℝ) by norm_num, show 1+(5503942869089091/25000000000000000000 : ℝ)+(612428681248773/12500000000000000000 : ℝ)=(25006728800231586637/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5503942869089091/25000000000000000000 : ℝ) ≤ ((21916267636640060841/21920000000000000000 : ℝ)+2*(379074840659/438400000000000 : ℝ)*(3097/20000 : ℝ))^(4623/1024 : ℝ) := by
    rw [show (21916267636640060841/21920000000000000000 : ℝ)+2*(379074840659/438400000000000 : ℝ)*(3097/20000 : ℝ)=(10000975187293643/10000000000000000 : ℝ) by norm_num, show 1+2*(5503942869089091/25000000000000000000 : ℝ)=(12505503942869089091/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (21916267636640060841/21920000000000000000 : ℝ)*(X 1 0+X 2 0)+(379074840659/438400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4623/1024 : ℝ)) (lo := (11101/100000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (21916267636640060841/21920000000000000000 : ℝ)) (alpha := (379074840659/438400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (21916267636640060841/21920000000000000000 : ℝ)*(X 0 1+X 2 1)+(379074840659/438400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4623/1024 : ℝ)) (lo := (11101/100000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (21916267636640060841/21920000000000000000 : ℝ)) (alpha := (379074840659/438400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (21916267636640060841/21920000000000000000 : ℝ)*(X 0 2+X 1 2)+(379074840659/438400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4623/1024 : ℝ)) (lo := (11101/100000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (21916267636640060841/21920000000000000000 : ℝ)) (alpha := (379074840659/438400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-224230701/1250000000 : ℝ)*X 0 0+(5426547103/10000000000 : ℝ)*X 0 1+(5219858153/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348556211/10000000000 : ℝ)*X 1 0+(-379919201/2000000000 : ℝ)*X 1 1+(2609929107/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674278117/5000000000 : ℝ)*X 2 0+(2609929101/5000000000 : ℝ)*X 2 1+(-1899595991/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4246155793/10000000000 : ℝ)*X 0 0+(4008858157/10000000000 : ℝ)*X 0 1+(4494766113/10000000000 : ℝ)*X 0 2+(4246155793/10000000000 : ℝ)*X 1 0+(4008858157/10000000000 : ℝ)*X 1 1+(4494766113/10000000000 : ℝ)*X 1 2+(4246155793/10000000000 : ℝ)*X 2 0+(4008858157/10000000000 : ℝ)*X 2 1+(4494766113/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-448468143/2500000000 : ℝ)*X 0 0+(1044186687/2000000000 : ℝ)*X 0 1+(1085092777/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((849243857/2000000000 : ℝ)*X 0 0+(898447721/2000000000 : ℝ)*X 0 1+(4011404267/10000000000 : ℝ)*X 0 2+(849243857/2000000000 : ℝ)*X 1 0+(898447721/2000000000 : ℝ)*X 1 1+(4011404267/10000000000 : ℝ)*X 1 2+(849243857/2000000000 : ℝ)*X 2 0+(898447721/2000000000 : ℝ)*X 2 1+(4011404267/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s6_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2853268829696839829944079997/548000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (423145477/50000000000000 : ℝ)*(base19) + (165430531/20000000000000 : ℝ)*(base23) + (2136413/10000000000000 : ℝ)*(lower2) + (2608337/2500000000000 : ℝ)*(upper3) + (93158417/100000000000000 : ℝ)*(upper5) + (1724058570386413/50000000000000 : ℝ)*(major0) + (1724058570386413/50000000000000 : ℝ)*(major1) + (1724058570386413/50000000000000 : ℝ)*(major2) + (483820369764257/10000000000000 : ℝ)*(sp0) + (120955472195199/2500000000000 : ℝ)*(sp1) + (4838218906946259/100000000000000 : ℝ)*(sp2) + (2058008476800263/100000000000000 : ℝ)*(sp3) + (2004557043/12500000000000 : ℝ)*(sp4) + (5897089967/100000000000000 : ℝ)*(sp5) + (2058014373890229/100000000000000 : ℝ)*(f.failure) + (2419109867049457/50000000000000 : ℝ)*(f.sum) + (56667144206793/10960000000000000000000000000 : ℝ)*base66 + (3270587081387896667/1096000000000000000000000000000000 : ℝ)*base68 + (9104900736059896667/1096000000000000000000000000000000 : ℝ)*base70 + (885383147035896667/1096000000000000000000000000000000 : ℝ)*base72 + (35933166358793/10960000000000000000000000000 : ℝ)*base74 + (20958221609899896667/1096000000000000000000000000000000 : ℝ)*base76 + (4002614341451896667/1096000000000000000000000000000000 : ℝ)*base78 + (6935534326315896667/1096000000000000000000000000000000 : ℝ)*base80 + (5026598893273/10960000000000000000000000000 : ℝ)*base82 + (3020197/312500000000000000000 : ℝ)*base90 + (3020197/312500000000000000000 : ℝ)*base92 + (3020197/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1564_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5235807/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11101/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5551/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1564_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1564_box_0 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1589069951/10000000000 : ℝ)*x 0 + (1349308943/2500000000 : ℝ)*x 1 + (215889397/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1589069951/10000000000 : ℝ)^4625 ≤ (2354592166433/25000000000000 : ℝ)^3601 := by
    have hnat : (1589069951 : ℕ)^4625*25000000000000^3601 ≤ 2354592166433^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1589069951 10000000000 2354592166433 25000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1349308943/2500000000 : ℝ)^4625 ≤ (45290820222389/100000000000000 : ℝ)^3601 := by
    have hnat : (1349308943 : ℕ)^4625*100000000000000^3601 ≤ 45290820222389^3601*2500000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349308943 2500000000 45290820222389 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215889397/400000000 : ℝ)^4625 ≤ (905816221873/2000000000000 : ℝ)^3601 := by
    have hnat : (215889397 : ℕ)^4625*2000000000000^3601 ≤ 905816221873^3601*400000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215889397 400000000 905816221873 2000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1589069951/10000000000 : ℝ), (1349308943/2500000000 : ℝ), (215889397/400000000 : ℝ)] ![(2354592166433/25000000000000 : ℝ), (45290820222389/100000000000000 : ℝ), (905816221873/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1589069951/10000000000 : ℝ)|^4625 ≤ (2354592166433/25000000000000 : ℝ)^3601
        have hw : |(-1589069951/10000000000 : ℝ)|=(1589069951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1349308943/2500000000 : ℝ)|^4625 ≤ (45290820222389/100000000000000 : ℝ)^3601
        have hw : |(1349308943/2500000000 : ℝ)|=(1349308943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215889397/400000000 : ℝ)|^4625 ≤ (905816221873/2000000000000 : ℝ)^3601
        have hw : |(215889397/400000000 : ℝ)|=(215889397/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_box_1 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2635569423/5000000000 : ℝ)*x 0 + (-441080869/2500000000 : ℝ)*x 1 + (2698617741/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2635569423/5000000000 : ℝ)^4625 ≤ (2746020074289/6250000000000 : ℝ)^3601 := by
    have hnat : (2635569423 : ℕ)^4625*6250000000000^3601 ≤ 2746020074289^3601*5000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635569423 5000000000 2746020074289 6250000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (441080869/2500000000 : ℝ)^4625 ≤ (10772861694727/100000000000000 : ℝ)^3601 := by
    have hnat : (441080869 : ℕ)^4625*100000000000000^3601 ≤ 10772861694727^3601*2500000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441080869 2500000000 10772861694727 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698617741/5000000000 : ℝ)^4625 ≤ (22645408548423/50000000000000 : ℝ)^3601 := by
    have hnat : (2698617741 : ℕ)^4625*50000000000000^3601 ≤ 22645408548423^3601*5000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698617741 5000000000 22645408548423 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2635569423/5000000000 : ℝ), (-441080869/2500000000 : ℝ), (2698617741/5000000000 : ℝ)] ![(2746020074289/6250000000000 : ℝ), (10772861694727/100000000000000 : ℝ), (22645408548423/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2635569423/5000000000 : ℝ)|^4625 ≤ (2746020074289/6250000000000 : ℝ)^3601
        have hw : |(2635569423/5000000000 : ℝ)|=(2635569423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-441080869/2500000000 : ℝ)|^4625 ≤ (10772861694727/100000000000000 : ℝ)^3601
        have hw : |(-441080869/2500000000 : ℝ)|=(441080869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698617741/5000000000 : ℝ)|^4625 ≤ (22645408548423/50000000000000 : ℝ)^3601
        have hw : |(2698617741/5000000000 : ℝ)|=(2698617741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_box_2 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5271139479/10000000000 : ℝ)*x 0 + (5397235271/10000000000 : ℝ)*x 1 + (-882161451/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5271139479/10000000000 : ℝ)^4625 ≤ (2196816398261/5000000000000 : ℝ)^3601 := by
    have hnat : (5271139479 : ℕ)^4625*5000000000000^3601 ≤ 2196816398261^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271139479 10000000000 2196816398261 5000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5397235271/10000000000 : ℝ)^4625 ≤ (9058162964549/20000000000000 : ℝ)^3601 := by
    have hnat : (5397235271 : ℕ)^4625*20000000000000^3601 ≤ 9058162964549^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397235271 10000000000 9058162964549 20000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (882161451/5000000000 : ℝ)^4625 ≤ (2693214298317/25000000000000 : ℝ)^3601 := by
    have hnat : (882161451 : ℕ)^4625*25000000000000^3601 ≤ 2693214298317^3601*5000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      882161451 5000000000 2693214298317 25000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5271139479/10000000000 : ℝ), (5397235271/10000000000 : ℝ), (-882161451/5000000000 : ℝ)] ![(2196816398261/5000000000000 : ℝ), (9058162964549/20000000000000 : ℝ), (2693214298317/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5271139479/10000000000 : ℝ)|^4625 ≤ (2196816398261/5000000000000 : ℝ)^3601
        have hw : |(5271139479/10000000000 : ℝ)|=(5271139479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5397235271/10000000000 : ℝ)|^4625 ≤ (9058162964549/20000000000000 : ℝ)^3601
        have hw : |(5397235271/10000000000 : ℝ)|=(5397235271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-882161451/5000000000 : ℝ)|^4625 ≤ (2693214298317/25000000000000 : ℝ)^3601
        have hw : |(-882161451/5000000000 : ℝ)|=(882161451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_box_3 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (138970863/312500000 : ℝ)*x 0 + (4152367503/10000000000 : ℝ)*x 1 + (4152368761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (138970863/312500000 : ℝ)^4625 ≤ (17659079606809/50000000000000 : ℝ)^3601 := by
    have hnat : (138970863 : ℕ)^4625*50000000000000^3601 ≤ 17659079606809^3601*312500000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138970863 312500000 17659079606809 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4152367503/10000000000 : ℝ)^4625 ≤ (32340914088679/100000000000000 : ℝ)^3601 := by
    have hnat : (4152367503 : ℕ)^4625*100000000000000^3601 ≤ 32340914088679^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4152367503 10000000000 32340914088679 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4152368761/10000000000 : ℝ)^4625 ≤ (8085231668221/25000000000000 : ℝ)^3601 := by
    have hnat : (4152368761 : ℕ)^4625*25000000000000^3601 ≤ 8085231668221^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4152368761 10000000000 8085231668221 25000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(138970863/312500000 : ℝ), (4152367503/10000000000 : ℝ), (4152368761/10000000000 : ℝ)] ![(17659079606809/50000000000000 : ℝ), (32340914088679/100000000000000 : ℝ), (8085231668221/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(138970863/312500000 : ℝ)|^4625 ≤ (17659079606809/50000000000000 : ℝ)^3601
        have hw : |(138970863/312500000 : ℝ)|=(138970863/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4152367503/10000000000 : ℝ)|^4625 ≤ (32340914088679/100000000000000 : ℝ)^3601
        have hw : |(4152367503/10000000000 : ℝ)|=(4152367503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4152368761/10000000000 : ℝ)|^4625 ≤ (8085231668221/25000000000000 : ℝ)^3601
        have hw : |(4152368761/10000000000 : ℝ)|=(4152368761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_box_4 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-400802923/2000000000 : ℝ)*x 0 + (524494573/1000000000 : ℝ)*x 1 + (5244946071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (400802923/2000000000 : ℝ)^4625 ≤ (12687779208797/100000000000000 : ℝ)^3601 := by
    have hnat : (400802923 : ℕ)^4625*100000000000000^3601 ≤ 12687779208797^3601*2000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400802923 2000000000 12687779208797 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524494573/1000000000 : ℝ)^4625 ≤ (545701357019/1250000000000 : ℝ)^3601 := by
    have hnat : (524494573 : ℕ)^4625*1250000000000^3601 ≤ 545701357019^3601*1000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524494573 1000000000 545701357019 1250000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244946071/10000000000 : ℝ)^4625 ≤ (5457014025867/12500000000000 : ℝ)^3601 := by
    have hnat : (5244946071 : ℕ)^4625*12500000000000^3601 ≤ 5457014025867^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244946071 10000000000 5457014025867 12500000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-400802923/2000000000 : ℝ), (524494573/1000000000 : ℝ), (5244946071/10000000000 : ℝ)] ![(12687779208797/100000000000000 : ℝ), (545701357019/1250000000000 : ℝ), (5457014025867/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-400802923/2000000000 : ℝ)|^4625 ≤ (12687779208797/100000000000000 : ℝ)^3601
        have hw : |(-400802923/2000000000 : ℝ)|=(400802923/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524494573/1000000000 : ℝ)|^4625 ≤ (545701357019/1250000000000 : ℝ)^3601
        have hw : |(524494573/1000000000 : ℝ)|=(524494573/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244946071/10000000000 : ℝ)|^4625 ≤ (5457014025867/12500000000000 : ℝ)^3601
        have hw : |(5244946071/10000000000 : ℝ)|=(5244946071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_box_5 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1344187417/2500000000 : ℝ)*x 0 + (-1827870249/10000000000 : ℝ)*x 1 + (2622473/5000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1344187417/2500000000 : ℝ)^4625 ≤ (22535072866743/50000000000000 : ℝ)^3601 := by
    have hnat : (1344187417 : ℕ)^4625*50000000000000^3601 ≤ 22535072866743^3601*2500000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344187417 2500000000 22535072866743 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1827870249/10000000000 : ℝ)^4625 ≤ (5636871399937/50000000000000 : ℝ)^3601 := by
    have hnat : (1827870249 : ℕ)^4625*50000000000000^3601 ≤ 5636871399937^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1827870249 10000000000 5636871399937 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622473/5000000 : ℝ)^4625 ≤ (545701393099/1250000000000 : ℝ)^3601 := by
    have hnat : (2622473 : ℕ)^4625*1250000000000^3601 ≤ 545701393099^3601*5000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622473 5000000 545701393099 1250000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1344187417/2500000000 : ℝ), (-1827870249/10000000000 : ℝ), (2622473/5000000 : ℝ)] ![(22535072866743/50000000000000 : ℝ), (5636871399937/50000000000000 : ℝ), (545701393099/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1344187417/2500000000 : ℝ)|^4625 ≤ (22535072866743/50000000000000 : ℝ)^3601
        have hw : |(1344187417/2500000000 : ℝ)|=(1344187417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1827870249/10000000000 : ℝ)|^4625 ≤ (5636871399937/50000000000000 : ℝ)^3601
        have hw : |(-1827870249/10000000000 : ℝ)|=(1827870249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622473/5000000 : ℝ)|^4625 ≤ (545701393099/1250000000000 : ℝ)^3601
        have hw : |(2622473/5000000 : ℝ)|=(2622473/5000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_box_6 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (8602799/16000000 : ℝ)*x 0 + (5244946373/10000000000 : ℝ)*x 1 + (-28560471/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8602799/16000000 : ℝ)^4625 ≤ (2816883911189/6250000000000 : ℝ)^3601 := by
    have hnat : (8602799 : ℕ)^4625*6250000000000^3601 ≤ 2816883911189^3601*16000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8602799 16000000 2816883911189 6250000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244946373/10000000000 : ℝ)^4625 ≤ (43656115435427/100000000000000 : ℝ)^3601 := by
    have hnat : (5244946373 : ℕ)^4625*100000000000000^3601 ≤ 43656115435427^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244946373 10000000000 43656115435427 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (28560471/156250000 : ℝ)^4625 ≤ (11273741968109/100000000000000 : ℝ)^3601 := by
    have hnat : (28560471 : ℕ)^4625*100000000000000^3601 ≤ 11273741968109^3601*156250000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28560471 156250000 11273741968109 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8602799/16000000 : ℝ), (5244946373/10000000000 : ℝ), (-28560471/156250000 : ℝ)] ![(2816883911189/6250000000000 : ℝ), (43656115435427/100000000000000 : ℝ), (11273741968109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8602799/16000000 : ℝ)|^4625 ≤ (2816883911189/6250000000000 : ℝ)^3601
        have hw : |(8602799/16000000 : ℝ)|=(8602799/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244946373/10000000000 : ℝ)|^4625 ≤ (43656115435427/100000000000000 : ℝ)^3601
        have hw : |(5244946373/10000000000 : ℝ)|=(5244946373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-28560471/156250000 : ℝ)|^4625 ≤ (11273741968109/100000000000000 : ℝ)^3601
        have hw : |(-28560471/156250000 : ℝ)|=(28560471/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_box_7 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2021290609/5000000000 : ℝ)*x 0 + (2177241859/5000000000 : ℝ)*x 1 + (2177241389/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2021290609/5000000000 : ℝ)^4625 ≤ (6249367831327/20000000000000 : ℝ)^3601 := by
    have hnat : (2021290609 : ℕ)^4625*20000000000000^3601 ≤ 6249367831327^3601*5000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2021290609 5000000000 6249367831327 20000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2177241859/5000000000 : ℝ)^4625 ≤ (34376585175523/100000000000000 : ℝ)^3601 := by
    have hnat : (2177241859 : ℕ)^4625*100000000000000^3601 ≤ 34376585175523^3601*5000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177241859 5000000000 34376585175523 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2177241389/5000000000 : ℝ)^4625 ≤ (17188287822217/50000000000000 : ℝ)^3601 := by
    have hnat : (2177241389 : ℕ)^4625*50000000000000^3601 ≤ 17188287822217^3601*5000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177241389 5000000000 17188287822217 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2021290609/5000000000 : ℝ), (2177241859/5000000000 : ℝ), (2177241389/5000000000 : ℝ)] ![(6249367831327/20000000000000 : ℝ), (34376585175523/100000000000000 : ℝ), (17188287822217/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2021290609/5000000000 : ℝ)|^4625 ≤ (6249367831327/20000000000000 : ℝ)^3601
        have hw : |(2021290609/5000000000 : ℝ)|=(2021290609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2177241859/5000000000 : ℝ)|^4625 ≤ (34376585175523/100000000000000 : ℝ)^3601
        have hw : |(2177241859/5000000000 : ℝ)|=(2177241859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2177241389/5000000000 : ℝ)|^4625 ≤ (17188287822217/50000000000000 : ℝ)^3601
        have hw : |(2177241389/5000000000 : ℝ)|=(2177241389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_box_8 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-958042261/5000000000 : ℝ)*x 0 + (1027542493/2000000000 : ℝ)*x 1 + (1083505321/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (958042261/5000000000 : ℝ)^4625 ≤ (11977279448407/100000000000000 : ℝ)^3601 := by
    have hnat : (958042261 : ℕ)^4625*100000000000000^3601 ≤ 11977279448407^3601*5000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      958042261 5000000000 11977279448407 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1027542493/2000000000 : ℝ)^4625 ≤ (42513094343467/100000000000000 : ℝ)^3601 := by
    have hnat : (1027542493 : ℕ)^4625*100000000000000^3601 ≤ 42513094343467^3601*2000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027542493 2000000000 42513094343467 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083505321/2000000000 : ℝ)^4625 ≤ (9101925238079/20000000000000 : ℝ)^3601 := by
    have hnat : (1083505321 : ℕ)^4625*20000000000000^3601 ≤ 9101925238079^3601*2000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083505321 2000000000 9101925238079 20000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-958042261/5000000000 : ℝ), (1027542493/2000000000 : ℝ), (1083505321/2000000000 : ℝ)] ![(11977279448407/100000000000000 : ℝ), (42513094343467/100000000000000 : ℝ), (9101925238079/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-958042261/5000000000 : ℝ)|^4625 ≤ (11977279448407/100000000000000 : ℝ)^3601
        have hw : |(-958042261/5000000000 : ℝ)|=(958042261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1027542493/2000000000 : ℝ)|^4625 ≤ (42513094343467/100000000000000 : ℝ)^3601
        have hw : |(1027542493/2000000000 : ℝ)|=(1027542493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1083505321/2000000000 : ℝ)|^4625 ≤ (9101925238079/20000000000000 : ℝ)^3601
        have hw : |(1083505321/2000000000 : ℝ)|=(1083505321/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_box_9 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1051412791/2000000000 : ℝ)*x 0 + (-438905801/2500000000 : ℝ)*x 1 + (5417526111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051412791/2000000000 : ℝ)^4625 ≤ (43785699375071/100000000000000 : ℝ)^3601 := by
    have hnat : (1051412791 : ℕ)^4625*100000000000000^3601 ≤ 43785699375071^3601*2000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051412791 2000000000 43785699375071 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (438905801/2500000000 : ℝ)^4625 ≤ (10704679754983/100000000000000 : ℝ)^3601 := by
    have hnat : (438905801 : ℕ)^4625*100000000000000^3601 ≤ 10704679754983^3601*2500000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438905801 2500000000 10704679754983 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5417526111/10000000000 : ℝ)^4625 ≤ (4550962086051/10000000000000 : ℝ)^3601 := by
    have hnat : (5417526111 : ℕ)^4625*10000000000000^3601 ≤ 4550962086051^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417526111 10000000000 4550962086051 10000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051412791/2000000000 : ℝ), (-438905801/2500000000 : ℝ), (5417526111/10000000000 : ℝ)] ![(43785699375071/100000000000000 : ℝ), (10704679754983/100000000000000 : ℝ), (4550962086051/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051412791/2000000000 : ℝ)|^4625 ≤ (43785699375071/100000000000000 : ℝ)^3601
        have hw : |(1051412791/2000000000 : ℝ)|=(1051412791/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-438905801/2500000000 : ℝ)|^4625 ≤ (10704679754983/100000000000000 : ℝ)^3601
        have hw : |(-438905801/2500000000 : ℝ)|=(438905801/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5417526111/10000000000 : ℝ)|^4625 ≤ (4550962086051/10000000000000 : ℝ)^3601
        have hw : |(5417526111/10000000000 : ℝ)|=(5417526111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_box_10 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (262853217/500000000 : ℝ)*x 0 + (1354381367/2500000000 : ℝ)*x 1 + (-438905891/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262853217/500000000 : ℝ)^4625 ≤ (10946425873391/25000000000000 : ℝ)^3601 := by
    have hnat : (262853217 : ℕ)^4625*25000000000000^3601 ≤ 10946425873391^3601*500000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262853217 500000000 10946425873391 25000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1354381367/2500000000 : ℝ)^4625 ≤ (4550961392303/10000000000000 : ℝ)^3601 := by
    have hnat : (1354381367 : ℕ)^4625*10000000000000^3601 ≤ 4550961392303^3601*2500000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354381367 2500000000 4550961392303 10000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (438905891/2500000000 : ℝ)^4625 ≤ (1338085321779/12500000000000 : ℝ)^3601 := by
    have hnat : (438905891 : ℕ)^4625*12500000000000^3601 ≤ 1338085321779^3601*2500000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438905891 2500000000 1338085321779 12500000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(262853217/500000000 : ℝ), (1354381367/2500000000 : ℝ), (-438905891/2500000000 : ℝ)] ![(10946425873391/25000000000000 : ℝ), (4550961392303/10000000000000 : ℝ), (1338085321779/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(262853217/500000000 : ℝ)|^4625 ≤ (10946425873391/25000000000000 : ℝ)^3601
        have hw : |(262853217/500000000 : ℝ)|=(262853217/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1354381367/2500000000 : ℝ)|^4625 ≤ (4550961392303/10000000000000 : ℝ)^3601
        have hw : |(1354381367/2500000000 : ℝ)|=(1354381367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-438905891/2500000000 : ℝ)|^4625 ≤ (1338085321779/12500000000000 : ℝ)^3601
        have hw : |(-438905891/2500000000 : ℝ)|=(438905891/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_box_11 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4499813533/10000000000 : ℝ)*x 0 + (2062702797/5000000000 : ℝ)*x 1 + (2062702961/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4499813533/10000000000 : ℝ)^4625 ≤ (35857088160961/100000000000000 : ℝ)^3601 := by
    have hnat : (4499813533 : ℕ)^4625*100000000000000^3601 ≤ 35857088160961^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4499813533 10000000000 35857088160961 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2062702797/5000000000 : ℝ)^4625 ≤ (32071454273977/100000000000000 : ℝ)^3601 := by
    have hnat : (2062702797 : ℕ)^4625*100000000000000^3601 ≤ 32071454273977^3601*5000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2062702797 5000000000 32071454273977 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2062702961/5000000000 : ℝ)^4625 ≤ (32071457549001/100000000000000 : ℝ)^3601 := by
    have hnat : (2062702961 : ℕ)^4625*100000000000000^3601 ≤ 32071457549001^3601*5000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2062702961 5000000000 32071457549001 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4499813533/10000000000 : ℝ), (2062702797/5000000000 : ℝ), (2062702961/5000000000 : ℝ)] ![(35857088160961/100000000000000 : ℝ), (32071454273977/100000000000000 : ℝ), (32071457549001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4499813533/10000000000 : ℝ)|^4625 ≤ (35857088160961/100000000000000 : ℝ)^3601
        have hw : |(4499813533/10000000000 : ℝ)|=(4499813533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2062702797/5000000000 : ℝ)|^4625 ≤ (32071454273977/100000000000000 : ℝ)^3601
        have hw : |(2062702797/5000000000 : ℝ)|=(2062702797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2062702961/5000000000 : ℝ)|^4625 ≤ (32071457549001/100000000000000 : ℝ)^3601
        have hw : |(2062702961/5000000000 : ℝ)|=(2062702961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_box_12 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-838344293/5000000000 : ℝ)*x 0 + (687647909/1250000000 : ℝ)*x 1 + (5229896221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (838344293/5000000000 : ℝ)^4625 ≤ (10090518076369/100000000000000 : ℝ)^3601 := by
    have hnat : (838344293 : ℕ)^4625*100000000000000^3601 ≤ 10090518076369^3601*5000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      838344293 5000000000 10090518076369 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (687647909/1250000000 : ℝ)^4625 ≤ (46414192448681/100000000000000 : ℝ)^3601 := by
    have hnat : (687647909 : ℕ)^4625*100000000000000^3601 ≤ 46414192448681^3601*1250000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      687647909 1250000000 46414192448681 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5229896221/10000000000 : ℝ)^4625 ≤ (21747644729913/50000000000000 : ℝ)^3601 := by
    have hnat : (5229896221 : ℕ)^4625*50000000000000^3601 ≤ 21747644729913^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229896221 10000000000 21747644729913 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-838344293/5000000000 : ℝ), (687647909/1250000000 : ℝ), (5229896221/10000000000 : ℝ)] ![(10090518076369/100000000000000 : ℝ), (46414192448681/100000000000000 : ℝ), (21747644729913/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-838344293/5000000000 : ℝ)|^4625 ≤ (10090518076369/100000000000000 : ℝ)^3601
        have hw : |(-838344293/5000000000 : ℝ)|=(838344293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(687647909/1250000000 : ℝ)|^4625 ≤ (46414192448681/100000000000000 : ℝ)^3601
        have hw : |(687647909/1250000000 : ℝ)|=(687647909/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5229896221/10000000000 : ℝ)|^4625 ≤ (21747644729913/50000000000000 : ℝ)^3601
        have hw : |(5229896221/10000000000 : ℝ)|=(5229896221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_box_13 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5387186957/10000000000 : ℝ)*x 0 + (-1833979779/10000000000 : ℝ)*x 1 + (5229896427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5387186957/10000000000 : ℝ)^4625 ≤ (4518254546267/10000000000000 : ℝ)^3601 := by
    have hnat : (5387186957 : ℕ)^4625*10000000000000^3601 ≤ 4518254546267^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387186957 10000000000 4518254546267 10000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1833979779/10000000000 : ℝ)^4625 ≤ (2264432572679/20000000000000 : ℝ)^3601 := by
    have hnat : (1833979779 : ℕ)^4625*20000000000000^3601 ≤ 2264432572679^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1833979779 10000000000 2264432572679 20000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5229896427/10000000000 : ℝ)^4625 ≤ (43495291660243/100000000000000 : ℝ)^3601 := by
    have hnat : (5229896427 : ℕ)^4625*100000000000000^3601 ≤ 43495291660243^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229896427 10000000000 43495291660243 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5387186957/10000000000 : ℝ), (-1833979779/10000000000 : ℝ), (5229896427/10000000000 : ℝ)] ![(4518254546267/10000000000000 : ℝ), (2264432572679/20000000000000 : ℝ), (43495291660243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5387186957/10000000000 : ℝ)|^4625 ≤ (4518254546267/10000000000000 : ℝ)^3601
        have hw : |(5387186957/10000000000 : ℝ)|=(5387186957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1833979779/10000000000 : ℝ)|^4625 ≤ (2264432572679/20000000000000 : ℝ)^3601
        have hw : |(-1833979779/10000000000 : ℝ)|=(1833979779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5229896427/10000000000 : ℝ)|^4625 ≤ (43495291660243/100000000000000 : ℝ)^3601
        have hw : |(5229896427/10000000000 : ℝ)|=(5229896427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_box_14 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5387188141/10000000000 : ℝ)*x 0 + (2614947741/5000000000 : ℝ)*x 1 + (-1833979443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5387188141/10000000000 : ℝ)^4625 ≤ (22591279108373/50000000000000 : ℝ)^3601 := by
    have hnat : (5387188141 : ℕ)^4625*50000000000000^3601 ≤ 22591279108373^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387188141 10000000000 22591279108373 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2614947741/5000000000 : ℝ)^4625 ≤ (21747640783049/50000000000000 : ℝ)^3601 := by
    have hnat : (2614947741 : ℕ)^4625*50000000000000^3601 ≤ 21747640783049^3601*5000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614947741 5000000000 21747640783049 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1833979443/10000000000 : ℝ)^4625 ≤ (566108009961/5000000000000 : ℝ)^3601 := by
    have hnat : (1833979443 : ℕ)^4625*5000000000000^3601 ≤ 566108009961^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1833979443 10000000000 566108009961 5000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5387188141/10000000000 : ℝ), (2614947741/5000000000 : ℝ), (-1833979443/10000000000 : ℝ)] ![(22591279108373/50000000000000 : ℝ), (21747640783049/50000000000000 : ℝ), (566108009961/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5387188141/10000000000 : ℝ)|^4625 ≤ (22591279108373/50000000000000 : ℝ)^3601
        have hw : |(5387188141/10000000000 : ℝ)|=(5387188141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2614947741/5000000000 : ℝ)|^4625 ≤ (21747640783049/50000000000000 : ℝ)^3601
        have hw : |(2614947741/5000000000 : ℝ)|=(2614947741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1833979443/10000000000 : ℝ)|^4625 ≤ (566108009961/5000000000000 : ℝ)^3601
        have hw : |(-1833979443/10000000000 : ℝ)|=(1833979443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_box_15 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (100043687/250000000 : ℝ)*x 0 + (2187216083/5000000000 : ℝ)*x 1 + (2187215299/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (100043687/250000000 : ℝ)^4625 ≤ (30842049497857/100000000000000 : ℝ)^3601 := by
    have hnat : (100043687 : ℕ)^4625*100000000000000^3601 ≤ 30842049497857^3601*250000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100043687 250000000 30842049497857 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2187216083/5000000000 : ℝ)^4625 ≤ (34578983201143/100000000000000 : ℝ)^3601 := by
    have hnat : (2187216083 : ℕ)^4625*100000000000000^3601 ≤ 34578983201143^3601*5000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187216083 5000000000 34578983201143 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2187215299/5000000000 : ℝ)^4625 ≤ (34578967281799/100000000000000 : ℝ)^3601 := by
    have hnat : (2187215299 : ℕ)^4625*100000000000000^3601 ≤ 34578967281799^3601*5000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187215299 5000000000 34578967281799 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(100043687/250000000 : ℝ), (2187216083/5000000000 : ℝ), (2187215299/5000000000 : ℝ)] ![(30842049497857/100000000000000 : ℝ), (34578983201143/100000000000000 : ℝ), (34578967281799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(100043687/250000000 : ℝ)|^4625 ≤ (30842049497857/100000000000000 : ℝ)^3601
        have hw : |(100043687/250000000 : ℝ)|=(100043687/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2187216083/5000000000 : ℝ)|^4625 ≤ (34578983201143/100000000000000 : ℝ)^3601
        have hw : |(2187216083/5000000000 : ℝ)|=(2187216083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2187215299/5000000000 : ℝ)|^4625 ≤ (34578967281799/100000000000000 : ℝ)^3601
        have hw : |(2187215299/5000000000 : ℝ)|=(2187215299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1564_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5235807/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5551/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31909/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29437/50000 : ℝ) ∧ (4043/5000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (86329/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5551/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5551/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5551/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5551/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5551/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5551/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5551/50000 : ℝ) ^ (4623/1024 : ℝ) ≤ (980284461357673/20000000000000000000 : ℝ) := by
    have hpowers : (5551/50000 : ℝ)^4623 ≤ (980284461357673/20000000000000000000 : ℝ)^1024 := by
      have hnat : (5551 : ℕ)^4623*20000000000000000000^1024 ≤ 980284461357673^1024*50000^4623 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5551 50000 980284461357673 20000000000000000000 4623 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5551/50000 : ℝ)) (X := (980284461357673/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4623 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3097/20000 : ℝ) ^ (4623/1024 : ℝ) ≤ (5503942869089091/25000000000000000000 : ℝ) := by
    have hpowers : (3097/20000 : ℝ)^4623 ≤ (5503942869089091/25000000000000000000 : ℝ)^1024 := by
      have hnat : (3097 : ℕ)^4623*25000000000000000000^1024 ≤ 5503942869089091^1024*20000^4623 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3097 20000 5503942869089091 25000000000000000000 4623 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3097/20000 : ℝ)) (X := (5503942869089091/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4623 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000980284461357673/10000000000000000000 : ℝ) ≤ (500010856294481/500000000000000 : ℝ) ^ (4623/1024 : ℝ) := by
    have hpowers : (10000980284461357673/10000000000000000000 : ℝ)^1024 ≤ (500010856294481/500000000000000 : ℝ)^4623 := by
      have hnat : (10000980284461357673 : ℕ)^1024*500000000000000^4623 ≤ 500010856294481^4623*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000980284461357673 10000000000000000000 500010856294481 500000000000000 1024 4623 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500010856294481/500000000000000 : ℝ)) (X := (10000980284461357673/10000000000000000000 : ℝ)) (by norm_num) 4623 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100026917193783144729/100000000000000000000 : ℝ) ≤ (1250074519573219/1250000000000000 : ℝ) ^ (4623/1024 : ℝ) := by
    have hpowers : (100026917193783144729/100000000000000000000 : ℝ)^1024 ≤ (1250074519573219/1250000000000000 : ℝ)^4623 := by
      have hnat : (100026917193783144729 : ℕ)^1024*1250000000000000^4623 ≤ 1250074519573219^4623*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100026917193783144729 100000000000000000000 1250074519573219 1250000000000000 1024 4623 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250074519573219/1250000000000000 : ℝ)) (X := (100026917193783144729/100000000000000000000 : ℝ)) (by norm_num) 4623 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12505503942869089091/12500000000000000000 : ℝ) ≤ (2500243796820471/2500000000000000 : ℝ) ^ (4623/1024 : ℝ) := by
    have hpowers : (12505503942869089091/12500000000000000000 : ℝ)^1024 ≤ (2500243796820471/2500000000000000 : ℝ)^4623 := by
      have hnat : (12505503942869089091 : ℕ)^1024*2500000000000000^4623 ≤ 2500243796820471^4623*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505503942869089091 12500000000000000000 2500243796820471 2500000000000000 1024 4623 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500243796820471/2500000000000000 : ℝ)) (X := (12505503942869089091/12500000000000000000 : ℝ)) (by norm_num) 4623 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(980284461357673/20000000000000000000 : ℝ) ≤ ((10955633916299322383/10957500000000000000 : ℝ)+2*(94757674033/109575000000000 : ℝ)*(5551/50000 : ℝ))^(4623/1024 : ℝ) := by
    rw [show (10955633916299322383/10957500000000000000 : ℝ)+2*(94757674033/109575000000000 : ℝ)*(5551/50000 : ℝ)=(500010856294481/500000000000000 : ℝ) by norm_num, show 1+2*(980284461357673/20000000000000000000 : ℝ)=(10000980284461357673/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5503942869089091/25000000000000000000 : ℝ)+(980284461357673/20000000000000000000 : ℝ) ≤ ((10955633916299322383/10957500000000000000 : ℝ)+(94757674033/109575000000000 : ℝ)*((3097/20000 : ℝ)+(5551/50000 : ℝ)))^(4623/1024 : ℝ) := by
    rw [show (10955633916299322383/10957500000000000000 : ℝ)+(94757674033/109575000000000 : ℝ)*((3097/20000 : ℝ)+(5551/50000 : ℝ))=(1250074519573219/1250000000000000 : ℝ) by norm_num, show 1+(5503942869089091/25000000000000000000 : ℝ)+(980284461357673/20000000000000000000 : ℝ)=(100026917193783144729/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5503942869089091/25000000000000000000 : ℝ) ≤ ((10955633916299322383/10957500000000000000 : ℝ)+2*(94757674033/109575000000000 : ℝ)*(3097/20000 : ℝ))^(4623/1024 : ℝ) := by
    rw [show (10955633916299322383/10957500000000000000 : ℝ)+2*(94757674033/109575000000000 : ℝ)*(3097/20000 : ℝ)=(2500243796820471/2500000000000000 : ℝ) by norm_num, show 1+2*(5503942869089091/25000000000000000000 : ℝ)=(12505503942869089091/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10955633916299322383/10957500000000000000 : ℝ)*(X 1 0+X 2 0)+(94757674033/109575000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4623/1024 : ℝ)) (lo := (5551/50000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (10955633916299322383/10957500000000000000 : ℝ)) (alpha := (94757674033/109575000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10955633916299322383/10957500000000000000 : ℝ)*(X 0 1+X 2 1)+(94757674033/109575000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4623/1024 : ℝ)) (lo := (5551/50000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (10955633916299322383/10957500000000000000 : ℝ)) (alpha := (94757674033/109575000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10955633916299322383/10957500000000000000 : ℝ)*(X 0 2+X 1 2)+(94757674033/109575000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4623/1024 : ℝ)) (lo := (5551/50000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (10955633916299322383/10957500000000000000 : ℝ)) (alpha := (94757674033/109575000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1589069951/10000000000 : ℝ)*X 0 0+(1349308943/2500000000 : ℝ)*X 0 1+(215889397/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2635569423/5000000000 : ℝ)*X 1 0+(-441080869/2500000000 : ℝ)*X 1 1+(2698617741/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5271139479/10000000000 : ℝ)*X 2 0+(5397235271/10000000000 : ℝ)*X 2 1+(-882161451/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((138970863/312500000 : ℝ)*X 0 0+(4152367503/10000000000 : ℝ)*X 0 1+(4152368761/10000000000 : ℝ)*X 0 2+(138970863/312500000 : ℝ)*X 1 0+(4152367503/10000000000 : ℝ)*X 1 1+(4152368761/10000000000 : ℝ)*X 1 2+(138970863/312500000 : ℝ)*X 2 0+(4152367503/10000000000 : ℝ)*X 2 1+(4152368761/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-400802923/2000000000 : ℝ)*X 0 0+(524494573/1000000000 : ℝ)*X 0 1+(5244946071/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1344187417/2500000000 : ℝ)*X 1 0+(-1827870249/10000000000 : ℝ)*X 1 1+(2622473/5000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((8602799/16000000 : ℝ)*X 2 0+(5244946373/10000000000 : ℝ)*X 2 1+(-28560471/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2021290609/5000000000 : ℝ)*X 0 0+(2177241859/5000000000 : ℝ)*X 0 1+(2177241389/5000000000 : ℝ)*X 0 2+(2021290609/5000000000 : ℝ)*X 1 0+(2177241859/5000000000 : ℝ)*X 1 1+(2177241389/5000000000 : ℝ)*X 1 2+(2021290609/5000000000 : ℝ)*X 2 0+(2177241859/5000000000 : ℝ)*X 2 1+(2177241389/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-958042261/5000000000 : ℝ)*X 0 0+(1027542493/2000000000 : ℝ)*X 0 1+(1083505321/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1051412791/2000000000 : ℝ)*X 1 0+(-438905801/2500000000 : ℝ)*X 1 1+(5417526111/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((262853217/500000000 : ℝ)*X 2 0+(1354381367/2500000000 : ℝ)*X 2 1+(-438905891/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4499813533/10000000000 : ℝ)*X 0 0+(2062702797/5000000000 : ℝ)*X 0 1+(2062702961/5000000000 : ℝ)*X 0 2+(4499813533/10000000000 : ℝ)*X 1 0+(2062702797/5000000000 : ℝ)*X 1 1+(2062702961/5000000000 : ℝ)*X 1 2+(4499813533/10000000000 : ℝ)*X 2 0+(2062702797/5000000000 : ℝ)*X 2 1+(2062702961/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-838344293/5000000000 : ℝ)*X 0 0+(687647909/1250000000 : ℝ)*X 0 1+(5229896221/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5387186957/10000000000 : ℝ)*X 1 0+(-1833979779/10000000000 : ℝ)*X 1 1+(5229896427/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5387188141/10000000000 : ℝ)*X 2 0+(2614947741/5000000000 : ℝ)*X 2 1+(-1833979443/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((100043687/250000000 : ℝ)*X 0 0+(2187216083/5000000000 : ℝ)*X 0 1+(2187215299/5000000000 : ℝ)*X 0 2+(100043687/250000000 : ℝ)*X 1 0+(2187216083/5000000000 : ℝ)*X 1 1+(2187215299/5000000000 : ℝ)*X 1 2+(100043687/250000000 : ℝ)*X 2 0+(2187216083/5000000000 : ℝ)*X 2 1+(2187215299/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31909/50000 : ℝ) ≤ (-9711954741602425200760567189743/15218750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (139328239/100000000000000 : ℝ)*(lower0) + (4067/25000000000000 : ℝ)*(upper3) + (3967867/20000000000000 : ℝ)*(lower4) + (574784312997237/25000000000000 : ℝ)*(major0) + (574784312997237/25000000000000 : ℝ)*(major1) + (574784312997237/25000000000000 : ℝ)*(major2) + (1082263183/50000000000000 : ℝ)*(sp1) + (811825498851917/25000000000000 : ℝ)*(sp4) + (811825101006241/25000000000000 : ℝ)*(sp5) + (405906540765987/12500000000000 : ℝ)*(sp6) + (1372231161570219/100000000000000 : ℝ)*(sp7) + (573143663/100000000000000 : ℝ)*(sp8) + (10048484687/20000000000000 : ℝ)*(sp14) + (12680203449/100000000000000 : ℝ)*(sp15) + (343060960443417/25000000000000 : ℝ)*(f.failure) + (324730256855133/10000000000000 : ℝ)*(f.sum) + (11288932421033/1826250000000000000000000000 : ℝ)*base65 + (81394634227634081/30437500000000000000000000000000 : ℝ)*base68 + (321022853833384081/30437500000000000000000000000000 : ℝ)*base70 + (270302181979053419/30437500000000000000000000000000 : ℝ)*base71 + (22892163067973/1826250000000000000000000000 : ℝ)*base73 + (78196614346071581/30437500000000000000000000000000 : ℝ)*base76 + (127090540820259081/30437500000000000000000000000000 : ℝ)*base78 + (247938356569803419/30437500000000000000000000000000 : ℝ)*base79 + (14477039532437/7305000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (207519/78125000000000000000 : ℝ)*base89 + (207519/78125000000000000000 : ℝ)*base91 + (207519/78125000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (29437/50000 : ℝ) ≤ (448012282208285424218495268723/760937500000000000000000000000 : ℝ) := by norm_num
    linear_combination (2564887/12500000000000 : ℝ)*(upper0) + (149467047/50000000000000 : ℝ)*(lower1) + (145182829/50000000000000 : ℝ)*(upper4) + (29736982456659/1250000000000 : ℝ)*(major0) + (29736982456659/1250000000000 : ℝ)*(major1) + (29736982456659/1250000000000 : ℝ)*(major2) + (8296002825387/250000000000 : ℝ)*(sp0) + (829586224397433/25000000000000 : ℝ)*(sp1) + (829600489275737/25000000000000 : ℝ)*(sp2) + (354970004329447/25000000000000 : ℝ)*(sp3) + (8320211/156250000000 : ℝ)*(sp7) + (2634092991/50000000000000 : ℝ)*(sp8) + (61500751051/100000000000000 : ℝ)*(sp9) + (888247567/20000000000000 : ℝ)*(sp10) + (354971335563207/25000000000000 : ℝ)*(f.failure) + (1659203199170391/50000000000000 : ℝ)*(f.sum) + (331508347319/121750000000000000000000000 : ℝ)*base66 + (1039987754932817/1521875000000000000000000000000 : ℝ)*base68 + (12615535778082817/1521875000000000000000000000000 : ℝ)*base70 + (12245230194992971/760937500000000000000000000000 : ℝ)*base72 + (194483492183/60875000000000000000000000 : ℝ)*base74 + (12351911477517971/760937500000000000000000000000 : ℝ)*base76 + (21067751362814067/1521875000000000000000000000000 : ℝ)*base78 + (1449511413673433/1521875000000000000000000000000 : ℝ)*base79 + (16644485159/15218750000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (653049/78125000000000000000 : ℝ)*base89 + (653049/78125000000000000000 : ℝ)*base91 + (653049/78125000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (4043/5000 : ℝ) ≤ (2953499694876498019110697187/3652500000000000000000000000 : ℝ) := by norm_num
    linear_combination (12854711/12500000000000 : ℝ)*(upper0) + (4490757/6250000000000 : ℝ)*(upper1) + (9849221/25000000000000 : ℝ)*(upper2) + (641553144748183/25000000000000 : ℝ)*(major0) + (641553144748183/25000000000000 : ℝ)*(major1) + (641553144748183/25000000000000 : ℝ)*(major2) + (12574808791/10000000000000 : ℝ)*(sp1) + (378931111/4000000000000 : ℝ)*(sp3) + (16927448703/100000000000000 : ℝ)*(sp4) + (1786901147311441/50000000000000 : ℝ)*(sp8) + (1786848541355863/50000000000000 : ℝ)*(sp9) + (893455707699909/25000000000000 : ℝ)*(sp10) + (76581935784667/5000000000000 : ℝ)*(sp11) + (902182013/25000000000000 : ℝ)*(sp12) + (306329637794223/20000000000000 : ℝ)*(f.failure) + (893455707699909/25000000000000 : ℝ)*(f.sum) + (29549841623539/21915000000000000000000000000 : ℝ)*base65 + (44277853854006379/30437500000000000000000000000000 : ℝ)*base68 + (60347667430693879/30437500000000000000000000000000 : ℝ)*base70 + (230035714820556121/30437500000000000000000000000000 : ℝ)*base71 + (13773069865091/21915000000000000000000000000 : ℝ)*base74 + (166755255681756379/30437500000000000000000000000000 : ℝ)*base76 + (258458494298681121/30437500000000000000000000000000 : ℝ)*base77 + (197515479482993621/30437500000000000000000000000000 : ℝ)*base79 + (130796957107541/21915000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (157039/62500000000000000000 : ℝ)*base90 + (157039/62500000000000000000 : ℝ)*base92 + (157039/62500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-86329/100000 : ℝ) ≤ (-13137874448000479339423305720097/15218750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (383979619/100000000000000 : ℝ)*(lower2) + (53909809/25000000000000 : ℝ)*(upper3) + (126235031/100000000000000 : ℝ)*(upper5) + (651634868010927/25000000000000 : ℝ)*(major0) + (651634868010927/25000000000000 : ℝ)*(major1) + (651634868010927/25000000000000 : ℝ)*(major2) + (11529289267/100000000000000 : ℝ)*(sp0) + (44205166737/20000000000000 : ℝ)*(sp5) + (271248610191/100000000000000 : ℝ)*(sp6) + (9189365047/100000000000000 : ℝ)*(sp7) + (1843062842725691/50000000000000 : ℝ)*(sp12) + (921479047226741/25000000000000 : ℝ)*(sp13) + (1842932983065229/50000000000000 : ℝ)*(sp14) + (1555708171900673/100000000000000 : ℝ)*(sp15) + (38892934031643/2500000000000 : ℝ)*(f.failure) + (3686137214740649/100000000000000 : ℝ)*(f.sum) + (57024846792533/7305000000000000000000000000 : ℝ)*base66 + (339282275198225449/30437500000000000000000000000000 : ℝ)*base67 + (42727736206462051/30437500000000000000000000000000 : ℝ)*base70 + (284537907509850449/30437500000000000000000000000000 : ℝ)*base71 + (33380851225537/7305000000000000000000000000 : ℝ)*base73 + (78764221362524551/30437500000000000000000000000000 : ℝ)*base76 + (123823522227037949/30437500000000000000000000000000 : ℝ)*base77 + (160390831143412949/30437500000000000000000000000000 : ℝ)*base79 + (2346303217721/3652500000000000000000000000 : ℝ)*base81 + (46599/7812500000000000000 : ℝ)*base90 + (46599/7812500000000000000 : ℝ)*base92 + (46599/7812500000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1564_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5235807/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5551/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31909/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29437/50000 : ℝ) else (4043/5000 : ℝ) ≤ X j i ∧ X j i ≤ (86329/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1564_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1564_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5235807/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11101/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31909/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29437/50000 : ℝ) else (4043/5000 : ℝ) ≤ X j i ∧ X j i ≤ (86329/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1564_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1564_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5235807/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11101/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31909/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29437/50000 : ℝ) else (4043/5000 : ℝ) ≤ X j i ∧ X j i ≤ (86329/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1564_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
