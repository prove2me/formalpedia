-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1678_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:27:58.47082+00:00
-- url     : https://prove2.me/submissions/d5ec6358-0dfe-49da-9047-5032a46f75c6

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
theorem support_rectangle_w1678_s3_0 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1536657679/10000000000 : ℝ)*x 0 + (5491519651/10000000000 : ℝ)*x 1 + (2566465867/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1536657679/10000000000 : ℝ)^5047 ≤ (4769813443983/50000000000000 : ℝ)^4023 := by
    have hnat : (1536657679 : ℕ)^5047*50000000000000^4023 ≤ 4769813443983^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1536657679 10000000000 4769813443983 50000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5491519651/10000000000 : ℝ)^5047 ≤ (5893113800483/12500000000000 : ℝ)^4023 := by
    have hnat : (5491519651 : ℕ)^5047*12500000000000^4023 ≤ 5893113800483^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5491519651 10000000000 5893113800483 12500000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2566465867/5000000000 : ℝ)^5047 ≤ (21657731349159/50000000000000 : ℝ)^4023 := by
    have hnat : (2566465867 : ℕ)^5047*50000000000000^4023 ≤ 21657731349159^4023*5000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2566465867 5000000000 21657731349159 50000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1536657679/10000000000 : ℝ), (5491519651/10000000000 : ℝ), (2566465867/5000000000 : ℝ)] ![(4769813443983/50000000000000 : ℝ), (5893113800483/12500000000000 : ℝ), (21657731349159/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1536657679/10000000000 : ℝ)|^5047 ≤ (4769813443983/50000000000000 : ℝ)^4023
        have hw : |(-1536657679/10000000000 : ℝ)|=(1536657679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5491519651/10000000000 : ℝ)|^5047 ≤ (5893113800483/12500000000000 : ℝ)^4023
        have hw : |(5491519651/10000000000 : ℝ)|=(5491519651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2566465867/5000000000 : ℝ)|^5047 ≤ (21657731349159/50000000000000 : ℝ)^4023
        have hw : |(2566465867/5000000000 : ℝ)|=(2566465867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_s3_1 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677103587/5000000000 : ℝ)*x 0 + (-430785043/2500000000 : ℝ)*x 1 + (160404117/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677103587/5000000000 : ℝ)^5047 ≤ (9134151461247/20000000000000 : ℝ)^4023 := by
    have hnat : (2677103587 : ℕ)^5047*20000000000000^4023 ≤ 9134151461247^4023*5000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677103587 5000000000 9134151461247 20000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (430785043/2500000000 : ℝ)^5047 ≤ (11013779870177/100000000000000 : ℝ)^4023 := by
    have hnat : (430785043 : ℕ)^5047*100000000000000^4023 ≤ 11013779870177^4023*2500000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430785043 2500000000 11013779870177 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (160404117/312500000 : ℝ)^5047 ≤ (8663092560837/20000000000000 : ℝ)^4023 := by
    have hnat : (160404117 : ℕ)^5047*20000000000000^4023 ≤ 8663092560837^4023*312500000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160404117 312500000 8663092560837 20000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677103587/5000000000 : ℝ), (-430785043/2500000000 : ℝ), (160404117/312500000 : ℝ)] ![(9134151461247/20000000000000 : ℝ), (11013779870177/100000000000000 : ℝ), (8663092560837/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677103587/5000000000 : ℝ)|^5047 ≤ (9134151461247/20000000000000 : ℝ)^4023
        have hw : |(2677103587/5000000000 : ℝ)|=(2677103587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-430785043/2500000000 : ℝ)|^5047 ≤ (11013779870177/100000000000000 : ℝ)^4023
        have hw : |(-430785043/2500000000 : ℝ)|=(430785043/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(160404117/312500000 : ℝ)|^5047 ≤ (8663092560837/20000000000000 : ℝ)^4023
        have hw : |(160404117/312500000 : ℝ)|=(160404117/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_s3_2 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677103597/5000000000 : ℝ)*x 0 + (5132931727/10000000000 : ℝ)*x 1 + (-1723140169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677103597/5000000000 : ℝ)^5047 ≤ (356802793127/781250000000 : ℝ)^4023 := by
    have hnat : (2677103597 : ℕ)^5047*781250000000^4023 ≤ 356802793127^4023*5000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677103597 5000000000 356802793127 781250000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5132931727/10000000000 : ℝ)^5047 ≤ (43315462624211/100000000000000 : ℝ)^4023 := by
    have hnat : (5132931727 : ℕ)^5047*100000000000000^4023 ≤ 43315462624211^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5132931727 10000000000 43315462624211 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1723140169/10000000000 : ℝ)^5047 ≤ (11013779846121/100000000000000 : ℝ)^4023 := by
    have hnat : (1723140169 : ℕ)^5047*100000000000000^4023 ≤ 11013779846121^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1723140169 10000000000 11013779846121 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677103597/5000000000 : ℝ), (5132931727/10000000000 : ℝ), (-1723140169/10000000000 : ℝ)] ![(356802793127/781250000000 : ℝ), (43315462624211/100000000000000 : ℝ), (11013779846121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677103597/5000000000 : ℝ)|^5047 ≤ (356802793127/781250000000 : ℝ)^4023
        have hw : |(2677103597/5000000000 : ℝ)|=(2677103597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5132931727/10000000000 : ℝ)|^5047 ≤ (43315462624211/100000000000000 : ℝ)^4023
        have hw : |(5132931727/10000000000 : ℝ)|=(5132931727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1723140169/10000000000 : ℝ)|^5047 ≤ (11013779846121/100000000000000 : ℝ)^4023
        have hw : |(-1723140169/10000000000 : ℝ)|=(1723140169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_s3_3 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (518503537/1250000000 : ℝ)*x 0 + (1842657099/5000000000 : ℝ)*x 1 + (581174481/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (518503537/1250000000 : ℝ)^5047 ≤ (4144560866757/12500000000000 : ℝ)^4023 := by
    have hnat : (518503537 : ℕ)^5047*12500000000000^4023 ≤ 4144560866757^4023*1250000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518503537 1250000000 4144560866757 12500000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1842657099/5000000000 : ℝ)^5047 ≤ (2858423006143/10000000000000 : ℝ)^4023 := by
    have hnat : (1842657099 : ℕ)^5047*10000000000000^4023 ≤ 2858423006143^4023*5000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1842657099 5000000000 2858423006143 10000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (581174481/1250000000 : ℝ)^5047 ≤ (38259282986883/100000000000000 : ℝ)^4023 := by
    have hnat : (581174481 : ℕ)^5047*100000000000000^4023 ≤ 38259282986883^4023*1250000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      581174481 1250000000 38259282986883 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(518503537/1250000000 : ℝ), (1842657099/5000000000 : ℝ), (581174481/1250000000 : ℝ)] ![(4144560866757/12500000000000 : ℝ), (2858423006143/10000000000000 : ℝ), (38259282986883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(518503537/1250000000 : ℝ)|^5047 ≤ (4144560866757/12500000000000 : ℝ)^4023
        have hw : |(518503537/1250000000 : ℝ)|=(518503537/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1842657099/5000000000 : ℝ)|^5047 ≤ (2858423006143/10000000000000 : ℝ)^4023
        have hw : |(1842657099/5000000000 : ℝ)|=(1842657099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(581174481/1250000000 : ℝ)|^5047 ≤ (38259282986883/100000000000000 : ℝ)^4023
        have hw : |(581174481/1250000000 : ℝ)|=(581174481/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_s3_4 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-307365571/2000000000 : ℝ)*x 0 + (5136793847/10000000000 : ℝ)*x 1 + (2743799787/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (307365571/2000000000 : ℝ)^5047 ≤ (1192619034087/12500000000000 : ℝ)^4023 := by
    have hnat : (307365571 : ℕ)^5047*12500000000000^4023 ≤ 1192619034087^4023*2000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      307365571 2000000000 1192619034087 12500000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5136793847/10000000000 : ℝ)^5047 ≤ (1083908841433/2500000000000 : ℝ)^4023 := by
    have hnat : (5136793847 : ℕ)^5047*2500000000000^4023 ≤ 1083908841433^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5136793847 10000000000 1083908841433 2500000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2743799787/5000000000 : ℝ)^5047 ≤ (4710269405419/10000000000000 : ℝ)^4023 := by
    have hnat : (2743799787 : ℕ)^5047*10000000000000^4023 ≤ 4710269405419^4023*5000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2743799787 5000000000 4710269405419 10000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-307365571/2000000000 : ℝ), (5136793847/10000000000 : ℝ), (2743799787/5000000000 : ℝ)] ![(1192619034087/12500000000000 : ℝ), (1083908841433/2500000000000 : ℝ), (4710269405419/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-307365571/2000000000 : ℝ)|^5047 ≤ (1192619034087/12500000000000 : ℝ)^4023
        have hw : |(-307365571/2000000000 : ℝ)|=(307365571/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5136793847/10000000000 : ℝ)|^5047 ≤ (1083908841433/2500000000000 : ℝ)^4023
        have hw : |(5136793847/10000000000 : ℝ)|=(5136793847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2743799787/5000000000 : ℝ)|^5047 ≤ (4710269405419/10000000000000 : ℝ)^4023
        have hw : |(2743799787/5000000000 : ℝ)|=(2743799787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_s3_5 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (657310651/1250000000 : ℝ)*x 0 + (-273694521/2000000000 : ℝ)*x 1 + (5487599519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (657310651/1250000000 : ℝ)^5047 ≤ (11162193255073/25000000000000 : ℝ)^4023 := by
    have hnat : (657310651 : ℕ)^5047*25000000000000^4023 ≤ 11162193255073^4023*1250000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657310651 1250000000 11162193255073 25000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (273694521/2000000000 : ℝ)^5047 ≤ (1649706700901/20000000000000 : ℝ)^4023 := by
    have hnat : (273694521 : ℕ)^5047*20000000000000^4023 ≤ 1649706700901^4023*2000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273694521 2000000000 1649706700901 20000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5487599519/10000000000 : ℝ)^5047 ≤ (9420538692387/20000000000000 : ℝ)^4023 := by
    have hnat : (5487599519 : ℕ)^5047*20000000000000^4023 ≤ 9420538692387^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5487599519 10000000000 9420538692387 20000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(657310651/1250000000 : ℝ), (-273694521/2000000000 : ℝ), (5487599519/10000000000 : ℝ)] ![(11162193255073/25000000000000 : ℝ), (1649706700901/20000000000000 : ℝ), (9420538692387/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(657310651/1250000000 : ℝ)|^5047 ≤ (11162193255073/25000000000000 : ℝ)^4023
        have hw : |(657310651/1250000000 : ℝ)|=(657310651/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-273694521/2000000000 : ℝ)|^5047 ≤ (1649706700901/20000000000000 : ℝ)^4023
        have hw : |(-273694521/2000000000 : ℝ)|=(273694521/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5487599519/10000000000 : ℝ)|^5047 ≤ (9420538692387/20000000000000 : ℝ)^4023
        have hw : |(5487599519/10000000000 : ℝ)|=(5487599519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_s3_6 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5258485471/10000000000 : ℝ)*x 0 + (2743799691/5000000000 : ℝ)*x 1 + (-1368472429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5258485471/10000000000 : ℝ)^5047 ≤ (22324387910887/50000000000000 : ℝ)^4023 := by
    have hnat : (5258485471 : ℕ)^5047*50000000000000^4023 ≤ 22324387910887^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258485471 10000000000 22324387910887 50000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2743799691/5000000000 : ℝ)^5047 ≤ (47102691986679/100000000000000 : ℝ)^4023 := by
    have hnat : (2743799691 : ℕ)^5047*100000000000000^4023 ≤ 47102691986679^4023*5000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2743799691 5000000000 47102691986679 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1368472429/10000000000 : ℝ)^5047 ≤ (8248532173633/100000000000000 : ℝ)^4023 := by
    have hnat : (1368472429 : ℕ)^5047*100000000000000^4023 ≤ 8248532173633^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368472429 10000000000 8248532173633 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5258485471/10000000000 : ℝ), (2743799691/5000000000 : ℝ), (-1368472429/10000000000 : ℝ)] ![(22324387910887/50000000000000 : ℝ), (47102691986679/100000000000000 : ℝ), (8248532173633/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5258485471/10000000000 : ℝ)|^5047 ≤ (22324387910887/50000000000000 : ℝ)^4023
        have hw : |(5258485471/10000000000 : ℝ)|=(5258485471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2743799691/5000000000 : ℝ)|^5047 ≤ (47102691986679/100000000000000 : ℝ)^4023
        have hw : |(2743799691/5000000000 : ℝ)|=(2743799691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1368472429/10000000000 : ℝ)|^5047 ≤ (8248532173633/100000000000000 : ℝ)^4023
        have hw : |(-1368472429/10000000000 : ℝ)|=(1368472429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_s3_7 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2074242337/5000000000 : ℝ)*x 0 + (231950583/500000000 : ℝ)*x 1 + (739170767/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2074242337/5000000000 : ℝ)^5047 ≤ (2072566469493/6250000000000 : ℝ)^4023 := by
    have hnat : (2074242337 : ℕ)^5047*6250000000000^4023 ≤ 2072566469493^4023*5000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074242337 5000000000 2072566469493 6250000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (231950583/500000000 : ℝ)^5047 ≤ (38152113146337/100000000000000 : ℝ)^4023 := by
    have hnat : (231950583 : ℕ)^5047*100000000000000^4023 ≤ 38152113146337^4023*500000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      231950583 500000000 38152113146337 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (739170767/2000000000 : ℝ)^5047 ≤ (28686823322607/100000000000000 : ℝ)^4023 := by
    have hnat : (739170767 : ℕ)^5047*100000000000000^4023 ≤ 28686823322607^4023*2000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      739170767 2000000000 28686823322607 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2074242337/5000000000 : ℝ), (231950583/500000000 : ℝ), (739170767/2000000000 : ℝ)] ![(2072566469493/6250000000000 : ℝ), (38152113146337/100000000000000 : ℝ), (28686823322607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2074242337/5000000000 : ℝ)|^5047 ≤ (2072566469493/6250000000000 : ℝ)^4023
        have hw : |(2074242337/5000000000 : ℝ)|=(2074242337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(231950583/500000000 : ℝ)|^5047 ≤ (38152113146337/100000000000000 : ℝ)^4023
        have hw : |(231950583/500000000 : ℝ)|=(231950583/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(739170767/2000000000 : ℝ)|^5047 ≤ (28686823322607/100000000000000 : ℝ)^4023
        have hw : |(739170767/2000000000 : ℝ)|=(739170767/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1678_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (46106879/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8677/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9673/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4851/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17321/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8677/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9673/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8677/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9673/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8677/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9673/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8677/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9673/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8677/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9673/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8677/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9673/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9673/100000 : ℝ) ^ (5039/1024 : ℝ) ≤ (254676951475001/25000000000000000000 : ℝ) := by
    have hpowers : (9673/100000 : ℝ)^5039 ≤ (254676951475001/25000000000000000000 : ℝ)^1024 := by
      have hnat : (9673 : ℕ)^5039*25000000000000000000^1024 ≤ 254676951475001^1024*100000^5039 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9673 100000 254676951475001 25000000000000000000 5039 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9673/100000 : ℝ)) (X := (254676951475001/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5039 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8677/50000 : ℝ) ^ (5039/1024 : ℝ) ≤ (9039255258063449/50000000000000000000 : ℝ) := by
    have hpowers : (8677/50000 : ℝ)^5039 ≤ (9039255258063449/50000000000000000000 : ℝ)^1024 := by
      have hnat : (8677 : ℕ)^5039*50000000000000000000^1024 ≤ 9039255258063449^1024*50000^5039 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8677 50000 9039255258063449 50000000000000000000 5039 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8677/50000 : ℝ)) (X := (9039255258063449/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5039 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500254676951475001/12500000000000000000 : ℝ) ≤ (5000020701494863/5000000000000000 : ℝ) ^ (5039/1024 : ℝ) := by
    have hpowers : (12500254676951475001/12500000000000000000 : ℝ)^1024 ≤ (5000020701494863/5000000000000000 : ℝ)^5039 := by
      have hnat : (12500254676951475001 : ℕ)^1024*5000000000000000^5039 ≤ 5000020701494863^5039*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500254676951475001 12500000000000000000 5000020701494863 5000000000000000 1024 5039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000020701494863/5000000000000000 : ℝ)) (X := (12500254676951475001/12500000000000000000 : ℝ)) (by norm_num) 5039 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50009548609161013451/50000000000000000000 : ℝ) ≤ (5000194027226717/5000000000000000 : ℝ) ^ (5039/1024 : ℝ) := by
    have hpowers : (50009548609161013451/50000000000000000000 : ℝ)^1024 ≤ (5000194027226717/5000000000000000 : ℝ)^5039 := by
      have hnat : (50009548609161013451 : ℕ)^1024*5000000000000000^5039 ≤ 5000194027226717^5039*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009548609161013451 50000000000000000000 5000194027226717 5000000000000000 1024 5039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000194027226717/5000000000000000 : ℝ)) (X := (50009548609161013451/50000000000000000000 : ℝ)) (by norm_num) 5039 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25009039255258063449/25000000000000000000 : ℝ) ≤ (5000367352958571/5000000000000000 : ℝ) ^ (5039/1024 : ℝ) := by
    have hpowers : (25009039255258063449/25000000000000000000 : ℝ)^1024 ≤ (5000367352958571/5000000000000000 : ℝ)^5039 := by
      have hnat : (25009039255258063449 : ℕ)^1024*5000000000000000^5039 ≤ 5000367352958571^5039*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009039255258063449 25000000000000000000 5000367352958571 5000000000000000 1024 5039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000367352958571/5000000000000000 : ℝ)) (X := (25009039255258063449/25000000000000000000 : ℝ)) (by norm_num) 5039 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(254676951475001/25000000000000000000 : ℝ) ≤ ((38401805848573595219/38405000000000000000 : ℝ)+2*(86662865927/192025000000000 : ℝ)*(9673/100000 : ℝ))^(5039/1024 : ℝ) := by
    rw [show (38401805848573595219/38405000000000000000 : ℝ)+2*(86662865927/192025000000000 : ℝ)*(9673/100000 : ℝ)=(5000020701494863/5000000000000000 : ℝ) by norm_num, show 1+2*(254676951475001/25000000000000000000 : ℝ)=(12500254676951475001/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9039255258063449/50000000000000000000 : ℝ)+(254676951475001/25000000000000000000 : ℝ) ≤ ((38401805848573595219/38405000000000000000 : ℝ)+(86662865927/192025000000000 : ℝ)*((8677/50000 : ℝ)+(9673/100000 : ℝ)))^(5039/1024 : ℝ) := by
    rw [show (38401805848573595219/38405000000000000000 : ℝ)+(86662865927/192025000000000 : ℝ)*((8677/50000 : ℝ)+(9673/100000 : ℝ))=(5000194027226717/5000000000000000 : ℝ) by norm_num, show 1+(9039255258063449/50000000000000000000 : ℝ)+(254676951475001/25000000000000000000 : ℝ)=(50009548609161013451/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9039255258063449/50000000000000000000 : ℝ) ≤ ((38401805848573595219/38405000000000000000 : ℝ)+2*(86662865927/192025000000000 : ℝ)*(8677/50000 : ℝ))^(5039/1024 : ℝ) := by
    rw [show (38401805848573595219/38405000000000000000 : ℝ)+2*(86662865927/192025000000000 : ℝ)*(8677/50000 : ℝ)=(5000367352958571/5000000000000000 : ℝ) by norm_num, show 1+2*(9039255258063449/50000000000000000000 : ℝ)=(25009039255258063449/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (38401805848573595219/38405000000000000000 : ℝ)*(X 1 0+X 2 0)+(86662865927/192025000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5039/1024 : ℝ)) (lo := (9673/100000 : ℝ)) (hi := (8677/50000 : ℝ)) (c := (38401805848573595219/38405000000000000000 : ℝ)) (alpha := (86662865927/192025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (38401805848573595219/38405000000000000000 : ℝ)*(X 0 1+X 2 1)+(86662865927/192025000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5039/1024 : ℝ)) (lo := (9673/100000 : ℝ)) (hi := (8677/50000 : ℝ)) (c := (38401805848573595219/38405000000000000000 : ℝ)) (alpha := (86662865927/192025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (38401805848573595219/38405000000000000000 : ℝ)*(X 0 2+X 1 2)+(86662865927/192025000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5039/1024 : ℝ)) (lo := (9673/100000 : ℝ)) (hi := (8677/50000 : ℝ)) (c := (38401805848573595219/38405000000000000000 : ℝ)) (alpha := (86662865927/192025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1536657679/10000000000 : ℝ)*X 0 0+(5491519651/10000000000 : ℝ)*X 0 1+(2566465867/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677103587/5000000000 : ℝ)*X 1 0+(-430785043/2500000000 : ℝ)*X 1 1+(160404117/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2677103597/5000000000 : ℝ)*X 2 0+(5132931727/10000000000 : ℝ)*X 2 1+(-1723140169/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((518503537/1250000000 : ℝ)*X 0 0+(1842657099/5000000000 : ℝ)*X 0 1+(581174481/1250000000 : ℝ)*X 0 2+(518503537/1250000000 : ℝ)*X 1 0+(1842657099/5000000000 : ℝ)*X 1 1+(581174481/1250000000 : ℝ)*X 1 2+(518503537/1250000000 : ℝ)*X 2 0+(1842657099/5000000000 : ℝ)*X 2 1+(581174481/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-307365571/2000000000 : ℝ)*X 0 0+(5136793847/10000000000 : ℝ)*X 0 1+(2743799787/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((657310651/1250000000 : ℝ)*X 1 0+(-273694521/2000000000 : ℝ)*X 1 1+(5487599519/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5258485471/10000000000 : ℝ)*X 2 0+(2743799691/5000000000 : ℝ)*X 2 1+(-1368472429/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2074242337/5000000000 : ℝ)*X 0 0+(231950583/500000000 : ℝ)*X 0 1+(739170767/2000000000 : ℝ)*X 0 2+(2074242337/5000000000 : ℝ)*X 1 0+(231950583/500000000 : ℝ)*X 1 1+(739170767/2000000000 : ℝ)*X 1 2+(2074242337/5000000000 : ℝ)*X 2 0+(231950583/500000000 : ℝ)*X 2 1+(739170767/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16246987167726404030048409993/1920250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1311622237/100000000000000 : ℝ)*(base19) + (24849197/2000000000000 : ℝ)*(base23) + (8521691/20000000000000 : ℝ)*(lower2) + (207295649/100000000000000 : ℝ)*(upper3) + (152408329/100000000000000 : ℝ)*(upper5) + (1913003569866517/100000000000000 : ℝ)*(major0) + (1913003569866517/100000000000000 : ℝ)*(major1) + (1913003569866517/100000000000000 : ℝ)*(major2) + (2788728813433047/100000000000000 : ℝ)*(sp0) + (1394369867453593/50000000000000 : ℝ)*(sp1) + (2788739804069573/100000000000000 : ℝ)*(sp2) + (25931522421317/2500000000000 : ℝ)*(sp3) + (12233096377/100000000000000 : ℝ)*(sp4) + (4914321893/100000000000000 : ℝ)*(sp7) + (518632905587287/50000000000000 : ℝ)*(f.failure) + (174296315408089/6250000000000 : ℝ)*(f.sum) + (37676131928933/19202500000000000000000000000 : ℝ)*base65 + (8343142830663182223/3840500000000000000000000000000000 : ℝ)*base67 + (45796016612835682223/3840500000000000000000000000000000 : ℝ)*base69 + (19052255759268182223/3840500000000000000000000000000000 : ℝ)*base71 + (10609371406837/4800625000000000000000000000 : ℝ)*base73 + (44427433361171682223/3840500000000000000000000000000000 : ℝ)*base75 + (39300309617049182223/3840500000000000000000000000000000 : ℝ)*base77 + (25770780123635682223/3840500000000000000000000000000000 : ℝ)*base79 + (127491936327773/19202500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (3147273/1250000000000000000000 : ℝ)*base89 + (3147273/1250000000000000000000 : ℝ)*base91 + (3147273/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15427923990927100486311/1200156250000000000000000000 : ℝ) := by norm_num
    linear_combination (951323053/50000000000000 : ℝ)*(base19) + (1087964333/50000000000000 : ℝ)*(base23) + (72431199/12500000000000 : ℝ)*(lower1) + (11341211/20000000000000 : ℝ)*(upper2) + (263422417/100000000000000 : ℝ)*(upper3) + (351567237/100000000000000 : ℝ)*(upper5) + (977706801457339/50000000000000 : ℝ)*(major0) + (977706801457339/50000000000000 : ℝ)*(major1) + (977706801457339/50000000000000 : ℝ)*(major2) + (628350619/50000000000000 : ℝ)*(sp2) + (1425282732100839/50000000000000 : ℝ)*(sp4) + (712640890388893/25000000000000 : ℝ)*(sp5) + (1425281015785887/50000000000000 : ℝ)*(sp6) + (53013065656501/5000000000000 : ℝ)*(sp7) + (53013065656501/5000000000000 : ℝ)*(f.failure) + (1425282732100839/50000000000000 : ℝ)*(f.sum) + (19952776746963/19202500000000000000000000000 : ℝ)*base66 + (7756399810303037759/1920250000000000000000000000000000 : ℝ)*base68 + (38830778899325462241/1920250000000000000000000000000000 : ℝ)*base69 + (3326929882899462241/1920250000000000000000000000000000 : ℝ)*base71 + (44135286927669/9601250000000000000000000000 : ℝ)*base74 + (13183757261831462241/1920250000000000000000000000000000 : ℝ)*base75 + (2912006052788037759/1920250000000000000000000000000000 : ℝ)*base78 + (5958942938670037759/1920250000000000000000000000000000 : ℝ)*base80 + (102853018728133/4800625000000000000000000000 : ℝ)*base81 + (329621/125000000000000000000 : ℝ)*base90 + (329621/125000000000000000000 : ℝ)*base92 + (329621/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1678_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (46106879/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8677/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9673/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4851/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17321/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1678_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1678_s4_0 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-768340123/5000000000 : ℝ)*x 0 + (2745715823/5000000000 : ℝ)*x 1 + (5133004663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (768340123/5000000000 : ℝ)^5047 ≤ (476990132239/5000000000000 : ℝ)^4023 := by
    have hnat : (768340123 : ℕ)^5047*5000000000000^4023 ≤ 476990132239^4023*5000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      768340123 5000000000 476990132239 5000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2745715823/5000000000 : ℝ)^5047 ≤ (11785990642617/25000000000000 : ℝ)^4023 := by
    have hnat : (2745715823 : ℕ)^5047*25000000000000^4023 ≤ 11785990642617^4023*5000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2745715823 5000000000 11785990642617 25000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5133004663/10000000000 : ℝ)^5047 ≤ (43316234777399/100000000000000 : ℝ)^4023 := by
    have hnat : (5133004663 : ℕ)^5047*100000000000000^4023 ≤ 43316234777399^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5133004663 10000000000 43316234777399 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-768340123/5000000000 : ℝ), (2745715823/5000000000 : ℝ), (5133004663/10000000000 : ℝ)] ![(476990132239/5000000000000 : ℝ), (11785990642617/25000000000000 : ℝ), (43316234777399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-768340123/5000000000 : ℝ)|^5047 ≤ (476990132239/5000000000000 : ℝ)^4023
        have hw : |(-768340123/5000000000 : ℝ)|=(768340123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2745715823/5000000000 : ℝ)|^5047 ≤ (11785990642617/25000000000000 : ℝ)^4023
        have hw : |(2745715823/5000000000 : ℝ)|=(2745715823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5133004663/10000000000 : ℝ)|^5047 ≤ (43316234777399/100000000000000 : ℝ)^4023
        have hw : |(5133004663/10000000000 : ℝ)|=(5133004663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_s4_1 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354182909/10000000000 : ℝ)*x 0 + (-344615271/2000000000 : ℝ)*x 1 + (80203197/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354182909/10000000000 : ℝ)^5047 ≤ (22835248822727/50000000000000 : ℝ)^4023 := by
    have hnat : (5354182909 : ℕ)^5047*50000000000000^4023 ≤ 22835248822727^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354182909 10000000000 22835248822727 50000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (344615271/2000000000 : ℝ)^5047 ≤ (2202653629799/20000000000000 : ℝ)^4023 := by
    have hnat : (344615271 : ℕ)^5047*20000000000000^4023 ≤ 2202653629799^4023*2000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344615271 2000000000 2202653629799 20000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (80203197/156250000 : ℝ)^5047 ≤ (5414529274391/12500000000000 : ℝ)^4023 := by
    have hnat : (80203197 : ℕ)^5047*12500000000000^4023 ≤ 5414529274391^4023*156250000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80203197 156250000 5414529274391 12500000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354182909/10000000000 : ℝ), (-344615271/2000000000 : ℝ), (80203197/156250000 : ℝ)] ![(22835248822727/50000000000000 : ℝ), (2202653629799/20000000000000 : ℝ), (5414529274391/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354182909/10000000000 : ℝ)|^5047 ≤ (22835248822727/50000000000000 : ℝ)^4023
        have hw : |(5354182909/10000000000 : ℝ)|=(5354182909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-344615271/2000000000 : ℝ)|^5047 ≤ (2202653629799/20000000000000 : ℝ)^4023
        have hw : |(-344615271/2000000000 : ℝ)|=(344615271/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(80203197/156250000 : ℝ)|^5047 ≤ (5414529274391/12500000000000 : ℝ)^4023
        have hw : |(80203197/156250000 : ℝ)|=(80203197/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_s4_2 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677091797/5000000000 : ℝ)*x 0 + (2566502097/5000000000 : ℝ)*x 1 + (-1723075987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677091797/5000000000 : ℝ)^5047 ≤ (2854406560979/6250000000000 : ℝ)^4023 := by
    have hnat : (2677091797 : ℕ)^5047*6250000000000^4023 ≤ 2854406560979^4023*5000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677091797 5000000000 2854406560979 6250000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2566502097/5000000000 : ℝ)^5047 ≤ (21658114906109/50000000000000 : ℝ)^4023 := by
    have hnat : (2566502097 : ℕ)^5047*50000000000000^4023 ≤ 21658114906109^4023*5000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2566502097 5000000000 21658114906109 50000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1723075987/10000000000 : ℝ)^5047 ≤ (440530607927/4000000000000 : ℝ)^4023 := by
    have hnat : (1723075987 : ℕ)^5047*4000000000000^4023 ≤ 440530607927^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1723075987 10000000000 440530607927 4000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677091797/5000000000 : ℝ), (2566502097/5000000000 : ℝ), (-1723075987/10000000000 : ℝ)] ![(2854406560979/6250000000000 : ℝ), (21658114906109/50000000000000 : ℝ), (440530607927/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677091797/5000000000 : ℝ)|^5047 ≤ (2854406560979/6250000000000 : ℝ)^4023
        have hw : |(2677091797/5000000000 : ℝ)|=(2677091797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2566502097/5000000000 : ℝ)|^5047 ≤ (21658114906109/50000000000000 : ℝ)^4023
        have hw : |(2566502097/5000000000 : ℝ)|=(2566502097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1723075987/10000000000 : ℝ)|^5047 ≤ (440530607927/4000000000000 : ℝ)^4023
        have hw : |(-1723075987/10000000000 : ℝ)|=(1723075987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_s4_3 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4148043773/10000000000 : ℝ)*x 0 + (1842764559/5000000000 : ℝ)*x 1 + (929835647/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4148043773/10000000000 : ℝ)^5047 ≤ (6631328427193/20000000000000 : ℝ)^4023 := by
    have hnat : (4148043773 : ℕ)^5047*20000000000000^4023 ≤ 6631328427193^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4148043773 10000000000 6631328427193 20000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1842764559/5000000000 : ℝ)^5047 ≤ (28586321356461/100000000000000 : ℝ)^4023 := by
    have hnat : (1842764559 : ℕ)^5047*100000000000000^4023 ≤ 28586321356461^4023*5000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1842764559 5000000000 28586321356461 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (929835647/2000000000 : ℝ)^5047 ≤ (38257036489979/100000000000000 : ℝ)^4023 := by
    have hnat : (929835647 : ℕ)^5047*100000000000000^4023 ≤ 38257036489979^4023*2000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      929835647 2000000000 38257036489979 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4148043773/10000000000 : ℝ), (1842764559/5000000000 : ℝ), (929835647/2000000000 : ℝ)] ![(6631328427193/20000000000000 : ℝ), (28586321356461/100000000000000 : ℝ), (38257036489979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4148043773/10000000000 : ℝ)|^5047 ≤ (6631328427193/20000000000000 : ℝ)^4023
        have hw : |(4148043773/10000000000 : ℝ)|=(4148043773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1842764559/5000000000 : ℝ)|^5047 ≤ (28586321356461/100000000000000 : ℝ)^4023
        have hw : |(1842764559/5000000000 : ℝ)|=(1842764559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(929835647/2000000000 : ℝ)|^5047 ≤ (38257036489979/100000000000000 : ℝ)^4023
        have hw : |(929835647/2000000000 : ℝ)|=(929835647/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_s4_4 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1536849909/10000000000 : ℝ)*x 0 + (5136863573/10000000000 : ℝ)*x 1 + (5487515059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1536849909/10000000000 : ℝ)^5047 ≤ (4770562019493/50000000000000 : ℝ)^4023 := by
    have hnat : (1536849909 : ℕ)^5047*50000000000000^4023 ≤ 4770562019493^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1536849909 10000000000 4770562019493 50000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5136863573/10000000000 : ℝ)^5047 ≤ (21678545984201/50000000000000 : ℝ)^4023 := by
    have hnat : (5136863573 : ℕ)^5047*50000000000000^4023 ≤ 21678545984201^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5136863573 10000000000 21678545984201 50000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5487515059/10000000000 : ℝ)^5047 ≤ (5887722996779/12500000000000 : ℝ)^4023 := by
    have hnat : (5487515059 : ℕ)^5047*12500000000000^4023 ≤ 5887722996779^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5487515059 10000000000 5887722996779 12500000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1536849909/10000000000 : ℝ), (5136863573/10000000000 : ℝ), (5487515059/10000000000 : ℝ)] ![(4770562019493/50000000000000 : ℝ), (21678545984201/50000000000000 : ℝ), (5887722996779/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1536849909/10000000000 : ℝ)|^5047 ≤ (4770562019493/50000000000000 : ℝ)^4023
        have hw : |(-1536849909/10000000000 : ℝ)|=(1536849909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5136863573/10000000000 : ℝ)|^5047 ≤ (21678545984201/50000000000000 : ℝ)^4023
        have hw : |(5136863573/10000000000 : ℝ)|=(5136863573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5487515059/10000000000 : ℝ)|^5047 ≤ (5887722996779/12500000000000 : ℝ)^4023
        have hw : |(5487515059/10000000000 : ℝ)|=(5487515059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_s4_5 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5258504613/10000000000 : ℝ)*x 0 + (-1368565483/10000000000 : ℝ)*x 1 + (5487515101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5258504613/10000000000 : ℝ)^5047 ≤ (44648979722919/100000000000000 : ℝ)^4023 := by
    have hnat : (5258504613 : ℕ)^5047*100000000000000^4023 ≤ 44648979722919^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258504613 10000000000 44648979722919 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1368565483/10000000000 : ℝ)^5047 ≤ (8249235833363/100000000000000 : ℝ)^4023 := by
    have hnat : (1368565483 : ℕ)^5047*100000000000000^4023 ≤ 8249235833363^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368565483 10000000000 8249235833363 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5487515101/10000000000 : ℝ)^5047 ≤ (23550892213249/50000000000000 : ℝ)^4023 := by
    have hnat : (5487515101 : ℕ)^5047*50000000000000^4023 ≤ 23550892213249^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5487515101 10000000000 23550892213249 50000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5258504613/10000000000 : ℝ), (-1368565483/10000000000 : ℝ), (5487515101/10000000000 : ℝ)] ![(44648979722919/100000000000000 : ℝ), (8249235833363/100000000000000 : ℝ), (23550892213249/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5258504613/10000000000 : ℝ)|^5047 ≤ (44648979722919/100000000000000 : ℝ)^4023
        have hw : |(5258504613/10000000000 : ℝ)|=(5258504613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1368565483/10000000000 : ℝ)|^5047 ≤ (8249235833363/100000000000000 : ℝ)^4023
        have hw : |(-1368565483/10000000000 : ℝ)|=(1368565483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5487515101/10000000000 : ℝ)|^5047 ≤ (23550892213249/50000000000000 : ℝ)^4023
        have hw : |(5487515101/10000000000 : ℝ)|=(5487515101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_s4_6 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5258504587/10000000000 : ℝ)*x 0 + (219500607/400000000 : ℝ)*x 1 + (-684282707/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5258504587/10000000000 : ℝ)^5047 ≤ (22324489722983/50000000000000 : ℝ)^4023 := by
    have hnat : (5258504587 : ℕ)^5047*50000000000000^4023 ≤ 22324489722983^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258504587 10000000000 22324489722983 50000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (219500607/400000000 : ℝ)^5047 ≤ (11775446305837/25000000000000 : ℝ)^4023 := by
    have hnat : (219500607 : ℕ)^5047*25000000000000^4023 ≤ 11775446305837^4023*400000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219500607 400000000 11775446305837 25000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (684282707/5000000000 : ℝ)^5047 ≤ (8249235311591/100000000000000 : ℝ)^4023 := by
    have hnat : (684282707 : ℕ)^5047*100000000000000^4023 ≤ 8249235311591^4023*5000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      684282707 5000000000 8249235311591 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5258504587/10000000000 : ℝ), (219500607/400000000 : ℝ), (-684282707/5000000000 : ℝ)] ![(22324489722983/50000000000000 : ℝ), (11775446305837/25000000000000 : ℝ), (8249235311591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5258504587/10000000000 : ℝ)|^5047 ≤ (22324489722983/50000000000000 : ℝ)^4023
        have hw : |(5258504587/10000000000 : ℝ)|=(5258504587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(219500607/400000000 : ℝ)|^5047 ≤ (11775446305837/25000000000000 : ℝ)^4023
        have hw : |(219500607/400000000 : ℝ)|=(219500607/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-684282707/5000000000 : ℝ)|^5047 ≤ (8249235311591/100000000000000 : ℝ)^4023
        have hw : |(-684282707/5000000000 : ℝ)|=(684282707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_s4_7 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (414850023/1000000000 : ℝ)*x 0 + (1159700783/2500000000 : ℝ)*x 1 + (92401469/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (414850023/1000000000 : ℝ)^5047 ≤ (33161219510371/100000000000000 : ℝ)^4023 := by
    have hnat : (414850023 : ℕ)^5047*100000000000000^4023 ≤ 33161219510371^4023*1000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414850023 1000000000 33161219510371 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1159700783/2500000000 : ℝ)^5047 ≤ (19074980830727/50000000000000 : ℝ)^4023 := by
    have hnat : (1159700783 : ℕ)^5047*50000000000000^4023 ≤ 19074980830727^4023*2500000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1159700783 2500000000 19074980830727 50000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (92401469/250000000 : ℝ)^5047 ≤ (28688818809833/100000000000000 : ℝ)^4023 := by
    have hnat : (92401469 : ℕ)^5047*100000000000000^4023 ≤ 28688818809833^4023*250000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92401469 250000000 28688818809833 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(414850023/1000000000 : ℝ), (1159700783/2500000000 : ℝ), (92401469/250000000 : ℝ)] ![(33161219510371/100000000000000 : ℝ), (19074980830727/50000000000000 : ℝ), (28688818809833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(414850023/1000000000 : ℝ)|^5047 ≤ (33161219510371/100000000000000 : ℝ)^4023
        have hw : |(414850023/1000000000 : ℝ)|=(414850023/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1159700783/2500000000 : ℝ)|^5047 ≤ (19074980830727/50000000000000 : ℝ)^4023
        have hw : |(1159700783/2500000000 : ℝ)|=(1159700783/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(92401469/250000000 : ℝ)|^5047 ≤ (28688818809833/100000000000000 : ℝ)^4023
        have hw : |(92401469/250000000 : ℝ)|=(92401469/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1678_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (46106879/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17321/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4851/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1213/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17319/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17321/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4851/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17321/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4851/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17321/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4851/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17321/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4851/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17321/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4851/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17321/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4851/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4851/50000 : ℝ) ^ (5039/1024 : ℝ) ≤ (1033825423517387/100000000000000000000 : ℝ) := by
    have hpowers : (4851/50000 : ℝ)^5039 ≤ (1033825423517387/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4851 : ℕ)^5039*100000000000000000000^1024 ≤ 1033825423517387^1024*50000^5039 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4851 50000 1033825423517387 100000000000000000000 5039 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4851/50000 : ℝ)) (X := (1033825423517387/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5039 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17321/100000 : ℝ) ^ (5039/1024 : ℝ) ≤ (17909970765223227/100000000000000000000 : ℝ) := by
    have hpowers : (17321/100000 : ℝ)^5039 ≤ (17909970765223227/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17321 : ℕ)^5039*100000000000000000000^1024 ≤ 17909970765223227^1024*100000^5039 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17321 100000 17909970765223227 100000000000000000000 5039 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17321/100000 : ℝ)) (X := (17909970765223227/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5039 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001033825423517387/50000000000000000000 : ℝ) ≤ (10000042017404779/10000000000000000 : ℝ) ^ (5039/1024 : ℝ) := by
    have hpowers : (50001033825423517387/50000000000000000000 : ℝ)^1024 ≤ (10000042017404779/10000000000000000 : ℝ)^5039 := by
      have hnat : (50001033825423517387 : ℕ)^1024*10000000000000000^5039 ≤ 10000042017404779^5039*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001033825423517387 50000000000000000000 10000042017404779 10000000000000000 1024 5039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000042017404779/10000000000000000 : ℝ)) (X := (50001033825423517387/50000000000000000000 : ℝ)) (by norm_num) 5039 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50009471898094370307/50000000000000000000 : ℝ) ≤ (200007698743183/200000000000000 : ℝ) ^ (5039/1024 : ℝ) := by
    have hpowers : (50009471898094370307/50000000000000000000 : ℝ)^1024 ≤ (200007698743183/200000000000000 : ℝ)^5039 := by
      have hnat : (50009471898094370307 : ℕ)^1024*200000000000000^5039 ≤ 200007698743183^5039*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009471898094370307 50000000000000000000 200007698743183 200000000000000 1024 5039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200007698743183/200000000000000 : ℝ)) (X := (50009471898094370307/50000000000000000000 : ℝ)) (by norm_num) 5039 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50017909970765223227/50000000000000000000 : ℝ) ≤ (10000727856913521/10000000000000000 : ℝ) ^ (5039/1024 : ℝ) := by
    have hpowers : (50017909970765223227/50000000000000000000 : ℝ)^1024 ≤ (10000727856913521/10000000000000000 : ℝ)^5039 := by
      have hnat : (50017909970765223227 : ℕ)^1024*10000000000000000^5039 ≤ 10000727856913521^5039*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017909970765223227 50000000000000000000 10000727856913521 10000000000000000 1024 5039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000727856913521/10000000000000000 : ℝ)) (X := (50017909970765223227/50000000000000000000 : ℝ)) (by norm_num) 5039 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1033825423517387/100000000000000000000 : ℝ) ≤ ((76183666115693196317/76190000000000000000 : ℝ)+2*(342919754371/761900000000000 : ℝ)*(4851/50000 : ℝ))^(5039/1024 : ℝ) := by
    rw [show (76183666115693196317/76190000000000000000 : ℝ)+2*(342919754371/761900000000000 : ℝ)*(4851/50000 : ℝ)=(10000042017404779/10000000000000000 : ℝ) by norm_num, show 1+2*(1033825423517387/100000000000000000000 : ℝ)=(50001033825423517387/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17909970765223227/100000000000000000000 : ℝ)+(1033825423517387/100000000000000000000 : ℝ) ≤ ((76183666115693196317/76190000000000000000 : ℝ)+(342919754371/761900000000000 : ℝ)*((17321/100000 : ℝ)+(4851/50000 : ℝ)))^(5039/1024 : ℝ) := by
    rw [show (76183666115693196317/76190000000000000000 : ℝ)+(342919754371/761900000000000 : ℝ)*((17321/100000 : ℝ)+(4851/50000 : ℝ))=(200007698743183/200000000000000 : ℝ) by norm_num, show 1+(17909970765223227/100000000000000000000 : ℝ)+(1033825423517387/100000000000000000000 : ℝ)=(50009471898094370307/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17909970765223227/100000000000000000000 : ℝ) ≤ ((76183666115693196317/76190000000000000000 : ℝ)+2*(342919754371/761900000000000 : ℝ)*(17321/100000 : ℝ))^(5039/1024 : ℝ) := by
    rw [show (76183666115693196317/76190000000000000000 : ℝ)+2*(342919754371/761900000000000 : ℝ)*(17321/100000 : ℝ)=(10000727856913521/10000000000000000 : ℝ) by norm_num, show 1+2*(17909970765223227/100000000000000000000 : ℝ)=(50017909970765223227/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (76183666115693196317/76190000000000000000 : ℝ)*(X 1 0+X 2 0)+(342919754371/761900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5039/1024 : ℝ)) (lo := (4851/50000 : ℝ)) (hi := (17321/100000 : ℝ)) (c := (76183666115693196317/76190000000000000000 : ℝ)) (alpha := (342919754371/761900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (76183666115693196317/76190000000000000000 : ℝ)*(X 0 1+X 2 1)+(342919754371/761900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5039/1024 : ℝ)) (lo := (4851/50000 : ℝ)) (hi := (17321/100000 : ℝ)) (c := (76183666115693196317/76190000000000000000 : ℝ)) (alpha := (342919754371/761900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (76183666115693196317/76190000000000000000 : ℝ)*(X 0 2+X 1 2)+(342919754371/761900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5039/1024 : ℝ)) (lo := (4851/50000 : ℝ)) (hi := (17321/100000 : ℝ)) (c := (76183666115693196317/76190000000000000000 : ℝ)) (alpha := (342919754371/761900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-768340123/5000000000 : ℝ)*X 0 0+(2745715823/5000000000 : ℝ)*X 0 1+(5133004663/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5354182909/10000000000 : ℝ)*X 1 0+(-344615271/2000000000 : ℝ)*X 1 1+(80203197/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2677091797/5000000000 : ℝ)*X 2 0+(2566502097/5000000000 : ℝ)*X 2 1+(-1723075987/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4148043773/10000000000 : ℝ)*X 0 0+(1842764559/5000000000 : ℝ)*X 0 1+(929835647/2000000000 : ℝ)*X 0 2+(4148043773/10000000000 : ℝ)*X 1 0+(1842764559/5000000000 : ℝ)*X 1 1+(929835647/2000000000 : ℝ)*X 1 2+(4148043773/10000000000 : ℝ)*X 2 0+(1842764559/5000000000 : ℝ)*X 2 1+(929835647/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1536849909/10000000000 : ℝ)*X 0 0+(5136863573/10000000000 : ℝ)*X 0 1+(5487515059/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5258504613/10000000000 : ℝ)*X 1 0+(-1368565483/10000000000 : ℝ)*X 1 1+(5487515101/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5258504587/10000000000 : ℝ)*X 2 0+(219500607/400000000 : ℝ)*X 2 1+(-684282707/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((414850023/1000000000 : ℝ)*X 0 0+(1159700783/2500000000 : ℝ)*X 0 1+(92401469/250000000 : ℝ)*X 0 2+(414850023/1000000000 : ℝ)*X 1 0+(1159700783/2500000000 : ℝ)*X 1 1+(92401469/250000000 : ℝ)*X 1 2+(414850023/1000000000 : ℝ)*X 2 0+(1159700783/2500000000 : ℝ)*X 2 1+(92401469/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15952135913844384493557/3809500000000000000000000000 : ℝ) := by norm_num
    linear_combination (315111463/100000000000000 : ℝ)*(base19) + (333471283/50000000000000 : ℝ)*(base23) + (10427477/50000000000000 : ℝ)*(lower2) + (52481743/50000000000000 : ℝ)*(upper5) + (3827702228771/200000000000 : ℝ)*(major0) + (3827702228771/200000000000 : ℝ)*(major1) + (3827702228771/200000000000 : ℝ)*(major2) + (2789970936818367/100000000000000 : ℝ)*(sp0) + (174373407184789/6250000000000 : ℝ)*(sp1) + (1394988028402483/50000000000000 : ℝ)*(sp2) + (129715471083767/12500000000000 : ℝ)*(sp3) + (1157385833/20000000000000 : ℝ)*(sp4) + (946839723/50000000000000 : ℝ)*(sp5) + (319354253/20000000000000 : ℝ)*(sp7) + (518862682720701/50000000000000 : ℝ)*(f.failure) + (697494180936883/25000000000000 : ℝ)*(f.sum) + (1225832175909/7619000000000000000000000000 : ℝ)*base66 + (57304008088153593/15238000000000000000000000000000 : ℝ)*base68 + (17660982257728407/15238000000000000000000000000000 : ℝ)*base69 + (12118688882040407/15238000000000000000000000000000 : ℝ)*base71 + (1210548047239/761900000000000000000000000 : ℝ)*base73 + (101067363411187593/15238000000000000000000000000000 : ℝ)*base76 + (48941252034820407/15238000000000000000000000000000 : ℝ)*base77 + (32928979892079593/15238000000000000000000000000000 : ℝ)*base80 + (10468576149429/3809500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1802179/1250000000000000000000 : ℝ)*base89 + (1802179/1250000000000000000000 : ℝ)*base91 + (1802179/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21405446194356257702013034917/1904750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1551574701/100000000000000 : ℝ)*(base19) + (1751442581/100000000000000 : ℝ)*(base23) + (117085527/25000000000000 : ℝ)*(lower1) + (121890639/50000000000000 : ℝ)*(upper3) + (5613533/6250000000000 : ℝ)*(lower4) + (221287729/100000000000000 : ℝ)*(upper5) + (978136973485267/50000000000000 : ℝ)*(major0) + (978136973485267/50000000000000 : ℝ)*(major1) + (978136973485267/50000000000000 : ℝ)*(major2) + (2372392521/100000000000000 : ℝ)*(sp2) + (57036394236033/2000000000000 : ℝ)*(sp4) + (57036363204539/2000000000000 : ℝ)*(sp5) + (712953896991637/25000000000000 : ℝ)*(sp6) + (1060727807541763/100000000000000 : ℝ)*(sp7) + (1060727807541763/100000000000000 : ℝ)*(f.failure) + (57036394236033/2000000000000 : ℝ)*(f.sum) + (96873071299157/19047500000000000000000000000 : ℝ)*base65 + (16132929600066861639/3809500000000000000000000000000000 : ℝ)*base67 + (5867100761741138361/3809500000000000000000000000000000 : ℝ)*base70 + (8765690683536138361/3809500000000000000000000000000000 : ℝ)*base72 + (60843322620961/9523750000000000000000000000 : ℝ)*base73 + (65309122574558861639/3809500000000000000000000000000000 : ℝ)*base75 + (6575745513636138361/3809500000000000000000000000000000 : ℝ)*base78 + (5060475174611138361/3809500000000000000000000000000000 : ℝ)*base80 + (85740183696919/38095000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (4087677/2500000000000000000000 : ℝ)*base89 + (4087677/2500000000000000000000 : ℝ)*base91 + (4087677/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1678_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (46106879/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17321/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4851/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1213/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17319/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1678_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1678_box_0 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-595519129/5000000000 : ℝ)*x 0 + (543483043/1000000000 : ℝ)*x 1 + (1358706973/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (595519129/5000000000 : ℝ)^5047 ≤ (866213938649/12500000000000 : ℝ)^4023 := by
    have hnat : (595519129 : ℕ)^5047*12500000000000^4023 ≤ 866213938649^4023*5000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      595519129 5000000000 866213938649 12500000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (543483043/1000000000 : ℝ)^5047 ≤ (23267578935931/50000000000000 : ℝ)^4023 := by
    have hnat : (543483043 : ℕ)^5047*50000000000000^4023 ≤ 23267578935931^4023*1000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543483043 1000000000 23267578935931 50000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358706973/2500000000 : ℝ)^5047 ≤ (46535130609087/100000000000000 : ℝ)^4023 := by
    have hnat : (1358706973 : ℕ)^5047*100000000000000^4023 ≤ 46535130609087^4023*2500000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358706973 2500000000 46535130609087 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-595519129/5000000000 : ℝ), (543483043/1000000000 : ℝ), (1358706973/2500000000 : ℝ)] ![(866213938649/12500000000000 : ℝ), (23267578935931/50000000000000 : ℝ), (46535130609087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-595519129/5000000000 : ℝ)|^5047 ≤ (866213938649/12500000000000 : ℝ)^4023
        have hw : |(-595519129/5000000000 : ℝ)|=(595519129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(543483043/1000000000 : ℝ)|^5047 ≤ (23267578935931/50000000000000 : ℝ)^4023
        have hw : |(543483043/1000000000 : ℝ)|=(543483043/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358706973/2500000000 : ℝ)|^5047 ≤ (46535130609087/100000000000000 : ℝ)^4023
        have hw : |(1358706973/2500000000 : ℝ)|=(1358706973/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_box_1 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (836171/1600000 : ℝ)*x 0 + (-743927989/5000000000 : ℝ)*x 1 + (5434830529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (836171/1600000 : ℝ)^5047 ≤ (8860748689979/20000000000000 : ℝ)^4023 := by
    have hnat : (836171 : ℕ)^5047*20000000000000^4023 ≤ 8860748689979^4023*1600000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      836171 1600000 8860748689979 20000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (743927989/5000000000 : ℝ)^5047 ≤ (229027440061/2500000000000 : ℝ)^4023 := by
    have hnat : (743927989 : ℕ)^5047*2500000000000^4023 ≤ 229027440061^4023*5000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      743927989 5000000000 229027440061 2500000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5434830529/10000000000 : ℝ)^5047 ≤ (46535158935303/100000000000000 : ℝ)^4023 := by
    have hnat : (5434830529 : ℕ)^5047*100000000000000^4023 ≤ 46535158935303^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434830529 10000000000 46535158935303 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(836171/1600000 : ℝ), (-743927989/5000000000 : ℝ), (5434830529/10000000000 : ℝ)] ![(8860748689979/20000000000000 : ℝ), (229027440061/2500000000000 : ℝ), (46535158935303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(836171/1600000 : ℝ)|^5047 ≤ (8860748689979/20000000000000 : ℝ)^4023
        have hw : |(836171/1600000 : ℝ)|=(836171/1600000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-743927989/5000000000 : ℝ)|^5047 ≤ (229027440061/2500000000000 : ℝ)^4023
        have hw : |(-743927989/5000000000 : ℝ)|=(743927989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5434830529/10000000000 : ℝ)|^5047 ≤ (46535158935303/100000000000000 : ℝ)^4023
        have hw : |(5434830529/10000000000 : ℝ)|=(5434830529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_box_2 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (130651737/250000000 : ℝ)*x 0 + (543482959/1000000000 : ℝ)*x 1 + (-1487856279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (130651737/250000000 : ℝ)^5047 ≤ (11075937803411/25000000000000 : ℝ)^4023 := by
    have hnat : (130651737 : ℕ)^5047*25000000000000^4023 ≤ 11075937803411^4023*250000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130651737 250000000 11075937803411 25000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (543482959/1000000000 : ℝ)^5047 ≤ (46535148848721/100000000000000 : ℝ)^4023 := by
    have hnat : (543482959 : ℕ)^5047*100000000000000^4023 ≤ 46535148848721^4023*1000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543482959 1000000000 46535148848721 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1487856279/10000000000 : ℝ)^5047 ≤ (9161099927511/100000000000000 : ℝ)^4023 := by
    have hnat : (1487856279 : ℕ)^5047*100000000000000^4023 ≤ 9161099927511^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1487856279 10000000000 9161099927511 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(130651737/250000000 : ℝ), (543482959/1000000000 : ℝ), (-1487856279/10000000000 : ℝ)] ![(11075937803411/25000000000000 : ℝ), (46535148848721/100000000000000 : ℝ), (9161099927511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(130651737/250000000 : ℝ)|^5047 ≤ (11075937803411/25000000000000 : ℝ)^4023
        have hw : |(130651737/250000000 : ℝ)|=(130651737/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(543482959/1000000000 : ℝ)|^5047 ≤ (46535148848721/100000000000000 : ℝ)^4023
        have hw : |(543482959/1000000000 : ℝ)|=(543482959/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1487856279/10000000000 : ℝ)|^5047 ≤ (9161099927511/100000000000000 : ℝ)^4023
        have hw : |(-1487856279/10000000000 : ℝ)|=(1487856279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_box_3 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2267075927/5000000000 : ℝ)*x 0 + (397829079/1000000000 : ℝ)*x 1 + (497286207/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2267075927/5000000000 : ℝ)^5047 ≤ (579271051643/1562500000000 : ℝ)^4023 := by
    have hnat : (2267075927 : ℕ)^5047*1562500000000^4023 ≤ 579271051643^4023*5000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2267075927 5000000000 579271051643 1562500000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (397829079/1000000000 : ℝ)^5047 ≤ (31463331967127/100000000000000 : ℝ)^4023 := by
    have hnat : (397829079 : ℕ)^5047*100000000000000^4023 ≤ 31463331967127^4023*1000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397829079 1000000000 31463331967127 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (497286207/1250000000 : ℝ)^5047 ≤ (1573166035789/5000000000000 : ℝ)^4023 := by
    have hnat : (497286207 : ℕ)^5047*5000000000000^4023 ≤ 1573166035789^4023*1250000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      497286207 1250000000 1573166035789 5000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2267075927/5000000000 : ℝ), (397829079/1000000000 : ℝ), (497286207/1250000000 : ℝ)] ![(579271051643/1562500000000 : ℝ), (31463331967127/100000000000000 : ℝ), (1573166035789/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2267075927/5000000000 : ℝ)|^5047 ≤ (579271051643/1562500000000 : ℝ)^4023
        have hw : |(2267075927/5000000000 : ℝ)|=(2267075927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(397829079/1000000000 : ℝ)|^5047 ≤ (31463331967127/100000000000000 : ℝ)^4023
        have hw : |(397829079/1000000000 : ℝ)|=(397829079/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(497286207/1250000000 : ℝ)|^5047 ≤ (1573166035789/5000000000000 : ℝ)^4023
        have hw : |(497286207/1250000000 : ℝ)|=(497286207/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_box_4 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1903473379/10000000000 : ℝ)*x 0 + (5174945263/10000000000 : ℝ)*x 1 + (1293736277/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1903473379/10000000000 : ℝ)^5047 ≤ (12478581910443/100000000000000 : ℝ)^4023 := by
    have hnat : (1903473379 : ℕ)^5047*100000000000000^4023 ≤ 12478581910443^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1903473379 10000000000 12478581910443 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5174945263/10000000000 : ℝ)^5047 ≤ (1367522183081/3125000000000 : ℝ)^4023 := by
    have hnat : (5174945263 : ℕ)^5047*3125000000000^4023 ≤ 1367522183081^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174945263 10000000000 1367522183081 3125000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1293736277/2500000000 : ℝ)^5047 ≤ (10940177053561/25000000000000 : ℝ)^4023 := by
    have hnat : (1293736277 : ℕ)^5047*25000000000000^4023 ≤ 10940177053561^4023*2500000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293736277 2500000000 10940177053561 25000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1903473379/10000000000 : ℝ), (5174945263/10000000000 : ℝ), (1293736277/2500000000 : ℝ)] ![(12478581910443/100000000000000 : ℝ), (1367522183081/3125000000000 : ℝ), (10940177053561/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1903473379/10000000000 : ℝ)|^5047 ≤ (12478581910443/100000000000000 : ℝ)^4023
        have hw : |(-1903473379/10000000000 : ℝ)|=(1903473379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5174945263/10000000000 : ℝ)|^5047 ≤ (1367522183081/3125000000000 : ℝ)^4023
        have hw : |(5174945263/10000000000 : ℝ)|=(5174945263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1293736277/2500000000 : ℝ)|^5047 ≤ (10940177053561/25000000000000 : ℝ)^4023
        have hw : |(1293736277/2500000000 : ℝ)|=(1293736277/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_box_5 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5403723963/10000000000 : ℝ)*x 0 + (-1600319991/10000000000 : ℝ)*x 1 + (1293736293/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5403723963/10000000000 : ℝ)^5047 ≤ (46201261088153/100000000000000 : ℝ)^4023 := by
    have hnat : (5403723963 : ℕ)^5047*100000000000000^4023 ≤ 46201261088153^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403723963 10000000000 46201261088153 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1600319991/10000000000 : ℝ)^5047 ≤ (10038030004141/100000000000000 : ℝ)^4023 := by
    have hnat : (1600319991 : ℕ)^5047*100000000000000^4023 ≤ 10038030004141^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1600319991 10000000000 10038030004141 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1293736293/2500000000 : ℝ)^5047 ≤ (43760708893201/100000000000000 : ℝ)^4023 := by
    have hnat : (1293736293 : ℕ)^5047*100000000000000^4023 ≤ 43760708893201^4023*2500000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293736293 2500000000 43760708893201 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5403723963/10000000000 : ℝ), (-1600319991/10000000000 : ℝ), (1293736293/2500000000 : ℝ)] ![(46201261088153/100000000000000 : ℝ), (10038030004141/100000000000000 : ℝ), (43760708893201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5403723963/10000000000 : ℝ)|^5047 ≤ (46201261088153/100000000000000 : ℝ)^4023
        have hw : |(5403723963/10000000000 : ℝ)|=(5403723963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1600319991/10000000000 : ℝ)|^5047 ≤ (10038030004141/100000000000000 : ℝ)^4023
        have hw : |(-1600319991/10000000000 : ℝ)|=(1600319991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1293736293/2500000000 : ℝ)|^5047 ≤ (43760708893201/100000000000000 : ℝ)^4023
        have hw : |(1293736293/2500000000 : ℝ)|=(1293736293/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_box_6 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1350931001/2500000000 : ℝ)*x 0 + (2587472547/5000000000 : ℝ)*x 1 + (-1600320041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1350931001/2500000000 : ℝ)^5047 ≤ (1848050461117/4000000000000 : ℝ)^4023 := by
    have hnat : (1350931001 : ℕ)^5047*4000000000000^4023 ≤ 1848050461117^4023*2500000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350931001 2500000000 1848050461117 4000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2587472547/5000000000 : ℝ)^5047 ≤ (43760708065723/100000000000000 : ℝ)^4023 := by
    have hnat : (2587472547 : ℕ)^5047*100000000000000^4023 ≤ 43760708065723^4023*5000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587472547 5000000000 43760708065723 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1600320041/10000000000 : ℝ)^5047 ≤ (2509507599399/25000000000000 : ℝ)^4023 := by
    have hnat : (1600320041 : ℕ)^5047*25000000000000^4023 ≤ 2509507599399^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1600320041 10000000000 2509507599399 25000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1350931001/2500000000 : ℝ), (2587472547/5000000000 : ℝ), (-1600320041/10000000000 : ℝ)] ![(1848050461117/4000000000000 : ℝ), (43760708065723/100000000000000 : ℝ), (2509507599399/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1350931001/2500000000 : ℝ)|^5047 ≤ (1848050461117/4000000000000 : ℝ)^4023
        have hw : |(1350931001/2500000000 : ℝ)|=(1350931001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2587472547/5000000000 : ℝ)|^5047 ≤ (43760708065723/100000000000000 : ℝ)^4023
        have hw : |(2587472547/5000000000 : ℝ)|=(2587472547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1600320041/10000000000 : ℝ)|^5047 ≤ (2509507599399/25000000000000 : ℝ)^4023
        have hw : |(-1600320041/10000000000 : ℝ)|=(1600320041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_box_7 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (29281569/78125000 : ℝ)*x 0 + (136576911/312500000 : ℝ)*x 1 + (4370461111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (29281569/78125000 : ℝ)^5047 ≤ (5839181663197/20000000000000 : ℝ)^4023 := by
    have hnat : (29281569 : ℕ)^5047*20000000000000^4023 ≤ 5839181663197^4023*78125000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29281569 78125000 5839181663197 20000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (136576911/312500000 : ℝ)^5047 ≤ (35402046043253/100000000000000 : ℝ)^4023 := by
    have hnat : (136576911 : ℕ)^5047*100000000000000^4023 ≤ 35402046043253^4023*312500000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136576911 312500000 35402046043253 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4370461111/10000000000 : ℝ)^5047 ≤ (17701022813303/50000000000000 : ℝ)^4023 := by
    have hnat : (4370461111 : ℕ)^5047*50000000000000^4023 ≤ 17701022813303^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4370461111 10000000000 17701022813303 50000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(29281569/78125000 : ℝ), (136576911/312500000 : ℝ), (4370461111/10000000000 : ℝ)] ![(5839181663197/20000000000000 : ℝ), (35402046043253/100000000000000 : ℝ), (17701022813303/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(29281569/78125000 : ℝ)|^5047 ≤ (5839181663197/20000000000000 : ℝ)^4023
        have hw : |(29281569/78125000 : ℝ)|=(29281569/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(136576911/312500000 : ℝ)|^5047 ≤ (35402046043253/100000000000000 : ℝ)^4023
        have hw : |(136576911/312500000 : ℝ)|=(136576911/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4370461111/10000000000 : ℝ)|^5047 ≤ (17701022813303/50000000000000 : ℝ)^4023
        have hw : |(4370461111/10000000000 : ℝ)|=(4370461111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_box_8 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1750875277/10000000000 : ℝ)*x 0 + (1246228687/2500000000 : ℝ)*x 1 + (547890859/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1750875277/10000000000 : ℝ)^5047 ≤ (11236630606489/100000000000000 : ℝ)^4023 := by
    have hnat : (1750875277 : ℕ)^5047*100000000000000^4023 ≤ 11236630606489^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1750875277 10000000000 11236630606489 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1246228687/2500000000 : ℝ)^5047 ≤ (8350848690609/20000000000000 : ℝ)^4023 := by
    have hnat : (1246228687 : ℕ)^5047*20000000000000^4023 ≤ 8350848690609^4023*2500000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1246228687 2500000000 8350848690609 20000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (547890859/1000000000 : ℝ)^5047 ≤ (47009125918551/100000000000000 : ℝ)^4023 := by
    have hnat : (547890859 : ℕ)^5047*100000000000000^4023 ≤ 47009125918551^4023*1000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547890859 1000000000 47009125918551 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1750875277/10000000000 : ℝ), (1246228687/2500000000 : ℝ), (547890859/1000000000 : ℝ)] ![(11236630606489/100000000000000 : ℝ), (8350848690609/20000000000000 : ℝ), (47009125918551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1750875277/10000000000 : ℝ)|^5047 ≤ (11236630606489/100000000000000 : ℝ)^4023
        have hw : |(-1750875277/10000000000 : ℝ)|=(1750875277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1246228687/2500000000 : ℝ)|^5047 ≤ (8350848690609/20000000000000 : ℝ)^4023
        have hw : |(1246228687/2500000000 : ℝ)|=(1246228687/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(547890859/1000000000 : ℝ)|^5047 ≤ (47009125918551/100000000000000 : ℝ)^4023
        have hw : |(547890859/1000000000 : ℝ)|=(547890859/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_box_9 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1298985873/2500000000 : ℝ)*x 0 + (-293582037/2000000000 : ℝ)*x 1 + (684863519/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1298985873/2500000000 : ℝ)^5047 ≤ (5497948567469/12500000000000 : ℝ)^4023 := by
    have hnat : (1298985873 : ℕ)^5047*12500000000000^4023 ≤ 5497948567469^4023*2500000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298985873 2500000000 5497948567469 12500000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (293582037/2000000000 : ℝ)^5047 ≤ (4503645121557/50000000000000 : ℝ)^4023 := by
    have hnat : (293582037 : ℕ)^5047*50000000000000^4023 ≤ 4503645121557^4023*2000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      293582037 2000000000 4503645121557 50000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (684863519/1250000000 : ℝ)^5047 ≤ (5876140150493/12500000000000 : ℝ)^4023 := by
    have hnat : (684863519 : ℕ)^5047*12500000000000^4023 ≤ 5876140150493^4023*1250000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      684863519 1250000000 5876140150493 12500000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1298985873/2500000000 : ℝ), (-293582037/2000000000 : ℝ), (684863519/1250000000 : ℝ)] ![(5497948567469/12500000000000 : ℝ), (4503645121557/50000000000000 : ℝ), (5876140150493/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1298985873/2500000000 : ℝ)|^5047 ≤ (5497948567469/12500000000000 : ℝ)^4023
        have hw : |(1298985873/2500000000 : ℝ)|=(1298985873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-293582037/2000000000 : ℝ)|^5047 ≤ (4503645121557/50000000000000 : ℝ)^4023
        have hw : |(-293582037/2000000000 : ℝ)|=(293582037/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(684863519/1250000000 : ℝ)|^5047 ≤ (5876140150493/12500000000000 : ℝ)^4023
        have hw : |(684863519/1250000000 : ℝ)|=(684863519/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_box_10 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (649492951/1250000000 : ℝ)*x 0 + (2739454069/5000000000 : ℝ)*x 1 + (-366977511/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (649492951/1250000000 : ℝ)^5047 ≤ (4398358977163/10000000000000 : ℝ)^4023 := by
    have hnat : (649492951 : ℕ)^5047*10000000000000^4023 ≤ 4398358977163^4023*1250000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649492951 1250000000 4398358977163 10000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2739454069/5000000000 : ℝ)^5047 ≤ (47009121053249/100000000000000 : ℝ)^4023 := by
    have hnat : (2739454069 : ℕ)^5047*100000000000000^4023 ≤ 47009121053249^4023*5000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2739454069 5000000000 47009121053249 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (366977511/2500000000 : ℝ)^5047 ≤ (140738893089/1562500000000 : ℝ)^4023 := by
    have hnat : (366977511 : ℕ)^5047*1562500000000^4023 ≤ 140738893089^4023*2500000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      366977511 2500000000 140738893089 1562500000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(649492951/1250000000 : ℝ), (2739454069/5000000000 : ℝ), (-366977511/2500000000 : ℝ)] ![(4398358977163/10000000000000 : ℝ), (47009121053249/100000000000000 : ℝ), (140738893089/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(649492951/1250000000 : ℝ)|^5047 ≤ (4398358977163/10000000000000 : ℝ)^4023
        have hw : |(649492951/1250000000 : ℝ)|=(649492951/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2739454069/5000000000 : ℝ)|^5047 ≤ (47009121053249/100000000000000 : ℝ)^4023
        have hw : |(2739454069/5000000000 : ℝ)|=(2739454069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-366977511/2500000000 : ℝ)|^5047 ≤ (140738893089/1562500000000 : ℝ)^4023
        have hw : |(-366977511/2500000000 : ℝ)|=(366977511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_box_11 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4662429031/10000000000 : ℝ)*x 0 + (1955800241/5000000000 : ℝ)*x 1 + (3911600651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4662429031/10000000000 : ℝ)^5047 ≤ (3839387796971/10000000000000 : ℝ)^4023 := by
    have hnat : (4662429031 : ℕ)^5047*10000000000000^4023 ≤ 3839387796971^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4662429031 10000000000 3839387796971 10000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1955800241/5000000000 : ℝ)^5047 ≤ (30803060175037/100000000000000 : ℝ)^4023 := by
    have hnat : (1955800241 : ℕ)^5047*100000000000000^4023 ≤ 30803060175037^4023*5000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1955800241 5000000000 30803060175037 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3911600651/10000000000 : ℝ)^5047 ≤ (246424494757/800000000000 : ℝ)^4023 := by
    have hnat : (3911600651 : ℕ)^5047*800000000000^4023 ≤ 246424494757^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3911600651 10000000000 246424494757 800000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4662429031/10000000000 : ℝ), (1955800241/5000000000 : ℝ), (3911600651/10000000000 : ℝ)] ![(3839387796971/10000000000000 : ℝ), (30803060175037/100000000000000 : ℝ), (246424494757/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4662429031/10000000000 : ℝ)|^5047 ≤ (3839387796971/10000000000000 : ℝ)^4023
        have hw : |(4662429031/10000000000 : ℝ)|=(4662429031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1955800241/5000000000 : ℝ)|^5047 ≤ (30803060175037/100000000000000 : ℝ)^4023
        have hw : |(1955800241/5000000000 : ℝ)|=(1955800241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3911600651/10000000000 : ℝ)|^5047 ≤ (246424494757/800000000000 : ℝ)^4023
        have hw : |(3911600651/10000000000 : ℝ)|=(3911600651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_box_12 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1307889/9765625 : ℝ)*x 0 + (350945559/625000000 : ℝ)*x 1 + (5149564287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1307889/9765625 : ℝ)^5047 ≤ (8028375519857/100000000000000 : ℝ)^4023 := by
    have hnat : (1307889 : ℕ)^5047*100000000000000^4023 ≤ 8028375519857^4023*9765625^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307889 9765625 8028375519857 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (350945559/625000000 : ℝ)^5047 ≤ (24240002654671/50000000000000 : ℝ)^4023 := by
    have hnat : (350945559 : ℕ)^5047*50000000000000^4023 ≤ 24240002654671^4023*625000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      350945559 625000000 24240002654671 50000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5149564287/10000000000 : ℝ)^5047 ≤ (43491619159737/100000000000000 : ℝ)^4023 := by
    have hnat : (5149564287 : ℕ)^5047*100000000000000^4023 ≤ 43491619159737^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5149564287 10000000000 43491619159737 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1307889/9765625 : ℝ), (350945559/625000000 : ℝ), (5149564287/10000000000 : ℝ)] ![(8028375519857/100000000000000 : ℝ), (24240002654671/50000000000000 : ℝ), (43491619159737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1307889/9765625 : ℝ)|^5047 ≤ (8028375519857/100000000000000 : ℝ)^4023
        have hw : |(-1307889/9765625 : ℝ)|=(1307889/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(350945559/625000000 : ℝ)|^5047 ≤ (24240002654671/50000000000000 : ℝ)^4023
        have hw : |(350945559/625000000 : ℝ)|=(350945559/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5149564287/10000000000 : ℝ)|^5047 ≤ (43491619159737/100000000000000 : ℝ)^4023
        have hw : |(5149564287/10000000000 : ℝ)|=(5149564287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_box_13 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5421099677/10000000000 : ℝ)*x 0 + (-1610813267/10000000000 : ℝ)*x 1 + (5149564057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5421099677/10000000000 : ℝ)^5047 ≤ (9277542369363/20000000000000 : ℝ)^4023 := by
    have hnat : (5421099677 : ℕ)^5047*20000000000000^4023 ≤ 9277542369363^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421099677 10000000000 9277542369363 20000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1610813267/10000000000 : ℝ)^5047 ≤ (2530167852889/25000000000000 : ℝ)^4023 := by
    have hnat : (1610813267 : ℕ)^5047*25000000000000^4023 ≤ 2530167852889^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1610813267 10000000000 2530167852889 25000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5149564057/10000000000 : ℝ)^5047 ≤ (4349161672279/10000000000000 : ℝ)^4023 := by
    have hnat : (5149564057 : ℕ)^5047*10000000000000^4023 ≤ 4349161672279^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5149564057 10000000000 4349161672279 10000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5421099677/10000000000 : ℝ), (-1610813267/10000000000 : ℝ), (5149564057/10000000000 : ℝ)] ![(9277542369363/20000000000000 : ℝ), (2530167852889/25000000000000 : ℝ), (4349161672279/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5421099677/10000000000 : ℝ)|^5047 ≤ (9277542369363/20000000000000 : ℝ)^4023
        have hw : |(5421099677/10000000000 : ℝ)|=(5421099677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1610813267/10000000000 : ℝ)|^5047 ≤ (2530167852889/25000000000000 : ℝ)^4023
        have hw : |(-1610813267/10000000000 : ℝ)|=(1610813267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5149564057/10000000000 : ℝ)|^5047 ≤ (4349161672279/10000000000000 : ℝ)^4023
        have hw : |(5149564057/10000000000 : ℝ)|=(5149564057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_box_14 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1355274937/2500000000 : ℝ)*x 0 + (5149564079/10000000000 : ℝ)*x 1 + (-1610813141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1355274937/2500000000 : ℝ)^5047 ≤ (9277542521799/20000000000000 : ℝ)^4023 := by
    have hnat : (1355274937 : ℕ)^5047*20000000000000^4023 ≤ 9277542521799^4023*2500000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355274937 2500000000 9277542521799 20000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5149564079/10000000000 : ℝ)^5047 ≤ (43491616955889/100000000000000 : ℝ)^4023 := by
    have hnat : (5149564079 : ℕ)^5047*100000000000000^4023 ≤ 43491616955889^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5149564079 10000000000 43491616955889 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1610813141/10000000000 : ℝ)^5047 ≤ (10120670418399/100000000000000 : ℝ)^4023 := by
    have hnat : (1610813141 : ℕ)^5047*100000000000000^4023 ≤ 10120670418399^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1610813141 10000000000 10120670418399 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1355274937/2500000000 : ℝ), (5149564079/10000000000 : ℝ), (-1610813141/10000000000 : ℝ)] ![(9277542521799/20000000000000 : ℝ), (43491616955889/100000000000000 : ℝ), (10120670418399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1355274937/2500000000 : ℝ)|^5047 ≤ (9277542521799/20000000000000 : ℝ)^4023
        have hw : |(1355274937/2500000000 : ℝ)|=(1355274937/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5149564079/10000000000 : ℝ)|^5047 ≤ (43491616955889/100000000000000 : ℝ)^4023
        have hw : |(5149564079/10000000000 : ℝ)|=(5149564079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1610813141/10000000000 : ℝ)|^5047 ≤ (10120670418399/100000000000000 : ℝ)^4023
        have hw : |(-1610813141/10000000000 : ℝ)|=(1610813141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_box_15 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1834144631/5000000000 : ℝ)*x 0 + (4408660917/10000000000 : ℝ)*x 1 + (2204330383/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1834144631/5000000000 : ℝ)^5047 ≤ (5683733279281/20000000000000 : ℝ)^4023 := by
    have hnat : (1834144631 : ℕ)^5047*20000000000000^4023 ≤ 5683733279281^4023*5000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1834144631 5000000000 5683733279281 20000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4408660917/10000000000 : ℝ)^5047 ≤ (2236916722911/6250000000000 : ℝ)^4023 := by
    have hnat : (4408660917 : ℕ)^5047*6250000000000^4023 ≤ 2236916722911^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4408660917 10000000000 2236916722911 6250000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2204330383/5000000000 : ℝ)^5047 ≤ (35790666028693/100000000000000 : ℝ)^4023 := by
    have hnat : (2204330383 : ℕ)^5047*100000000000000^4023 ≤ 35790666028693^4023*5000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2204330383 5000000000 35790666028693 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1834144631/5000000000 : ℝ), (4408660917/10000000000 : ℝ), (2204330383/5000000000 : ℝ)] ![(5683733279281/20000000000000 : ℝ), (2236916722911/6250000000000 : ℝ), (35790666028693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1834144631/5000000000 : ℝ)|^5047 ≤ (5683733279281/20000000000000 : ℝ)^4023
        have hw : |(1834144631/5000000000 : ℝ)|=(1834144631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4408660917/10000000000 : ℝ)|^5047 ≤ (2236916722911/6250000000000 : ℝ)^4023
        have hw : |(4408660917/10000000000 : ℝ)|=(4408660917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2204330383/5000000000 : ℝ)|^5047 ≤ (35790666028693/100000000000000 : ℝ)^4023
        have hw : |(2204330383/5000000000 : ℝ)|=(2204330383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1678_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (46106879/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17319/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1213/12500 : ℝ)*pair X i i ≤ pair X i h) :
    -(33241/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(57643/100000 : ℝ) ∧ (80371/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (89951/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17319/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1213/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17319/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1213/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17319/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1213/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17319/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1213/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17319/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1213/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17319/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1213/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1213/12500 : ℝ) ^ (5039/1024 : ℝ) ≤ (1034874569320303/100000000000000000000 : ℝ) := by
    have hpowers : (1213/12500 : ℝ)^5039 ≤ (1034874569320303/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1213 : ℕ)^5039*100000000000000000000^1024 ≤ 1034874569320303^1024*12500^5039 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1213 12500 1034874569320303 100000000000000000000 5039 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1213/12500 : ℝ)) (X := (1034874569320303/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5039 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17319/100000 : ℝ) ^ (5039/1024 : ℝ) ≤ (223747457729393/1250000000000000000 : ℝ) := by
    have hpowers : (17319/100000 : ℝ)^5039 ≤ (223747457729393/1250000000000000000 : ℝ)^1024 := by
      have hnat : (17319 : ℕ)^5039*1250000000000000000^1024 ≤ 223747457729393^1024*100000^5039 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17319 100000 223747457729393 1250000000000000000 5039 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17319/100000 : ℝ)) (X := (223747457729393/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 5039 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001034874569320303/50000000000000000000 : ℝ) ≤ (10000042060044493/10000000000000000 : ℝ) ^ (5039/1024 : ℝ) := by
    have hpowers : (50001034874569320303/50000000000000000000 : ℝ)^1024 ≤ (10000042060044493/10000000000000000 : ℝ)^5039 := by
      have hnat : (50001034874569320303 : ℕ)^1024*10000000000000000^5039 ≤ 10000042060044493^5039*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001034874569320303 50000000000000000000 10000042060044493 10000000000000000 1024 5039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000042060044493/10000000000000000 : ℝ)) (X := (50001034874569320303/50000000000000000000 : ℝ)) (by norm_num) 5039 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100018934671187671743/100000000000000000000 : ℝ) ≤ (625024046984593/625000000000000 : ℝ) ^ (5039/1024 : ℝ) := by
    have hpowers : (100018934671187671743/100000000000000000000 : ℝ)^1024 ≤ (625024046984593/625000000000000 : ℝ)^5039 := by
      have hnat : (100018934671187671743 : ℕ)^1024*625000000000000^5039 ≤ 625024046984593^5039*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100018934671187671743 100000000000000000000 625024046984593 625000000000000 1024 5039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625024046984593/625000000000000 : ℝ)) (X := (100018934671187671743/100000000000000000000 : ℝ)) (by norm_num) 5039 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (625223747457729393/625000000000000000 : ℝ) ≤ (10000727443462483/10000000000000000 : ℝ) ^ (5039/1024 : ℝ) := by
    have hpowers : (625223747457729393/625000000000000000 : ℝ)^1024 ≤ (10000727443462483/10000000000000000 : ℝ)^5039 := by
      have hnat : (625223747457729393 : ℕ)^1024*10000000000000000^5039 ≤ 10000727443462483^5039*625000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        625223747457729393 625000000000000000 10000727443462483 10000000000000000 1024 5039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000727443462483/10000000000000000 : ℝ)) (X := (625223747457729393/625000000000000000 : ℝ)) (by norm_num) 5039 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1034874569320303/100000000000000000000 : ℝ) ≤ ((15228733865310127847/15230000000000000000 : ℝ)+2*(68538341799/152300000000000 : ℝ)*(1213/12500 : ℝ))^(5039/1024 : ℝ) := by
    rw [show (15228733865310127847/15230000000000000000 : ℝ)+2*(68538341799/152300000000000 : ℝ)*(1213/12500 : ℝ)=(10000042060044493/10000000000000000 : ℝ) by norm_num, show 1+2*(1034874569320303/100000000000000000000 : ℝ)=(50001034874569320303/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(223747457729393/1250000000000000000 : ℝ)+(1034874569320303/100000000000000000000 : ℝ) ≤ ((15228733865310127847/15230000000000000000 : ℝ)+(68538341799/152300000000000 : ℝ)*((17319/100000 : ℝ)+(1213/12500 : ℝ)))^(5039/1024 : ℝ) := by
    rw [show (15228733865310127847/15230000000000000000 : ℝ)+(68538341799/152300000000000 : ℝ)*((17319/100000 : ℝ)+(1213/12500 : ℝ))=(625024046984593/625000000000000 : ℝ) by norm_num, show 1+(223747457729393/1250000000000000000 : ℝ)+(1034874569320303/100000000000000000000 : ℝ)=(100018934671187671743/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(223747457729393/1250000000000000000 : ℝ) ≤ ((15228733865310127847/15230000000000000000 : ℝ)+2*(68538341799/152300000000000 : ℝ)*(17319/100000 : ℝ))^(5039/1024 : ℝ) := by
    rw [show (15228733865310127847/15230000000000000000 : ℝ)+2*(68538341799/152300000000000 : ℝ)*(17319/100000 : ℝ)=(10000727443462483/10000000000000000 : ℝ) by norm_num, show 1+2*(223747457729393/1250000000000000000 : ℝ)=(625223747457729393/625000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15228733865310127847/15230000000000000000 : ℝ)*(X 1 0+X 2 0)+(68538341799/152300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5039/1024 : ℝ)) (lo := (1213/12500 : ℝ)) (hi := (17319/100000 : ℝ)) (c := (15228733865310127847/15230000000000000000 : ℝ)) (alpha := (68538341799/152300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15228733865310127847/15230000000000000000 : ℝ)*(X 0 1+X 2 1)+(68538341799/152300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5039/1024 : ℝ)) (lo := (1213/12500 : ℝ)) (hi := (17319/100000 : ℝ)) (c := (15228733865310127847/15230000000000000000 : ℝ)) (alpha := (68538341799/152300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15228733865310127847/15230000000000000000 : ℝ)*(X 0 2+X 1 2)+(68538341799/152300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5039/1024 : ℝ)) (lo := (1213/12500 : ℝ)) (hi := (17319/100000 : ℝ)) (c := (15228733865310127847/15230000000000000000 : ℝ)) (alpha := (68538341799/152300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-595519129/5000000000 : ℝ)*X 0 0+(543483043/1000000000 : ℝ)*X 0 1+(1358706973/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((836171/1600000 : ℝ)*X 1 0+(-743927989/5000000000 : ℝ)*X 1 1+(5434830529/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((130651737/250000000 : ℝ)*X 2 0+(543482959/1000000000 : ℝ)*X 2 1+(-1487856279/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2267075927/5000000000 : ℝ)*X 0 0+(397829079/1000000000 : ℝ)*X 0 1+(497286207/1250000000 : ℝ)*X 0 2+(2267075927/5000000000 : ℝ)*X 1 0+(397829079/1000000000 : ℝ)*X 1 1+(497286207/1250000000 : ℝ)*X 1 2+(2267075927/5000000000 : ℝ)*X 2 0+(397829079/1000000000 : ℝ)*X 2 1+(497286207/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1903473379/10000000000 : ℝ)*X 0 0+(5174945263/10000000000 : ℝ)*X 0 1+(1293736277/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5403723963/10000000000 : ℝ)*X 1 0+(-1600319991/10000000000 : ℝ)*X 1 1+(1293736293/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1350931001/2500000000 : ℝ)*X 2 0+(2587472547/5000000000 : ℝ)*X 2 1+(-1600320041/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((29281569/78125000 : ℝ)*X 0 0+(136576911/312500000 : ℝ)*X 0 1+(4370461111/10000000000 : ℝ)*X 0 2+(29281569/78125000 : ℝ)*X 1 0+(136576911/312500000 : ℝ)*X 1 1+(4370461111/10000000000 : ℝ)*X 1 2+(29281569/78125000 : ℝ)*X 2 0+(136576911/312500000 : ℝ)*X 2 1+(4370461111/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1750875277/10000000000 : ℝ)*X 0 0+(1246228687/2500000000 : ℝ)*X 0 1+(547890859/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1298985873/2500000000 : ℝ)*X 1 0+(-293582037/2000000000 : ℝ)*X 1 1+(684863519/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((649492951/1250000000 : ℝ)*X 2 0+(2739454069/5000000000 : ℝ)*X 2 1+(-366977511/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4662429031/10000000000 : ℝ)*X 0 0+(1955800241/5000000000 : ℝ)*X 0 1+(3911600651/10000000000 : ℝ)*X 0 2+(4662429031/10000000000 : ℝ)*X 1 0+(1955800241/5000000000 : ℝ)*X 1 1+(3911600651/10000000000 : ℝ)*X 1 2+(4662429031/10000000000 : ℝ)*X 2 0+(1955800241/5000000000 : ℝ)*X 2 1+(3911600651/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1307889/9765625 : ℝ)*X 0 0+(350945559/625000000 : ℝ)*X 0 1+(5149564287/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5421099677/10000000000 : ℝ)*X 1 0+(-1610813267/10000000000 : ℝ)*X 1 1+(5149564057/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1355274937/2500000000 : ℝ)*X 2 0+(5149564079/10000000000 : ℝ)*X 2 1+(-1610813141/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1834144631/5000000000 : ℝ)*X 0 0+(4408660917/10000000000 : ℝ)*X 0 1+(2204330383/5000000000 : ℝ)*X 0 2+(1834144631/5000000000 : ℝ)*X 1 0+(4408660917/10000000000 : ℝ)*X 1 1+(2204330383/5000000000 : ℝ)*X 1 2+(1834144631/5000000000 : ℝ)*X 2 0+(4408660917/10000000000 : ℝ)*X 2 1+(2204330383/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-33241/50000 : ℝ) ≤ (-2531194074172986353529642279/3807500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1105783/50000000000000 : ℝ)*(upper0) + (356533/3125000000000 : ℝ)*(upper3) + (368811/20000000000000 : ℝ)*(upper5) + (1274388095362193/100000000000000 : ℝ)*(major0) + (1274388095362193/100000000000000 : ℝ)*(major1) + (1274388095362193/100000000000000 : ℝ)*(major2) + (467347423/100000000000000 : ℝ)*(sp1) + (901211009/100000000000000 : ℝ)*(sp2) + (154977147/50000000000000 : ℝ)*(sp3) + (939969383136761/50000000000000 : ℝ)*(sp4) + (469984679746029/25000000000000 : ℝ)*(sp5) + (1879938285120531/100000000000000 : ℝ)*(sp6) + (345498207469537/50000000000000 : ℝ)*(sp7) + (210029009/50000000000000 : ℝ)*(sp8) + (86374590611671/12500000000000 : ℝ)*(f.failure) + (93996959316577/5000000000000 : ℝ)*(f.sum) + (27135547590907/7615000000000000000000000000 : ℝ)*base65 + (3977514882813011529/1523000000000000000000000000000000 : ℝ)*base68 + (1911076563418988471/1523000000000000000000000000000000 : ℝ)*base69 + (6737624197274988471/1523000000000000000000000000000000 : ℝ)*base71 + (33326093016537/7615000000000000000000000000 : ℝ)*base73 + (6744530705289988471/1523000000000000000000000000000000 : ℝ)*base75 + (1172728886903011529/1523000000000000000000000000000000 : ℝ)*base78 + (724395219715011529/1523000000000000000000000000000000 : ℝ)*base80 + (45855822103667/7615000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (2340191/312500000000000000000 : ℝ)*base90 + (2340191/312500000000000000000 : ℝ)*base92 + (2340191/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (57643/100000 : ℝ) ≤ (87793701960184204466929228486419/152300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7192359/50000000000000 : ℝ)*(lower1) + (82422899/100000000000000 : ℝ)*(lower2) + (23786151/20000000000000 : ℝ)*(lower5) + (274000767364147/20000000000000 : ℝ)*(major0) + (274000767364147/20000000000000 : ℝ)*(major1) + (274000767364147/20000000000000 : ℝ)*(major2) + (988970931088947/50000000000000 : ℝ)*(sp0) + (1977933326302127/100000000000000 : ℝ)*(sp1) + (988968407162569/50000000000000 : ℝ)*(sp2) + (3714186835527/500000000000 : ℝ)*(sp3) + (8961983653/50000000000000 : ℝ)*(sp5) + (2887188859/20000000000000 : ℝ)*(sp6) + (3975951421/100000000000000 : ℝ)*(sp7) + (9388091539/100000000000000 : ℝ)*(sp8) + (371420671528411/50000000000000 : ℝ)*(f.failure) + (1977951250269433/100000000000000 : ℝ)*(f.sum) + (1349819712569/761500000000000000000000000 : ℝ)*base66 + (2352799483533001509/304600000000000000000000000000000 : ℝ)*base67 + (2857924972410001509/304600000000000000000000000000000 : ℝ)*base69 + (2549929227339401509/304600000000000000000000000000000 : ℝ)*base71 + (3072988049033/1523000000000000000000000000 : ℝ)*base73 + (3815178490467801509/304600000000000000000000000000000 : ℝ)*base75 + (916371461476201509/304600000000000000000000000000000 : ℝ)*base77 + (2404234069566201509/304600000000000000000000000000000 : ℝ)*base79 + (10638048888171/1523000000000000000000000000 : ℝ)*base81 + (3539269/1250000000000000000000 : ℝ)*base89 + (3539269/1250000000000000000000 : ℝ)*base91 + (3539269/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (80371/100000 : ℝ) ≤ (153010263695606954369477785700979/190375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7285653/50000000000000 : ℝ)*(upper0) + (1208311/5000000000000 : ℝ)*(lower3) + (220457/800000000000 : ℝ)*(upper4) + (703504609885719/50000000000000 : ℝ)*(major0) + (703504609885719/50000000000000 : ℝ)*(major1) + (703504609885719/50000000000000 : ℝ)*(major2) + (26673951/12500000000000 : ℝ)*(sp0) + (338164599/25000000000000 : ℝ)*(sp2) + (1821162771/50000000000000 : ℝ)*(sp3) + (506079730838911/25000000000000 : ℝ)*(sp8) + (1012160533296911/50000000000000 : ℝ)*(sp9) + (1012159856967713/50000000000000 : ℝ)*(sp10) + (381451350871341/50000000000000 : ℝ)*(sp11) + (192984657/10000000000000 : ℝ)*(sp12) + (5960205813033/781250000000 : ℝ)*(f.failure) + (1012160533296911/50000000000000 : ℝ)*(f.sum) + (4036487774037/475937500000000000000000000 : ℝ)*base65 + (4402940351766383007/761500000000000000000000000000000 : ℝ)*base68 + (5637495790532383007/761500000000000000000000000000000 : ℝ)*base70 + (614552461306616993/761500000000000000000000000000000 : ℝ)*base71 + (9644640552237/1903750000000000000000000000 : ℝ)*base74 + (3622170093199383007/761500000000000000000000000000000 : ℝ)*base76 + (5037684840329383007/761500000000000000000000000000000 : ℝ)*base78 + (7818148445520383007/761500000000000000000000000000000 : ℝ)*base80 + (1119659831693/1903750000000000000000000000 : ℝ)*base81 + (5301/610351562500000000 : ℝ)*base89 + (5301/610351562500000000 : ℝ)*base91 + (5301/610351562500000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-89951/100000 : ℝ) ≤ (-684955246433422159102892735009289/761500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (44685483/50000000000000 : ℝ)*(lower0) + (47164021/50000000000000 : ℝ)*(lower1) + (32158017/100000000000000 : ℝ)*(lower2) + (1452856184382629/100000000000000 : ℝ)*(major0) + (1452856184382629/100000000000000 : ℝ)*(major1) + (1452856184382629/100000000000000 : ℝ)*(major2) + (628822687/100000000000000 : ℝ)*(sp0) + (15924088323/25000000000000 : ℝ)*(sp5) + (13491400093/25000000000000 : ℝ)*(sp6) + (10596883771/100000000000000 : ℝ)*(sp7) + (5369822616501/250000000000 : ℝ)*(sp12) + (429573195813959/20000000000000 : ℝ)*(sp13) + (429575141964543/20000000000000 : ℝ)*(sp14) + (157550963362009/20000000000000 : ℝ)*(sp15) + (98470676711727/12500000000000 : ℝ)*(f.failure) + (2147929675423087/100000000000000 : ℝ)*(f.sum) + (1684951318731/7615000000000000000000000000 : ℝ)*base65 + (5497866200472069763/1523000000000000000000000000000000 : ℝ)*base67 + (5043088976148069763/1523000000000000000000000000000000 : ℝ)*base69 + (572580617265930237/1523000000000000000000000000000000 : ℝ)*base72 + (24045861094729/7615000000000000000000000000 : ℝ)*base74 + (11076965303143069763/1523000000000000000000000000000000 : ℝ)*base75 + (2885218940603069763/1523000000000000000000000000000000 : ℝ)*base77 + (2489182052216930237/1523000000000000000000000000000000 : ℝ)*base80 + (27205174166411/7615000000000000000000000000 : ℝ)*base81 + (954967/312500000000000000000 : ℝ)*base90 + (954967/312500000000000000000 : ℝ)*base92 + (954967/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1678_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (46106879/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17319/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1213/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(33241/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(57643/100000 : ℝ) else (80371/100000 : ℝ) ≤ X j i ∧ X j i ≤ (89951/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1678_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1678_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (46106879/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8677/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9673/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(33241/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(57643/100000 : ℝ) else (80371/100000 : ℝ) ≤ X j i ∧ X j i ≤ (89951/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1678_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1678_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1678_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (46106879/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8677/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9673/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(33241/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(57643/100000 : ℝ) else (80371/100000 : ℝ) ≤ X j i ∧ X j i ≤ (89951/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1678_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
