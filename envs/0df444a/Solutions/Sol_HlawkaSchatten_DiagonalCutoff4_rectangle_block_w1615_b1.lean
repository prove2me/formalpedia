-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1615_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:52:29.476614+00:00
-- url     : https://prove2.me/submissions/bf75c892-6203-402c-9046-05bd72250e54

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
theorem support_rectangle_w1615_s3_0 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-211459607/1250000000 : ℝ)*x 0 + (2729204647/5000000000 : ℝ)*x 1 + (5180854849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211459607/1250000000 : ℝ)^4779 ≤ (2605056878893/25000000000000 : ℝ)^3755 := by
    have hnat : (211459607 : ℕ)^4779*25000000000000^3755 ≤ 2605056878893^3755*1250000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211459607 1250000000 2605056878893 25000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2729204647/5000000000 : ℝ)^4779 ≤ (46276789035777/100000000000000 : ℝ)^3755 := by
    have hnat : (2729204647 : ℕ)^4779*100000000000000^3755 ≤ 46276789035777^3755*5000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729204647 5000000000 46276789035777 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5180854849/10000000000 : ℝ)^4779 ≤ (2165149171521/5000000000000 : ℝ)^3755 := by
    have hnat : (5180854849 : ℕ)^4779*5000000000000^3755 ≤ 2165149171521^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180854849 10000000000 2165149171521 5000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-211459607/1250000000 : ℝ), (2729204647/5000000000 : ℝ), (5180854849/10000000000 : ℝ)] ![(2605056878893/25000000000000 : ℝ), (46276789035777/100000000000000 : ℝ), (2165149171521/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-211459607/1250000000 : ℝ)|^4779 ≤ (2605056878893/25000000000000 : ℝ)^3755
        have hw : |(-211459607/1250000000 : ℝ)|=(211459607/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2729204647/5000000000 : ℝ)|^4779 ≤ (46276789035777/100000000000000 : ℝ)^3755
        have hw : |(2729204647/5000000000 : ℝ)|=(2729204647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5180854849/10000000000 : ℝ)|^4779 ≤ (2165149171521/5000000000000 : ℝ)^3755
        have hw : |(5180854849/10000000000 : ℝ)|=(5180854849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1615_s3_1 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352984201/10000000000 : ℝ)*x 0 + (-366955951/2000000000 : ℝ)*x 1 + (5180854763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352984201/10000000000 : ℝ)^4779 ≤ (22571127470847/50000000000000 : ℝ)^3755 := by
    have hnat : (5352984201 : ℕ)^4779*50000000000000^3755 ≤ 22571127470847^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352984201 10000000000 22571127470847 50000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (366955951/2000000000 : ℝ)^4779 ≤ (5777381265167/50000000000000 : ℝ)^3755 := by
    have hnat : (366955951 : ℕ)^4779*50000000000000^3755 ≤ 5777381265167^3755*2000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      366955951 2000000000 5777381265167 50000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5180854763/10000000000 : ℝ)^4779 ≤ (43302982515587/100000000000000 : ℝ)^3755 := by
    have hnat : (5180854763 : ℕ)^4779*100000000000000^3755 ≤ 43302982515587^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180854763 10000000000 43302982515587 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352984201/10000000000 : ℝ), (-366955951/2000000000 : ℝ), (5180854763/10000000000 : ℝ)] ![(22571127470847/50000000000000 : ℝ), (5777381265167/50000000000000 : ℝ), (43302982515587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352984201/10000000000 : ℝ)|^4779 ≤ (22571127470847/50000000000000 : ℝ)^3755
        have hw : |(5352984201/10000000000 : ℝ)|=(5352984201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-366955951/2000000000 : ℝ)|^4779 ≤ (5777381265167/50000000000000 : ℝ)^3755
        have hw : |(-366955951/2000000000 : ℝ)|=(366955951/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5180854763/10000000000 : ℝ)|^4779 ≤ (43302982515587/100000000000000 : ℝ)^3755
        have hw : |(5180854763/10000000000 : ℝ)|=(5180854763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1615_s3_2 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338246063/2500000000 : ℝ)*x 0 + (5180854593/10000000000 : ℝ)*x 1 + (-229347489/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338246063/2500000000 : ℝ)^4779 ≤ (11285563872267/25000000000000 : ℝ)^3755 := by
    have hnat : (1338246063 : ℕ)^4779*25000000000000^3755 ≤ 11285563872267^3755*2500000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338246063 2500000000 11285563872267 25000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5180854593/10000000000 : ℝ)^4779 ≤ (10825745176799/25000000000000 : ℝ)^3755 := by
    have hnat : (5180854593 : ℕ)^4779*25000000000000^3755 ≤ 10825745176799^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180854593 10000000000 10825745176799 25000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (229347489/1250000000 : ℝ)^4779 ≤ (11554763788691/100000000000000 : ℝ)^3755 := by
    have hnat : (229347489 : ℕ)^4779*100000000000000^3755 ≤ 11554763788691^3755*1250000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229347489 1250000000 11554763788691 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338246063/2500000000 : ℝ), (5180854593/10000000000 : ℝ), (-229347489/1250000000 : ℝ)] ![(11285563872267/25000000000000 : ℝ), (10825745176799/25000000000000 : ℝ), (11554763788691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338246063/2500000000 : ℝ)|^4779 ≤ (11285563872267/25000000000000 : ℝ)^3755
        have hw : |(1338246063/2500000000 : ℝ)|=(1338246063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5180854593/10000000000 : ℝ)|^4779 ≤ (10825745176799/25000000000000 : ℝ)^3755
        have hw : |(5180854593/10000000000 : ℝ)|=(5180854593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-229347489/1250000000 : ℝ)|^4779 ≤ (11554763788691/100000000000000 : ℝ)^3755
        have hw : |(-229347489/1250000000 : ℝ)|=(229347489/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1615_s3_3 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (131511799/312500000 : ℝ)*x 0 + (3875805963/10000000000 : ℝ)*x 1 + (4562345919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (131511799/312500000 : ℝ)^4779 ≤ (830901671013/2500000000000 : ℝ)^3755 := by
    have hnat : (131511799 : ℕ)^4779*2500000000000^3755 ≤ 830901671013^3755*312500000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131511799 312500000 830901671013 2500000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3875805963/10000000000 : ℝ)^4779 ≤ (748250643819/2500000000000 : ℝ)^3755 := by
    have hnat : (3875805963 : ℕ)^4779*2500000000000^3755 ≤ 748250643819^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3875805963 10000000000 748250643819 2500000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4562345919/10000000000 : ℝ)^4779 ≤ (9208476847609/25000000000000 : ℝ)^3755 := by
    have hnat : (4562345919 : ℕ)^4779*25000000000000^3755 ≤ 9208476847609^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4562345919 10000000000 9208476847609 25000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(131511799/312500000 : ℝ), (3875805963/10000000000 : ℝ), (4562345919/10000000000 : ℝ)] ![(830901671013/2500000000000 : ℝ), (748250643819/2500000000000 : ℝ), (9208476847609/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(131511799/312500000 : ℝ)|^4779 ≤ (830901671013/2500000000000 : ℝ)^3755
        have hw : |(131511799/312500000 : ℝ)|=(131511799/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3875805963/10000000000 : ℝ)|^4779 ≤ (748250643819/2500000000000 : ℝ)^3755
        have hw : |(3875805963/10000000000 : ℝ)|=(3875805963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4562345919/10000000000 : ℝ)|^4779 ≤ (9208476847609/25000000000000 : ℝ)^3755
        have hw : |(4562345919/10000000000 : ℝ)|=(4562345919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1615_s3_4 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-845873429/5000000000 : ℝ)*x 0 + (5182928561/10000000000 : ℝ)*x 1 + (1364078451/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (845873429/5000000000 : ℝ)^4779 ≤ (416831051899/4000000000000 : ℝ)^3755 := by
    have hnat : (845873429 : ℕ)^4779*4000000000000^3755 ≤ 416831051899^3755*5000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845873429 5000000000 416831051899 4000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5182928561/10000000000 : ℝ)^4779 ≤ (10831260986057/25000000000000 : ℝ)^3755 := by
    have hnat : (5182928561 : ℕ)^4779*25000000000000^3755 ≤ 10831260986057^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182928561 10000000000 10831260986057 25000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1364078451/2500000000 : ℝ)^4779 ≤ (46254179738439/100000000000000 : ℝ)^3755 := by
    have hnat : (1364078451 : ℕ)^4779*100000000000000^3755 ≤ 46254179738439^3755*2500000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364078451 2500000000 46254179738439 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-845873429/5000000000 : ℝ), (5182928561/10000000000 : ℝ), (1364078451/2500000000 : ℝ)] ![(416831051899/4000000000000 : ℝ), (10831260986057/25000000000000 : ℝ), (46254179738439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-845873429/5000000000 : ℝ)|^4779 ≤ (416831051899/4000000000000 : ℝ)^3755
        have hw : |(-845873429/5000000000 : ℝ)|=(845873429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5182928561/10000000000 : ℝ)|^4779 ≤ (10831260986057/25000000000000 : ℝ)^3755
        have hw : |(5182928561/10000000000 : ℝ)|=(5182928561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1364078451/2500000000 : ℝ)|^4779 ≤ (46254179738439/100000000000000 : ℝ)^3755
        have hw : |(1364078451/2500000000 : ℝ)|=(1364078451/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1615_s3_5 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055841443/2000000000 : ℝ)*x 0 + (-1559320281/10000000000 : ℝ)*x 1 + (27281569/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055841443/2000000000 : ℝ)^4779 ≤ (2771994495261/6250000000000 : ℝ)^3755 := by
    have hnat : (1055841443 : ℕ)^4779*6250000000000^3755 ≤ 2771994495261^3755*2000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055841443 2000000000 2771994495261 6250000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1559320281/10000000000 : ℝ)^4779 ≤ (1878781673673/20000000000000 : ℝ)^3755 := by
    have hnat : (1559320281 : ℕ)^4779*20000000000000^3755 ≤ 1878781673673^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1559320281 10000000000 1878781673673 20000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (27281569/50000000 : ℝ)^4779 ≤ (46254179695283/100000000000000 : ℝ)^3755 := by
    have hnat : (27281569 : ℕ)^4779*100000000000000^3755 ≤ 46254179695283^3755*50000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27281569 50000000 46254179695283 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055841443/2000000000 : ℝ), (-1559320281/10000000000 : ℝ), (27281569/50000000 : ℝ)] ![(2771994495261/6250000000000 : ℝ), (1878781673673/20000000000000 : ℝ), (46254179695283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055841443/2000000000 : ℝ)|^4779 ≤ (2771994495261/6250000000000 : ℝ)^3755
        have hw : |(1055841443/2000000000 : ℝ)|=(1055841443/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1559320281/10000000000 : ℝ)|^4779 ≤ (1878781673673/20000000000000 : ℝ)^3755
        have hw : |(-1559320281/10000000000 : ℝ)|=(1559320281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(27281569/50000000 : ℝ)|^4779 ≤ (46254179695283/100000000000000 : ℝ)^3755
        have hw : |(27281569/50000000 : ℝ)|=(27281569/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1615_s3_6 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319801803/2500000000 : ℝ)*x 0 + (1364078449/2500000000 : ℝ)*x 1 + (-1559320291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319801803/2500000000 : ℝ)^4779 ≤ (44351911892099/100000000000000 : ℝ)^3755 := by
    have hnat : (1319801803 : ℕ)^4779*100000000000000^3755 ≤ 44351911892099^3755*2500000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319801803 2500000000 44351911892099 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1364078449/2500000000 : ℝ)^4779 ≤ (46254179652127/100000000000000 : ℝ)^3755 := by
    have hnat : (1364078449 : ℕ)^4779*100000000000000^3755 ≤ 46254179652127^3755*2500000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364078449 2500000000 46254179652127 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1559320291/10000000000 : ℝ)^4779 ≤ (9393908445037/100000000000000 : ℝ)^3755 := by
    have hnat : (1559320291 : ℕ)^4779*100000000000000^3755 ≤ 9393908445037^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1559320291 10000000000 9393908445037 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319801803/2500000000 : ℝ), (1364078449/2500000000 : ℝ), (-1559320291/10000000000 : ℝ)] ![(44351911892099/100000000000000 : ℝ), (46254179652127/100000000000000 : ℝ), (9393908445037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319801803/2500000000 : ℝ)|^4779 ≤ (44351911892099/100000000000000 : ℝ)^3755
        have hw : |(1319801803/2500000000 : ℝ)|=(1319801803/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1364078449/2500000000 : ℝ)|^4779 ≤ (46254179652127/100000000000000 : ℝ)^3755
        have hw : |(1364078449/2500000000 : ℝ)|=(1364078449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1559320291/10000000000 : ℝ)|^4779 ≤ (9393908445037/100000000000000 : ℝ)^3755
        have hw : |(-1559320291/10000000000 : ℝ)|=(1559320291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1615_s3_7 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2104275471/5000000000 : ℝ)*x 0 + (4557215961/10000000000 : ℝ)*x 1 + (1940495069/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2104275471/5000000000 : ℝ)^4779 ≤ (33237809483513/100000000000000 : ℝ)^3755 := by
    have hnat : (2104275471 : ℕ)^4779*100000000000000^3755 ≤ 33237809483513^3755*5000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2104275471 5000000000 33237809483513 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4557215961/10000000000 : ℝ)^4779 ≤ (36781204568159/100000000000000 : ℝ)^3755 := by
    have hnat : (4557215961 : ℕ)^4779*100000000000000^3755 ≤ 36781204568159^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4557215961 10000000000 36781204568159 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1940495069/5000000000 : ℝ)^4779 ≤ (29980985935933/100000000000000 : ℝ)^3755 := by
    have hnat : (1940495069 : ℕ)^4779*100000000000000^3755 ≤ 29980985935933^3755*5000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1940495069 5000000000 29980985935933 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2104275471/5000000000 : ℝ), (4557215961/10000000000 : ℝ), (1940495069/5000000000 : ℝ)] ![(33237809483513/100000000000000 : ℝ), (36781204568159/100000000000000 : ℝ), (29980985935933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2104275471/5000000000 : ℝ)|^4779 ≤ (33237809483513/100000000000000 : ℝ)^3755
        have hw : |(2104275471/5000000000 : ℝ)|=(2104275471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4557215961/10000000000 : ℝ)|^4779 ≤ (36781204568159/100000000000000 : ℝ)^3755
        have hw : |(4557215961/10000000000 : ℝ)|=(4557215961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1940495069/5000000000 : ℝ)|^4779 ≤ (29980985935933/100000000000000 : ℝ)^3755
        have hw : |(1940495069/5000000000 : ℝ)|=(1940495069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1615_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (173676369/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16473/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5171/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10457/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2043/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16473/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5171/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16473/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5171/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16473/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5171/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16473/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5171/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16473/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5171/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16473/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5171/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5171/50000 : ℝ) ^ (4775/1024 : ℝ) ≤ (1270533911909317/50000000000000000000 : ℝ) := by
    have hpowers : (5171/50000 : ℝ)^4775 ≤ (1270533911909317/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5171 : ℕ)^4775*50000000000000000000^1024 ≤ 1270533911909317^1024*50000^4775 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5171 50000 1270533911909317 50000000000000000000 4775 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5171/50000 : ℝ)) (X := (1270533911909317/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4775 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16473/100000 : ℝ) ^ (4775/1024 : ℝ) ≤ (22271208522251541/100000000000000000000 : ℝ) := by
    have hpowers : (16473/100000 : ℝ)^4775 ≤ (22271208522251541/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16473 : ℕ)^4775*100000000000000000000^1024 ≤ 22271208522251541^1024*100000^4775 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16473 100000 22271208522251541 100000000000000000000 4775 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16473/100000 : ℝ)) (X := (22271208522251541/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4775 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001270533911909317/25000000000000000000 : ℝ) ≤ (1250013623044569/1250000000000000 : ℝ) ^ (4775/1024 : ℝ) := by
    have hpowers : (25001270533911909317/25000000000000000000 : ℝ)^1024 ≤ (1250013623044569/1250000000000000 : ℝ)^4775 := by
      have hnat : (25001270533911909317 : ℕ)^1024*1250000000000000^4775 ≤ 1250013623044569^4775*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001270533911909317 25000000000000000000 1250013623044569 1250000000000000 1024 4775 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250013623044569/1250000000000000 : ℝ)) (X := (25001270533911909317/25000000000000000000 : ℝ)) (by norm_num) 4775 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4000992491053842807/4000000000000000000 : ℝ) ≤ (100005320480669/100000000000000 : ℝ) ^ (4775/1024 : ℝ) := by
    have hpowers : (4000992491053842807/4000000000000000000 : ℝ)^1024 ≤ (100005320480669/100000000000000 : ℝ)^4775 := by
      have hnat : (4000992491053842807 : ℕ)^1024*100000000000000^4775 ≤ 100005320480669^4775*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4000992491053842807 4000000000000000000 100005320480669 100000000000000 1024 4775 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100005320480669/100000000000000 : ℝ)) (X := (4000992491053842807/4000000000000000000 : ℝ)) (by norm_num) 4775 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50022271208522251541/50000000000000000000 : ℝ) ≤ (312529847243039/312500000000000 : ℝ) ^ (4775/1024 : ℝ) := by
    have hpowers : (50022271208522251541/50000000000000000000 : ℝ)^1024 ≤ (312529847243039/312500000000000 : ℝ)^4775 := by
      have hnat : (50022271208522251541 : ℕ)^1024*312500000000000^4775 ≤ 312529847243039^4775*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022271208522251541 50000000000000000000 312529847243039 312500000000000 1024 4775 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312529847243039/312500000000000 : ℝ)) (X := (50022271208522251541/50000000000000000000 : ℝ)) (by norm_num) 4775 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1270533911909317/50000000000000000000 : ℝ) ≤ ((1532547938332629557/1532750000000000000 : ℝ)+2*(105765927587/153275000000000 : ℝ)*(5171/50000 : ℝ))^(4775/1024 : ℝ) := by
    rw [show (1532547938332629557/1532750000000000000 : ℝ)+2*(105765927587/153275000000000 : ℝ)*(5171/50000 : ℝ)=(1250013623044569/1250000000000000 : ℝ) by norm_num, show 1+2*(1270533911909317/50000000000000000000 : ℝ)=(25001270533911909317/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(22271208522251541/100000000000000000000 : ℝ)+(1270533911909317/50000000000000000000 : ℝ) ≤ ((1532547938332629557/1532750000000000000 : ℝ)+(105765927587/153275000000000 : ℝ)*((16473/100000 : ℝ)+(5171/50000 : ℝ)))^(4775/1024 : ℝ) := by
    rw [show (1532547938332629557/1532750000000000000 : ℝ)+(105765927587/153275000000000 : ℝ)*((16473/100000 : ℝ)+(5171/50000 : ℝ))=(100005320480669/100000000000000 : ℝ) by norm_num, show 1+(22271208522251541/100000000000000000000 : ℝ)+(1270533911909317/50000000000000000000 : ℝ)=(4000992491053842807/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(22271208522251541/100000000000000000000 : ℝ) ≤ ((1532547938332629557/1532750000000000000 : ℝ)+2*(105765927587/153275000000000 : ℝ)*(16473/100000 : ℝ))^(4775/1024 : ℝ) := by
    rw [show (1532547938332629557/1532750000000000000 : ℝ)+2*(105765927587/153275000000000 : ℝ)*(16473/100000 : ℝ)=(312529847243039/312500000000000 : ℝ) by norm_num, show 1+2*(22271208522251541/100000000000000000000 : ℝ)=(50022271208522251541/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1532547938332629557/1532750000000000000 : ℝ)*(X 1 0+X 2 0)+(105765927587/153275000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4775/1024 : ℝ)) (lo := (5171/50000 : ℝ)) (hi := (16473/100000 : ℝ)) (c := (1532547938332629557/1532750000000000000 : ℝ)) (alpha := (105765927587/153275000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1532547938332629557/1532750000000000000 : ℝ)*(X 0 1+X 2 1)+(105765927587/153275000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4775/1024 : ℝ)) (lo := (5171/50000 : ℝ)) (hi := (16473/100000 : ℝ)) (c := (1532547938332629557/1532750000000000000 : ℝ)) (alpha := (105765927587/153275000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1532547938332629557/1532750000000000000 : ℝ)*(X 0 2+X 1 2)+(105765927587/153275000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4775/1024 : ℝ)) (lo := (5171/50000 : ℝ)) (hi := (16473/100000 : ℝ)) (c := (1532547938332629557/1532750000000000000 : ℝ)) (alpha := (105765927587/153275000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-211459607/1250000000 : ℝ)*X 0 0+(2729204647/5000000000 : ℝ)*X 0 1+(5180854849/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352984201/10000000000 : ℝ)*X 1 0+(-366955951/2000000000 : ℝ)*X 1 1+(5180854763/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338246063/2500000000 : ℝ)*X 2 0+(5180854593/10000000000 : ℝ)*X 2 1+(-229347489/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((131511799/312500000 : ℝ)*X 0 0+(3875805963/10000000000 : ℝ)*X 0 1+(4562345919/10000000000 : ℝ)*X 0 2+(131511799/312500000 : ℝ)*X 1 0+(3875805963/10000000000 : ℝ)*X 1 1+(4562345919/10000000000 : ℝ)*X 1 2+(131511799/312500000 : ℝ)*X 2 0+(3875805963/10000000000 : ℝ)*X 2 1+(4562345919/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-845873429/5000000000 : ℝ)*X 0 0+(5182928561/10000000000 : ℝ)*X 0 1+(1364078451/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1055841443/2000000000 : ℝ)*X 1 0+(-1559320281/10000000000 : ℝ)*X 1 1+(27281569/50000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1319801803/2500000000 : ℝ)*X 2 0+(1364078449/2500000000 : ℝ)*X 2 1+(-1559320291/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2104275471/5000000000 : ℝ)*X 0 0+(4557215961/10000000000 : ℝ)*X 0 1+(1940495069/5000000000 : ℝ)*X 0 2+(2104275471/5000000000 : ℝ)*X 1 0+(4557215961/10000000000 : ℝ)*X 1 1+(1940495069/5000000000 : ℝ)*X 1 2+(2104275471/5000000000 : ℝ)*X 2 0+(4557215961/10000000000 : ℝ)*X 2 1+(1940495069/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (51826150000534281323996973/3831875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (356049589/20000000000000 : ℝ)*(base19) + (1724329977/100000000000000 : ℝ)*(base23) + (48307737/100000000000000 : ℝ)*(lower2) + (405523733/100000000000000 : ℝ)*(upper3) + (225908547/100000000000000 : ℝ)*(upper5) + (63244089197273/2500000000000 : ℝ)*(major0) + (63244089197273/2500000000000 : ℝ)*(major1) + (63244089197273/2500000000000 : ℝ)*(major2) + (360291508441163/10000000000000 : ℝ)*(sp0) + (1801464301468409/50000000000000 : ℝ)*(sp1) + (3602928658854787/100000000000000 : ℝ)*(sp2) + (182073373835779/12500000000000 : ℝ)*(sp3) + (7649386567/50000000000000 : ℝ)*(sp4) + (2327769287/25000000000000 : ℝ)*(sp7) + (1456596301763379/100000000000000 : ℝ)*(f.failure) + (900732595796191/25000000000000 : ℝ)*(f.sum) + (2591918380777/1532750000000000000000000000 : ℝ)*base66 + (57317328620753189/3831875000000000000000000000000 : ℝ)*base68 + (48584329155253189/3831875000000000000000000000000 : ℝ)*base70 + (26848939293210689/3831875000000000000000000000000 : ℝ)*base72 + (19981839427021/3065500000000000000000000000 : ℝ)*base74 + (34855979908483189/3831875000000000000000000000000 : ℝ)*base76 + (12328439471764439/3831875000000000000000000000000 : ℝ)*base78 + (3891869925086883/478984375000000000000000000000 : ℝ)*base80 + (245600828787/766375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (38109149/10000000000000000000000 : ℝ)*base90 + (38109149/10000000000000000000000 : ℝ)*base92 + (38109149/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (650067454023750350580163581/76637500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (640043071/50000000000000 : ℝ)*(base19) + (173764797/12500000000000 : ℝ)*(base23) + (175197021/100000000000000 : ℝ)*(upper3) + (52242797/100000000000000 : ℝ)*(lower4) + (7236993/4000000000000 : ℝ)*(upper5) + (2568318623305263/100000000000000 : ℝ)*(major0) + (2568318623305263/100000000000000 : ℝ)*(major1) + (2568318623305263/100000000000000 : ℝ)*(major2) + (14701671113/100000000000000 : ℝ)*(sp1) + (1955339863/12500000000000 : ℝ)*(sp2) + (1828920647300953/50000000000000 : ℝ)*(sp4) + (914456328211163/25000000000000 : ℝ)*(sp5) + (3657824261764627/100000000000000 : ℝ)*(sp6) + (73939783463151/5000000000000 : ℝ)*(sp7) + (73939783463151/5000000000000 : ℝ)*(f.failure) + (1828920647300953/50000000000000 : ℝ)*(f.sum) + (27166979467/3831875000000000000000000000 : ℝ)*base66 + (1704377787194618491/153275000000000000000000000000000 : ℝ)*base67 + (1047547249783668491/153275000000000000000000000000000 : ℝ)*base69 + (849683395210693491/153275000000000000000000000000000 : ℝ)*base71 + (93160730882609/30655000000000000000000000000 : ℝ)*base73 + (830379812040043491/153275000000000000000000000000000 : ℝ)*base75 + (684155616387968491/153275000000000000000000000000000 : ℝ)*base77 + (682220088503668491/153275000000000000000000000000000 : ℝ)*base79 + (44625406163501/30655000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (4021281/500000000000000000000 : ℝ)*base90 + (4021281/500000000000000000000 : ℝ)*base92 + (4021281/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1615_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (173676369/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16473/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5171/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10457/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2043/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1615_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1615_s4_0 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-338356219/2000000000 : ℝ)*x 0 + (5457891719/10000000000 : ℝ)*x 1 + (518130301/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (338356219/2000000000 : ℝ)^4779 ≤ (1042104470129/10000000000000 : ℝ)^3755 := by
    have hnat : (338356219 : ℕ)^4779*10000000000000^3755 ≤ 1042104470129^3755*2000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338356219 2000000000 1042104470129 10000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5457891719/10000000000 : ℝ)^4779 ≤ (46271204438189/100000000000000 : ℝ)^3755 := by
    have hnat : (5457891719 : ℕ)^4779*100000000000000^3755 ≤ 46271204438189^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457891719 10000000000 46271204438189 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (518130301/1000000000 : ℝ)^4779 ≤ (1353367213819/3125000000000 : ℝ)^3755 := by
    have hnat : (518130301 : ℕ)^4779*3125000000000^3755 ≤ 1353367213819^3755*1000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518130301 1000000000 1353367213819 3125000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-338356219/2000000000 : ℝ), (5457891719/10000000000 : ℝ), (518130301/1000000000 : ℝ)] ![(1042104470129/10000000000000 : ℝ), (46271204438189/100000000000000 : ℝ), (1353367213819/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-338356219/2000000000 : ℝ)|^4779 ≤ (1042104470129/10000000000000 : ℝ)^3755
        have hw : |(-338356219/2000000000 : ℝ)|=(338356219/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5457891719/10000000000 : ℝ)|^4779 ≤ (46271204438189/100000000000000 : ℝ)^3755
        have hw : |(5457891719/10000000000 : ℝ)|=(5457891719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(518130301/1000000000 : ℝ)|^4779 ≤ (1353367213819/3125000000000 : ℝ)^3755
        have hw : |(518130301/1000000000 : ℝ)|=(518130301/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1615_s4_1 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352845441/10000000000 : ℝ)*x 0 + (-183437063/1000000000 : ℝ)*x 1 + (5181303009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352845441/10000000000 : ℝ)^4779 ≤ (22570382829517/50000000000000 : ℝ)^3755 := by
    have hnat : (5352845441 : ℕ)^4779*50000000000000^3755 ≤ 22570382829517^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352845441 10000000000 22570382829517 50000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (183437063/1000000000 : ℝ)^4779 ≤ (2887870872069/25000000000000 : ℝ)^3755 := by
    have hnat : (183437063 : ℕ)^4779*25000000000000^3755 ≤ 2887870872069^3755*1000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183437063 1000000000 2887870872069 25000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5181303009/10000000000 : ℝ)^4779 ≤ (4330775083157/10000000000000 : ℝ)^3755 := by
    have hnat : (5181303009 : ℕ)^4779*10000000000000^3755 ≤ 4330775083157^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181303009 10000000000 4330775083157 10000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352845441/10000000000 : ℝ), (-183437063/1000000000 : ℝ), (5181303009/10000000000 : ℝ)] ![(22570382829517/50000000000000 : ℝ), (2887870872069/25000000000000 : ℝ), (4330775083157/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352845441/10000000000 : ℝ)|^4779 ≤ (22570382829517/50000000000000 : ℝ)^3755
        have hw : |(5352845441/10000000000 : ℝ)|=(5352845441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-183437063/1000000000 : ℝ)|^4779 ≤ (2887870872069/25000000000000 : ℝ)^3755
        have hw : |(-183437063/1000000000 : ℝ)|=(183437063/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5181303009/10000000000 : ℝ)|^4779 ≤ (4330775083157/10000000000000 : ℝ)^3755
        have hw : |(5181303009/10000000000 : ℝ)|=(5181303009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1615_s4_2 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352845437/10000000000 : ℝ)*x 0 + (1036260603/2000000000 : ℝ)*x 1 + (-1834370629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352845437/10000000000 : ℝ)^4779 ≤ (45140765616103/100000000000000 : ℝ)^3755 := by
    have hnat : (5352845437 : ℕ)^4779*100000000000000^3755 ≤ 45140765616103^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352845437 10000000000 45140765616103 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036260603/2000000000 : ℝ)^4779 ≤ (43307750895397/100000000000000 : ℝ)^3755 := by
    have hnat : (1036260603 : ℕ)^4779*100000000000000^3755 ≤ 43307750895397^3755*2000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036260603 2000000000 43307750895397 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1834370629/10000000000 : ℝ)^4779 ≤ (11551483480261/100000000000000 : ℝ)^3755 := by
    have hnat : (1834370629 : ℕ)^4779*100000000000000^3755 ≤ 11551483480261^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1834370629 10000000000 11551483480261 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352845437/10000000000 : ℝ), (1036260603/2000000000 : ℝ), (-1834370629/10000000000 : ℝ)] ![(45140765616103/100000000000000 : ℝ), (43307750895397/100000000000000 : ℝ), (11551483480261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352845437/10000000000 : ℝ)|^4779 ≤ (45140765616103/100000000000000 : ℝ)^3755
        have hw : |(5352845437/10000000000 : ℝ)|=(5352845437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036260603/2000000000 : ℝ)|^4779 ≤ (43307750895397/100000000000000 : ℝ)^3755
        have hw : |(1036260603/2000000000 : ℝ)|=(1036260603/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1834370629/10000000000 : ℝ)|^4779 ≤ (11551483480261/100000000000000 : ℝ)^3755
        have hw : |(-1834370629/10000000000 : ℝ)|=(1834370629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1615_s4_3 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4208444663/10000000000 : ℝ)*x 0 + (77539881/200000000 : ℝ)*x 1 + (1140285947/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4208444663/10000000000 : ℝ)^4779 ≤ (16618370616809/50000000000000 : ℝ)^3755 := by
    have hnat : (4208444663 : ℕ)^4779*50000000000000^3755 ≤ 16618370616809^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4208444663 10000000000 16618370616809 50000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (77539881/200000000 : ℝ)^4779 ≤ (93567821713/312500000000 : ℝ)^3755 := by
    have hnat : (77539881 : ℕ)^4779*312500000000^3755 ≤ 93567821713^3755*200000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77539881 200000000 93567821713 312500000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1140285947/2500000000 : ℝ)^4779 ≤ (460269447507/1250000000000 : ℝ)^3755 := by
    have hnat : (1140285947 : ℕ)^4779*1250000000000^3755 ≤ 460269447507^3755*2500000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1140285947 2500000000 460269447507 1250000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4208444663/10000000000 : ℝ), (77539881/200000000 : ℝ), (1140285947/2500000000 : ℝ)] ![(16618370616809/50000000000000 : ℝ), (93567821713/312500000000 : ℝ), (460269447507/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4208444663/10000000000 : ℝ)|^4779 ≤ (16618370616809/50000000000000 : ℝ)^3755
        have hw : |(4208444663/10000000000 : ℝ)|=(4208444663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(77539881/200000000 : ℝ)|^4779 ≤ (93567821713/312500000000 : ℝ)^3755
        have hw : |(77539881/200000000 : ℝ)|=(77539881/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1140285947/2500000000 : ℝ)|^4779 ≤ (460269447507/1250000000000 : ℝ)^3755
        have hw : |(1140285947/2500000000 : ℝ)|=(1140285947/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1615_s4_4 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-338370091/2000000000 : ℝ)*x 0 + (2591681313/5000000000 : ℝ)*x 1 + (5455810493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (338370091/2000000000 : ℝ)^4779 ≤ (2605397114833/25000000000000 : ℝ)^3755 := by
    have hnat : (338370091 : ℕ)^4779*25000000000000^3755 ≤ 2605397114833^3755*2000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338370091 2000000000 2605397114833 25000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591681313/5000000000 : ℝ)^4779 ≤ (43329661908901/100000000000000 : ℝ)^3755 := by
    have hnat : (2591681313 : ℕ)^4779*100000000000000^3755 ≤ 43329661908901^3755*5000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591681313 5000000000 43329661908901 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5455810493/10000000000 : ℝ)^4779 ≤ (11562187403779/25000000000000 : ℝ)^3755 := by
    have hnat : (5455810493 : ℕ)^4779*25000000000000^3755 ≤ 11562187403779^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5455810493 10000000000 11562187403779 25000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-338370091/2000000000 : ℝ), (2591681313/5000000000 : ℝ), (5455810493/10000000000 : ℝ)] ![(2605397114833/25000000000000 : ℝ), (43329661908901/100000000000000 : ℝ), (11562187403779/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-338370091/2000000000 : ℝ)|^4779 ≤ (2605397114833/25000000000000 : ℝ)^3755
        have hw : |(-338370091/2000000000 : ℝ)|=(338370091/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591681313/5000000000 : ℝ)|^4779 ≤ (43329661908901/100000000000000 : ℝ)^3755
        have hw : |(2591681313/5000000000 : ℝ)|=(2591681313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5455810493/10000000000 : ℝ)|^4779 ≤ (11562187403779/25000000000000 : ℝ)^3755
        have hw : |(5455810493/10000000000 : ℝ)|=(5455810493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1615_s4_5 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055865081/2000000000 : ℝ)*x 0 + (-62394537/400000000 : ℝ)*x 1 + (1091162131/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055865081/2000000000 : ℝ)^4779 ≤ (2217658782489/5000000000000 : ℝ)^3755 := by
    have hnat : (1055865081 : ℕ)^4779*5000000000000^3755 ≤ 2217658782489^3755*2000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055865081 2000000000 2217658782489 5000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (62394537/400000000 : ℝ)^4779 ≤ (2349518243043/25000000000000 : ℝ)^3755 := by
    have hnat : (62394537 : ℕ)^4779*25000000000000^3755 ≤ 2349518243043^3755*400000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62394537 400000000 2349518243043 25000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1091162131/2000000000 : ℝ)^4779 ≤ (144527348009/312500000000 : ℝ)^3755 := by
    have hnat : (1091162131 : ℕ)^4779*312500000000^3755 ≤ 144527348009^3755*2000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091162131 2000000000 144527348009 312500000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055865081/2000000000 : ℝ), (-62394537/400000000 : ℝ), (1091162131/2000000000 : ℝ)] ![(2217658782489/5000000000000 : ℝ), (2349518243043/25000000000000 : ℝ), (144527348009/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055865081/2000000000 : ℝ)|^4779 ≤ (2217658782489/5000000000000 : ℝ)^3755
        have hw : |(1055865081/2000000000 : ℝ)|=(1055865081/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-62394537/400000000 : ℝ)|^4779 ≤ (2349518243043/25000000000000 : ℝ)^3755
        have hw : |(-62394537/400000000 : ℝ)|=(62394537/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1091162131/2000000000 : ℝ)|^4779 ≤ (144527348009/312500000000 : ℝ)^3755
        have hw : |(1091162131/2000000000 : ℝ)|=(1091162131/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1615_s4_6 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639662841/5000000000 : ℝ)*x 0 + (2727905297/5000000000 : ℝ)*x 1 + (-2495781/16000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639662841/5000000000 : ℝ)^4779 ≤ (22176589305781/50000000000000 : ℝ)^3755 := by
    have hnat : (2639662841 : ℕ)^4779*50000000000000^3755 ≤ 22176589305781^3755*5000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639662841 5000000000 22176589305781 50000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2727905297/5000000000 : ℝ)^4779 ≤ (11562187676193/25000000000000 : ℝ)^3755 := by
    have hnat : (2727905297 : ℕ)^4779*25000000000000^3755 ≤ 11562187676193^3755*5000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2727905297 5000000000 11562187676193 25000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2495781/16000000 : ℝ)^4779 ≤ (9398070671787/100000000000000 : ℝ)^3755 := by
    have hnat : (2495781 : ℕ)^4779*100000000000000^3755 ≤ 9398070671787^3755*16000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2495781 16000000 9398070671787 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639662841/5000000000 : ℝ), (2727905297/5000000000 : ℝ), (-2495781/16000000 : ℝ)] ![(22176589305781/50000000000000 : ℝ), (11562187676193/25000000000000 : ℝ), (9398070671787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639662841/5000000000 : ℝ)|^4779 ≤ (22176589305781/50000000000000 : ℝ)^3755
        have hw : |(2639662841/5000000000 : ℝ)|=(2639662841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2727905297/5000000000 : ℝ)|^4779 ≤ (11562187676193/25000000000000 : ℝ)^3755
        have hw : |(2727905297/5000000000 : ℝ)|=(2727905297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2495781/16000000 : ℝ)|^4779 ≤ (9398070671787/100000000000000 : ℝ)^3755
        have hw : |(-2495781/16000000 : ℝ)|=(2495781/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1615_s4_7 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4208616439/10000000000 : ℝ)*x 0 + (4556049051/10000000000 : ℝ)*x 1 + (3882142247/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4208616439/10000000000 : ℝ)^4779 ≤ (3323846782197/10000000000000 : ℝ)^3755 := by
    have hnat : (4208616439 : ℕ)^4779*10000000000000^3755 ≤ 3323846782197^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4208616439 10000000000 3323846782197 10000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4556049051/10000000000 : ℝ)^4779 ≤ (7353843706171/20000000000000 : ℝ)^3755 := by
    have hnat : (4556049051 : ℕ)^4779*20000000000000^3755 ≤ 7353843706171^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4556049051 10000000000 7353843706171 20000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3882142247/10000000000 : ℝ)^4779 ≤ (14996156816253/50000000000000 : ℝ)^3755 := by
    have hnat : (3882142247 : ℕ)^4779*50000000000000^3755 ≤ 14996156816253^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3882142247 10000000000 14996156816253 50000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4208616439/10000000000 : ℝ), (4556049051/10000000000 : ℝ), (3882142247/10000000000 : ℝ)] ![(3323846782197/10000000000000 : ℝ), (7353843706171/20000000000000 : ℝ), (14996156816253/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4208616439/10000000000 : ℝ)|^4779 ≤ (3323846782197/10000000000000 : ℝ)^3755
        have hw : |(4208616439/10000000000 : ℝ)|=(4208616439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4556049051/10000000000 : ℝ)|^4779 ≤ (7353843706171/20000000000000 : ℝ)^3755
        have hw : |(4556049051/10000000000 : ℝ)|=(4556049051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3882142247/10000000000 : ℝ)|^4779 ≤ (14996156816253/50000000000000 : ℝ)^3755
        have hw : |(3882142247/10000000000 : ℝ)|=(3882142247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1615_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (173676369/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2043/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10457/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10467/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16333/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2043/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10457/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2043/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10457/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2043/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10457/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2043/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10457/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2043/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10457/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2043/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10457/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10457/100000 : ℝ) ^ (4775/1024 : ℝ) ≤ (2675537700961479/100000000000000000000 : ℝ) := by
    have hpowers : (10457/100000 : ℝ)^4775 ≤ (2675537700961479/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10457 : ℕ)^4775*100000000000000000000^1024 ≤ 2675537700961479^1024*100000^4775 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10457 100000 2675537700961479 100000000000000000000 4775 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10457/100000 : ℝ)) (X := (2675537700961479/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4775 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2043/12500 : ℝ) ^ (4775/1024 : ℝ) ≤ (21469523264277791/100000000000000000000 : ℝ) := by
    have hpowers : (2043/12500 : ℝ)^4775 ≤ (21469523264277791/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2043 : ℕ)^4775*100000000000000000000^1024 ≤ 21469523264277791^1024*12500^4775 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2043 12500 21469523264277791 100000000000000000000 4775 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2043/12500 : ℝ)) (X := (21469523264277791/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4775 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002675537700961479/50000000000000000000 : ℝ) ≤ (1000011475154029/1000000000000000 : ℝ) ^ (4775/1024 : ℝ) := by
    have hpowers : (50002675537700961479/50000000000000000000 : ℝ)^1024 ≤ (1000011475154029/1000000000000000 : ℝ)^4775 := by
      have hnat : (50002675537700961479 : ℕ)^1024*1000000000000000^4775 ≤ 1000011475154029^4775*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002675537700961479 50000000000000000000 1000011475154029 1000000000000000 1024 4775 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000011475154029/1000000000000000 : ℝ)) (X := (50002675537700961479/50000000000000000000 : ℝ)) (by norm_num) 4775 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10002414506096523927/10000000000000000000 : ℝ) ≤ (10000517742366393/10000000000000000 : ℝ) ^ (4775/1024 : ℝ) := by
    have hpowers : (10002414506096523927/10000000000000000000 : ℝ)^1024 ≤ (10000517742366393/10000000000000000 : ℝ)^4775 := by
      have hnat : (10002414506096523927 : ℕ)^1024*10000000000000000^4775 ≤ 10000517742366393^4775*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002414506096523927 10000000000000000000 10000517742366393 10000000000000000 1024 4775 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000517742366393/10000000000000000 : ℝ)) (X := (10002414506096523927/10000000000000000000 : ℝ)) (by norm_num) 4775 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50021469523264277791/50000000000000000000 : ℝ) ≤ (625057545824531/625000000000000 : ℝ) ^ (4775/1024 : ℝ) := by
    have hpowers : (50021469523264277791/50000000000000000000 : ℝ)^1024 ≤ (625057545824531/625000000000000 : ℝ)^4775 := by
      have hnat : (50021469523264277791 : ℕ)^1024*625000000000000^4775 ≤ 625057545824531^4775*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021469523264277791 50000000000000000000 625057545824531 625000000000000 1024 4775 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625057545824531/625000000000000 : ℝ)) (X := (50021469523264277791/50000000000000000000 : ℝ)) (by norm_num) 4775 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2675537700961479/100000000000000000000 : ℝ) ≤ ((57482663468926337/57490234375000000 : ℝ)+2*(402990826103/588700000000000 : ℝ)*(10457/100000 : ℝ))^(4775/1024 : ℝ) := by
    rw [show (57482663468926337/57490234375000000 : ℝ)+2*(402990826103/588700000000000 : ℝ)*(10457/100000 : ℝ)=(1000011475154029/1000000000000000 : ℝ) by norm_num, show 1+2*(2675537700961479/100000000000000000000 : ℝ)=(50002675537700961479/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(21469523264277791/100000000000000000000 : ℝ)+(2675537700961479/100000000000000000000 : ℝ) ≤ ((57482663468926337/57490234375000000 : ℝ)+(402990826103/588700000000000 : ℝ)*((2043/12500 : ℝ)+(10457/100000 : ℝ)))^(4775/1024 : ℝ) := by
    rw [show (57482663468926337/57490234375000000 : ℝ)+(402990826103/588700000000000 : ℝ)*((2043/12500 : ℝ)+(10457/100000 : ℝ))=(10000517742366393/10000000000000000 : ℝ) by norm_num, show 1+(21469523264277791/100000000000000000000 : ℝ)+(2675537700961479/100000000000000000000 : ℝ)=(10002414506096523927/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(21469523264277791/100000000000000000000 : ℝ) ≤ ((57482663468926337/57490234375000000 : ℝ)+2*(402990826103/588700000000000 : ℝ)*(2043/12500 : ℝ))^(4775/1024 : ℝ) := by
    rw [show (57482663468926337/57490234375000000 : ℝ)+2*(402990826103/588700000000000 : ℝ)*(2043/12500 : ℝ)=(625057545824531/625000000000000 : ℝ) by norm_num, show 1+2*(21469523264277791/100000000000000000000 : ℝ)=(50021469523264277791/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (57482663468926337/57490234375000000 : ℝ)*(X 1 0+X 2 0)+(402990826103/588700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4775/1024 : ℝ)) (lo := (10457/100000 : ℝ)) (hi := (2043/12500 : ℝ)) (c := (57482663468926337/57490234375000000 : ℝ)) (alpha := (402990826103/588700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (57482663468926337/57490234375000000 : ℝ)*(X 0 1+X 2 1)+(402990826103/588700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4775/1024 : ℝ)) (lo := (10457/100000 : ℝ)) (hi := (2043/12500 : ℝ)) (c := (57482663468926337/57490234375000000 : ℝ)) (alpha := (402990826103/588700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (57482663468926337/57490234375000000 : ℝ)*(X 0 2+X 1 2)+(402990826103/588700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4775/1024 : ℝ)) (lo := (10457/100000 : ℝ)) (hi := (2043/12500 : ℝ)) (c := (57482663468926337/57490234375000000 : ℝ)) (alpha := (402990826103/588700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-338356219/2000000000 : ℝ)*X 0 0+(5457891719/10000000000 : ℝ)*X 0 1+(518130301/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352845441/10000000000 : ℝ)*X 1 0+(-183437063/1000000000 : ℝ)*X 1 1+(5181303009/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352845437/10000000000 : ℝ)*X 2 0+(1036260603/2000000000 : ℝ)*X 2 1+(-1834370629/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4208444663/10000000000 : ℝ)*X 0 0+(77539881/200000000 : ℝ)*X 0 1+(1140285947/2500000000 : ℝ)*X 0 2+(4208444663/10000000000 : ℝ)*X 1 0+(77539881/200000000 : ℝ)*X 1 1+(1140285947/2500000000 : ℝ)*X 1 2+(4208444663/10000000000 : ℝ)*X 2 0+(77539881/200000000 : ℝ)*X 2 1+(1140285947/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-338370091/2000000000 : ℝ)*X 0 0+(2591681313/5000000000 : ℝ)*X 0 1+(5455810493/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1055865081/2000000000 : ℝ)*X 1 0+(-62394537/400000000 : ℝ)*X 1 1+(1091162131/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2639662841/5000000000 : ℝ)*X 2 0+(2727905297/5000000000 : ℝ)*X 2 1+(-2495781/16000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4208616439/10000000000 : ℝ)*X 0 0+(4556049051/10000000000 : ℝ)*X 0 1+(3882142247/10000000000 : ℝ)*X 0 2+(4208616439/10000000000 : ℝ)*X 1 0+(4556049051/10000000000 : ℝ)*X 1 1+(3882142247/10000000000 : ℝ)*X 1 2+(4208616439/10000000000 : ℝ)*X 2 0+(4556049051/10000000000 : ℝ)*X 2 1+(3882142247/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12970886476368050800278351/1437255859375000000000000000000 : ℝ) := by norm_num
    linear_combination (371398883/25000000000000 : ℝ)*(base19) + (1389529461/100000000000000 : ℝ)*(base23) + (24988239/50000000000000 : ℝ)*(lower2) + (44521027/20000000000000 : ℝ)*(upper3) + (38869311/25000000000000 : ℝ)*(upper5) + (79331195814211/3125000000000 : ℝ)*(major0) + (79331195814211/3125000000000 : ℝ)*(major1) + (2538598266054753/100000000000000 : ℝ)*(major2) + (1807747549891397/50000000000000 : ℝ)*(sp0) + (90387789246621/2500000000000 : ℝ)*(sp1) + (361551166593091/10000000000000 : ℝ)*(sp2) + (365418831509591/25000000000000 : ℝ)*(sp3) + (17955677577/100000000000000 : ℝ)*(sp4) + (490611593/6250000000000 : ℝ)*(sp7) + (365420793955963/25000000000000 : ℝ)*(f.failure) + (903878263865093/25000000000000 : ℝ)*(f.sum) + (36359739615177/11774000000000000000000000000 : ℝ)*base65 + (2311223583263418557/183968750000000000000000000000000 : ℝ)*base68 + (257785047450783199/91984375000000000000000000000000 : ℝ)*base70 + (2137199600339543557/183968750000000000000000000000000 : ℝ)*base72 + (65361511882491/11774000000000000000000000000 : ℝ)*base73 + (87361763591568603/11498046875000000000000000000000 : ℝ)*base76 + (64353562531792069/6570312500000000000000000000000 : ℝ)*base78 + (79733044538542069/6570312500000000000000000000000 : ℝ)*base80 + (3255546659513/14717500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (261653/2500000000000000000000 : ℝ)*base90 + (261653/2500000000000000000000 : ℝ)*base92 + (25261653/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2832058445189929600142337/410644531250000000000000000000 : ℝ) := by norm_num
    linear_combination (35668797/6250000000000 : ℝ)*(base19) + (240886989/25000000000000 : ℝ)*(base23) + (20611599/10000000000000 : ℝ)*(lower1) + (2253641/2000000000000 : ℝ)*(upper3) + (13886347/20000000000000 : ℝ)*(lower4) + (171526063/100000000000000 : ℝ)*(upper5) + (1288575587182989/50000000000000 : ℝ)*(major0) + (1288575587182989/50000000000000 : ℝ)*(major1) + (1288575587182989/50000000000000 : ℝ)*(major2) + (98733907/2000000000000 : ℝ)*(sp2) + (3670420811787879/100000000000000 : ℝ)*(sp4) + (3670420241087127/100000000000000 : ℝ)*(sp5) + (3670414911544573/100000000000000 : ℝ)*(sp6) + (185485163382099/12500000000000 : ℝ)*(sp7) + (185485163382099/12500000000000 : ℝ)*(f.failure) + (3670420811787879/100000000000000 : ℝ)*(f.sum) + (7385704367647/4205000000000000000000000000 : ℝ)*base65 + (295528559377225643/13140625000000000000000000000000 : ℝ)*base67 + (74248453092323759/6570312500000000000000000000000 : ℝ)*base69 + (409740704288948759/6570312500000000000000000000000 : ℝ)*base71 + (23865496008477/4205000000000000000000000000 : ℝ)*base73 + (3760572455070869/102661132812500000000000000000 : ℝ)*base76 + (80404297122569393/13140625000000000000000000000000 : ℝ)*base77 + (123127812235381893/13140625000000000000000000000000 : ℝ)*base79 + (208008863083/4205000000000000000000000000 : ℝ)*base82 + (11081469/1250000000000000000000 : ℝ)*base90 + (11081469/1250000000000000000000 : ℝ)*base92 + (11081469/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1615_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (173676369/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2043/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10457/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10467/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16333/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1615_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1615_s5_0 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-67671587/400000000 : ℝ)*x 0 + (2728924173/5000000000 : ℝ)*x 1 + (129533517/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67671587/400000000 : ℝ)^4779 ≤ (2605277991287/25000000000000 : ℝ)^3755 := by
    have hnat : (67671587 : ℕ)^4779*25000000000000^3755 ≤ 2605277991287^3755*400000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67671587 400000000 2605277991287 25000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2728924173/5000000000 : ℝ)^4779 ≤ (925414729063/2000000000000 : ℝ)^3755 := by
    have hnat : (2728924173 : ℕ)^4779*2000000000000^3755 ≤ 925414729063^3755*5000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728924173 5000000000 925414729063 2000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (129533517/250000000 : ℝ)^4779 ≤ (4330815157029/10000000000000 : ℝ)^3755 := by
    have hnat : (129533517 : ℕ)^4779*10000000000000^3755 ≤ 4330815157029^3755*250000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129533517 250000000 4330815157029 10000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-67671587/400000000 : ℝ), (2728924173/5000000000 : ℝ), (129533517/250000000 : ℝ)] ![(2605277991287/25000000000000 : ℝ), (925414729063/2000000000000 : ℝ), (4330815157029/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-67671587/400000000 : ℝ)|^4779 ≤ (2605277991287/25000000000000 : ℝ)^3755
        have hw : |(-67671587/400000000 : ℝ)|=(67671587/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2728924173/5000000000 : ℝ)|^4779 ≤ (925414729063/2000000000000 : ℝ)^3755
        have hw : |(2728924173/5000000000 : ℝ)|=(2728924173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(129533517/250000000 : ℝ)|^4779 ≤ (4330815157029/10000000000000 : ℝ)^3755
        have hw : |(129533517/250000000 : ℝ)|=(129533517/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1615_s5_1 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352833879/10000000000 : ℝ)*x 0 + (-1834335993/10000000000 : ℝ)*x 1 + (5181340769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352833879/10000000000 : ℝ)^4779 ≤ (11285160391733/25000000000000 : ℝ)^3755 := by
    have hnat : (5352833879 : ℕ)^4779*25000000000000^3755 ≤ 11285160391733^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352833879 10000000000 11285160391733 25000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1834335993/10000000000 : ℝ)^4779 ≤ (721950368119/6250000000000 : ℝ)^3755 := by
    have hnat : (1834335993 : ℕ)^4779*6250000000000^3755 ≤ 721950368119^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1834335993 10000000000 721950368119 6250000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5181340769/10000000000 : ℝ)^4779 ≤ (2165407625853/5000000000000 : ℝ)^3755 := by
    have hnat : (5181340769 : ℕ)^4779*5000000000000^3755 ≤ 2165407625853^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181340769 10000000000 2165407625853 5000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352833879/10000000000 : ℝ), (-1834335993/10000000000 : ℝ), (5181340769/10000000000 : ℝ)] ![(11285160391733/25000000000000 : ℝ), (721950368119/6250000000000 : ℝ), (2165407625853/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352833879/10000000000 : ℝ)|^4779 ≤ (11285160391733/25000000000000 : ℝ)^3755
        have hw : |(5352833879/10000000000 : ℝ)|=(5352833879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1834335993/10000000000 : ℝ)|^4779 ≤ (721950368119/6250000000000 : ℝ)^3755
        have hw : |(-1834335993/10000000000 : ℝ)|=(1834335993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5181340769/10000000000 : ℝ)|^4779 ≤ (2165407625853/5000000000000 : ℝ)^3755
        have hw : |(5181340769/10000000000 : ℝ)|=(5181340769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1615_s5_2 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352833769/10000000000 : ℝ)*x 0 + (5181340857/10000000000 : ℝ)*x 1 + (-917168013/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352833769/10000000000 : ℝ)^4779 ≤ (45140640386329/100000000000000 : ℝ)^3755 := by
    have hnat : (5352833769 : ℕ)^4779*100000000000000^3755 ≤ 45140640386329^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352833769 10000000000 45140640386329 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5181340857/10000000000 : ℝ)^4779 ≤ (43308153453193/100000000000000 : ℝ)^3755 := by
    have hnat : (5181340857 : ℕ)^4779*100000000000000^3755 ≤ 43308153453193^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181340857 10000000000 43308153453193 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (917168013/5000000000 : ℝ)^4779 ≤ (5775603077191/50000000000000 : ℝ)^3755 := by
    have hnat : (917168013 : ℕ)^4779*50000000000000^3755 ≤ 5775603077191^3755*5000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      917168013 5000000000 5775603077191 50000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352833769/10000000000 : ℝ), (5181340857/10000000000 : ℝ), (-917168013/5000000000 : ℝ)] ![(45140640386329/100000000000000 : ℝ), (43308153453193/100000000000000 : ℝ), (5775603077191/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352833769/10000000000 : ℝ)|^4779 ≤ (45140640386329/100000000000000 : ℝ)^3755
        have hw : |(5352833769/10000000000 : ℝ)|=(5352833769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5181340857/10000000000 : ℝ)|^4779 ≤ (43308153453193/100000000000000 : ℝ)^3755
        have hw : |(5181340857/10000000000 : ℝ)|=(5181340857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-917168013/5000000000 : ℝ)|^4779 ≤ (5775603077191/50000000000000 : ℝ)^3755
        have hw : |(-917168013/5000000000 : ℝ)|=(917168013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1615_s5_3 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4208450331/10000000000 : ℝ)*x 0 + (969273433/2500000000 : ℝ)*x 1 + (2280521441/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4208450331/10000000000 : ℝ)^4779 ≤ (4154599775577/12500000000000 : ℝ)^3755 := by
    have hnat : (4208450331 : ℕ)^4779*12500000000000^3755 ≤ 4154599775577^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4208450331 10000000000 4154599775577 12500000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (969273433/2500000000 : ℝ)^4779 ≤ (29942682723981/100000000000000 : ℝ)^3755 := by
    have hnat : (969273433 : ℕ)^4779*100000000000000^3755 ≤ 29942682723981^3755*2500000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      969273433 2500000000 29942682723981 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2280521441/5000000000 : ℝ)^4779 ≤ (3682051905749/10000000000000 : ℝ)^3755 := by
    have hnat : (2280521441 : ℕ)^4779*10000000000000^3755 ≤ 3682051905749^3755*5000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2280521441 5000000000 3682051905749 10000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4208450331/10000000000 : ℝ), (969273433/2500000000 : ℝ), (2280521441/5000000000 : ℝ)] ![(4154599775577/12500000000000 : ℝ), (29942682723981/100000000000000 : ℝ), (3682051905749/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4208450331/10000000000 : ℝ)|^4779 ≤ (4154599775577/12500000000000 : ℝ)^3755
        have hw : |(4208450331/10000000000 : ℝ)|=(4208450331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(969273433/2500000000 : ℝ)|^4779 ≤ (29942682723981/100000000000000 : ℝ)^3755
        have hw : |(969273433/2500000000 : ℝ)|=(969273433/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2280521441/5000000000 : ℝ)|^4779 ≤ (3682051905749/10000000000000 : ℝ)^3755
        have hw : |(2280521441/5000000000 : ℝ)|=(2280521441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1615_s5_4 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-845929673/5000000000 : ℝ)*x 0 + (2591699623/5000000000 : ℝ)*x 1 + (68197099/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (845929673/5000000000 : ℝ)^4779 ≤ (10421658162089/100000000000000 : ℝ)^3755 := by
    have hnat : (845929673 : ℕ)^4779*100000000000000^3755 ≤ 10421658162089^3755*5000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845929673 5000000000 10421658162089 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591699623/5000000000 : ℝ)^4779 ≤ (8666010301889/20000000000000 : ℝ)^3755 := by
    have hnat : (2591699623 : ℕ)^4779*20000000000000^3755 ≤ 8666010301889^3755*5000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591699623 5000000000 8666010301889 20000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (68197099/125000000 : ℝ)^4779 ≤ (1445259072177/3125000000000 : ℝ)^3755 := by
    have hnat : (68197099 : ℕ)^4779*3125000000000^3755 ≤ 1445259072177^3755*125000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68197099 125000000 1445259072177 3125000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-845929673/5000000000 : ℝ), (2591699623/5000000000 : ℝ), (68197099/125000000 : ℝ)] ![(10421658162089/100000000000000 : ℝ), (8666010301889/20000000000000 : ℝ), (1445259072177/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-845929673/5000000000 : ℝ)|^4779 ≤ (10421658162089/100000000000000 : ℝ)^3755
        have hw : |(-845929673/5000000000 : ℝ)|=(845929673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591699623/5000000000 : ℝ)|^4779 ≤ (8666010301889/20000000000000 : ℝ)^3755
        have hw : |(2591699623/5000000000 : ℝ)|=(2591699623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(68197099/125000000 : ℝ)|^4779 ≤ (1445259072177/3125000000000 : ℝ)^3755
        have hw : |(68197099/125000000 : ℝ)|=(68197099/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1615_s5_5 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279336363/10000000000 : ℝ)*x 0 + (-1559908663/10000000000 : ℝ)*x 1 + (2727883821/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279336363/10000000000 : ℝ)^4779 ≤ (22176646408321/50000000000000 : ℝ)^3755 := by
    have hnat : (5279336363 : ℕ)^4779*50000000000000^3755 ≤ 22176646408321^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279336363 10000000000 22176646408321 50000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1559908663/10000000000 : ℝ)^4779 ≤ (939841985631/10000000000000 : ℝ)^3755 := by
    have hnat : (1559908663 : ℕ)^4779*10000000000000^3755 ≤ 939841985631^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1559908663 10000000000 939841985631 10000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2727883821/5000000000 : ℝ)^4779 ≤ (46248287310421/100000000000000 : ℝ)^3755 := by
    have hnat : (2727883821 : ℕ)^4779*100000000000000^3755 ≤ 46248287310421^3755*5000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2727883821 5000000000 46248287310421 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279336363/10000000000 : ℝ), (-1559908663/10000000000 : ℝ), (2727883821/5000000000 : ℝ)] ![(22176646408321/50000000000000 : ℝ), (939841985631/10000000000000 : ℝ), (46248287310421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279336363/10000000000 : ℝ)|^4779 ≤ (22176646408321/50000000000000 : ℝ)^3755
        have hw : |(5279336363/10000000000 : ℝ)|=(5279336363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1559908663/10000000000 : ℝ)|^4779 ≤ (939841985631/10000000000000 : ℝ)^3755
        have hw : |(-1559908663/10000000000 : ℝ)|=(1559908663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2727883821/5000000000 : ℝ)|^4779 ≤ (46248287310421/100000000000000 : ℝ)^3755
        have hw : |(2727883821/5000000000 : ℝ)|=(2727883821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1615_s5_6 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (659916991/1250000000 : ℝ)*x 0 + (5455768303/10000000000 : ℝ)*x 1 + (-1559908339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (659916991/1250000000 : ℝ)^4779 ≤ (5544161020683/12500000000000 : ℝ)^3755 := by
    have hnat : (659916991 : ℕ)^4779*12500000000000^3755 ≤ 5544161020683^3755*1250000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659916991 1250000000 5544161020683 12500000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5455768303/10000000000 : ℝ)^4779 ≤ (9249658888343/20000000000000 : ℝ)^3755 := by
    have hnat : (5455768303 : ℕ)^4779*20000000000000^3755 ≤ 9249658888343^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5455768303 10000000000 9249658888343 20000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1559908339/10000000000 : ℝ)^4779 ≤ (4699208685937/50000000000000 : ℝ)^3755 := by
    have hnat : (1559908339 : ℕ)^4779*50000000000000^3755 ≤ 4699208685937^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1559908339 10000000000 4699208685937 50000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(659916991/1250000000 : ℝ), (5455768303/10000000000 : ℝ), (-1559908339/10000000000 : ℝ)] ![(5544161020683/12500000000000 : ℝ), (9249658888343/20000000000000 : ℝ), (4699208685937/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(659916991/1250000000 : ℝ)|^4779 ≤ (5544161020683/12500000000000 : ℝ)^3755
        have hw : |(659916991/1250000000 : ℝ)|=(659916991/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5455768303/10000000000 : ℝ)|^4779 ≤ (9249658888343/20000000000000 : ℝ)^3755
        have hw : |(5455768303/10000000000 : ℝ)|=(5455768303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1559908339/10000000000 : ℝ)|^4779 ≤ (4699208685937/50000000000000 : ℝ)^3755
        have hw : |(-1559908339/10000000000 : ℝ)|=(1559908339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1615_s5_7 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1052155451/2500000000 : ℝ)*x 0 + (4555951389/10000000000 : ℝ)*x 1 + (3882238781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1052155451/2500000000 : ℝ)^4779 ≤ (33238521748011/100000000000000 : ℝ)^3755 := by
    have hnat : (1052155451 : ℕ)^4779*100000000000000^3755 ≤ 33238521748011^3755*2500000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052155451 2500000000 33238521748011 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4555951389/10000000000 : ℝ)^4779 ≤ (36768215423437/100000000000000 : ℝ)^3755 := by
    have hnat : (4555951389 : ℕ)^4779*100000000000000^3755 ≤ 36768215423437^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4555951389 10000000000 36768215423437 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3882238781/10000000000 : ℝ)^4779 ≤ (1874578925619/6250000000000 : ℝ)^3755 := by
    have hnat : (3882238781 : ℕ)^4779*6250000000000^3755 ≤ 1874578925619^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3882238781 10000000000 1874578925619 6250000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1052155451/2500000000 : ℝ), (4555951389/10000000000 : ℝ), (3882238781/10000000000 : ℝ)] ![(33238521748011/100000000000000 : ℝ), (36768215423437/100000000000000 : ℝ), (1874578925619/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1052155451/2500000000 : ℝ)|^4779 ≤ (33238521748011/100000000000000 : ℝ)^3755
        have hw : |(1052155451/2500000000 : ℝ)|=(1052155451/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4555951389/10000000000 : ℝ)|^4779 ≤ (36768215423437/100000000000000 : ℝ)^3755
        have hw : |(4555951389/10000000000 : ℝ)|=(4555951389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3882238781/10000000000 : ℝ)|^4779 ≤ (1874578925619/6250000000000 : ℝ)^3755
        have hw : |(3882238781/10000000000 : ℝ)|=(3882238781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1615_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (173676369/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16333/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10467/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2617/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4083/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16333/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10467/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16333/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10467/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16333/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10467/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16333/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10467/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16333/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10467/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16333/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10467/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10467/100000 : ℝ) ^ (4775/1024 : ℝ) ≤ (2687489630723989/100000000000000000000 : ℝ) := by
    have hpowers : (10467/100000 : ℝ)^4775 ≤ (2687489630723989/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10467 : ℕ)^4775*100000000000000000000^1024 ≤ 2687489630723989^1024*100000^4775 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10467 100000 2687489630723989 100000000000000000000 4775 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10467/100000 : ℝ)) (X := (2687489630723989/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4775 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16333/100000 : ℝ) ^ (4775/1024 : ℝ) ≤ (5350556601332183/25000000000000000000 : ℝ) := by
    have hpowers : (16333/100000 : ℝ)^4775 ≤ (5350556601332183/25000000000000000000 : ℝ)^1024 := by
      have hnat : (16333 : ℕ)^4775*25000000000000000000^1024 ≤ 5350556601332183^1024*100000^4775 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16333 100000 5350556601332183 25000000000000000000 4775 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16333/100000 : ℝ)) (X := (5350556601332183/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4775 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002687489630723989/50000000000000000000 : ℝ) ≤ (2500028816034397/2500000000000000 : ℝ) ^ (4775/1024 : ℝ) := by
    have hpowers : (50002687489630723989/50000000000000000000 : ℝ)^1024 ≤ (2500028816034397/2500000000000000 : ℝ)^4775 := by
      have hnat : (50002687489630723989 : ℕ)^1024*2500000000000000^4775 ≤ 2500028816034397^4775*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002687489630723989 50000000000000000000 2500028816034397 2500000000000000 1024 4775 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500028816034397/2500000000000000 : ℝ)) (X := (50002687489630723989/50000000000000000000 : ℝ)) (by norm_num) 4775 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100024089716036052721/100000000000000000000 : ℝ) ≤ (10000516555717747/10000000000000000 : ℝ) ^ (4775/1024 : ℝ) := by
    have hpowers : (100024089716036052721/100000000000000000000 : ℝ)^1024 ≤ (10000516555717747/10000000000000000 : ℝ)^4775 := by
      have hnat : (100024089716036052721 : ℕ)^1024*10000000000000000^4775 ≤ 10000516555717747^4775*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100024089716036052721 100000000000000000000 10000516555717747 10000000000000000 1024 4775 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000516555717747/10000000000000000 : ℝ)) (X := (100024089716036052721/100000000000000000000 : ℝ)) (by norm_num) 4775 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12505350556601332183/12500000000000000000 : ℝ) ≤ (5000458923648953/5000000000000000 : ℝ) ^ (4775/1024 : ℝ) := by
    have hpowers : (12505350556601332183/12500000000000000000 : ℝ)^1024 ≤ (5000458923648953/5000000000000000 : ℝ)^4775 := by
      have hnat : (12505350556601332183 : ℕ)^1024*5000000000000000^4775 ≤ 5000458923648953^4775*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505350556601332183 12500000000000000000 5000458923648953 5000000000000000 1024 4775 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000458923648953/5000000000000000 : ℝ)) (X := (12505350556601332183/12500000000000000000 : ℝ)) (by norm_num) 4775 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2687489630723989/100000000000000000000 : ℝ) ≤ ((29326137750746021351/29330000000000000000 : ℝ)+2*(401291580159/586600000000000 : ℝ)*(10467/100000 : ℝ))^(4775/1024 : ℝ) := by
    rw [show (29326137750746021351/29330000000000000000 : ℝ)+2*(401291580159/586600000000000 : ℝ)*(10467/100000 : ℝ)=(2500028816034397/2500000000000000 : ℝ) by norm_num, show 1+2*(2687489630723989/100000000000000000000 : ℝ)=(50002687489630723989/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5350556601332183/25000000000000000000 : ℝ)+(2687489630723989/100000000000000000000 : ℝ) ≤ ((29326137750746021351/29330000000000000000 : ℝ)+(401291580159/586600000000000 : ℝ)*((16333/100000 : ℝ)+(10467/100000 : ℝ)))^(4775/1024 : ℝ) := by
    rw [show (29326137750746021351/29330000000000000000 : ℝ)+(401291580159/586600000000000 : ℝ)*((16333/100000 : ℝ)+(10467/100000 : ℝ))=(10000516555717747/10000000000000000 : ℝ) by norm_num, show 1+(5350556601332183/25000000000000000000 : ℝ)+(2687489630723989/100000000000000000000 : ℝ)=(100024089716036052721/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5350556601332183/25000000000000000000 : ℝ) ≤ ((29326137750746021351/29330000000000000000 : ℝ)+2*(401291580159/586600000000000 : ℝ)*(16333/100000 : ℝ))^(4775/1024 : ℝ) := by
    rw [show (29326137750746021351/29330000000000000000 : ℝ)+2*(401291580159/586600000000000 : ℝ)*(16333/100000 : ℝ)=(5000458923648953/5000000000000000 : ℝ) by norm_num, show 1+2*(5350556601332183/25000000000000000000 : ℝ)=(12505350556601332183/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (29326137750746021351/29330000000000000000 : ℝ)*(X 1 0+X 2 0)+(401291580159/586600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4775/1024 : ℝ)) (lo := (10467/100000 : ℝ)) (hi := (16333/100000 : ℝ)) (c := (29326137750746021351/29330000000000000000 : ℝ)) (alpha := (401291580159/586600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (29326137750746021351/29330000000000000000 : ℝ)*(X 0 1+X 2 1)+(401291580159/586600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4775/1024 : ℝ)) (lo := (10467/100000 : ℝ)) (hi := (16333/100000 : ℝ)) (c := (29326137750746021351/29330000000000000000 : ℝ)) (alpha := (401291580159/586600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (29326137750746021351/29330000000000000000 : ℝ)*(X 0 2+X 1 2)+(401291580159/586600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4775/1024 : ℝ)) (lo := (10467/100000 : ℝ)) (hi := (16333/100000 : ℝ)) (c := (29326137750746021351/29330000000000000000 : ℝ)) (alpha := (401291580159/586600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-67671587/400000000 : ℝ)*X 0 0+(2728924173/5000000000 : ℝ)*X 0 1+(129533517/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352833879/10000000000 : ℝ)*X 1 0+(-1834335993/10000000000 : ℝ)*X 1 1+(5181340769/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352833769/10000000000 : ℝ)*X 2 0+(5181340857/10000000000 : ℝ)*X 2 1+(-917168013/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4208450331/10000000000 : ℝ)*X 0 0+(969273433/2500000000 : ℝ)*X 0 1+(2280521441/5000000000 : ℝ)*X 0 2+(4208450331/10000000000 : ℝ)*X 1 0+(969273433/2500000000 : ℝ)*X 1 1+(2280521441/5000000000 : ℝ)*X 1 2+(4208450331/10000000000 : ℝ)*X 2 0+(969273433/2500000000 : ℝ)*X 2 1+(2280521441/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-845929673/5000000000 : ℝ)*X 0 0+(2591699623/5000000000 : ℝ)*X 0 1+(68197099/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5279336363/10000000000 : ℝ)*X 1 0+(-1559908663/10000000000 : ℝ)*X 1 1+(2727883821/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((659916991/1250000000 : ℝ)*X 2 0+(5455768303/10000000000 : ℝ)*X 2 1+(-1559908339/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1052155451/2500000000 : ℝ)*X 0 0+(4555951389/10000000000 : ℝ)*X 0 1+(3882238781/10000000000 : ℝ)*X 0 2+(1052155451/2500000000 : ℝ)*X 1 0+(4555951389/10000000000 : ℝ)*X 1 1+(3882238781/10000000000 : ℝ)*X 1 2+(1052155451/2500000000 : ℝ)*X 2 0+(4555951389/10000000000 : ℝ)*X 2 1+(3882238781/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (101367842144923675707423/14665000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1212821419/100000000000000 : ℝ)*(base19) + (135409987/12500000000000 : ℝ)*(base23) + (29559183/100000000000000 : ℝ)*(lower2) + (38454839/20000000000000 : ℝ)*(upper3) + (116738043/100000000000000 : ℝ)*(upper5) + (317417417688531/12500000000000 : ℝ)*(major0) + (317417417688531/12500000000000 : ℝ)*(major1) + (317417417688531/12500000000000 : ℝ)*(major2) + (1808276557653183/50000000000000 : ℝ)*(sp0) + (3616567364892329/100000000000000 : ℝ)*(sp1) + (904141873608463/25000000000000 : ℝ)*(sp2) + (91381443449979/6250000000000 : ℝ)*(sp3) + (15462407381/100000000000000 : ℝ)*(sp4) + (6779695433/100000000000000 : ℝ)*(sp7) + (1462109874895097/100000000000000 : ℝ)*(f.failure) + (904142144428437/25000000000000 : ℝ)*(f.sum) + (7102019812721/3666250000000000000000000000 : ℝ)*base66 + (2740992933858900381/366625000000000000000000000000000 : ℝ)*base67 + (1273421534633849619/366625000000000000000000000000000 : ℝ)*base70 + (743654301286400381/366625000000000000000000000000000 : ℝ)*base71 + (706721591231/916562500000000000000000000 : ℝ)*base73 + (2554143335225474619/366625000000000000000000000000000 : ℝ)*base76 + (1233489499636275381/366625000000000000000000000000000 : ℝ)*base77 + (1099362073299349619/366625000000000000000000000000000 : ℝ)*base80 + (19748699275169/14665000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (97137207/10000000000000000000000 : ℝ)*base90 + (97137207/10000000000000000000000 : ℝ)*base92 + (97137207/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (375150650800334845414269879/104750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (128742073/10000000000000 : ℝ)*(base19) + (33268881/2500000000000 : ℝ)*(base23) + (5358483/2000000000000 : ℝ)*(lower1) + (58522273/50000000000000 : ℝ)*(upper2) + (43008529/20000000000000 : ℝ)*(upper3) + (35526639/50000000000000 : ℝ)*(upper5) + (1288946837296701/50000000000000 : ℝ)*(major0) + (1288946837296701/50000000000000 : ℝ)*(major1) + (1288946837296701/50000000000000 : ℝ)*(major2) + (8917602407/100000000000000 : ℝ)*(sp2) + (917869600829413/25000000000000 : ℝ)*(sp4) + (1835738557948461/50000000000000 : ℝ)*(sp5) + (917867038740001/25000000000000 : ℝ)*(sp6) + (742154413244729/50000000000000 : ℝ)*(sp7) + (742154413244729/50000000000000 : ℝ)*(f.failure) + (917869600829413/25000000000000 : ℝ)*(f.sum) + (110829316979859/14665000000000000000000000000 : ℝ)*base65 + (3961558688100186949/1466500000000000000000000000000000 : ℝ)*base68 + (4917736609863813051/1466500000000000000000000000000000 : ℝ)*base69 + (5149965360406186949/1466500000000000000000000000000000 : ℝ)*base72 + (55774630443919/14665000000000000000000000000 : ℝ)*base73 + (14444598565677813051/1466500000000000000000000000000000 : ℝ)*base75 + (1558698985104686949/1466500000000000000000000000000000 : ℝ)*base78 + (1983698378363686949/1466500000000000000000000000000000 : ℝ)*base80 + (257364693580059/14665000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (58890999/5000000000000000000000 : ℝ)*base90 + (58890999/5000000000000000000000 : ℝ)*base92 + (58890999/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1615_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (173676369/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16333/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10467/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2617/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4083/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1615_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1615_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (173676369/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16473/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5171/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2617/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4083/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1615_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1615_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1615_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (173676369/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16473/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5171/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2617/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4083/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1615_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
