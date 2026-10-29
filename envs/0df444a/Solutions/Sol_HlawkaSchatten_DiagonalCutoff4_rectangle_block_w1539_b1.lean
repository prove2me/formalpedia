-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1539_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:06:53.943338+00:00
-- url     : https://prove2.me/submissions/ed10c005-8812-4729-9a1a-8e81f67ae0f3

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
theorem support_rectangle_w1539_s3_0 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-457123163/2500000000 : ℝ)*x 0 + (5432142533/10000000000 : ℝ)*x 1 + (2608363847/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (457123163/2500000000 : ℝ)^4575 ≤ (11202202774243/100000000000000 : ℝ)^3551 := by
    have hnat : (457123163 : ℕ)^4575*100000000000000^3551 ≤ 11202202774243^3551*2500000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      457123163 2500000000 11202202774243 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5432142533/10000000000 : ℝ)^4575 ≤ (22777965623819/50000000000000 : ℝ)^3551 := by
    have hnat : (5432142533 : ℕ)^4575*50000000000000^3551 ≤ 22777965623819^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432142533 10000000000 22777965623819 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2608363847/5000000000 : ℝ)^4575 ≤ (2702616622267/6250000000000 : ℝ)^3551 := by
    have hnat : (2608363847 : ℕ)^4575*6250000000000^3551 ≤ 2702616622267^3551*5000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608363847 5000000000 2702616622267 6250000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-457123163/2500000000 : ℝ), (5432142533/10000000000 : ℝ), (2608363847/5000000000 : ℝ)] ![(11202202774243/100000000000000 : ℝ), (22777965623819/50000000000000 : ℝ), (2702616622267/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-457123163/2500000000 : ℝ)|^4575 ≤ (11202202774243/100000000000000 : ℝ)^3551
        have hw : |(-457123163/2500000000 : ℝ)|=(457123163/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5432142533/10000000000 : ℝ)|^4575 ≤ (22777965623819/50000000000000 : ℝ)^3551
        have hw : |(5432142533/10000000000 : ℝ)|=(5432142533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2608363847/5000000000 : ℝ)|^4575 ≤ (2702616622267/6250000000000 : ℝ)^3551
        have hw : |(2608363847/5000000000 : ℝ)|=(2608363847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_s3_1 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350681503/10000000000 : ℝ)*x 0 + (-1938814299/10000000000 : ℝ)*x 1 + (2608363831/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350681503/10000000000 : ℝ)^4575 ≤ (11169419040633/25000000000000 : ℝ)^3551 := by
    have hnat : (5350681503 : ℕ)^4575*25000000000000^3551 ≤ 11169419040633^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350681503 10000000000 11169419040633 25000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1938814299/10000000000 : ℝ)^4575 ≤ (12080458208623/100000000000000 : ℝ)^3551 := by
    have hnat : (1938814299 : ℕ)^4575*100000000000000^3551 ≤ 12080458208623^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1938814299 10000000000 12080458208623 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2608363831/5000000000 : ℝ)^4575 ≤ (10810466403633/25000000000000 : ℝ)^3551 := by
    have hnat : (2608363831 : ℕ)^4575*25000000000000^3551 ≤ 10810466403633^3551*5000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608363831 5000000000 10810466403633 25000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350681503/10000000000 : ℝ), (-1938814299/10000000000 : ℝ), (2608363831/5000000000 : ℝ)] ![(11169419040633/25000000000000 : ℝ), (12080458208623/100000000000000 : ℝ), (10810466403633/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350681503/10000000000 : ℝ)|^4575 ≤ (11169419040633/25000000000000 : ℝ)^3551
        have hw : |(5350681503/10000000000 : ℝ)|=(5350681503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1938814299/10000000000 : ℝ)|^4575 ≤ (12080458208623/100000000000000 : ℝ)^3551
        have hw : |(-1938814299/10000000000 : ℝ)|=(1938814299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2608363831/5000000000 : ℝ)|^4575 ≤ (10810466403633/25000000000000 : ℝ)^3551
        have hw : |(2608363831/5000000000 : ℝ)|=(2608363831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_s3_2 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675340761/5000000000 : ℝ)*x 0 + (2608363823/5000000000 : ℝ)*x 1 + (-969407147/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675340761/5000000000 : ℝ)^4575 ≤ (44677676366929/100000000000000 : ℝ)^3551 := by
    have hnat : (2675340761 : ℕ)^4575*100000000000000^3551 ≤ 44677676366929^3551*5000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675340761 5000000000 44677676366929 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608363823/5000000000 : ℝ)^4575 ≤ (43241865443661/100000000000000 : ℝ)^3551 := by
    have hnat : (2608363823 : ℕ)^4575*100000000000000^3551 ≤ 43241865443661^3551*5000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608363823 5000000000 43241865443661 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (969407147/5000000000 : ℝ)^4575 ≤ (2416091633697/20000000000000 : ℝ)^3551 := by
    have hnat : (969407147 : ℕ)^4575*20000000000000^3551 ≤ 2416091633697^3551*5000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      969407147 5000000000 2416091633697 20000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675340761/5000000000 : ℝ), (2608363823/5000000000 : ℝ), (-969407147/5000000000 : ℝ)] ![(44677676366929/100000000000000 : ℝ), (43241865443661/100000000000000 : ℝ), (2416091633697/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675340761/5000000000 : ℝ)|^4575 ≤ (44677676366929/100000000000000 : ℝ)^3551
        have hw : |(2675340761/5000000000 : ℝ)|=(2675340761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608363823/5000000000 : ℝ)|^4575 ≤ (43241865443661/100000000000000 : ℝ)^3551
        have hw : |(2608363823/5000000000 : ℝ)|=(2608363823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-969407147/5000000000 : ℝ)|^4575 ≤ (2416091633697/20000000000000 : ℝ)^3551
        have hw : |(-969407147/5000000000 : ℝ)|=(969407147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_s3_3 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4257134797/10000000000 : ℝ)*x 0 + (802857229/2000000000 : ℝ)*x 1 + (2256032689/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4257134797/10000000000 : ℝ)^4575 ≤ (33278686943647/100000000000000 : ℝ)^3551 := by
    have hnat : (4257134797 : ℕ)^4575*100000000000000^3551 ≤ 33278686943647^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4257134797 10000000000 33278686943647 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (802857229/2000000000 : ℝ)^4575 ≤ (15426630332729/50000000000000 : ℝ)^3551 := by
    have hnat : (802857229 : ℕ)^4575*50000000000000^3551 ≤ 15426630332729^3551*2000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      802857229 2000000000 15426630332729 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2256032689/5000000000 : ℝ)^4575 ≤ (17934026185463/50000000000000 : ℝ)^3551 := by
    have hnat : (2256032689 : ℕ)^4575*50000000000000^3551 ≤ 17934026185463^3551*5000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2256032689 5000000000 17934026185463 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4257134797/10000000000 : ℝ), (802857229/2000000000 : ℝ), (2256032689/5000000000 : ℝ)] ![(33278686943647/100000000000000 : ℝ), (15426630332729/50000000000000 : ℝ), (17934026185463/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4257134797/10000000000 : ℝ)|^4575 ≤ (33278686943647/100000000000000 : ℝ)^3551
        have hw : |(4257134797/10000000000 : ℝ)|=(4257134797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(802857229/2000000000 : ℝ)|^4575 ≤ (15426630332729/50000000000000 : ℝ)^3551
        have hw : |(802857229/2000000000 : ℝ)|=(802857229/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2256032689/5000000000 : ℝ)|^4575 ≤ (17934026185463/50000000000000 : ℝ)^3551
        have hw : |(2256032689/5000000000 : ℝ)|=(2256032689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_s3_4 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-914261191/5000000000 : ℝ)*x 0 + (163058327/312500000 : ℝ)*x 1 + (1086199037/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (914261191/5000000000 : ℝ)^4575 ≤ (5601218719147/50000000000000 : ℝ)^3551 := by
    have hnat : (914261191 : ℕ)^4575*50000000000000^3551 ≤ 5601218719147^3551*5000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      914261191 5000000000 5601218719147 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163058327/312500000 : ℝ)^4575 ≤ (43254027714633/100000000000000 : ℝ)^3551 := by
    have hnat : (163058327 : ℕ)^4575*100000000000000^3551 ≤ 43254027714633^3551*312500000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163058327 312500000 43254027714633 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1086199037/2000000000 : ℝ)^4575 ≤ (45543534831857/100000000000000 : ℝ)^3551 := by
    have hnat : (1086199037 : ℕ)^4575*100000000000000^3551 ≤ 45543534831857^3551*2000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086199037 2000000000 45543534831857 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-914261191/5000000000 : ℝ), (163058327/312500000 : ℝ), (1086199037/2000000000 : ℝ)] ![(5601218719147/50000000000000 : ℝ), (43254027714633/100000000000000 : ℝ), (45543534831857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-914261191/5000000000 : ℝ)|^4575 ≤ (5601218719147/50000000000000 : ℝ)^3551
        have hw : |(-914261191/5000000000 : ℝ)|=(914261191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163058327/312500000 : ℝ)|^4575 ≤ (43254027714633/100000000000000 : ℝ)^3551
        have hw : |(163058327/312500000 : ℝ)|=(163058327/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1086199037/2000000000 : ℝ)|^4575 ≤ (45543534831857/100000000000000 : ℝ)^3551
        have hw : |(1086199037/2000000000 : ℝ)|=(1086199037/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_s3_5 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293912481/10000000000 : ℝ)*x 0 + (-344909359/2000000000 : ℝ)*x 1 + (1357748797/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293912481/10000000000 : ℝ)^4575 ≤ (44067905172037/100000000000000 : ℝ)^3551 := by
    have hnat : (5293912481 : ℕ)^4575*100000000000000^3551 ≤ 44067905172037^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293912481 10000000000 44067905172037 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (344909359/2000000000 : ℝ)^4575 ≤ (2597139986731/25000000000000 : ℝ)^3551 := by
    have hnat : (344909359 : ℕ)^4575*25000000000000^3551 ≤ 2597139986731^3551*2000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344909359 2000000000 2597139986731 25000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357748797/2500000000 : ℝ)^4575 ≤ (45543534864269/100000000000000 : ℝ)^3551 := by
    have hnat : (1357748797 : ℕ)^4575*100000000000000^3551 ≤ 45543534864269^3551*2500000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357748797 2500000000 45543534864269 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293912481/10000000000 : ℝ), (-344909359/2000000000 : ℝ), (1357748797/2500000000 : ℝ)] ![(44067905172037/100000000000000 : ℝ), (2597139986731/25000000000000 : ℝ), (45543534864269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293912481/10000000000 : ℝ)|^4575 ≤ (44067905172037/100000000000000 : ℝ)^3551
        have hw : |(5293912481/10000000000 : ℝ)|=(5293912481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-344909359/2000000000 : ℝ)|^4575 ≤ (2597139986731/25000000000000 : ℝ)^3551
        have hw : |(-344909359/2000000000 : ℝ)|=(344909359/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1357748797/2500000000 : ℝ)|^4575 ≤ (45543534864269/100000000000000 : ℝ)^3551
        have hw : |(1357748797/2500000000 : ℝ)|=(1357748797/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_s3_6 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (33086953/62500000 : ℝ)*x 0 + (1357748797/2500000000 : ℝ)*x 1 + (-1724546797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33086953/62500000 : ℝ)^4575 ≤ (1377122036291/3125000000000 : ℝ)^3551 := by
    have hnat : (33086953 : ℕ)^4575*3125000000000^3551 ≤ 1377122036291^3551*62500000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33086953 62500000 1377122036291 3125000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1357748797/2500000000 : ℝ)^4575 ≤ (45543534864269/100000000000000 : ℝ)^3551 := by
    have hnat : (1357748797 : ℕ)^4575*100000000000000^3551 ≤ 45543534864269^3551*2500000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357748797 2500000000 45543534864269 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1724546797/10000000000 : ℝ)^4575 ≤ (5194279981223/50000000000000 : ℝ)^3551 := by
    have hnat : (1724546797 : ℕ)^4575*50000000000000^3551 ≤ 5194279981223^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1724546797 10000000000 5194279981223 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33086953/62500000 : ℝ), (1357748797/2500000000 : ℝ), (-1724546797/10000000000 : ℝ)] ![(1377122036291/3125000000000 : ℝ), (45543534864269/100000000000000 : ℝ), (5194279981223/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33086953/62500000 : ℝ)|^4575 ≤ (1377122036291/3125000000000 : ℝ)^3551
        have hw : |(33086953/62500000 : ℝ)|=(33086953/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1357748797/2500000000 : ℝ)|^4575 ≤ (45543534864269/100000000000000 : ℝ)^3551
        have hw : |(1357748797/2500000000 : ℝ)|=(1357748797/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1724546797/10000000000 : ℝ)|^4575 ≤ (5194279981223/50000000000000 : ℝ)^3551
        have hw : |(-1724546797/10000000000 : ℝ)|=(1724546797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_s3_7 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4257203539/10000000000 : ℝ)*x 0 + (4509433919/10000000000 : ℝ)*x 1 + (4016937423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4257203539/10000000000 : ℝ)^4575 ≤ (1663968963621/5000000000000 : ℝ)^3551 := by
    have hnat : (4257203539 : ℕ)^4575*5000000000000^3551 ≤ 1663968963621^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4257203539 10000000000 1663968963621 5000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4509433919/10000000000 : ℝ)^4575 ≤ (35841103975009/100000000000000 : ℝ)^3551 := by
    have hnat : (4509433919 : ℕ)^4575*100000000000000^3551 ≤ 35841103975009^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4509433919 10000000000 35841103975009 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4016937423/10000000000 : ℝ)^4575 ≤ (30879516739279/100000000000000 : ℝ)^3551 := by
    have hnat : (4016937423 : ℕ)^4575*100000000000000^3551 ≤ 30879516739279^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4016937423 10000000000 30879516739279 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4257203539/10000000000 : ℝ), (4509433919/10000000000 : ℝ), (4016937423/10000000000 : ℝ)] ![(1663968963621/5000000000000 : ℝ), (35841103975009/100000000000000 : ℝ), (30879516739279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4257203539/10000000000 : ℝ)|^4575 ≤ (1663968963621/5000000000000 : ℝ)^3551
        have hw : |(4257203539/10000000000 : ℝ)|=(4257203539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4509433919/10000000000 : ℝ)|^4575 ≤ (35841103975009/100000000000000 : ℝ)^3551
        have hw : |(4509433919/10000000000 : ℝ)|=(4509433919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4016937423/10000000000 : ℝ)|^4575 ≤ (30879516739279/100000000000000 : ℝ)^3551
        have hw : |(4016937423/10000000000 : ℝ)|=(4016937423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1539_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165539681/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7951/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1329/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (1097/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3107/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7951/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1329/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7951/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1329/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7951/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1329/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7951/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1329/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7951/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1329/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7951/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1329/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1329/12500 : ℝ) ^ (4573/1024 : ℝ) ≤ (899637080621249/20000000000000000000 : ℝ) := by
    have hpowers : (1329/12500 : ℝ)^4573 ≤ (899637080621249/20000000000000000000 : ℝ)^1024 := by
      have hnat : (1329 : ℕ)^4573*20000000000000000000^1024 ≤ 899637080621249^1024*12500^4573 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1329 12500 899637080621249 20000000000000000000 4573 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1329/12500 : ℝ)) (X := (899637080621249/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4573 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7951/50000 : ℝ) ^ (4573/1024 : ℝ) ≤ (27153574027787929/100000000000000000000 : ℝ) := by
    have hpowers : (7951/50000 : ℝ)^4573 ≤ (27153574027787929/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7951 : ℕ)^4573*100000000000000000000^1024 ≤ 27153574027787929^1024*50000^4573 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7951 50000 27153574027787929 100000000000000000000 4573 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7951/50000 : ℝ)) (X := (27153574027787929/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4573 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000899637080621249/10000000000000000000 : ℝ) ≤ (10000201442425707/10000000000000000 : ℝ) ^ (4573/1024 : ℝ) := by
    have hpowers : (10000899637080621249/10000000000000000000 : ℝ)^1024 ≤ (10000201442425707/10000000000000000 : ℝ)^4573 := by
      have hnat : (10000899637080621249 : ℕ)^1024*10000000000000000^4573 ≤ 10000201442425707^4573*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000899637080621249 10000000000000000000 10000201442425707 10000000000000000 1024 4573 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000201442425707/10000000000000000 : ℝ)) (X := (10000899637080621249/10000000000000000000 : ℝ)) (by norm_num) 4573 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50015825879715447087/50000000000000000000 : ℝ) ≤ (1250088583592833/1250000000000000 : ℝ) ^ (4573/1024 : ℝ) := by
    have hpowers : (50015825879715447087/50000000000000000000 : ℝ)^1024 ≤ (1250088583592833/1250000000000000 : ℝ)^4573 := by
      have hnat : (50015825879715447087 : ℕ)^1024*1250000000000000^4573 ≤ 1250088583592833^4573*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015825879715447087 50000000000000000000 1250088583592833 1250000000000000 1024 4573 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250088583592833/1250000000000000 : ℝ)) (X := (50015825879715447087/50000000000000000000 : ℝ)) (by norm_num) 4573 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027153574027787929/50000000000000000000 : ℝ) ≤ (10001215895059621/10000000000000000 : ℝ) ^ (4573/1024 : ℝ) := by
    have hpowers : (50027153574027787929/50000000000000000000 : ℝ)^1024 ≤ (10001215895059621/10000000000000000 : ℝ)^4573 := by
      have hnat : (50027153574027787929 : ℕ)^1024*10000000000000000^4573 ≤ 10001215895059621^4573*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027153574027787929 50000000000000000000 10001215895059621 10000000000000000 1024 4573 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001215895059621/10000000000000000 : ℝ)) (X := (50027153574027787929/50000000000000000000 : ℝ)) (by norm_num) 4573 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(899637080621249/20000000000000000000 : ℝ) ≤ ((26345137970589851121/26350000000000000000 : ℝ)+2*(507226316957/527000000000000 : ℝ)*(1329/12500 : ℝ))^(4573/1024 : ℝ) := by
    rw [show (26345137970589851121/26350000000000000000 : ℝ)+2*(507226316957/527000000000000 : ℝ)*(1329/12500 : ℝ)=(10000201442425707/10000000000000000 : ℝ) by norm_num, show 1+2*(899637080621249/20000000000000000000 : ℝ)=(10000899637080621249/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27153574027787929/100000000000000000000 : ℝ)+(899637080621249/20000000000000000000 : ℝ) ≤ ((26345137970589851121/26350000000000000000 : ℝ)+(507226316957/527000000000000 : ℝ)*((7951/50000 : ℝ)+(1329/12500 : ℝ)))^(4573/1024 : ℝ) := by
    rw [show (26345137970589851121/26350000000000000000 : ℝ)+(507226316957/527000000000000 : ℝ)*((7951/50000 : ℝ)+(1329/12500 : ℝ))=(1250088583592833/1250000000000000 : ℝ) by norm_num, show 1+(27153574027787929/100000000000000000000 : ℝ)+(899637080621249/20000000000000000000 : ℝ)=(50015825879715447087/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27153574027787929/100000000000000000000 : ℝ) ≤ ((26345137970589851121/26350000000000000000 : ℝ)+2*(507226316957/527000000000000 : ℝ)*(7951/50000 : ℝ))^(4573/1024 : ℝ) := by
    rw [show (26345137970589851121/26350000000000000000 : ℝ)+2*(507226316957/527000000000000 : ℝ)*(7951/50000 : ℝ)=(10001215895059621/10000000000000000 : ℝ) by norm_num, show 1+2*(27153574027787929/100000000000000000000 : ℝ)=(50027153574027787929/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26345137970589851121/26350000000000000000 : ℝ)*(X 1 0+X 2 0)+(507226316957/527000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4573/1024 : ℝ)) (lo := (1329/12500 : ℝ)) (hi := (7951/50000 : ℝ)) (c := (26345137970589851121/26350000000000000000 : ℝ)) (alpha := (507226316957/527000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26345137970589851121/26350000000000000000 : ℝ)*(X 0 1+X 2 1)+(507226316957/527000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4573/1024 : ℝ)) (lo := (1329/12500 : ℝ)) (hi := (7951/50000 : ℝ)) (c := (26345137970589851121/26350000000000000000 : ℝ)) (alpha := (507226316957/527000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26345137970589851121/26350000000000000000 : ℝ)*(X 0 2+X 1 2)+(507226316957/527000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4573/1024 : ℝ)) (lo := (1329/12500 : ℝ)) (hi := (7951/50000 : ℝ)) (c := (26345137970589851121/26350000000000000000 : ℝ)) (alpha := (507226316957/527000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-457123163/2500000000 : ℝ)*X 0 0+(5432142533/10000000000 : ℝ)*X 0 1+(2608363847/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350681503/10000000000 : ℝ)*X 1 0+(-1938814299/10000000000 : ℝ)*X 1 1+(2608363831/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675340761/5000000000 : ℝ)*X 2 0+(2608363823/5000000000 : ℝ)*X 2 1+(-969407147/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4257134797/10000000000 : ℝ)*X 0 0+(802857229/2000000000 : ℝ)*X 0 1+(2256032689/5000000000 : ℝ)*X 0 2+(4257134797/10000000000 : ℝ)*X 1 0+(802857229/2000000000 : ℝ)*X 1 1+(2256032689/5000000000 : ℝ)*X 1 2+(4257134797/10000000000 : ℝ)*X 2 0+(802857229/2000000000 : ℝ)*X 2 1+(2256032689/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-914261191/5000000000 : ℝ)*X 0 0+(163058327/312500000 : ℝ)*X 0 1+(1086199037/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5293912481/10000000000 : ℝ)*X 1 0+(-344909359/2000000000 : ℝ)*X 1 1+(1357748797/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((33086953/62500000 : ℝ)*X 2 0+(1357748797/2500000000 : ℝ)*X 2 1+(-1724546797/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4257203539/10000000000 : ℝ)*X 0 0+(4509433919/10000000000 : ℝ)*X 0 1+(4016937423/10000000000 : ℝ)*X 0 2+(4257203539/10000000000 : ℝ)*X 1 0+(4509433919/10000000000 : ℝ)*X 1 1+(4016937423/10000000000 : ℝ)*X 1 2+(4257203539/10000000000 : ℝ)*X 2 0+(4509433919/10000000000 : ℝ)*X 2 1+(4016937423/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (346378901976974719031704629/65875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (29674831/3125000000000 : ℝ)*(base19) + (92250967/10000000000000 : ℝ)*(base23) + (932501/4000000000000 : ℝ)*(lower2) + (121534087/100000000000000 : ℝ)*(upper3) + (96759907/100000000000000 : ℝ)*(upper5) + (166279281012861/5000000000000 : ℝ)*(major0) + (166279281012861/5000000000000 : ℝ)*(major1) + (166279281012861/5000000000000 : ℝ)*(major2) + (290138788122497/6250000000000 : ℝ)*(sp0) + (2321117246793399/50000000000000 : ℝ)*(sp1) + (116055863016793/2500000000000 : ℝ)*(sp2) + (251116113151111/12500000000000 : ℝ)*(sp3) + (7416610719/50000000000000 : ℝ)*(sp4) + (3358426683/50000000000000 : ℝ)*(sp7) + (1004467811031127/50000000000000 : ℝ)*(f.failure) + (464223544318139/10000000000000 : ℝ)*(f.sum) + (30518493839/41171875000000000000000000 : ℝ)*base66 + (1144971755368382819/131750000000000000000000000000000 : ℝ)*base68 + (626247030574882819/131750000000000000000000000000000 : ℝ)*base70 + (480670290201882819/131750000000000000000000000000000 : ℝ)*base72 + (3233091868083/1317500000000000000000000000 : ℝ)*base74 + (504841982341382819/131750000000000000000000000000000 : ℝ)*base76 + (91791778962382819/131750000000000000000000000000000 : ℝ)*base78 + (763223162304382819/131750000000000000000000000000000 : ℝ)*base80 + (2680477440079/658750000000000000000000000 : ℝ)*base82 + (44650487/5000000000000000000000 : ℝ)*base89 + (44650487/5000000000000000000000 : ℝ)*base91 + (44650487/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15868491904888894532448563697/1317500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (966454377/50000000000000 : ℝ)*(base19) + (2093716291/100000000000000 : ℝ)*(base23) + (250547521/100000000000000 : ℝ)*(upper3) + (36564789/50000000000000 : ℝ)*(lower4) + (248598799/100000000000000 : ℝ)*(upper5) + (3361235095335381/100000000000000 : ℝ)*(major0) + (3361235095335381/100000000000000 : ℝ)*(major1) + (3361235095335381/100000000000000 : ℝ)*(major2) + (29589505733/100000000000000 : ℝ)*(sp1) + (15893033257/50000000000000 : ℝ)*(sp2) + (4691998862201857/100000000000000 : ℝ)*(sp4) + (4691967339787369/100000000000000 : ℝ)*(sp5) + (1172991245604763/25000000000000 : ℝ)*(sp6) + (2030470926989029/100000000000000 : ℝ)*(sp7) + (2030470926989029/100000000000000 : ℝ)*(f.failure) + (4691998862201857/100000000000000 : ℝ)*(f.sum) + (71575222916333/26350000000000000000000000000 : ℝ)*base66 + (27219121786269662101/2635000000000000000000000000000000 : ℝ)*base67 + (8267193985485337899/2635000000000000000000000000000000 : ℝ)*base70 + (13712943076069662101/2635000000000000000000000000000000 : ℝ)*base71 + (41896944856467/26350000000000000000000000000 : ℝ)*base73 + (17118901742159662101/2635000000000000000000000000000000 : ℝ)*base75 + (2159748475269662101/2635000000000000000000000000000000 : ℝ)*base77 + (56670106950337899/2635000000000000000000000000000000 : ℝ)*base80 + (96283471673833/26350000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (51159749/10000000000000000000000 : ℝ)*base89 + (51159749/10000000000000000000000 : ℝ)*base91 + (51159749/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1539_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165539681/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7951/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1329/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1097/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3107/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1539_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1539_s4_0 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-228601741/1250000000 : ℝ)*x 0 + (54300091/100000000 : ℝ)*x 1 + (5218648481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (228601741/1250000000 : ℝ)^4575 ≤ (11204738719781/100000000000000 : ℝ)^3551 := by
    have hnat : (228601741 : ℕ)^4575*100000000000000^3551 ≤ 11204738719781^3551*1250000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228601741 1250000000 11204738719781 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54300091/100000000 : ℝ)^4575 ≤ (22766440685361/50000000000000 : ℝ)^3551 := by
    have hnat : (54300091 : ℕ)^4575*50000000000000^3551 ≤ 22766440685361^3551*100000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54300091 100000000 22766440685361 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218648481/10000000000 : ℝ)^4575 ≤ (10815594972471/25000000000000 : ℝ)^3551 := by
    have hnat : (5218648481 : ℕ)^4575*25000000000000^3551 ≤ 10815594972471^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218648481 10000000000 10815594972471 25000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-228601741/1250000000 : ℝ), (54300091/100000000 : ℝ), (5218648481/10000000000 : ℝ)] ![(11204738719781/100000000000000 : ℝ), (22766440685361/50000000000000 : ℝ), (10815594972471/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-228601741/1250000000 : ℝ)|^4575 ≤ (11204738719781/100000000000000 : ℝ)^3551
        have hw : |(-228601741/1250000000 : ℝ)|=(228601741/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(54300091/100000000 : ℝ)|^4575 ≤ (22766440685361/50000000000000 : ℝ)^3551
        have hw : |(54300091/100000000 : ℝ)|=(54300091/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218648481/10000000000 : ℝ)|^4575 ≤ (10815594972471/25000000000000 : ℝ)^3551
        have hw : |(5218648481/10000000000 : ℝ)|=(5218648481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_s4_1 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267506003/500000000 : ℝ)*x 0 + (-15496089/80000000 : ℝ)*x 1 + (326165523/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267506003/500000000 : ℝ)^4575 ≤ (22335818192083/50000000000000 : ℝ)^3551 := by
    have hnat : (267506003 : ℕ)^4575*50000000000000^3551 ≤ 22335818192083^3551*500000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267506003 500000000 22335818192083 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (15496089/80000000 : ℝ)^4575 ≤ (6032992463689/50000000000000 : ℝ)^3551 := by
    have hnat : (15496089 : ℕ)^4575*50000000000000^3551 ≤ 6032992463689^3551*80000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15496089 80000000 6032992463689 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (326165523/625000000 : ℝ)^4575 ≤ (5407797335373/12500000000000 : ℝ)^3551 := by
    have hnat : (326165523 : ℕ)^4575*12500000000000^3551 ≤ 5407797335373^3551*625000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326165523 625000000 5407797335373 12500000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267506003/500000000 : ℝ), (-15496089/80000000 : ℝ), (326165523/625000000 : ℝ)] ![(22335818192083/50000000000000 : ℝ), (6032992463689/50000000000000 : ℝ), (5407797335373/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267506003/500000000 : ℝ)|^4575 ≤ (22335818192083/50000000000000 : ℝ)^3551
        have hw : |(267506003/500000000 : ℝ)|=(267506003/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-15496089/80000000 : ℝ)|^4575 ≤ (6032992463689/50000000000000 : ℝ)^3551
        have hw : |(-15496089/80000000 : ℝ)|=(15496089/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(326165523/625000000 : ℝ)|^4575 ≤ (5407797335373/12500000000000 : ℝ)^3551
        have hw : |(326165523/625000000 : ℝ)|=(326165523/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_s4_2 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (133753/250000 : ℝ)*x 0 + (2609324213/5000000000 : ℝ)*x 1 + (-1937011127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133753/250000 : ℝ)^4575 ≤ (279197723367/625000000000 : ℝ)^3551 := by
    have hnat : (133753 : ℕ)^4575*625000000000^3551 ≤ 279197723367^3551*250000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133753 250000 279197723367 625000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609324213/5000000000 : ℝ)^4575 ≤ (8652475860491/20000000000000 : ℝ)^3551 := by
    have hnat : (2609324213 : ℕ)^4575*20000000000000^3551 ≤ 8652475860491^3551*5000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609324213 5000000000 8652475860491 20000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1937011127/10000000000 : ℝ)^4575 ≤ (12065984943429/100000000000000 : ℝ)^3551 := by
    have hnat : (1937011127 : ℕ)^4575*100000000000000^3551 ≤ 12065984943429^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1937011127 10000000000 12065984943429 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133753/250000 : ℝ), (2609324213/5000000000 : ℝ), (-1937011127/10000000000 : ℝ)] ![(279197723367/625000000000 : ℝ), (8652475860491/20000000000000 : ℝ), (12065984943429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133753/250000 : ℝ)|^4575 ≤ (279197723367/625000000000 : ℝ)^3551
        have hw : |(133753/250000 : ℝ)|=(133753/250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609324213/5000000000 : ℝ)|^4575 ≤ (8652475860491/20000000000000 : ℝ)^3551
        have hw : |(2609324213/5000000000 : ℝ)|=(2609324213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1937011127/10000000000 : ℝ)|^4575 ≤ (12065984943429/100000000000000 : ℝ)^3551
        have hw : |(-1937011127/10000000000 : ℝ)|=(1937011127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_s4_3 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2128668491/5000000000 : ℝ)*x 0 + (2009473677/5000000000 : ℝ)*x 1 + (450735839/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2128668491/5000000000 : ℝ)^4575 ≤ (33280723240607/100000000000000 : ℝ)^3551 := by
    have hnat : (2128668491 : ℕ)^4575*100000000000000^3551 ≤ 33280723240607^3551*5000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128668491 5000000000 33280723240607 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2009473677/5000000000 : ℝ)^4575 ≤ (15449712385653/50000000000000 : ℝ)^3551 := by
    have hnat : (2009473677 : ℕ)^4575*50000000000000^3551 ≤ 15449712385653^3551*5000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2009473677 5000000000 15449712385653 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (450735839/1000000000 : ℝ)^4575 ≤ (2238740748589/6250000000000 : ℝ)^3551 := by
    have hnat : (450735839 : ℕ)^4575*6250000000000^3551 ≤ 2238740748589^3551*1000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450735839 1000000000 2238740748589 6250000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2128668491/5000000000 : ℝ), (2009473677/5000000000 : ℝ), (450735839/1000000000 : ℝ)] ![(33280723240607/100000000000000 : ℝ), (15449712385653/50000000000000 : ℝ), (2238740748589/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2128668491/5000000000 : ℝ)|^4575 ≤ (33280723240607/100000000000000 : ℝ)^3551
        have hw : |(2128668491/5000000000 : ℝ)|=(2128668491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2009473677/5000000000 : ℝ)|^4575 ≤ (15449712385653/50000000000000 : ℝ)^3551
        have hw : |(2009473677/5000000000 : ℝ)|=(2009473677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(450735839/1000000000 : ℝ)|^4575 ≤ (2238740748589/6250000000000 : ℝ)^3551
        have hw : |(450735839/1000000000 : ℝ)|=(450735839/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_s4_4 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1828842161/10000000000 : ℝ)*x 0 + (652468063/1250000000 : ℝ)*x 1 + (5428904861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1828842161/10000000000 : ℝ)^4575 ≤ (2240992315803/20000000000000 : ℝ)^3551 := by
    have hnat : (1828842161 : ℕ)^4575*20000000000000^3551 ≤ 2240992315803^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1828842161 10000000000 2240992315803 20000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (652468063/1250000000 : ℝ)^4575 ≤ (21637043175223/50000000000000 : ℝ)^3551 := by
    have hnat : (652468063 : ℕ)^4575*50000000000000^3551 ≤ 21637043175223^3551*1250000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652468063 1250000000 21637043175223 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5428904861/10000000000 : ℝ)^4575 ≤ (45520952060039/100000000000000 : ℝ)^3551 := by
    have hnat : (5428904861 : ℕ)^4575*100000000000000^3551 ≤ 45520952060039^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428904861 10000000000 45520952060039 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1828842161/10000000000 : ℝ), (652468063/1250000000 : ℝ), (5428904861/10000000000 : ℝ)] ![(2240992315803/20000000000000 : ℝ), (21637043175223/50000000000000 : ℝ), (45520952060039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1828842161/10000000000 : ℝ)|^4575 ≤ (2240992315803/20000000000000 : ℝ)^3551
        have hw : |(-1828842161/10000000000 : ℝ)|=(1828842161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(652468063/1250000000 : ℝ)|^4575 ≤ (21637043175223/50000000000000 : ℝ)^3551
        have hw : |(652468063/1250000000 : ℝ)|=(652468063/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5428904861/10000000000 : ℝ)|^4575 ≤ (45520952060039/100000000000000 : ℝ)^3551
        have hw : |(5428904861/10000000000 : ℝ)|=(5428904861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_s4_5 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647209883/5000000000 : ℝ)*x 0 + (-1726755497/10000000000 : ℝ)*x 1 + (5428904603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647209883/5000000000 : ℝ)^4575 ≤ (44073345738199/100000000000000 : ℝ)^3551 := by
    have hnat : (2647209883 : ℕ)^4575*100000000000000^3551 ≤ 44073345738199^3551*5000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647209883 5000000000 44073345738199 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1726755497/10000000000 : ℝ)^4575 ≤ (10405704970399/100000000000000 : ℝ)^3551 := by
    have hnat : (1726755497 : ℕ)^4575*100000000000000^3551 ≤ 10405704970399^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1726755497 10000000000 10405704970399 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5428904603/10000000000 : ℝ)^4575 ≤ (711264832389/1562500000000 : ℝ)^3551 := by
    have hnat : (5428904603 : ℕ)^4575*1562500000000^3551 ≤ 711264832389^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428904603 10000000000 711264832389 1562500000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647209883/5000000000 : ℝ), (-1726755497/10000000000 : ℝ), (5428904603/10000000000 : ℝ)] ![(44073345738199/100000000000000 : ℝ), (10405704970399/100000000000000 : ℝ), (711264832389/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647209883/5000000000 : ℝ)|^4575 ≤ (44073345738199/100000000000000 : ℝ)^3551
        have hw : |(2647209883/5000000000 : ℝ)|=(2647209883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1726755497/10000000000 : ℝ)|^4575 ≤ (10405704970399/100000000000000 : ℝ)^3551
        have hw : |(-1726755497/10000000000 : ℝ)|=(1726755497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5428904603/10000000000 : ℝ)|^4575 ≤ (711264832389/1562500000000 : ℝ)^3551
        have hw : |(5428904603/10000000000 : ℝ)|=(5428904603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_s4_6 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058884063/2000000000 : ℝ)*x 0 + (1357226093/2500000000 : ℝ)*x 1 + (-86337753/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058884063/2000000000 : ℝ)^4575 ≤ (22036675813117/50000000000000 : ℝ)^3551 := by
    have hnat : (1058884063 : ℕ)^4575*50000000000000^3551 ≤ 22036675813117^3551*2000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058884063 2000000000 22036675813117 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1357226093/2500000000 : ℝ)^4575 ≤ (45520946777431/100000000000000 : ℝ)^3551 := by
    have hnat : (1357226093 : ℕ)^4575*100000000000000^3551 ≤ 45520946777431^3551*2500000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357226093 2500000000 45520946777431 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (86337753/500000000 : ℝ)^4575 ≤ (5202850788783/50000000000000 : ℝ)^3551 := by
    have hnat : (86337753 : ℕ)^4575*50000000000000^3551 ≤ 5202850788783^3551*500000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86337753 500000000 5202850788783 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058884063/2000000000 : ℝ), (1357226093/2500000000 : ℝ), (-86337753/500000000 : ℝ)] ![(22036675813117/50000000000000 : ℝ), (45520946777431/100000000000000 : ℝ), (5202850788783/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058884063/2000000000 : ℝ)|^4575 ≤ (22036675813117/50000000000000 : ℝ)^3551
        have hw : |(1058884063/2000000000 : ℝ)|=(1058884063/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1357226093/2500000000 : ℝ)|^4575 ≤ (45520946777431/100000000000000 : ℝ)^3551
        have hw : |(1357226093/2500000000 : ℝ)|=(1357226093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-86337753/500000000 : ℝ)|^4575 ≤ (5202850788783/50000000000000 : ℝ)^3551
        have hw : |(-86337753/500000000 : ℝ)|=(86337753/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_s4_7 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2128701051/5000000000 : ℝ)*x 0 + (1126206189/2500000000 : ℝ)*x 1 + (4021499527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2128701051/5000000000 : ℝ)^4575 ≤ (33281379099639/100000000000000 : ℝ)^3551 := by
    have hnat : (2128701051 : ℕ)^4575*100000000000000^3551 ≤ 33281379099639^3551*5000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128701051 5000000000 33281379099639 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1126206189/2500000000 : ℝ)^4575 ≤ (1789695656139/5000000000000 : ℝ)^3551 := by
    have hnat : (1126206189 : ℕ)^4575*5000000000000^3551 ≤ 1789695656139^3551*2500000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126206189 2500000000 1789695656139 5000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4021499527/10000000000 : ℝ)^4575 ≤ (30924707757679/100000000000000 : ℝ)^3551 := by
    have hnat : (4021499527 : ℕ)^4575*100000000000000^3551 ≤ 30924707757679^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4021499527 10000000000 30924707757679 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2128701051/5000000000 : ℝ), (1126206189/2500000000 : ℝ), (4021499527/10000000000 : ℝ)] ![(33281379099639/100000000000000 : ℝ), (1789695656139/5000000000000 : ℝ), (30924707757679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2128701051/5000000000 : ℝ)|^4575 ≤ (33281379099639/100000000000000 : ℝ)^3551
        have hw : |(2128701051/5000000000 : ℝ)|=(2128701051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1126206189/2500000000 : ℝ)|^4575 ≤ (1789695656139/5000000000000 : ℝ)^3551
        have hw : |(1126206189/2500000000 : ℝ)|=(1126206189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4021499527/10000000000 : ℝ)|^4575 ≤ (30924707757679/100000000000000 : ℝ)^3551
        have hw : |(4021499527/10000000000 : ℝ)|=(4021499527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1539_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165539681/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3107/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1097/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (11011/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1549/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3107/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1097/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3107/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1097/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3107/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1097/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3107/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1097/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3107/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1097/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3107/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1097/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1097/10000 : ℝ) ^ (4573/1024 : ℝ) ≤ (5172914039574723/100000000000000000000 : ℝ) := by
    have hpowers : (1097/10000 : ℝ)^4573 ≤ (5172914039574723/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1097 : ℕ)^4573*100000000000000000000^1024 ≤ 5172914039574723^1024*10000^4573 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1097 10000 5172914039574723 100000000000000000000 4573 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1097/10000 : ℝ)) (X := (5172914039574723/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4573 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3107/20000 : ℝ) ^ (4573/1024 : ℝ) ≤ (24464784109305219/100000000000000000000 : ℝ) := by
    have hpowers : (3107/20000 : ℝ)^4573 ≤ (24464784109305219/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3107 : ℕ)^4573*100000000000000000000^1024 ≤ 24464784109305219^1024*20000^4573 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3107 20000 24464784109305219 100000000000000000000 4573 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3107/20000 : ℝ)) (X := (24464784109305219/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4573 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005172914039574723/50000000000000000000 : ℝ) ≤ (10000231657613589/10000000000000000 : ℝ) ^ (4573/1024 : ℝ) := by
    have hpowers : (50005172914039574723/50000000000000000000 : ℝ)^1024 ≤ (10000231657613589/10000000000000000 : ℝ)^4573 := by
      have hnat : (50005172914039574723 : ℕ)^1024*10000000000000000^4573 ≤ 10000231657613589^4573*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005172914039574723 50000000000000000000 10000231657613589 10000000000000000 1024 4573 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000231657613589/10000000000000000 : ℝ)) (X := (50005172914039574723/50000000000000000000 : ℝ)) (by norm_num) 4573 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50014818849074439971/50000000000000000000 : ℝ) ≤ (2500165894998957/2500000000000000 : ℝ) ^ (4573/1024 : ℝ) := by
    have hpowers : (50014818849074439971/50000000000000000000 : ℝ)^1024 ≤ (2500165894998957/2500000000000000 : ℝ)^4573 := by
      have hnat : (50014818849074439971 : ℕ)^1024*2500000000000000^4573 ≤ 2500165894998957^4573*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014818849074439971 50000000000000000000 2500165894998957 2500000000000000 1024 4573 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500165894998957/2500000000000000 : ℝ)) (X := (50014818849074439971/50000000000000000000 : ℝ)) (by norm_num) 4573 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50024464784109305219/50000000000000000000 : ℝ) ≤ (10001095502378067/10000000000000000 : ℝ) ^ (4573/1024 : ℝ) := by
    have hpowers : (50024464784109305219/50000000000000000000 : ℝ)^1024 ≤ (10001095502378067/10000000000000000 : ℝ)^4573 := by
      have hnat : (50024464784109305219 : ℕ)^1024*10000000000000000^4573 ≤ 10001095502378067^4573*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024464784109305219 50000000000000000000 10001095502378067 10000000000000000 1024 4573 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001095502378067/10000000000000000 : ℝ)) (X := (50024464784109305219/50000000000000000000 : ℝ)) (by norm_num) 4573 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5172914039574723/100000000000000000000 : ℝ) ≤ ((365132649119517681/365200000000000000 : ℝ)+2*(431922382239/456500000000000 : ℝ)*(1097/10000 : ℝ))^(4573/1024 : ℝ) := by
    rw [show (365132649119517681/365200000000000000 : ℝ)+2*(431922382239/456500000000000 : ℝ)*(1097/10000 : ℝ)=(10000231657613589/10000000000000000 : ℝ) by norm_num, show 1+2*(5172914039574723/100000000000000000000 : ℝ)=(50005172914039574723/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(24464784109305219/100000000000000000000 : ℝ)+(5172914039574723/100000000000000000000 : ℝ) ≤ ((365132649119517681/365200000000000000 : ℝ)+(431922382239/456500000000000 : ℝ)*((3107/20000 : ℝ)+(1097/10000 : ℝ)))^(4573/1024 : ℝ) := by
    rw [show (365132649119517681/365200000000000000 : ℝ)+(431922382239/456500000000000 : ℝ)*((3107/20000 : ℝ)+(1097/10000 : ℝ))=(2500165894998957/2500000000000000 : ℝ) by norm_num, show 1+(24464784109305219/100000000000000000000 : ℝ)+(5172914039574723/100000000000000000000 : ℝ)=(50014818849074439971/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(24464784109305219/100000000000000000000 : ℝ) ≤ ((365132649119517681/365200000000000000 : ℝ)+2*(431922382239/456500000000000 : ℝ)*(3107/20000 : ℝ))^(4573/1024 : ℝ) := by
    rw [show (365132649119517681/365200000000000000 : ℝ)+2*(431922382239/456500000000000 : ℝ)*(3107/20000 : ℝ)=(10001095502378067/10000000000000000 : ℝ) by norm_num, show 1+2*(24464784109305219/100000000000000000000 : ℝ)=(50024464784109305219/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (365132649119517681/365200000000000000 : ℝ)*(X 1 0+X 2 0)+(431922382239/456500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4573/1024 : ℝ)) (lo := (1097/10000 : ℝ)) (hi := (3107/20000 : ℝ)) (c := (365132649119517681/365200000000000000 : ℝ)) (alpha := (431922382239/456500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (365132649119517681/365200000000000000 : ℝ)*(X 0 1+X 2 1)+(431922382239/456500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4573/1024 : ℝ)) (lo := (1097/10000 : ℝ)) (hi := (3107/20000 : ℝ)) (c := (365132649119517681/365200000000000000 : ℝ)) (alpha := (431922382239/456500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (365132649119517681/365200000000000000 : ℝ)*(X 0 2+X 1 2)+(431922382239/456500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4573/1024 : ℝ)) (lo := (1097/10000 : ℝ)) (hi := (3107/20000 : ℝ)) (c := (365132649119517681/365200000000000000 : ℝ)) (alpha := (431922382239/456500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-228601741/1250000000 : ℝ)*X 0 0+(54300091/100000000 : ℝ)*X 0 1+(5218648481/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267506003/500000000 : ℝ)*X 1 0+(-15496089/80000000 : ℝ)*X 1 1+(326165523/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((133753/250000 : ℝ)*X 2 0+(2609324213/5000000000 : ℝ)*X 2 1+(-1937011127/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2128668491/5000000000 : ℝ)*X 0 0+(2009473677/5000000000 : ℝ)*X 0 1+(450735839/1000000000 : ℝ)*X 0 2+(2128668491/5000000000 : ℝ)*X 1 0+(2009473677/5000000000 : ℝ)*X 1 1+(450735839/1000000000 : ℝ)*X 1 2+(2128668491/5000000000 : ℝ)*X 2 0+(2009473677/5000000000 : ℝ)*X 2 1+(450735839/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1828842161/10000000000 : ℝ)*X 0 0+(652468063/1250000000 : ℝ)*X 0 1+(5428904861/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647209883/5000000000 : ℝ)*X 1 0+(-1726755497/10000000000 : ℝ)*X 1 1+(5428904603/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1058884063/2000000000 : ℝ)*X 2 0+(1357226093/2500000000 : ℝ)*X 2 1+(-86337753/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2128701051/5000000000 : ℝ)*X 0 0+(1126206189/2500000000 : ℝ)*X 0 1+(4021499527/10000000000 : ℝ)*X 0 2+(2128701051/5000000000 : ℝ)*X 1 0+(1126206189/2500000000 : ℝ)*X 1 1+(4021499527/10000000000 : ℝ)*X 1 2+(2128701051/5000000000 : ℝ)*X 2 0+(1126206189/2500000000 : ℝ)*X 2 1+(4021499527/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (151850092592575422518553/22825000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1269977687/100000000000000 : ℝ)*(base19) + (571453353/50000000000000 : ℝ)*(base23) + (39596783/100000000000000 : ℝ)*(lower2) + (176436831/100000000000000 : ℝ)*(upper3) + (27968817/25000000000000 : ℝ)*(upper5) + (847345103440871/25000000000000 : ℝ)*(major0) + (847345103440871/25000000000000 : ℝ)*(major1) + (847345103440871/25000000000000 : ℝ)*(major2) + (118281739371271/2500000000000 : ℝ)*(sp0) + (946257250122399/20000000000000 : ℝ)*(sp1) + (4731286377682977/100000000000000 : ℝ)*(sp2) + (25593299841361/1250000000000 : ℝ)*(sp3) + (17945738843/100000000000000 : ℝ)*(sp4) + (1819573699/20000000000000 : ℝ)*(sp7) + (1023736542588687/50000000000000 : ℝ)*(f.failure) + (2365643760294841/50000000000000 : ℝ)*(f.sum) + (78257418545901/22825000000000000000000000000 : ℝ)*base65 + (63825067032884649/9130000000000000000000000000000 : ℝ)*base68 + (36436128997964649/9130000000000000000000000000000 : ℝ)*base70 + (15872367019175351/9130000000000000000000000000000 : ℝ)*base71 + (78468251795449/22825000000000000000000000000 : ℝ)*base74 + (2446858370425351/9130000000000000000000000000000 : ℝ)*base75 + (41608738680175351/9130000000000000000000000000000 : ℝ)*base77 + (74204337075784649/9130000000000000000000000000000 : ℝ)*base80 + (23496272659887/11412500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (39811153/5000000000000000000000 : ℝ)*base90 + (39811153/5000000000000000000000 : ℝ)*base92 + (39811153/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (68044126952607288919596363/9130000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (172335039/20000000000000 : ℝ)*(base19) + (1469716019/100000000000000 : ℝ)*(base23) + (11184297/10000000000000 : ℝ)*(upper3) + (19495993/100000000000000 : ℝ)*(lower4) + (322214419/100000000000000 : ℝ)*(upper5) + (3425014728360359/100000000000000 : ℝ)*(major0) + (3425014728360359/100000000000000 : ℝ)*(major1) + (3425014728360359/100000000000000 : ℝ)*(major2) + (3773643363/50000000000000 : ℝ)*(sp1) + (14719380551/100000000000000 : ℝ)*(sp2) + (956205995281101/20000000000000 : ℝ)*(sp4) + (37351730995653/781250000000 : ℝ)*(sp5) + (956202757461787/20000000000000 : ℝ)*(sp6) + (206899923188831/10000000000000 : ℝ)*(sp7) + (206899923188831/10000000000000 : ℝ)*(f.failure) + (956205995281101/20000000000000 : ℝ)*(f.sum) + (17251454500537/11412500000000000000000000000 : ℝ)*base66 + (274195034593448279/36520000000000000000000000000000 : ℝ)*base67 + (136555087980048279/36520000000000000000000000000000 : ℝ)*base69 + (19726024874568279/36520000000000000000000000000000 : ℝ)*base71 + (122257751951151/22825000000000000000000000000 : ℝ)*base73 + (421896054772248279/36520000000000000000000000000000 : ℝ)*base75 + (253551547115648279/36520000000000000000000000000000 : ℝ)*base77 + (277557598996071721/36520000000000000000000000000000 : ℝ)*base80 + (15508868362231/5706250000000000000000000000 : ℝ)*base82 + (3497089/1000000000000000000000 : ℝ)*base90 + (3497089/1000000000000000000000 : ℝ)*base92 + (3497089/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1539_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165539681/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3107/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1097/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11011/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1539_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1539_s5_0 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-365770237/2000000000 : ℝ)*x 0 + (339360489/625000000 : ℝ)*x 1 + (5218864997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (365770237/2000000000 : ℝ)^4575 ≤ (11205032810823/100000000000000 : ℝ)^3551 := by
    have hnat : (365770237 : ℕ)^4575*100000000000000^3551 ≤ 11205032810823^3551*2000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      365770237 2000000000 11205032810823 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339360489/625000000 : ℝ)^4575 ≤ (45530274758997/100000000000000 : ℝ)^3551 := by
    have hnat : (339360489 : ℕ)^4575*100000000000000^3551 ≤ 45530274758997^3551*625000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339360489 625000000 45530274758997 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218864997/10000000000 : ℝ)^4575 ≤ (8652938481853/20000000000000 : ℝ)^3551 := by
    have hnat : (5218864997 : ℕ)^4575*20000000000000^3551 ≤ 8652938481853^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218864997 10000000000 8652938481853 20000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-365770237/2000000000 : ℝ), (339360489/625000000 : ℝ), (5218864997/10000000000 : ℝ)] ![(11205032810823/100000000000000 : ℝ), (45530274758997/100000000000000 : ℝ), (8652938481853/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-365770237/2000000000 : ℝ)|^4575 ≤ (11205032810823/100000000000000 : ℝ)^3551
        have hw : |(-365770237/2000000000 : ℝ)|=(365770237/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(339360489/625000000 : ℝ)|^4575 ≤ (45530274758997/100000000000000 : ℝ)^3551
        have hw : |(339360489/625000000 : ℝ)|=(339360489/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218864997/10000000000 : ℝ)|^4575 ≤ (8652938481853/20000000000000 : ℝ)^3551
        have hw : |(5218864997/10000000000 : ℝ)|=(5218864997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_s5_1 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070011219/2000000000 : ℝ)*x 0 + (-38736173/200000000 : ℝ)*x 1 + (1304716233/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070011219/2000000000 : ℝ)^4575 ≤ (5583868535747/12500000000000 : ℝ)^3551 := by
    have hnat : (1070011219 : ℕ)^4575*12500000000000^3551 ≤ 5583868535747^3551*2000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070011219 2000000000 5583868535747 12500000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (38736173/200000000 : ℝ)^4575 ≤ (6032179996267/50000000000000 : ℝ)^3551 := by
    have hnat : (38736173 : ℕ)^4575*50000000000000^3551 ≤ 6032179996267^3551*200000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38736173 200000000 6032179996267 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304716233/2500000000 : ℝ)^4575 ≤ (21632345857511/50000000000000 : ℝ)^3551 := by
    have hnat : (1304716233 : ℕ)^4575*50000000000000^3551 ≤ 21632345857511^3551*2500000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304716233 2500000000 21632345857511 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070011219/2000000000 : ℝ), (-38736173/200000000 : ℝ), (1304716233/2500000000 : ℝ)] ![(5583868535747/12500000000000 : ℝ), (6032179996267/50000000000000 : ℝ), (21632345857511/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070011219/2000000000 : ℝ)|^4575 ≤ (5583868535747/12500000000000 : ℝ)^3551
        have hw : |(1070011219/2000000000 : ℝ)|=(1070011219/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-38736173/200000000 : ℝ)|^4575 ≤ (6032179996267/50000000000000 : ℝ)^3551
        have hw : |(-38736173/200000000 : ℝ)|=(38736173/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304716233/2500000000 : ℝ)|^4575 ≤ (21632345857511/50000000000000 : ℝ)^3551
        have hw : |(1304716233/2500000000 : ℝ)|=(1304716233/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_s5_2 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350056057/10000000000 : ℝ)*x 0 + (326179061/625000000 : ℝ)*x 1 + (-1936808641/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350056057/10000000000 : ℝ)^4575 ≤ (8934189575439/20000000000000 : ℝ)^3551 := by
    have hnat : (5350056057 : ℕ)^4575*20000000000000^3551 ≤ 8934189575439^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350056057 10000000000 8934189575439 20000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (326179061/625000000 : ℝ)^4575 ≤ (43264692184971/100000000000000 : ℝ)^3551 := by
    have hnat : (326179061 : ℕ)^4575*100000000000000^3551 ≤ 43264692184971^3551*625000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326179061 625000000 43264692184971 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1936808641/10000000000 : ℝ)^4575 ≤ (12064359920307/100000000000000 : ℝ)^3551 := by
    have hnat : (1936808641 : ℕ)^4575*100000000000000^3551 ≤ 12064359920307^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1936808641 10000000000 12064359920307 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350056057/10000000000 : ℝ), (326179061/625000000 : ℝ), (-1936808641/10000000000 : ℝ)] ![(8934189575439/20000000000000 : ℝ), (43264692184971/100000000000000 : ℝ), (12064359920307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350056057/10000000000 : ℝ)|^4575 ≤ (8934189575439/20000000000000 : ℝ)^3551
        have hw : |(5350056057/10000000000 : ℝ)|=(5350056057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(326179061/625000000 : ℝ)|^4575 ≤ (43264692184971/100000000000000 : ℝ)^3551
        have hw : |(326179061/625000000 : ℝ)|=(326179061/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1936808641/10000000000 : ℝ)|^4575 ≤ (12064359920307/100000000000000 : ℝ)^3551
        have hw : |(-1936808641/10000000000 : ℝ)|=(1936808641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_s5_3 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (851471917/2000000000 : ℝ)*x 0 + (4019473683/10000000000 : ℝ)*x 1 + (4506826931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (851471917/2000000000 : ℝ)^4575 ≤ (16640475443709/50000000000000 : ℝ)^3551 := by
    have hnat : (851471917 : ℕ)^4575*50000000000000^3551 ≤ 16640475443709^3551*2000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      851471917 2000000000 16640475443709 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4019473683/10000000000 : ℝ)^4575 ≤ (30904638446883/100000000000000 : ℝ)^3551 := by
    have hnat : (4019473683 : ℕ)^4575*100000000000000^3551 ≤ 30904638446883^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4019473683 10000000000 30904638446883 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4506826931/10000000000 : ℝ)^4575 ≤ (17907205327227/50000000000000 : ℝ)^3551 := by
    have hnat : (4506826931 : ℕ)^4575*50000000000000^3551 ≤ 17907205327227^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506826931 10000000000 17907205327227 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(851471917/2000000000 : ℝ), (4019473683/10000000000 : ℝ), (4506826931/10000000000 : ℝ)] ![(16640475443709/50000000000000 : ℝ), (30904638446883/100000000000000 : ℝ), (17907205327227/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(851471917/2000000000 : ℝ)|^4575 ≤ (16640475443709/50000000000000 : ℝ)^3551
        have hw : |(851471917/2000000000 : ℝ)|=(851471917/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4019473683/10000000000 : ℝ)|^4575 ≤ (30904638446883/100000000000000 : ℝ)^3551
        have hw : |(4019473683/10000000000 : ℝ)|=(4019473683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4506826931/10000000000 : ℝ)|^4575 ≤ (17907205327227/50000000000000 : ℝ)^3551
        have hw : |(4506826931/10000000000 : ℝ)|=(4506826931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_s5_4 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-457219767/2500000000 : ℝ)*x 0 + (2609978339/5000000000 : ℝ)*x 1 + (5428668107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (457219767/2500000000 : ℝ)^4575 ≤ (5602626454297/50000000000000 : ℝ)^3551 := by
    have hnat : (457219767 : ℕ)^4575*50000000000000^3551 ≤ 5602626454297^3551*2500000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      457219767 2500000000 5602626454297 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609978339/5000000000 : ℝ)^4575 ≤ (43276352631651/100000000000000 : ℝ)^3551 := by
    have hnat : (2609978339 : ℕ)^4575*100000000000000^3551 ≤ 43276352631651^3551*5000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609978339 5000000000 43276352631651 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5428668107/10000000000 : ℝ)^4575 ≤ (11379598612797/25000000000000 : ℝ)^3551 := by
    have hnat : (5428668107 : ℕ)^4575*25000000000000^3551 ≤ 11379598612797^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428668107 10000000000 11379598612797 25000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-457219767/2500000000 : ℝ), (2609978339/5000000000 : ℝ), (5428668107/10000000000 : ℝ)] ![(5602626454297/50000000000000 : ℝ), (43276352631651/100000000000000 : ℝ), (11379598612797/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-457219767/2500000000 : ℝ)|^4575 ≤ (5602626454297/50000000000000 : ℝ)^3551
        have hw : |(-457219767/2500000000 : ℝ)|=(457219767/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609978339/5000000000 : ℝ)|^4575 ≤ (43276352631651/100000000000000 : ℝ)^3551
        have hw : |(2609978339/5000000000 : ℝ)|=(2609978339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5428668107/10000000000 : ℝ)|^4575 ≤ (11379598612797/25000000000000 : ℝ)^3551
        have hw : |(5428668107/10000000000 : ℝ)|=(5428668107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_s5_5 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294477049/10000000000 : ℝ)*x 0 + (-345401091/2000000000 : ℝ)*x 1 + (1085733617/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294477049/10000000000 : ℝ)^4575 ≤ (11018490025107/25000000000000 : ℝ)^3551 := by
    have hnat : (5294477049 : ℕ)^4575*25000000000000^3551 ≤ 11018490025107^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294477049 10000000000 11018490025107 25000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (345401091/2000000000 : ℝ)^4575 ≤ (650477854061/6250000000000 : ℝ)^3551 := by
    have hnat : (345401091 : ℕ)^4575*6250000000000^3551 ≤ 650477854061^3551*2000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345401091 2000000000 650477854061 6250000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1085733617/2000000000 : ℝ)^4575 ≤ (5689799276691/12500000000000 : ℝ)^3551 := by
    have hnat : (1085733617 : ℕ)^4575*12500000000000^3551 ≤ 5689799276691^3551*2000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085733617 2000000000 5689799276691 12500000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294477049/10000000000 : ℝ), (-345401091/2000000000 : ℝ), (1085733617/2000000000 : ℝ)] ![(11018490025107/25000000000000 : ℝ), (650477854061/6250000000000 : ℝ), (5689799276691/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294477049/10000000000 : ℝ)|^4575 ≤ (11018490025107/25000000000000 : ℝ)^3551
        have hw : |(5294477049/10000000000 : ℝ)|=(5294477049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-345401091/2000000000 : ℝ)|^4575 ≤ (650477854061/6250000000000 : ℝ)^3551
        have hw : |(-345401091/2000000000 : ℝ)|=(345401091/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1085733617/2000000000 : ℝ)|^4575 ≤ (5689799276691/12500000000000 : ℝ)^3551
        have hw : |(1085733617/2000000000 : ℝ)|=(1085733617/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_s5_6 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647238509/5000000000 : ℝ)*x 0 + (1357167027/2500000000 : ℝ)*x 1 + (-1727005467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647238509/5000000000 : ℝ)^4575 ≤ (44073959767951/100000000000000 : ℝ)^3551 := by
    have hnat : (2647238509 : ℕ)^4575*100000000000000^3551 ≤ 44073959767951^3551*5000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647238509 5000000000 44073959767951 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1357167027/2500000000 : ℝ)^4575 ≤ (45518394461991/100000000000000 : ℝ)^3551 := by
    have hnat : (1357167027 : ℕ)^4575*100000000000000^3551 ≤ 45518394461991^3551*2500000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357167027 2500000000 45518394461991 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1727005467/10000000000 : ℝ)^4575 ≤ (10407645758147/100000000000000 : ℝ)^3551 := by
    have hnat : (1727005467 : ℕ)^4575*100000000000000^3551 ≤ 10407645758147^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1727005467 10000000000 10407645758147 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647238509/5000000000 : ℝ), (1357167027/2500000000 : ℝ), (-1727005467/10000000000 : ℝ)] ![(44073959767951/100000000000000 : ℝ), (45518394461991/100000000000000 : ℝ), (10407645758147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647238509/5000000000 : ℝ)|^4575 ≤ (44073959767951/100000000000000 : ℝ)^3551
        have hw : |(2647238509/5000000000 : ℝ)|=(2647238509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1357167027/2500000000 : ℝ)|^4575 ≤ (45518394461991/100000000000000 : ℝ)^3551
        have hw : |(1357167027/2500000000 : ℝ)|=(1357167027/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1727005467/10000000000 : ℝ)|^4575 ≤ (10407645758147/100000000000000 : ℝ)^3551
        have hw : |(-1727005467/10000000000 : ℝ)|=(1727005467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_s5_7 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1064356007/2500000000 : ℝ)*x 0 + (563038017/1250000000 : ℝ)*x 1 + (100550379/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1064356007/2500000000 : ℝ)^4575 ≤ (33281599928993/100000000000000 : ℝ)^3551 := by
    have hnat : (1064356007 : ℕ)^4575*100000000000000^3551 ≤ 33281599928993^3551*2500000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064356007 2500000000 33281599928993 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (563038017/1250000000 : ℝ)^4575 ≤ (7157716727381/20000000000000 : ℝ)^3551 := by
    have hnat : (563038017 : ℕ)^4575*20000000000000^3551 ≤ 7157716727381^3551*1250000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563038017 1250000000 7157716727381 20000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (100550379/250000000 : ℝ)^4575 ≤ (15464908207317/50000000000000 : ℝ)^3551 := by
    have hnat : (100550379 : ℕ)^4575*50000000000000^3551 ≤ 15464908207317^3551*250000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100550379 250000000 15464908207317 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1064356007/2500000000 : ℝ), (563038017/1250000000 : ℝ), (100550379/250000000 : ℝ)] ![(33281599928993/100000000000000 : ℝ), (7157716727381/20000000000000 : ℝ), (15464908207317/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1064356007/2500000000 : ℝ)|^4575 ≤ (33281599928993/100000000000000 : ℝ)^3551
        have hw : |(1064356007/2500000000 : ℝ)|=(1064356007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(563038017/1250000000 : ℝ)|^4575 ≤ (7157716727381/20000000000000 : ℝ)^3551
        have hw : |(563038017/1250000000 : ℝ)|=(563038017/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(100550379/250000000 : ℝ)|^4575 ≤ (15464908207317/50000000000000 : ℝ)^3551
        have hw : |(100550379/250000000 : ℝ)|=(100550379/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1539_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165539681/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11011/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1377/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3097/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11011/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11011/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11011/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11011/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11011/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11011/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11011/100000 : ℝ) ^ (4573/1024 : ℝ) ≤ (328738455987361/6250000000000000000 : ℝ) := by
    have hpowers : (11011/100000 : ℝ)^4573 ≤ (328738455987361/6250000000000000000 : ℝ)^1024 := by
      have hnat : (11011 : ℕ)^4573*6250000000000000000^1024 ≤ 328738455987361^1024*100000^4573 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11011 100000 328738455987361 6250000000000000000 4573 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11011/100000 : ℝ)) (X := (328738455987361/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4573 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1549/10000 : ℝ) ^ (4573/1024 : ℝ) ≤ (12074945345275509/50000000000000000000 : ℝ) := by
    have hpowers : (1549/10000 : ℝ)^4573 ≤ (12074945345275509/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1549 : ℕ)^4573*50000000000000000000^1024 ≤ 12074945345275509^1024*10000^4573 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1549 10000 12074945345275509 50000000000000000000 4573 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1549/10000 : ℝ)) (X := (12074945345275509/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4573 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125328738455987361/3125000000000000000 : ℝ) ≤ (10000235549136971/10000000000000000 : ℝ) ^ (4573/1024 : ℝ) := by
    have hpowers : (3125328738455987361/3125000000000000000 : ℝ)^1024 ≤ (10000235549136971/10000000000000000 : ℝ)^4573 := by
      have hnat : (3125328738455987361 : ℕ)^1024*10000000000000000^4573 ≤ 10000235549136971^4573*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125328738455987361 3125000000000000000 10000235549136971 10000000000000000 1024 4573 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000235549136971/10000000000000000 : ℝ)) (X := (3125328738455987361/3125000000000000000 : ℝ)) (by norm_num) 4573 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50014704852993174397/50000000000000000000 : ℝ) ≤ (1000065847589577/1000000000000000 : ℝ) ^ (4573/1024 : ℝ) := by
    have hpowers : (50014704852993174397/50000000000000000000 : ℝ)^1024 ≤ (1000065847589577/1000000000000000 : ℝ)^4573 := by
      have hnat : (50014704852993174397 : ℕ)^1024*1000000000000000^4573 ≤ 1000065847589577^4573*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014704852993174397 50000000000000000000 1000065847589577 1000000000000000 1024 4573 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000065847589577/1000000000000000 : ℝ)) (X := (50014704852993174397/50000000000000000000 : ℝ)) (by norm_num) 4573 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25012074945345275509/25000000000000000000 : ℝ) ≤ (10001081402654569/10000000000000000 : ℝ) ^ (4573/1024 : ℝ) := by
    have hpowers : (25012074945345275509/25000000000000000000 : ℝ)^1024 ≤ (10001081402654569/10000000000000000 : ℝ)^4573 := by
      have hnat : (25012074945345275509 : ℕ)^1024*10000000000000000^4573 ≤ 10001081402654569^4573*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012074945345275509 25000000000000000000 10001081402654569 10000000000000000 1024 4573 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001081402654569/10000000000000000 : ℝ)) (X := (25012074945345275509/25000000000000000000 : ℝ)) (by norm_num) 4573 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(328738455987361/6250000000000000000 : ℝ) ≤ ((44781741331502221531/44790000000000000000 : ℝ)+2*(422926758799/447900000000000 : ℝ)*(11011/100000 : ℝ))^(4573/1024 : ℝ) := by
    rw [show (44781741331502221531/44790000000000000000 : ℝ)+2*(422926758799/447900000000000 : ℝ)*(11011/100000 : ℝ)=(10000235549136971/10000000000000000 : ℝ) by norm_num, show 1+2*(328738455987361/6250000000000000000 : ℝ)=(3125328738455987361/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(12074945345275509/50000000000000000000 : ℝ)+(328738455987361/6250000000000000000 : ℝ) ≤ ((44781741331502221531/44790000000000000000 : ℝ)+(422926758799/447900000000000 : ℝ)*((1549/10000 : ℝ)+(11011/100000 : ℝ)))^(4573/1024 : ℝ) := by
    rw [show (44781741331502221531/44790000000000000000 : ℝ)+(422926758799/447900000000000 : ℝ)*((1549/10000 : ℝ)+(11011/100000 : ℝ))=(1000065847589577/1000000000000000 : ℝ) by norm_num, show 1+(12074945345275509/50000000000000000000 : ℝ)+(328738455987361/6250000000000000000 : ℝ)=(50014704852993174397/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(12074945345275509/50000000000000000000 : ℝ) ≤ ((44781741331502221531/44790000000000000000 : ℝ)+2*(422926758799/447900000000000 : ℝ)*(1549/10000 : ℝ))^(4573/1024 : ℝ) := by
    rw [show (44781741331502221531/44790000000000000000 : ℝ)+2*(422926758799/447900000000000 : ℝ)*(1549/10000 : ℝ)=(10001081402654569/10000000000000000 : ℝ) by norm_num, show 1+2*(12074945345275509/50000000000000000000 : ℝ)=(25012074945345275509/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (44781741331502221531/44790000000000000000 : ℝ)*(X 1 0+X 2 0)+(422926758799/447900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4573/1024 : ℝ)) (lo := (11011/100000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (44781741331502221531/44790000000000000000 : ℝ)) (alpha := (422926758799/447900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (44781741331502221531/44790000000000000000 : ℝ)*(X 0 1+X 2 1)+(422926758799/447900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4573/1024 : ℝ)) (lo := (11011/100000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (44781741331502221531/44790000000000000000 : ℝ)) (alpha := (422926758799/447900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (44781741331502221531/44790000000000000000 : ℝ)*(X 0 2+X 1 2)+(422926758799/447900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4573/1024 : ℝ)) (lo := (11011/100000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (44781741331502221531/44790000000000000000 : ℝ)) (alpha := (422926758799/447900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-365770237/2000000000 : ℝ)*X 0 0+(339360489/625000000 : ℝ)*X 0 1+(5218864997/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070011219/2000000000 : ℝ)*X 1 0+(-38736173/200000000 : ℝ)*X 1 1+(1304716233/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350056057/10000000000 : ℝ)*X 2 0+(326179061/625000000 : ℝ)*X 2 1+(-1936808641/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((851471917/2000000000 : ℝ)*X 0 0+(4019473683/10000000000 : ℝ)*X 0 1+(4506826931/10000000000 : ℝ)*X 0 2+(851471917/2000000000 : ℝ)*X 1 0+(4019473683/10000000000 : ℝ)*X 1 1+(4506826931/10000000000 : ℝ)*X 1 2+(851471917/2000000000 : ℝ)*X 2 0+(4019473683/10000000000 : ℝ)*X 2 1+(4506826931/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-457219767/2500000000 : ℝ)*X 0 0+(2609978339/5000000000 : ℝ)*X 0 1+(5428668107/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294477049/10000000000 : ℝ)*X 1 0+(-345401091/2000000000 : ℝ)*X 1 1+(1085733617/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647238509/5000000000 : ℝ)*X 2 0+(1357167027/2500000000 : ℝ)*X 2 1+(-1727005467/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1064356007/2500000000 : ℝ)*X 0 0+(563038017/1250000000 : ℝ)*X 0 1+(100550379/250000000 : ℝ)*X 0 2+(1064356007/2500000000 : ℝ)*X 1 0+(563038017/1250000000 : ℝ)*X 1 1+(100550379/250000000 : ℝ)*X 1 2+(1064356007/2500000000 : ℝ)*X 2 0+(563038017/1250000000 : ℝ)*X 2 1+(100550379/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2383286319688596850417/746500000000000000000000000 : ℝ) := by norm_num
    linear_combination (134682599/25000000000000 : ℝ)*(base19) + (47856411/10000000000000 : ℝ)*(base23) + (7085737/50000000000000 : ℝ)*(lower2) + (87322607/100000000000000 : ℝ)*(upper3) + (355387/500000000000 : ℝ)*(upper5) + (6793440964877/200000000000 : ℝ)*(major0) + (6793440964877/200000000000 : ℝ)*(major1) + (6793440964877/200000000000 : ℝ)*(major2) + (948305420750283/20000000000000 : ℝ)*(sp0) + (4741533210856871/100000000000000 : ℝ)*(sp1) + (1185383317755789/25000000000000 : ℝ)*(sp2) + (410380662174709/20000000000000 : ℝ)*(sp3) + (1661458963/25000000000000 : ℝ)*(sp4) + (1898997859/50000000000000 : ℝ)*(sp7) + (2051907108869263/100000000000000 : ℝ)*(f.failure) + (2370766874793633/50000000000000 : ℝ)*(f.sum) + (2018226361939/2239500000000000000000000000 : ℝ)*base65 + (42358274321575313/8958000000000000000000000000000 : ℝ)*base68 + (21303585465385313/8958000000000000000000000000000 : ℝ)*base70 + (27165266023225313/8958000000000000000000000000000 : ℝ)*base72 + (14207873719807/4479000000000000000000000000 : ℝ)*base74 + (28047336761440687/8958000000000000000000000000000 : ℝ)*base75 + (13334952493948687/8958000000000000000000000000000 : ℝ)*base77 + (90823056051304687/8958000000000000000000000000000 : ℝ)*base79 + (7038170663341/4479000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (67725103/10000000000000000000000 : ℝ)*base89 + (67725103/10000000000000000000000 : ℝ)*base91 + (67725103/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (719665537038852544250288757/93312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9940377/800000000000 : ℝ)*(base19) + (163157589/12500000000000 : ℝ)*(base23) + (404337647/100000000000000 : ℝ)*(lower1) + (9570691/6250000000000 : ℝ)*(upper3) + (8794863/20000000000000 : ℝ)*(lower4) + (81954167/50000000000000 : ℝ)*(upper5) + (429045097855347/12500000000000 : ℝ)*(major0) + (429045097855347/12500000000000 : ℝ)*(major1) + (429045097855347/12500000000000 : ℝ)*(major2) + (734489919/100000000000000 : ℝ)*(sp2) + (4791284437089471/100000000000000 : ℝ)*(sp4) + (2395641597271173/50000000000000 : ℝ)*(sp5) + (119782059933471/2500000000000 : ℝ)*(sp6) + (2073436871515281/100000000000000 : ℝ)*(sp7) + (2073436871515281/100000000000000 : ℝ)*(f.failure) + (4791284437089471/100000000000000 : ℝ)*(f.sum) + (57828537807/29160156250000000000000000 : ℝ)*base66 + (1761633337094524581/186625000000000000000000000000000 : ℝ)*base68 + (53122756420600419/186625000000000000000000000000000 : ℝ)*base69 + (5883143681735024581/186625000000000000000000000000000 : ℝ)*base72 + (19650348432741/3732500000000000000000000000 : ℝ)*base74 + (7558942598255524581/186625000000000000000000000000000 : ℝ)*base76 + (234854364567149581/186625000000000000000000000000000 : ℝ)*base78 + (1365836936815725419/186625000000000000000000000000000 : ℝ)*base79 + (1378873960543/7465000000000000000000000000 : ℝ)*base81 + (3365361/10000000000000000000000 : ℝ)*base89 + (3365361/10000000000000000000000 : ℝ)*base91 + (3365361/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1539_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165539681/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11011/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1377/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1539_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1539_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165539681/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7951/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1329/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1377/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1539_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1539_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1539_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165539681/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7951/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1329/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1377/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1539_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
