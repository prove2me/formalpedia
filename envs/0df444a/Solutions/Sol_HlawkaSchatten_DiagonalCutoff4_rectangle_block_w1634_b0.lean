-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1634_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:00:53.715984+00:00
-- url     : https://prove2.me/submissions/4353a1cc-2e55-4041-b9c5-64a1fbde31af

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
theorem support_rectangle_w1634_s0_0 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-60846087/400000000 : ℝ)*x 0 + (1451368879/2500000000 : ℝ)*x 1 + (2455237291/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (60846087/400000000 : ℝ)^4855 ≤ (1839090180599/20000000000000 : ℝ)^3831 := by
    have hnat : (60846087 : ℕ)^4855*20000000000000^3831 ≤ 1839090180599^3831*400000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60846087 400000000 1839090180599 20000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1451368879/2500000000 : ℝ)^4855 ≤ (25100551674477/50000000000000 : ℝ)^3831 := by
    have hnat : (1451368879 : ℕ)^4855*50000000000000^3831 ≤ 25100551674477^3831*2500000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1451368879 2500000000 25100551674477 50000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2455237291/5000000000 : ℝ)^4855 ≤ (1268857678941/3125000000000 : ℝ)^3831 := by
    have hnat : (2455237291 : ℕ)^4855*3125000000000^3831 ≤ 1268857678941^3831*5000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2455237291 5000000000 1268857678941 3125000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-60846087/400000000 : ℝ), (1451368879/2500000000 : ℝ), (2455237291/5000000000 : ℝ)] ![(1839090180599/20000000000000 : ℝ), (25100551674477/50000000000000 : ℝ), (1268857678941/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-60846087/400000000 : ℝ)|^4855 ≤ (1839090180599/20000000000000 : ℝ)^3831
        have hw : |(-60846087/400000000 : ℝ)|=(60846087/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1451368879/2500000000 : ℝ)|^4855 ≤ (25100551674477/50000000000000 : ℝ)^3831
        have hw : |(1451368879/2500000000 : ℝ)|=(1451368879/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2455237291/5000000000 : ℝ)|^4855 ≤ (1268857678941/3125000000000 : ℝ)^3831
        have hw : |(2455237291/5000000000 : ℝ)|=(2455237291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_s0_1 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5443932769/10000000000 : ℝ)*x 0 + (-1007044431/5000000000 : ℝ)*x 1 + (982095253/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5443932769/10000000000 : ℝ)^4855 ≤ (4627261517101/10000000000000 : ℝ)^3831 := by
    have hnat : (5443932769 : ℕ)^4855*10000000000000^3831 ≤ 4627261517101^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5443932769 10000000000 4627261517101 10000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1007044431/5000000000 : ℝ)^4855 ≤ (13123921455571/100000000000000 : ℝ)^3831 := by
    have hnat : (1007044431 : ℕ)^4855*100000000000000^3831 ≤ 13123921455571^3831*5000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007044431 5000000000 13123921455571 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (982095253/2000000000 : ℝ)^4855 ≤ (20301731681067/50000000000000 : ℝ)^3831 := by
    have hnat : (982095253 : ℕ)^4855*50000000000000^3831 ≤ 20301731681067^3831*2000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      982095253 2000000000 20301731681067 50000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5443932769/10000000000 : ℝ), (-1007044431/5000000000 : ℝ), (982095253/2000000000 : ℝ)] ![(4627261517101/10000000000000 : ℝ), (13123921455571/100000000000000 : ℝ), (20301731681067/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5443932769/10000000000 : ℝ)|^4855 ≤ (4627261517101/10000000000000 : ℝ)^3831
        have hw : |(5443932769/10000000000 : ℝ)|=(5443932769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1007044431/5000000000 : ℝ)|^4855 ≤ (13123921455571/100000000000000 : ℝ)^3831
        have hw : |(-1007044431/5000000000 : ℝ)|=(1007044431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(982095253/2000000000 : ℝ)|^4855 ≤ (20301731681067/50000000000000 : ℝ)^3831
        have hw : |(982095253/2000000000 : ℝ)|=(982095253/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_s0_2 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1360983451/2500000000 : ℝ)*x 0 + (4910474921/10000000000 : ℝ)*x 1 + (-2014089217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1360983451/2500000000 : ℝ)^4855 ≤ (23136313159913/50000000000000 : ℝ)^3831 := by
    have hnat : (1360983451 : ℕ)^4855*50000000000000^3831 ≤ 23136313159913^3831*2500000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360983451 2500000000 23136313159913 50000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4910474921/10000000000 : ℝ)^4855 ≤ (20301724639233/50000000000000 : ℝ)^3831 := by
    have hnat : (4910474921 : ℕ)^4855*50000000000000^3831 ≤ 20301724639233^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4910474921 10000000000 20301724639233 50000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2014089217/10000000000 : ℝ)^4855 ≤ (524956975483/4000000000000 : ℝ)^3831 := by
    have hnat : (2014089217 : ℕ)^4855*4000000000000^3831 ≤ 524956975483^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2014089217 10000000000 524956975483 4000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1360983451/2500000000 : ℝ), (4910474921/10000000000 : ℝ), (-2014089217/10000000000 : ℝ)] ![(23136313159913/50000000000000 : ℝ), (20301724639233/50000000000000 : ℝ), (524956975483/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1360983451/2500000000 : ℝ)|^4855 ≤ (23136313159913/50000000000000 : ℝ)^3831
        have hw : |(1360983451/2500000000 : ℝ)|=(1360983451/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4910474921/10000000000 : ℝ)|^4855 ≤ (20301724639233/50000000000000 : ℝ)^3831
        have hw : |(4910474921/10000000000 : ℝ)|=(4910474921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2014089217/10000000000 : ℝ)|^4855 ≤ (524956975483/4000000000000 : ℝ)^3831
        have hw : |(-2014089217/10000000000 : ℝ)|=(2014089217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_s0_3 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (819634619/2000000000 : ℝ)*x 0 + (3078874797/10000000000 : ℝ)*x 1 + (5347856879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (819634619/2000000000 : ℝ)^4855 ≤ (32287791789753/100000000000000 : ℝ)^3831 := by
    have hnat : (819634619 : ℕ)^4855*100000000000000^3831 ≤ 32287791789753^3831*2000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      819634619 2000000000 32287791789753 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3078874797/10000000000 : ℝ)^4855 ≤ (561801298591/2500000000000 : ℝ)^3831 := by
    have hnat : (3078874797 : ℕ)^4855*2500000000000^3831 ≤ 561801298591^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3078874797 10000000000 561801298591 2500000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5347856879/10000000000 : ℝ)^4855 ≤ (45240156249371/100000000000000 : ℝ)^3831 := by
    have hnat : (5347856879 : ℕ)^4855*100000000000000^3831 ≤ 45240156249371^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347856879 10000000000 45240156249371 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(819634619/2000000000 : ℝ), (3078874797/10000000000 : ℝ), (5347856879/10000000000 : ℝ)] ![(32287791789753/100000000000000 : ℝ), (561801298591/2500000000000 : ℝ), (45240156249371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(819634619/2000000000 : ℝ)|^4855 ≤ (32287791789753/100000000000000 : ℝ)^3831
        have hw : |(819634619/2000000000 : ℝ)|=(819634619/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3078874797/10000000000 : ℝ)|^4855 ≤ (561801298591/2500000000000 : ℝ)^3831
        have hw : |(3078874797/10000000000 : ℝ)|=(3078874797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5347856879/10000000000 : ℝ)|^4855 ≤ (45240156249371/100000000000000 : ℝ)^3831
        have hw : |(5347856879/10000000000 : ℝ)|=(5347856879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_s0_4 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1523636377/10000000000 : ℝ)*x 0 + (4932864033/10000000000 : ℝ)*x 1 + (2891151771/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1523636377/10000000000 : ℝ)^4855 ≤ (9214486175439/100000000000000 : ℝ)^3831 := by
    have hnat : (1523636377 : ℕ)^4855*100000000000000^3831 ≤ 9214486175439^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1523636377 10000000000 9214486175439 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4932864033/10000000000 : ℝ)^4855 ≤ (20419102895159/50000000000000 : ℝ)^3831 := by
    have hnat : (4932864033 : ℕ)^4855*50000000000000^3831 ≤ 20419102895159^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4932864033 10000000000 20419102895159 50000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2891151771/5000000000 : ℝ)^4855 ≤ (49947308021281/100000000000000 : ℝ)^3831 := by
    have hnat : (2891151771 : ℕ)^4855*100000000000000^3831 ≤ 49947308021281^3831*5000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2891151771 5000000000 49947308021281 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1523636377/10000000000 : ℝ), (4932864033/10000000000 : ℝ), (2891151771/5000000000 : ℝ)] ![(9214486175439/100000000000000 : ℝ), (20419102895159/50000000000000 : ℝ), (49947308021281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1523636377/10000000000 : ℝ)|^4855 ≤ (9214486175439/100000000000000 : ℝ)^3831
        have hw : |(-1523636377/10000000000 : ℝ)|=(1523636377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4932864033/10000000000 : ℝ)|^4855 ≤ (20419102895159/50000000000000 : ℝ)^3831
        have hw : |(4932864033/10000000000 : ℝ)|=(4932864033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2891151771/5000000000 : ℝ)|^4855 ≤ (49947308021281/100000000000000 : ℝ)^3831
        have hw : |(2891151771/5000000000 : ℝ)|=(2891151771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_s0_5 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1039919251/2000000000 : ℝ)*x 0 + (-571130161/5000000000 : ℝ)*x 1 + (5782303801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1039919251/2000000000 : ℝ)^4855 ≤ (21828317219773/50000000000000 : ℝ)^3831 := by
    have hnat : (1039919251 : ℕ)^4855*50000000000000^3831 ≤ 21828317219773^3831*2000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039919251 2000000000 21828317219773 50000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (571130161/5000000000 : ℝ)^4855 ≤ (399753418169/6250000000000 : ℝ)^3831 := by
    have hnat : (571130161 : ℕ)^4855*6250000000000^3831 ≤ 399753418169^3831*5000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      571130161 5000000000 399753418169 6250000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5782303801/10000000000 : ℝ)^4855 ≤ (4994731085651/10000000000000 : ℝ)^3831 := by
    have hnat : (5782303801 : ℕ)^4855*10000000000000^3831 ≤ 4994731085651^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5782303801 10000000000 4994731085651 10000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1039919251/2000000000 : ℝ), (-571130161/5000000000 : ℝ), (5782303801/10000000000 : ℝ)] ![(21828317219773/50000000000000 : ℝ), (399753418169/6250000000000 : ℝ), (4994731085651/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1039919251/2000000000 : ℝ)|^4855 ≤ (21828317219773/50000000000000 : ℝ)^3831
        have hw : |(1039919251/2000000000 : ℝ)|=(1039919251/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-571130161/5000000000 : ℝ)|^4855 ≤ (399753418169/6250000000000 : ℝ)^3831
        have hw : |(-571130161/5000000000 : ℝ)|=(571130161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5782303801/10000000000 : ℝ)|^4855 ≤ (4994731085651/10000000000000 : ℝ)^3831
        have hw : |(5782303801/10000000000 : ℝ)|=(5782303801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_s0_6 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5199596309/10000000000 : ℝ)*x 0 + (2891151811/5000000000 : ℝ)*x 1 + (-571130259/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5199596309/10000000000 : ℝ)^4855 ≤ (2728539688383/6250000000000 : ℝ)^3831 := by
    have hnat : (5199596309 : ℕ)^4855*6250000000000^3831 ≤ 2728539688383^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5199596309 10000000000 2728539688383 6250000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2891151811/5000000000 : ℝ)^4855 ≤ (49947308897027/100000000000000 : ℝ)^3831 := by
    have hnat : (2891151811 : ℕ)^4855*100000000000000^3831 ≤ 49947308897027^3831*5000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2891151811 5000000000 49947308897027 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (571130259/5000000000 : ℝ)^4855 ≤ (3198028040777/50000000000000 : ℝ)^3831 := by
    have hnat : (571130259 : ℕ)^4855*50000000000000^3831 ≤ 3198028040777^3831*5000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      571130259 5000000000 3198028040777 50000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5199596309/10000000000 : ℝ), (2891151811/5000000000 : ℝ), (-571130259/5000000000 : ℝ)] ![(2728539688383/6250000000000 : ℝ), (49947308897027/100000000000000 : ℝ), (3198028040777/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5199596309/10000000000 : ℝ)|^4855 ≤ (2728539688383/6250000000000 : ℝ)^3831
        have hw : |(5199596309/10000000000 : ℝ)|=(5199596309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2891151811/5000000000 : ℝ)|^4855 ≤ (49947308897027/100000000000000 : ℝ)^3831
        have hw : |(2891151811/5000000000 : ℝ)|=(2891151811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-571130259/5000000000 : ℝ)|^4855 ≤ (3198028040777/50000000000000 : ℝ)^3831
        have hw : |(-571130259/5000000000 : ℝ)|=(571130259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_s0_7 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1026117881/2500000000 : ℝ)*x 0 + (2645548349/5000000000 : ℝ)*x 1 + (196101161/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1026117881/2500000000 : ℝ)^4855 ≤ (16175345596697/50000000000000 : ℝ)^3831 := by
    have hnat : (1026117881 : ℕ)^4855*50000000000000^3831 ≤ 16175345596697^3831*2500000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026117881 2500000000 16175345596697 50000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2645548349/5000000000 : ℝ)^4855 ≤ (22316257607603/50000000000000 : ℝ)^3831 := by
    have hnat : (2645548349 : ℕ)^4855*50000000000000^3831 ≤ 22316257607603^3831*5000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2645548349 5000000000 22316257607603 50000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (196101161/625000000 : ℝ)^4855 ≤ (11508396788863/50000000000000 : ℝ)^3831 := by
    have hnat : (196101161 : ℕ)^4855*50000000000000^3831 ≤ 11508396788863^3831*625000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196101161 625000000 11508396788863 50000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1026117881/2500000000 : ℝ), (2645548349/5000000000 : ℝ), (196101161/625000000 : ℝ)] ![(16175345596697/50000000000000 : ℝ), (22316257607603/50000000000000 : ℝ), (11508396788863/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1026117881/2500000000 : ℝ)|^4855 ≤ (16175345596697/50000000000000 : ℝ)^3831
        have hw : |(1026117881/2500000000 : ℝ)|=(1026117881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2645548349/5000000000 : ℝ)|^4855 ≤ (22316257607603/50000000000000 : ℝ)^3831
        have hw : |(2645548349/5000000000 : ℝ)|=(2645548349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(196101161/625000000 : ℝ)|^4855 ≤ (11508396788863/50000000000000 : ℝ)^3831
        have hw : |(196101161/625000000 : ℝ)|=(196101161/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1634_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (17675869/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (4527/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (11851/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4851/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4851 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4851*1^1024 ≤ 0^1024*1^4851 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4851 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4851 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4851/1024 : ℝ) ≤ (1302677558640934617/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4851 ≤ (1302677558640934617/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4851*100000000000000000000^1024 ≤ 1302677558640934617^1024*5^4851 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1302677558640934617 100000000000000000000 4851 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1302677558640934617/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4851 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4851/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4851 := by
      have hnat : (1 : ℕ)^1024*1^4851 ≤ 1^4851*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4851 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4851 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101302677558640934617/100000000000000000000 : ℝ) ≤ (313354939806857/312500000000000 : ℝ) ^ (4851/1024 : ℝ) := by
    have hpowers : (101302677558640934617/100000000000000000000 : ℝ)^1024 ≤ (313354939806857/312500000000000 : ℝ)^4851 := by
      have hnat : (101302677558640934617 : ℕ)^1024*312500000000000^4851 ≤ 313354939806857^4851*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101302677558640934617 100000000000000000000 313354939806857 312500000000000 1024 4851 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (313354939806857/312500000000000 : ℝ)) (X := (101302677558640934617/100000000000000000000 : ℝ)) (by norm_num) 4851 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51302677558640934617/50000000000000000000 : ℝ) ≤ (157104939806857/156250000000000 : ℝ) ^ (4851/1024 : ℝ) := by
    have hpowers : (51302677558640934617/50000000000000000000 : ℝ)^1024 ≤ (157104939806857/156250000000000 : ℝ)^4851 := by
      have hnat : (51302677558640934617 : ℕ)^1024*156250000000000^4851 ≤ 157104939806857^4851*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51302677558640934617 50000000000000000000 157104939806857 156250000000000 1024 4851 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (157104939806857/156250000000000 : ℝ)) (X := (51302677558640934617/50000000000000000000 : ℝ)) (by norm_num) 4851 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(854939806857/125000000000000 : ℝ)*(0 : ℝ))^(4851/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(854939806857/125000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1302677558640934617/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(854939806857/125000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4851/1024 : ℝ) := by
    rw [show (1 : ℝ)+(854939806857/125000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(313354939806857/312500000000000 : ℝ) by norm_num, show 1+(1302677558640934617/100000000000000000000 : ℝ)+(0 : ℝ)=(101302677558640934617/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1302677558640934617/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(854939806857/125000000000000 : ℝ)*(2/5 : ℝ))^(4851/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(854939806857/125000000000000 : ℝ)*(2/5 : ℝ)=(157104939806857/156250000000000 : ℝ) by norm_num, show 1+2*(1302677558640934617/100000000000000000000 : ℝ)=(51302677558640934617/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(854939806857/125000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4851/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (854939806857/125000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(854939806857/125000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4851/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (854939806857/125000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(854939806857/125000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4851/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (854939806857/125000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-60846087/400000000 : ℝ)*X 0 0+(1451368879/2500000000 : ℝ)*X 0 1+(2455237291/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5443932769/10000000000 : ℝ)*X 1 0+(-1007044431/5000000000 : ℝ)*X 1 1+(982095253/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1360983451/2500000000 : ℝ)*X 2 0+(4910474921/10000000000 : ℝ)*X 2 1+(-2014089217/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((819634619/2000000000 : ℝ)*X 0 0+(3078874797/10000000000 : ℝ)*X 0 1+(5347856879/10000000000 : ℝ)*X 0 2+(819634619/2000000000 : ℝ)*X 1 0+(3078874797/10000000000 : ℝ)*X 1 1+(5347856879/10000000000 : ℝ)*X 1 2+(819634619/2000000000 : ℝ)*X 2 0+(3078874797/10000000000 : ℝ)*X 2 1+(5347856879/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1523636377/10000000000 : ℝ)*X 0 0+(4932864033/10000000000 : ℝ)*X 0 1+(2891151771/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1039919251/2000000000 : ℝ)*X 1 0+(-571130161/5000000000 : ℝ)*X 1 1+(5782303801/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5199596309/10000000000 : ℝ)*X 2 0+(2891151811/5000000000 : ℝ)*X 2 1+(-571130259/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1026117881/2500000000 : ℝ)*X 0 0+(2645548349/5000000000 : ℝ)*X 0 1+(196101161/625000000 : ℝ)*X 0 2+(1026117881/2500000000 : ℝ)*X 1 0+(2645548349/5000000000 : ℝ)*X 1 1+(196101161/625000000 : ℝ)*X 1 2+(1026117881/2500000000 : ℝ)*X 2 0+(2645548349/5000000000 : ℝ)*X 2 1+(196101161/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3214546619233517664009/781250000000000000000000000 : ℝ) := by norm_num
    linear_combination (656797061/100000000000000 : ℝ)*(base19) + (104273443/12500000000000 : ℝ)*(base23) + (29674189/20000000000000 : ℝ)*(upper3) + (19072969/100000000000000 : ℝ)*(upper4) + (54715891/100000000000000 : ℝ)*(upper5) + (779027874136333/100000000000000 : ℝ)*(major0) + (779027874136333/100000000000000 : ℝ)*(major1) + (779027874136333/100000000000000 : ℝ)*(major2) + (111732171801063/10000000000000 : ℝ)*(sp0) + (1117325350511841/100000000000000 : ℝ)*(sp1) + (558662586560679/50000000000000 : ℝ)*(sp2) + (44072768830771/10000000000000 : ℝ)*(sp3) + (4289298273/100000000000000 : ℝ)*(sp4) + (1915502057/100000000000000 : ℝ)*(sp7) + (220364801904883/50000000000000 : ℝ)*(f.failure) + (558663003654451/50000000000000 : ℝ)*(f.sum) + (2845142816631/6250000000000000000000000000 : ℝ)*base65 + (102761078077119/12500000000000000000000000000 : ℝ)*base68 + (140219763114619/12500000000000000000000000000 : ℝ)*base70 + (69976856852119/12500000000000000000000000000 : ℝ)*base72 + (81029477119/6250000000000000000000000000 : ℝ)*base74 + (64579316102119/12500000000000000000000000000 : ℝ)*base76 + (80828958139619/12500000000000000000000000000 : ℝ)*base78 + (44823735939619/12500000000000000000000000000 : ℝ)*base80 + (13043363989619/6250000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (2631673/500000000000000000000 : ℝ)*base90 + (2631673/500000000000000000000 : ℝ)*base92 + (2631673/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3368744169324685936359/1562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (60771201/12500000000000 : ℝ)*(base19) + (263967113/50000000000000 : ℝ)*(base23) + (18719641/50000000000000 : ℝ)*(base39) + (29341053/50000000000000 : ℝ)*(upper3) + (34358871/100000000000000 : ℝ)*(upper5) + (410402862046983/50000000000000 : ℝ)*(major0) + (410402862046983/50000000000000 : ℝ)*(major1) + (205201421663671/25000000000000 : ℝ)*(major2) + (2028613853/100000000000000 : ℝ)*(sp1) + (467738111/25000000000000 : ℝ)*(sp2) + (294311551727033/25000000000000 : ℝ)*(sp4) + (1177243692124671/100000000000000 : ℝ)*(sp5) + (147155480682593/12500000000000 : ℝ)*(sp6) + (464365131973973/100000000000000 : ℝ)*(sp7) + (464365131973973/100000000000000 : ℝ)*(f.failure) + (588623122173707/50000000000000 : ℝ)*(f.sum) + (93663697861/250000000000000000000000000 : ℝ)*base65 + (16824548873297/3125000000000000000000000000 : ℝ)*base67 + (3372857887569/6250000000000000000000000000 : ℝ)*base70 + (5569649264203/3125000000000000000000000000 : ℝ)*base72 + (1318637518361/250000000000000000000000000 : ℝ)*base73 + (6854204787431/6250000000000000000000000000 : ℝ)*base75 + (4146331287431/6250000000000000000000000000 : ℝ)*base77 + (2950275725069/6250000000000000000000000000 : ℝ)*base80 + (7535260150069/3125000000000000000000000000 : ℝ)*base82 + (1842463/1000000000000000000000 : ℝ)*base90 + (1842463/1000000000000000000000 : ℝ)*base92 + (1842463/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1634_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (17675869/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4527/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (11851/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1634_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1634_s1_0 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1633800361/10000000000 : ℝ)*x 0 + (5508827553/10000000000 : ℝ)*x 1 + (2567026953/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1633800361/10000000000 : ℝ)^4855 ≤ (2013364812451/20000000000000 : ℝ)^3831 := by
    have hnat : (1633800361 : ℕ)^4855*20000000000000^3831 ≤ 2013364812451^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1633800361 10000000000 2013364812451 20000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5508827553/10000000000 : ℝ)^4855 ≤ (2935797461881/6250000000000 : ℝ)^3831 := by
    have hnat : (5508827553 : ℕ)^4855*6250000000000^3831 ≤ 2935797461881^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5508827553 10000000000 2935797461881 6250000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2567026953/5000000000 : ℝ)^4855 ≤ (2148020826277/5000000000000 : ℝ)^3831 := by
    have hnat : (2567026953 : ℕ)^4855*5000000000000^3831 ≤ 2148020826277^3831*5000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2567026953 5000000000 2148020826277 5000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1633800361/10000000000 : ℝ), (5508827553/10000000000 : ℝ), (2567026953/5000000000 : ℝ)] ![(2013364812451/20000000000000 : ℝ), (2935797461881/6250000000000 : ℝ), (2148020826277/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1633800361/10000000000 : ℝ)|^4855 ≤ (2013364812451/20000000000000 : ℝ)^3831
        have hw : |(-1633800361/10000000000 : ℝ)|=(1633800361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5508827553/10000000000 : ℝ)|^4855 ≤ (2935797461881/6250000000000 : ℝ)^3831
        have hw : |(5508827553/10000000000 : ℝ)|=(5508827553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2567026953/5000000000 : ℝ)|^4855 ≤ (2148020826277/5000000000000 : ℝ)^3831
        have hw : |(2567026953/5000000000 : ℝ)|=(2567026953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_s1_1 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2682514463/5000000000 : ℝ)*x 0 + (-914533657/5000000000 : ℝ)*x 1 + (5134053681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2682514463/5000000000 : ℝ)^4855 ≤ (45424330816867/100000000000000 : ℝ)^3831 := by
    have hnat : (2682514463 : ℕ)^4855*100000000000000^3831 ≤ 45424330816867^3831*5000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2682514463 5000000000 45424330816867 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (914533657/5000000000 : ℝ)^4855 ≤ (11615255021261/100000000000000 : ℝ)^3831 := by
    have hnat : (914533657 : ℕ)^4855*100000000000000^3831 ≤ 11615255021261^3831*5000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      914533657 5000000000 11615255021261 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5134053681/10000000000 : ℝ)^4855 ≤ (8592082827911/20000000000000 : ℝ)^3831 := by
    have hnat : (5134053681 : ℕ)^4855*20000000000000^3831 ≤ 8592082827911^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5134053681 10000000000 8592082827911 20000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2682514463/5000000000 : ℝ), (-914533657/5000000000 : ℝ), (5134053681/10000000000 : ℝ)] ![(45424330816867/100000000000000 : ℝ), (11615255021261/100000000000000 : ℝ), (8592082827911/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2682514463/5000000000 : ℝ)|^4855 ≤ (45424330816867/100000000000000 : ℝ)^3831
        have hw : |(2682514463/5000000000 : ℝ)|=(2682514463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-914533657/5000000000 : ℝ)|^4855 ≤ (11615255021261/100000000000000 : ℝ)^3831
        have hw : |(-914533657/5000000000 : ℝ)|=(914533657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5134053681/10000000000 : ℝ)|^4855 ≤ (8592082827911/20000000000000 : ℝ)^3831
        have hw : |(5134053681/10000000000 : ℝ)|=(5134053681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_s1_2 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (670628729/1250000000 : ℝ)*x 0 + (320878287/625000000 : ℝ)*x 1 + (-914533771/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (670628729/1250000000 : ℝ)^4855 ≤ (45424340538109/100000000000000 : ℝ)^3831 := by
    have hnat : (670628729 : ℕ)^4855*100000000000000^3831 ≤ 45424340538109^3831*1250000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      670628729 1250000000 45424340538109 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (320878287/625000000 : ℝ)^4855 ≤ (4296040259139/10000000000000 : ℝ)^3831 := by
    have hnat : (320878287 : ℕ)^4855*10000000000000^3831 ≤ 4296040259139^3831*625000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      320878287 625000000 4296040259139 10000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (914533771/5000000000 : ℝ)^4855 ≤ (2323051371231/20000000000000 : ℝ)^3831 := by
    have hnat : (914533771 : ℕ)^4855*20000000000000^3831 ≤ 2323051371231^3831*5000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      914533771 5000000000 2323051371231 20000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(670628729/1250000000 : ℝ), (320878287/625000000 : ℝ), (-914533771/5000000000 : ℝ)] ![(45424340538109/100000000000000 : ℝ), (4296040259139/10000000000000 : ℝ), (2323051371231/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(670628729/1250000000 : ℝ)|^4855 ≤ (45424340538109/100000000000000 : ℝ)^3831
        have hw : |(670628729/1250000000 : ℝ)|=(670628729/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(320878287/625000000 : ℝ)|^4855 ≤ (4296040259139/10000000000000 : ℝ)^3831
        have hw : |(320878287/625000000 : ℝ)|=(320878287/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-914533771/5000000000 : ℝ)|^4855 ≤ (2323051371231/20000000000000 : ℝ)^3831
        have hw : |(-914533771/5000000000 : ℝ)|=(914533771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_s1_3 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4184427581/10000000000 : ℝ)*x 0 + (3729342631/10000000000 : ℝ)*x 1 + (2339730441/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4184427581/10000000000 : ℝ)^4855 ≤ (33151407456203/100000000000000 : ℝ)^3831 := by
    have hnat : (4184427581 : ℕ)^4855*100000000000000^3831 ≤ 33151407456203^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4184427581 10000000000 33151407456203 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3729342631/10000000000 : ℝ)^4855 ≤ (7162630457679/25000000000000 : ℝ)^3831 := by
    have hnat : (3729342631 : ℕ)^4855*25000000000000^3831 ≤ 7162630457679^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3729342631 10000000000 7162630457679 25000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2339730441/5000000000 : ℝ)^4855 ≤ (9549517675827/25000000000000 : ℝ)^3831 := by
    have hnat : (2339730441 : ℕ)^4855*25000000000000^3831 ≤ 9549517675827^3831*5000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2339730441 5000000000 9549517675827 25000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4184427581/10000000000 : ℝ), (3729342631/10000000000 : ℝ), (2339730441/5000000000 : ℝ)] ![(33151407456203/100000000000000 : ℝ), (7162630457679/25000000000000 : ℝ), (9549517675827/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4184427581/10000000000 : ℝ)|^4855 ≤ (33151407456203/100000000000000 : ℝ)^3831
        have hw : |(4184427581/10000000000 : ℝ)|=(4184427581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3729342631/10000000000 : ℝ)|^4855 ≤ (7162630457679/25000000000000 : ℝ)^3831
        have hw : |(3729342631/10000000000 : ℝ)|=(3729342631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2339730441/5000000000 : ℝ)|^4855 ≤ (9549517675827/25000000000000 : ℝ)^3831
        have hw : |(2339730441/5000000000 : ℝ)|=(2339730441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_s1_4 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-102123751/625000000 : ℝ)*x 0 + (5137958157/10000000000 : ℝ)*x 1 + (5504865547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (102123751/625000000 : ℝ)^4855 ≤ (5034113464247/50000000000000 : ℝ)^3831 := by
    have hnat : (102123751 : ℕ)^4855*50000000000000^3831 ≤ 5034113464247^3831*625000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102123751 625000000 5034113464247 50000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5137958157/10000000000 : ℝ)^4855 ≤ (8600364576081/20000000000000 : ℝ)^3831 := by
    have hnat : (5137958157 : ℕ)^4855*20000000000000^3831 ≤ 8600364576081^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5137958157 10000000000 8600364576081 20000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5504865547/10000000000 : ℝ)^4855 ≤ (23464975083159/50000000000000 : ℝ)^3831 := by
    have hnat : (5504865547 : ℕ)^4855*50000000000000^3831 ≤ 23464975083159^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5504865547 10000000000 23464975083159 50000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-102123751/625000000 : ℝ), (5137958157/10000000000 : ℝ), (5504865547/10000000000 : ℝ)] ![(5034113464247/50000000000000 : ℝ), (8600364576081/20000000000000 : ℝ), (23464975083159/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-102123751/625000000 : ℝ)|^4855 ≤ (5034113464247/50000000000000 : ℝ)^3831
        have hw : |(-102123751/625000000 : ℝ)|=(102123751/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5137958157/10000000000 : ℝ)|^4855 ≤ (8600364576081/20000000000000 : ℝ)^3831
        have hw : |(5137958157/10000000000 : ℝ)|=(5137958157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5504865547/10000000000 : ℝ)|^4855 ≤ (23464975083159/50000000000000 : ℝ)^3831
        have hw : |(5504865547/10000000000 : ℝ)|=(5504865547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_s1_5 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (210600121/400000000 : ℝ)*x 0 + (-1458254517/10000000000 : ℝ)*x 1 + (5504865933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210600121/400000000 : ℝ)^4855 ≤ (4435375468621/10000000000000 : ℝ)^3831 := by
    have hnat : (210600121 : ℕ)^4855*10000000000000^3831 ≤ 4435375468621^3831*400000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210600121 400000000 4435375468621 10000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1458254517/10000000000 : ℝ)^4855 ≤ (435814548803/5000000000000 : ℝ)^3831 := by
    have hnat : (1458254517 : ℕ)^4855*5000000000000^3831 ≤ 435814548803^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1458254517 10000000000 435814548803 5000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5504865933/10000000000 : ℝ)^4855 ≤ (46929954336623/100000000000000 : ℝ)^3831 := by
    have hnat : (5504865933 : ℕ)^4855*100000000000000^3831 ≤ 46929954336623^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5504865933 10000000000 46929954336623 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210600121/400000000 : ℝ), (-1458254517/10000000000 : ℝ), (5504865933/10000000000 : ℝ)] ![(4435375468621/10000000000000 : ℝ), (435814548803/5000000000000 : ℝ), (46929954336623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210600121/400000000 : ℝ)|^4855 ≤ (4435375468621/10000000000000 : ℝ)^3831
        have hw : |(210600121/400000000 : ℝ)|=(210600121/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1458254517/10000000000 : ℝ)|^4855 ≤ (435814548803/5000000000000 : ℝ)^3831
        have hw : |(-1458254517/10000000000 : ℝ)|=(1458254517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5504865933/10000000000 : ℝ)|^4855 ≤ (46929954336623/100000000000000 : ℝ)^3831
        have hw : |(5504865933/10000000000 : ℝ)|=(5504865933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_s1_6 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (658125291/1250000000 : ℝ)*x 0 + (5504866187/10000000000 : ℝ)*x 1 + (-45570473/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (658125291/1250000000 : ℝ)^4855 ≤ (22176873622517/50000000000000 : ℝ)^3831 := by
    have hnat : (658125291 : ℕ)^4855*50000000000000^3831 ≤ 22176873622517^3831*1250000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658125291 1250000000 22176873622517 50000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5504866187/10000000000 : ℝ)^4855 ≤ (46929957080813/100000000000000 : ℝ)^3831 := by
    have hnat : (5504866187 : ℕ)^4855*100000000000000^3831 ≤ 46929957080813^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5504866187 10000000000 46929957080813 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (45570473/312500000 : ℝ)^4855 ≤ (2179073916227/25000000000000 : ℝ)^3831 := by
    have hnat : (45570473 : ℕ)^4855*25000000000000^3831 ≤ 2179073916227^3831*312500000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45570473 312500000 2179073916227 25000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(658125291/1250000000 : ℝ), (5504866187/10000000000 : ℝ), (-45570473/312500000 : ℝ)] ![(22176873622517/50000000000000 : ℝ), (46929957080813/100000000000000 : ℝ), (2179073916227/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(658125291/1250000000 : ℝ)|^4855 ≤ (22176873622517/50000000000000 : ℝ)^3831
        have hw : |(658125291/1250000000 : ℝ)|=(658125291/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5504866187/10000000000 : ℝ)|^4855 ≤ (46929957080813/100000000000000 : ℝ)^3831
        have hw : |(5504866187/10000000000 : ℝ)|=(5504866187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-45570473/312500000 : ℝ)|^4855 ≤ (2179073916227/25000000000000 : ℝ)^3831
        have hw : |(-45570473/312500000 : ℝ)|=(45570473/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_s1_7 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2092439897/5000000000 : ℝ)*x 0 + (933912731/2000000000 : ℝ)*x 1 + (3739385891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2092439897/5000000000 : ℝ)^4855 ≤ (33155947837363/100000000000000 : ℝ)^3831 := by
    have hnat : (2092439897 : ℕ)^4855*100000000000000^3831 ≤ 33155947837363^3831*5000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2092439897 5000000000 33155947837363 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (933912731/2000000000 : ℝ)^4855 ≤ (2380982167877/6250000000000 : ℝ)^3831 := by
    have hnat : (933912731 : ℕ)^4855*6250000000000^3831 ≤ 2380982167877^3831*2000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      933912731 2000000000 2380982167877 6250000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3739385891/10000000000 : ℝ)^4855 ≤ (28748337451899/100000000000000 : ℝ)^3831 := by
    have hnat : (3739385891 : ℕ)^4855*100000000000000^3831 ≤ 28748337451899^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3739385891 10000000000 28748337451899 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2092439897/5000000000 : ℝ), (933912731/2000000000 : ℝ), (3739385891/10000000000 : ℝ)] ![(33155947837363/100000000000000 : ℝ), (2380982167877/6250000000000 : ℝ), (28748337451899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2092439897/5000000000 : ℝ)|^4855 ≤ (33155947837363/100000000000000 : ℝ)^3831
        have hw : |(2092439897/5000000000 : ℝ)|=(2092439897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(933912731/2000000000 : ℝ)|^4855 ≤ (2380982167877/6250000000000 : ℝ)^3831
        have hw : |(933912731/2000000000 : ℝ)|=(933912731/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3739385891/10000000000 : ℝ)|^4855 ≤ (28748337451899/100000000000000 : ℝ)^3831
        have hw : |(3739385891/10000000000 : ℝ)|=(3739385891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1634_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (17675869/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (11851/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4527/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9527/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17481/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (11851/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4527/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (11851/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4527/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (11851/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4527/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (11851/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4527/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (11851/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4527/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (11851/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4527/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4527/100000 : ℝ) ^ (4851/1024 : ℝ) ≤ (42871112612513/100000000000000000000 : ℝ) := by
    have hpowers : (4527/100000 : ℝ)^4851 ≤ (42871112612513/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4527 : ℕ)^4851*100000000000000000000^1024 ≤ 42871112612513^1024*100000^4851 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4527 100000 42871112612513 100000000000000000000 4851 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4527/100000 : ℝ)) (X := (42871112612513/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4851 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (11851/50000 : ℝ) ^ (4851/1024 : ℝ) ≤ (2729644119230377/2500000000000000000 : ℝ) := by
    have hpowers : (11851/50000 : ℝ)^4851 ≤ (2729644119230377/2500000000000000000 : ℝ)^1024 := by
      have hnat : (11851 : ℕ)^4851*2500000000000000000^1024 ≤ 2729644119230377^1024*50000^4851 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11851 50000 2729644119230377 2500000000000000000 4851 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11851/50000 : ℝ)) (X := (2729644119230377/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4851 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000042871112612513/50000000000000000000 : ℝ) ≤ (250000045248407/250000000000000 : ℝ) ^ (4851/1024 : ℝ) := by
    have hpowers : (50000042871112612513/50000000000000000000 : ℝ)^1024 ≤ (250000045248407/250000000000000 : ℝ)^4851 := by
      have hnat : (50000042871112612513 : ℕ)^1024*250000000000000^4851 ≤ 250000045248407^4851*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000042871112612513 50000000000000000000 250000045248407 250000000000000 1024 4851 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250000045248407/250000000000000 : ℝ)) (X := (50000042871112612513/50000000000000000000 : ℝ)) (by norm_num) 4851 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100109228635881827593/100000000000000000000 : ℝ) ≤ (10002304719914213/10000000000000000 : ℝ) ^ (4851/1024 : ℝ) := by
    have hpowers : (100109228635881827593/100000000000000000000 : ℝ)^1024 ≤ (10002304719914213/10000000000000000 : ℝ)^4851 := by
      have hnat : (100109228635881827593 : ℕ)^1024*10000000000000000^4851 ≤ 10002304719914213^4851*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100109228635881827593 100000000000000000000 10002304719914213 10000000000000000 1024 4851 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002304719914213/10000000000000000 : ℝ)) (X := (100109228635881827593/100000000000000000000 : ℝ)) (by norm_num) 4851 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1252729644119230377/1250000000000000000 : ℝ) ≤ (5002303814946073/5000000000000000 : ℝ) ^ (4851/1024 : ℝ) := by
    have hpowers : (1252729644119230377/1250000000000000000 : ℝ)^1024 ≤ (5002303814946073/5000000000000000 : ℝ)^4851 := by
      have hnat : (1252729644119230377 : ℕ)^1024*5000000000000000^4851 ≤ 5002303814946073^4851*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1252729644119230377 1250000000000000000 5002303814946073 5000000000000000 1024 4851 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002303814946073/5000000000000000 : ℝ)) (X := (1252729644119230377/1250000000000000000 : ℝ)) (by norm_num) 4851 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(42871112612513/100000000000000000000 : ℝ) ≤ ((95864592079293981809/95875000000000000000 : ℝ)+2*(2302909977933/1917500000000000 : ℝ)*(4527/100000 : ℝ))^(4851/1024 : ℝ) := by
    rw [show (95864592079293981809/95875000000000000000 : ℝ)+2*(2302909977933/1917500000000000 : ℝ)*(4527/100000 : ℝ)=(250000045248407/250000000000000 : ℝ) by norm_num, show 1+2*(42871112612513/100000000000000000000 : ℝ)=(50000042871112612513/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2729644119230377/2500000000000000000 : ℝ)+(42871112612513/100000000000000000000 : ℝ) ≤ ((95864592079293981809/95875000000000000000 : ℝ)+(2302909977933/1917500000000000 : ℝ)*((11851/50000 : ℝ)+(4527/100000 : ℝ)))^(4851/1024 : ℝ) := by
    rw [show (95864592079293981809/95875000000000000000 : ℝ)+(2302909977933/1917500000000000 : ℝ)*((11851/50000 : ℝ)+(4527/100000 : ℝ))=(10002304719914213/10000000000000000 : ℝ) by norm_num, show 1+(2729644119230377/2500000000000000000 : ℝ)+(42871112612513/100000000000000000000 : ℝ)=(100109228635881827593/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2729644119230377/2500000000000000000 : ℝ) ≤ ((95864592079293981809/95875000000000000000 : ℝ)+2*(2302909977933/1917500000000000 : ℝ)*(11851/50000 : ℝ))^(4851/1024 : ℝ) := by
    rw [show (95864592079293981809/95875000000000000000 : ℝ)+2*(2302909977933/1917500000000000 : ℝ)*(11851/50000 : ℝ)=(5002303814946073/5000000000000000 : ℝ) by norm_num, show 1+2*(2729644119230377/2500000000000000000 : ℝ)=(1252729644119230377/1250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (95864592079293981809/95875000000000000000 : ℝ)*(X 1 0+X 2 0)+(2302909977933/1917500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4851/1024 : ℝ)) (lo := (4527/100000 : ℝ)) (hi := (11851/50000 : ℝ)) (c := (95864592079293981809/95875000000000000000 : ℝ)) (alpha := (2302909977933/1917500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (95864592079293981809/95875000000000000000 : ℝ)*(X 0 1+X 2 1)+(2302909977933/1917500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4851/1024 : ℝ)) (lo := (4527/100000 : ℝ)) (hi := (11851/50000 : ℝ)) (c := (95864592079293981809/95875000000000000000 : ℝ)) (alpha := (2302909977933/1917500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (95864592079293981809/95875000000000000000 : ℝ)*(X 0 2+X 1 2)+(2302909977933/1917500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4851/1024 : ℝ)) (lo := (4527/100000 : ℝ)) (hi := (11851/50000 : ℝ)) (c := (95864592079293981809/95875000000000000000 : ℝ)) (alpha := (2302909977933/1917500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1633800361/10000000000 : ℝ)*X 0 0+(5508827553/10000000000 : ℝ)*X 0 1+(2567026953/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2682514463/5000000000 : ℝ)*X 1 0+(-914533657/5000000000 : ℝ)*X 1 1+(5134053681/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((670628729/1250000000 : ℝ)*X 2 0+(320878287/625000000 : ℝ)*X 2 1+(-914533771/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4184427581/10000000000 : ℝ)*X 0 0+(3729342631/10000000000 : ℝ)*X 0 1+(2339730441/5000000000 : ℝ)*X 0 2+(4184427581/10000000000 : ℝ)*X 1 0+(3729342631/10000000000 : ℝ)*X 1 1+(2339730441/5000000000 : ℝ)*X 1 2+(4184427581/10000000000 : ℝ)*X 2 0+(3729342631/10000000000 : ℝ)*X 2 1+(2339730441/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-102123751/625000000 : ℝ)*X 0 0+(5137958157/10000000000 : ℝ)*X 0 1+(5504865547/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((210600121/400000000 : ℝ)*X 1 0+(-1458254517/10000000000 : ℝ)*X 1 1+(5504865933/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((658125291/1250000000 : ℝ)*X 2 0+(5504866187/10000000000 : ℝ)*X 2 1+(-45570473/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2092439897/5000000000 : ℝ)*X 0 0+(933912731/2000000000 : ℝ)*X 0 1+(3739385891/10000000000 : ℝ)*X 0 2+(2092439897/5000000000 : ℝ)*X 1 0+(933912731/2000000000 : ℝ)*X 1 1+(3739385891/10000000000 : ℝ)*X 1 2+(2092439897/5000000000 : ℝ)*X 2 0+(933912731/2000000000 : ℝ)*X 2 1+(3739385891/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2122207448888471148943273989/184375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8504447/1562500000000 : ℝ)*(base1) + (810462991/50000000000000 : ℝ)*(base19) + (2071523399/100000000000000 : ℝ)*(base23) + (105726213/50000000000000 : ℝ)*(upper3) + (73131757/50000000000000 : ℝ)*(upper5) + (930199300589091/50000000000000 : ℝ)*(major0) + (930199300589091/50000000000000 : ℝ)*(major1) + (930199300589091/50000000000000 : ℝ)*(major2) + (1334141687571389/50000000000000 : ℝ)*(sp0) + (2668287623061413/100000000000000 : ℝ)*(sp1) + (667071793115999/25000000000000 : ℝ)*(sp2) + (1052503304085847/100000000000000 : ℝ)*(sp3) + (3206564613/50000000000000 : ℝ)*(sp4) + (3726322583/100000000000000 : ℝ)*(sp7) + (263126893673259/25000000000000 : ℝ)*(f.failure) + (667072310996849/25000000000000 : ℝ)*(f.sum) + (11977213681563/7375000000000000000000000000 : ℝ)*base66 + (359201260171500337/368750000000000000000000000000000 : ℝ)*base68 + (5933911382552750337/368750000000000000000000000000000 : ℝ)*base70 + (1010134767240250337/368750000000000000000000000000000 : ℝ)*base72 + (9934880647031/3687500000000000000000000000 : ℝ)*base73 + (1243090604840999663/368750000000000000000000000000000 : ℝ)*base75 + (1772155253527750337/368750000000000000000000000000000 : ℝ)*base78 + (3212762389553499663/368750000000000000000000000000000 : ℝ)*base79 + (52357935714063/7375000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (112929/250000000000000000000 : ℝ)*base90 + (112929/250000000000000000000 : ℝ)*base92 + (112929/250000000000000000000 : ℝ)*base94 + (1/50000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1277033301673804861845431457/599218750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (119340893/20000000000000 : ℝ)*(base19) + (6926653/2000000000000 : ℝ)*(base23) + (38885283/50000000000000 : ℝ)*(upper2) + (1243627/781250000000 : ℝ)*(upper3) + (237534000077359/12500000000000 : ℝ)*(major0) + (237534000077359/12500000000000 : ℝ)*(major1) + (237534000077359/12500000000000 : ℝ)*(major2) + (5777744973/100000000000000 : ℝ)*(sp1) + (3815632793/100000000000000 : ℝ)*(sp2) + (8155409/800000000000 : ℝ)*(sp3) + (1362739128490741/50000000000000 : ℝ)*(sp4) + (681367970633011/25000000000000 : ℝ)*(sp5) + (1362737047508019/50000000000000 : ℝ)*(sp6) + (53753232689567/5000000000000 : ℝ)*(sp7) + (215013134643493/20000000000000 : ℝ)*(f.failure) + (1362739128490741/50000000000000 : ℝ)*(f.sum) + (152953469222299/95875000000000000000000000000 : ℝ)*base66 + (608668430112674931/1198437500000000000000000000000000 : ℝ)*base67 + (9084648322020137569/1198437500000000000000000000000000 : ℝ)*base70 + (7953961896259200069/1198437500000000000000000000000000 : ℝ)*base72 + (172738370484701/95875000000000000000000000000 : ℝ)*base73 + (1907957314797049931/1198437500000000000000000000000000 : ℝ)*base75 + (1448625019500174931/1198437500000000000000000000000000 : ℝ)*base77 + (5173627258087674931/1198437500000000000000000000000000 : ℝ)*base79 + (6535407634491/1498046875000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (29583/200000000000000000000 : ℝ)*base90 + (29583/200000000000000000000 : ℝ)*base92 + (29583/200000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1634_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (17675869/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (11851/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4527/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9527/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17481/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1634_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1634_s2_0 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-65789609/400000000 : ℝ)*x 0 + (5456992651/10000000000 : ℝ)*x 1 + (647336639/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65789609/400000000 : ℝ)^4855 ≤ (2538081223323/25000000000000 : ℝ)^3831 := by
    have hnat : (65789609 : ℕ)^4855*25000000000000^3831 ≤ 2538081223323^3831*400000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65789609 400000000 2538081223323 25000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5456992651/10000000000 : ℝ)^4855 ≤ (46413338715301/100000000000000 : ℝ)^3831 := by
    have hnat : (5456992651 : ℕ)^4855*100000000000000^3831 ≤ 46413338715301^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5456992651 10000000000 46413338715301 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (647336639/1250000000 : ℝ)^4855 ≤ (21717168189369/50000000000000 : ℝ)^3831 := by
    have hnat : (647336639 : ℕ)^4855*50000000000000^3831 ≤ 21717168189369^3831*1250000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647336639 1250000000 21717168189369 50000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-65789609/400000000 : ℝ), (5456992651/10000000000 : ℝ), (647336639/1250000000 : ℝ)] ![(2538081223323/25000000000000 : ℝ), (46413338715301/100000000000000 : ℝ), (21717168189369/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-65789609/400000000 : ℝ)|^4855 ≤ (2538081223323/25000000000000 : ℝ)^3831
        have hw : |(-65789609/400000000 : ℝ)|=(65789609/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5456992651/10000000000 : ℝ)|^4855 ≤ (46413338715301/100000000000000 : ℝ)^3831
        have hw : |(5456992651/10000000000 : ℝ)|=(5456992651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(647336639/1250000000 : ℝ)|^4855 ≤ (21717168189369/50000000000000 : ℝ)^3831
        have hw : |(647336639/1250000000 : ℝ)|=(647336639/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_s2_1 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351388489/10000000000 : ℝ)*x 0 + (-894118193/5000000000 : ℝ)*x 1 + (161834161/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351388489/10000000000 : ℝ)^4855 ≤ (5659752596241/12500000000000 : ℝ)^3831 := by
    have hnat : (5351388489 : ℕ)^4855*12500000000000^3831 ≤ 5659752596241^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351388489 10000000000 5659752596241 12500000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (894118193/5000000000 : ℝ)^4855 ≤ (11287642410791/100000000000000 : ℝ)^3831 := by
    have hnat : (894118193 : ℕ)^4855*100000000000000^3831 ≤ 11287642410791^3831*5000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      894118193 5000000000 11287642410791 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (161834161/312500000 : ℝ)^4855 ≤ (5429292100487/12500000000000 : ℝ)^3831 := by
    have hnat : (161834161 : ℕ)^4855*12500000000000^3831 ≤ 5429292100487^3831*312500000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161834161 312500000 5429292100487 12500000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351388489/10000000000 : ℝ), (-894118193/5000000000 : ℝ), (161834161/312500000 : ℝ)] ![(5659752596241/12500000000000 : ℝ), (11287642410791/100000000000000 : ℝ), (5429292100487/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351388489/10000000000 : ℝ)|^4855 ≤ (5659752596241/12500000000000 : ℝ)^3831
        have hw : |(5351388489/10000000000 : ℝ)|=(5351388489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-894118193/5000000000 : ℝ)|^4855 ≤ (11287642410791/100000000000000 : ℝ)^3831
        have hw : |(-894118193/5000000000 : ℝ)|=(894118193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(161834161/312500000 : ℝ)|^4855 ≤ (5429292100487/12500000000000 : ℝ)^3831
        have hw : |(161834161/312500000 : ℝ)|=(161834161/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_s2_2 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535138849/1000000000 : ℝ)*x 0 + (8285909/16000000 : ℝ)*x 1 + (-89411821/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535138849/1000000000 : ℝ)^4855 ≤ (45278020780651/100000000000000 : ℝ)^3831 := by
    have hnat : (535138849 : ℕ)^4855*100000000000000^3831 ≤ 45278020780651^3831*1000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535138849 1000000000 45278020780651 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8285909/16000000 : ℝ)^4855 ≤ (21717168258457/50000000000000 : ℝ)^3831 := by
    have hnat : (8285909 : ℕ)^4855*50000000000000^3831 ≤ 21717168258457^3831*16000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8285909 16000000 21717168258457 50000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (89411821/500000000 : ℝ)^4855 ≤ (1128764268277/10000000000000 : ℝ)^3831 := by
    have hnat : (89411821 : ℕ)^4855*10000000000000^3831 ≤ 1128764268277^3831*500000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89411821 500000000 1128764268277 10000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535138849/1000000000 : ℝ), (8285909/16000000 : ℝ), (-89411821/500000000 : ℝ)] ![(45278020780651/100000000000000 : ℝ), (21717168258457/50000000000000 : ℝ), (1128764268277/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535138849/1000000000 : ℝ)|^4855 ≤ (45278020780651/100000000000000 : ℝ)^3831
        have hw : |(535138849/1000000000 : ℝ)|=(535138849/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8285909/16000000 : ℝ)|^4855 ≤ (21717168258457/50000000000000 : ℝ)^3831
        have hw : |(8285909/16000000 : ℝ)|=(8285909/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-89411821/500000000 : ℝ)|^4855 ≤ (1128764268277/10000000000000 : ℝ)^3831
        have hw : |(-89411821/500000000 : ℝ)|=(89411821/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_s2_3 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (838510001/2000000000 : ℝ)*x 0 + (3850800063/10000000000 : ℝ)*x 1 + (4556337613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (838510001/2000000000 : ℝ)^4855 ≤ (8308244870677/25000000000000 : ℝ)^3831 := by
    have hnat : (838510001 : ℕ)^4855*25000000000000^3831 ≤ 8308244870677^3831*2000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      838510001 2000000000 8308244870677 25000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3850800063/10000000000 : ℝ)^4855 ≤ (14919064589011/50000000000000 : ℝ)^3831 := by
    have hnat : (3850800063 : ℕ)^4855*50000000000000^3831 ≤ 14919064589011^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3850800063 10000000000 14919064589011 50000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4556337613/10000000000 : ℝ)^4855 ≤ (1154027853949/3125000000000 : ℝ)^3831 := by
    have hnat : (4556337613 : ℕ)^4855*3125000000000^3831 ≤ 1154027853949^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4556337613 10000000000 1154027853949 3125000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(838510001/2000000000 : ℝ), (3850800063/10000000000 : ℝ), (4556337613/10000000000 : ℝ)] ![(8308244870677/25000000000000 : ℝ), (14919064589011/50000000000000 : ℝ), (1154027853949/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(838510001/2000000000 : ℝ)|^4855 ≤ (8308244870677/25000000000000 : ℝ)^3831
        have hw : |(838510001/2000000000 : ℝ)|=(838510001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3850800063/10000000000 : ℝ)|^4855 ≤ (14919064589011/50000000000000 : ℝ)^3831
        have hw : |(3850800063/10000000000 : ℝ)|=(3850800063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4556337613/10000000000 : ℝ)|^4855 ≤ (1154027853949/3125000000000 : ℝ)^3831
        have hw : |(4556337613/10000000000 : ℝ)|=(4556337613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_s2_4 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1644813197/10000000000 : ℝ)*x 0 + (5180852907/10000000000 : ℝ)*x 1 + (545480967/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1644813197/10000000000 : ℝ)^4855 ≤ (5076447859879/50000000000000 : ℝ)^3831 := by
    have hnat : (1644813197 : ℕ)^4855*50000000000000^3831 ≤ 5076447859879^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1644813197 10000000000 5076447859879 50000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5180852907/10000000000 : ℝ)^4855 ≤ (43457293997097/100000000000000 : ℝ)^3831 := by
    have hnat : (5180852907 : ℕ)^4855*100000000000000^3831 ≤ 43457293997097^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180852907 10000000000 43457293997097 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (545480967/1000000000 : ℝ)^4855 ≤ (9277962053711/20000000000000 : ℝ)^3831 := by
    have hnat : (545480967 : ℕ)^4855*20000000000000^3831 ≤ 9277962053711^3831*1000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545480967 1000000000 9277962053711 20000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1644813197/10000000000 : ℝ), (5180852907/10000000000 : ℝ), (545480967/1000000000 : ℝ)] ![(5076447859879/50000000000000 : ℝ), (43457293997097/100000000000000 : ℝ), (9277962053711/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1644813197/10000000000 : ℝ)|^4855 ≤ (5076447859879/50000000000000 : ℝ)^3831
        have hw : |(-1644813197/10000000000 : ℝ)|=(1644813197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5180852907/10000000000 : ℝ)|^4855 ≤ (43457293997097/100000000000000 : ℝ)^3831
        have hw : |(5180852907/10000000000 : ℝ)|=(5180852907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(545480967/1000000000 : ℝ)|^4855 ≤ (9277962053711/20000000000000 : ℝ)^3831
        have hw : |(545480967/1000000000 : ℝ)|=(545480967/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_s2_5 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277187751/10000000000 : ℝ)*x 0 + (-1512119671/10000000000 : ℝ)*x 1 + (1363702451/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277187751/10000000000 : ℝ)^4855 ≤ (44483879117393/100000000000000 : ℝ)^3831 := by
    have hnat : (5277187751 : ℕ)^4855*100000000000000^3831 ≤ 44483879117393^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277187751 10000000000 44483879117393 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1512119671/10000000000 : ℝ)^4855 ≤ (570394322493/6250000000000 : ℝ)^3831 := by
    have hnat : (1512119671 : ℕ)^4855*6250000000000^3831 ≤ 570394322493^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1512119671 10000000000 570394322493 6250000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1363702451/2500000000 : ℝ)^4855 ≤ (46389811712747/100000000000000 : ℝ)^3831 := by
    have hnat : (1363702451 : ℕ)^4855*100000000000000^3831 ≤ 46389811712747^3831*2500000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1363702451 2500000000 46389811712747 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277187751/10000000000 : ℝ), (-1512119671/10000000000 : ℝ), (1363702451/2500000000 : ℝ)] ![(44483879117393/100000000000000 : ℝ), (570394322493/6250000000000 : ℝ), (46389811712747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277187751/10000000000 : ℝ)|^4855 ≤ (44483879117393/100000000000000 : ℝ)^3831
        have hw : |(5277187751/10000000000 : ℝ)|=(5277187751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1512119671/10000000000 : ℝ)|^4855 ≤ (570394322493/6250000000000 : ℝ)^3831
        have hw : |(-1512119671/10000000000 : ℝ)|=(1512119671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1363702451/2500000000 : ℝ)|^4855 ≤ (46389811712747/100000000000000 : ℝ)^3831
        have hw : |(1363702451/2500000000 : ℝ)|=(1363702451/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_s2_6 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319297159/2500000000 : ℝ)*x 0 + (1363702207/2500000000 : ℝ)*x 1 + (-1512119809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319297159/2500000000 : ℝ)^4855 ≤ (44483888571499/100000000000000 : ℝ)^3831 := by
    have hnat : (1319297159 : ℕ)^4855*100000000000000^3831 ≤ 44483888571499^3831*2500000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319297159 2500000000 44483888571499 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1363702207/2500000000 : ℝ)^4855 ≤ (23194900596929/50000000000000 : ℝ)^3831 := by
    have hnat : (1363702207 : ℕ)^4855*50000000000000^3831 ≤ 23194900596929^3831*2500000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1363702207 2500000000 23194900596929 50000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1512119809/10000000000 : ℝ)^4855 ≤ (1825262043081/20000000000000 : ℝ)^3831 := by
    have hnat : (1512119809 : ℕ)^4855*20000000000000^3831 ≤ 1825262043081^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1512119809 10000000000 1825262043081 20000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319297159/2500000000 : ℝ), (1363702207/2500000000 : ℝ), (-1512119809/10000000000 : ℝ)] ![(44483888571499/100000000000000 : ℝ), (23194900596929/50000000000000 : ℝ), (1825262043081/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319297159/2500000000 : ℝ)|^4855 ≤ (44483888571499/100000000000000 : ℝ)^3831
        have hw : |(1319297159/2500000000 : ℝ)|=(1319297159/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1363702207/2500000000 : ℝ)|^4855 ≤ (23194900596929/50000000000000 : ℝ)^3831
        have hw : |(1363702207/2500000000 : ℝ)|=(1363702207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1512119809/10000000000 : ℝ)|^4855 ≤ (1825262043081/20000000000000 : ℝ)^3831
        have hw : |(-1512119809/10000000000 : ℝ)|=(1512119809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_s2_7 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4192735719/10000000000 : ℝ)*x 0 + (1137716033/2500000000 : ℝ)*x 1 + (3856333333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4192735719/10000000000 : ℝ)^4855 ≤ (3323484506893/10000000000000 : ℝ)^3831 := by
    have hnat : (4192735719 : ℕ)^4855*10000000000000^3831 ≤ 3323484506893^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4192735719 10000000000 3323484506893 10000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1137716033/2500000000 : ℝ)^4855 ≤ (36872680325443/100000000000000 : ℝ)^3831 := by
    have hnat : (1137716033 : ℕ)^4855*100000000000000^3831 ≤ 36872680325443^3831*2500000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1137716033 2500000000 36872680325443 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3856333333/10000000000 : ℝ)^4855 ≤ (29892474595379/100000000000000 : ℝ)^3831 := by
    have hnat : (3856333333 : ℕ)^4855*100000000000000^3831 ≤ 29892474595379^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3856333333 10000000000 29892474595379 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4192735719/10000000000 : ℝ), (1137716033/2500000000 : ℝ), (3856333333/10000000000 : ℝ)] ![(3323484506893/10000000000000 : ℝ), (36872680325443/100000000000000 : ℝ), (29892474595379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4192735719/10000000000 : ℝ)|^4855 ≤ (3323484506893/10000000000000 : ℝ)^3831
        have hw : |(4192735719/10000000000 : ℝ)|=(4192735719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1137716033/2500000000 : ℝ)|^4855 ≤ (36872680325443/100000000000000 : ℝ)^3831
        have hw : |(1137716033/2500000000 : ℝ)|=(1137716033/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3856333333/10000000000 : ℝ)|^4855 ≤ (29892474595379/100000000000000 : ℝ)^3831
        have hw : |(3856333333/10000000000 : ℝ)|=(3856333333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1634_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (17675869/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9527/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10491/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (41/250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17481/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9527/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17481/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9527/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17481/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9527/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17481/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9527/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17481/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9527/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17481/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9527/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9527/100000 : ℝ) ^ (4851/1024 : ℝ) ≤ (1455473341658777/100000000000000000000 : ℝ) := by
    have hpowers : (9527/100000 : ℝ)^4851 ≤ (1455473341658777/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9527 : ℕ)^4851*100000000000000000000^1024 ≤ 1455473341658777^1024*100000^4851 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9527 100000 1455473341658777 100000000000000000000 4851 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9527/100000 : ℝ)) (X := (1455473341658777/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4851 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17481/100000 : ℝ) ^ (4851/1024 : ℝ) ≤ (12905524453207691/50000000000000000000 : ℝ) := by
    have hpowers : (17481/100000 : ℝ)^4851 ≤ (12905524453207691/50000000000000000000 : ℝ)^1024 := by
      have hnat : (17481 : ℕ)^4851*50000000000000000000^1024 ≤ 12905524453207691^1024*100000^4851 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17481 100000 12905524453207691 50000000000000000000 4851 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17481/100000 : ℝ)) (X := (12905524453207691/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4851 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001455473341658777/50000000000000000000 : ℝ) ≤ (10000061446612607/10000000000000000 : ℝ) ^ (4851/1024 : ℝ) := by
    have hpowers : (50001455473341658777/50000000000000000000 : ℝ)^1024 ≤ (10000061446612607/10000000000000000 : ℝ)^4851 := by
      have hnat : (50001455473341658777 : ℕ)^1024*10000000000000000^4851 ≤ 10000061446612607^4851*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001455473341658777 50000000000000000000 10000061446612607 10000000000000000 1024 4851 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000061446612607/10000000000000000 : ℝ)) (X := (50001455473341658777/50000000000000000000 : ℝ)) (by norm_num) 4851 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100027266522248074159/100000000000000000000 : ℝ) ≤ (10000575508477863/10000000000000000 : ℝ) ^ (4851/1024 : ℝ) := by
    have hpowers : (100027266522248074159/100000000000000000000 : ℝ)^1024 ≤ (10000575508477863/10000000000000000 : ℝ)^4851 := by
      have hnat : (100027266522248074159 : ℕ)^1024*10000000000000000^4851 ≤ 10000575508477863^4851*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100027266522248074159 100000000000000000000 10000575508477863 10000000000000000 1024 4851 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000575508477863/10000000000000000 : ℝ)) (X := (100027266522248074159/100000000000000000000 : ℝ)) (by norm_num) 4851 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25012905524453207691/25000000000000000000 : ℝ) ≤ (10001089570343119/10000000000000000 : ℝ) ^ (4851/1024 : ℝ) := by
    have hpowers : (25012905524453207691/25000000000000000000 : ℝ)^1024 ≤ (10001089570343119/10000000000000000 : ℝ)^4851 := by
      have hnat : (25012905524453207691 : ℕ)^1024*10000000000000000^4851 ≤ 10001089570343119^4851*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012905524453207691 25000000000000000000 10001089570343119 10000000000000000 1024 4851 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001089570343119/10000000000000000 : ℝ)) (X := (25012905524453207691/25000000000000000000 : ℝ)) (by norm_num) 4851 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1455473341658777/100000000000000000000 : ℝ) ≤ ((39765346905788044127/39770000000000000000 : ℝ)+2*(64257733157/99425000000000 : ℝ)*(9527/100000 : ℝ))^(4851/1024 : ℝ) := by
    rw [show (39765346905788044127/39770000000000000000 : ℝ)+2*(64257733157/99425000000000 : ℝ)*(9527/100000 : ℝ)=(10000061446612607/10000000000000000 : ℝ) by norm_num, show 1+2*(1455473341658777/100000000000000000000 : ℝ)=(50001455473341658777/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(12905524453207691/50000000000000000000 : ℝ)+(1455473341658777/100000000000000000000 : ℝ) ≤ ((39765346905788044127/39770000000000000000 : ℝ)+(64257733157/99425000000000 : ℝ)*((17481/100000 : ℝ)+(9527/100000 : ℝ)))^(4851/1024 : ℝ) := by
    rw [show (39765346905788044127/39770000000000000000 : ℝ)+(64257733157/99425000000000 : ℝ)*((17481/100000 : ℝ)+(9527/100000 : ℝ))=(10000575508477863/10000000000000000 : ℝ) by norm_num, show 1+(12905524453207691/50000000000000000000 : ℝ)+(1455473341658777/100000000000000000000 : ℝ)=(100027266522248074159/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(12905524453207691/50000000000000000000 : ℝ) ≤ ((39765346905788044127/39770000000000000000 : ℝ)+2*(64257733157/99425000000000 : ℝ)*(17481/100000 : ℝ))^(4851/1024 : ℝ) := by
    rw [show (39765346905788044127/39770000000000000000 : ℝ)+2*(64257733157/99425000000000 : ℝ)*(17481/100000 : ℝ)=(10001089570343119/10000000000000000 : ℝ) by norm_num, show 1+2*(12905524453207691/50000000000000000000 : ℝ)=(25012905524453207691/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (39765346905788044127/39770000000000000000 : ℝ)*(X 1 0+X 2 0)+(64257733157/99425000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4851/1024 : ℝ)) (lo := (9527/100000 : ℝ)) (hi := (17481/100000 : ℝ)) (c := (39765346905788044127/39770000000000000000 : ℝ)) (alpha := (64257733157/99425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (39765346905788044127/39770000000000000000 : ℝ)*(X 0 1+X 2 1)+(64257733157/99425000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4851/1024 : ℝ)) (lo := (9527/100000 : ℝ)) (hi := (17481/100000 : ℝ)) (c := (39765346905788044127/39770000000000000000 : ℝ)) (alpha := (64257733157/99425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (39765346905788044127/39770000000000000000 : ℝ)*(X 0 2+X 1 2)+(64257733157/99425000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4851/1024 : ℝ)) (lo := (9527/100000 : ℝ)) (hi := (17481/100000 : ℝ)) (c := (39765346905788044127/39770000000000000000 : ℝ)) (alpha := (64257733157/99425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-65789609/400000000 : ℝ)*X 0 0+(5456992651/10000000000 : ℝ)*X 0 1+(647336639/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351388489/10000000000 : ℝ)*X 1 0+(-894118193/5000000000 : ℝ)*X 1 1+(161834161/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((535138849/1000000000 : ℝ)*X 2 0+(8285909/16000000 : ℝ)*X 2 1+(-89411821/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((838510001/2000000000 : ℝ)*X 0 0+(3850800063/10000000000 : ℝ)*X 0 1+(4556337613/10000000000 : ℝ)*X 0 2+(838510001/2000000000 : ℝ)*X 1 0+(3850800063/10000000000 : ℝ)*X 1 1+(4556337613/10000000000 : ℝ)*X 1 2+(838510001/2000000000 : ℝ)*X 2 0+(3850800063/10000000000 : ℝ)*X 2 1+(4556337613/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1644813197/10000000000 : ℝ)*X 0 0+(5180852907/10000000000 : ℝ)*X 0 1+(545480967/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5277187751/10000000000 : ℝ)*X 1 0+(-1512119671/10000000000 : ℝ)*X 1 1+(1363702451/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1319297159/2500000000 : ℝ)*X 2 0+(1363702207/2500000000 : ℝ)*X 2 1+(-1512119809/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4192735719/10000000000 : ℝ)*X 0 0+(1137716033/2500000000 : ℝ)*X 0 1+(3856333333/10000000000 : ℝ)*X 0 2+(4192735719/10000000000 : ℝ)*X 1 0+(1137716033/2500000000 : ℝ)*X 1 1+(3856333333/10000000000 : ℝ)*X 1 2+(4192735719/10000000000 : ℝ)*X 2 0+(1137716033/2500000000 : ℝ)*X 2 1+(3856333333/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11349401947858890598770712359/994250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (70697221/4000000000000 : ℝ)*(base19) + (815018201/50000000000000 : ℝ)*(base23) + (73884263/100000000000000 : ℝ)*(lower2) + (73554769/25000000000000 : ℝ)*(upper3) + (5191807/3125000000000 : ℝ)*(upper5) + (1252667462960461/50000000000000 : ℝ)*(major0) + (1252667462960461/50000000000000 : ℝ)*(major1) + (1252667462960461/50000000000000 : ℝ)*(major2) + (449159116050399/12500000000000 : ℝ)*(sp0) + (3593291887241037/100000000000000 : ℝ)*(sp1) + (89832300615879/2500000000000 : ℝ)*(sp2) + (1417366692779207/100000000000000 : ℝ)*(sp3) + (2072626837/10000000000000 : ℝ)*(sp4) + (9123889791/100000000000000 : ℝ)*(sp7) + (708687908334499/50000000000000 : ℝ)*(f.failure) + (1796646827335781/50000000000000 : ℝ)*(f.sum) + (23941524132237/9942500000000000000000000000 : ℝ)*base66 + (4054632088877562547/1988500000000000000000000000000000 : ℝ)*base67 + (3055594451002062547/1988500000000000000000000000000000 : ℝ)*base69 + (18720560836169437453/1988500000000000000000000000000000 : ℝ)*base72 + (15100249447319/19885000000000000000000000000 : ℝ)*base74 + (8573826674032062547/1988500000000000000000000000000000 : ℝ)*base75 + (561754030861062547/1988500000000000000000000000000000 : ℝ)*base77 + (15511574410815437453/1988500000000000000000000000000000 : ℝ)*base80 + (1817749254413/9942500000000000000000000000 : ℝ)*base81 + (2504631/500000000000000000000 : ℝ)*base89 + (2504631/500000000000000000000 : ℝ)*base91 + (2504631/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (203441646455900439335207799/62140625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (182295233/100000000000000 : ℝ)*(base19) + (1095052419/100000000000000 : ℝ)*(base23) + (132647969/100000000000000 : ℝ)*(lower4) + (66098163/100000000000000 : ℝ)*(lower5) + (159063640874971/6250000000000 : ℝ)*(major0) + (159063640874971/6250000000000 : ℝ)*(major1) + (159063640874971/6250000000000 : ℝ)*(major2) + (596529869/12500000000000 : ℝ)*(sp1) + (8274680829/100000000000000 : ℝ)*(sp2) + (456875263/20000000000000 : ℝ)*(sp3) + (912552503806901/25000000000000 : ℝ)*(sp4) + (1825102530346709/50000000000000 : ℝ)*(sp5) + (912550161373589/25000000000000 : ℝ)*(sp6) + (1439824099265437/100000000000000 : ℝ)*(sp7) + (179978297955219/12500000000000 : ℝ)*(f.failure) + (912552503806901/25000000000000 : ℝ)*(f.sum) + (16779905663229/9942500000000000000000000000 : ℝ)*base65 + (247045809304832817/248562500000000000000000000000000 : ℝ)*base67 + (1652189521967145317/248562500000000000000000000000000 : ℝ)*base69 + (2032976353113645317/248562500000000000000000000000000 : ℝ)*base71 + (33414753552807/19885000000000000000000000000 : ℝ)*base74 + (1546650854855145317/248562500000000000000000000000000 : ℝ)*base75 + (717223142747395317/248562500000000000000000000000000 : ℝ)*base77 + (1193257194257979683/248562500000000000000000000000000 : ℝ)*base80 + (1782499278161/2485625000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1089689/125000000000000000000 : ℝ)*base90 + (1089689/125000000000000000000 : ℝ)*base92 + (1089689/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1634_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (17675869/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9527/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10491/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (41/250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1634_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1634_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (17675869/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10491/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (41/250 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1634_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1634_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1634_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (17675869/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10491/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (41/250 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1634_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
