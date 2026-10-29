-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1634_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:00:56.68499+00:00
-- url     : https://prove2.me/submissions/3183f3d7-5ac3-48bd-add6-00c939031cf8

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
theorem support_rectangle_w1634_box_0 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-69091711/500000000 : ℝ)*x 0 + (5412030263/10000000000 : ℝ)*x 1 + (541203039/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (69091711/500000000 : ℝ)^4855 ≤ (4070762098153/50000000000000 : ℝ)^3831 := by
    have hnat : (69091711 : ℕ)^4855*50000000000000^3831 ≤ 4070762098153^3831*500000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69091711 500000000 4070762098153 50000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412030263/10000000000 : ℝ)^4855 ≤ (358822165723/781250000000 : ℝ)^3831 := by
    have hnat : (5412030263 : ℕ)^4855*781250000000^3831 ≤ 358822165723^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412030263 10000000000 358822165723 781250000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541203039/1000000000 : ℝ)^4855 ≤ (9185847715683/20000000000000 : ℝ)^3831 := by
    have hnat : (541203039 : ℕ)^4855*20000000000000^3831 ≤ 9185847715683^3831*1000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541203039 1000000000 9185847715683 20000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-69091711/500000000 : ℝ), (5412030263/10000000000 : ℝ), (541203039/1000000000 : ℝ)] ![(4070762098153/50000000000000 : ℝ), (358822165723/781250000000 : ℝ), (9185847715683/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-69091711/500000000 : ℝ)|^4855 ≤ (4070762098153/50000000000000 : ℝ)^3831
        have hw : |(-69091711/500000000 : ℝ)|=(69091711/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412030263/10000000000 : ℝ)|^4855 ≤ (358822165723/781250000000 : ℝ)^3831
        have hw : |(5412030263/10000000000 : ℝ)|=(5412030263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541203039/1000000000 : ℝ)|^4855 ≤ (9185847715683/20000000000000 : ℝ)^3831
        have hw : |(541203039/1000000000 : ℝ)|=(541203039/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_box_1 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1312809013/2500000000 : ℝ)*x 0 + (-50242549/312500000 : ℝ)*x 1 + (1353007553/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1312809013/2500000000 : ℝ)^4855 ≤ (345365857673/781250000000 : ℝ)^3831 := by
    have hnat : (1312809013 : ℕ)^4855*781250000000^3831 ≤ 345365857673^3831*2500000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1312809013 2500000000 345365857673 781250000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (50242549/312500000 : ℝ)^4855 ≤ (4931966771263/50000000000000 : ℝ)^3831 := by
    have hnat : (50242549 : ℕ)^4855*50000000000000^3831 ≤ 4931966771263^3831*312500000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50242549 312500000 4931966771263 50000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353007553/2500000000 : ℝ)^4855 ≤ (11482309166011/25000000000000 : ℝ)^3831 := by
    have hnat : (1353007553 : ℕ)^4855*25000000000000^3831 ≤ 11482309166011^3831*2500000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353007553 2500000000 11482309166011 25000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1312809013/2500000000 : ℝ), (-50242549/312500000 : ℝ), (1353007553/2500000000 : ℝ)] ![(345365857673/781250000000 : ℝ), (4931966771263/50000000000000 : ℝ), (11482309166011/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1312809013/2500000000 : ℝ)|^4855 ≤ (345365857673/781250000000 : ℝ)^3831
        have hw : |(1312809013/2500000000 : ℝ)|=(1312809013/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-50242549/312500000 : ℝ)|^4855 ≤ (4931966771263/50000000000000 : ℝ)^3831
        have hw : |(-50242549/312500000 : ℝ)|=(50242549/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353007553/2500000000 : ℝ)|^4855 ≤ (11482309166011/25000000000000 : ℝ)^3831
        have hw : |(1353007553/2500000000 : ℝ)|=(1353007553/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_box_2 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5251235919/10000000000 : ℝ)*x 0 + (5412030361/10000000000 : ℝ)*x 1 + (-321552309/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251235919/10000000000 : ℝ)^4855 ≤ (44206828363229/100000000000000 : ℝ)^3831 := by
    have hnat : (5251235919 : ℕ)^4855*100000000000000^3831 ≤ 44206828363229^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251235919 10000000000 44206828363229 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412030361/10000000000 : ℝ)^4855 ≤ (45929238266523/100000000000000 : ℝ)^3831 := by
    have hnat : (5412030361 : ℕ)^4855*100000000000000^3831 ≤ 45929238266523^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412030361 10000000000 45929238266523 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (321552309/2000000000 : ℝ)^4855 ≤ (9863933363699/100000000000000 : ℝ)^3831 := by
    have hnat : (321552309 : ℕ)^4855*100000000000000^3831 ≤ 9863933363699^3831*2000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321552309 2000000000 9863933363699 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251235919/10000000000 : ℝ), (5412030361/10000000000 : ℝ), (-321552309/2000000000 : ℝ)] ![(44206828363229/100000000000000 : ℝ), (45929238266523/100000000000000 : ℝ), (9863933363699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251235919/10000000000 : ℝ)|^4855 ≤ (44206828363229/100000000000000 : ℝ)^3831
        have hw : |(5251235919/10000000000 : ℝ)|=(5251235919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412030361/10000000000 : ℝ)|^4855 ≤ (45929238266523/100000000000000 : ℝ)^3831
        have hw : |(5412030361/10000000000 : ℝ)|=(5412030361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-321552309/2000000000 : ℝ)|^4855 ≤ (9863933363699/100000000000000 : ℝ)^3831
        have hw : |(-321552309/2000000000 : ℝ)|=(321552309/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_box_3 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (894223421/2000000000 : ℝ)*x 0 + (1016631019/2500000000 : ℝ)*x 1 + (2033262061/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (894223421/2000000000 : ℝ)^4855 ≤ (36055759937869/100000000000000 : ℝ)^3831 := by
    have hnat : (894223421 : ℕ)^4855*100000000000000^3831 ≤ 36055759937869^3831*2000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      894223421 2000000000 36055759937869 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1016631019/2500000000 : ℝ)^4855 ≤ (31972119791547/100000000000000 : ℝ)^3831 := by
    have hnat : (1016631019 : ℕ)^4855*100000000000000^3831 ≤ 31972119791547^3831*2500000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016631019 2500000000 31972119791547 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2033262061/5000000000 : ℝ)^4855 ≤ (15986060124941/50000000000000 : ℝ)^3831 := by
    have hnat : (2033262061 : ℕ)^4855*50000000000000^3831 ≤ 15986060124941^3831*5000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2033262061 5000000000 15986060124941 50000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(894223421/2000000000 : ℝ), (1016631019/2500000000 : ℝ), (2033262061/5000000000 : ℝ)] ![(36055759937869/100000000000000 : ℝ), (31972119791547/100000000000000 : ℝ), (15986060124941/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(894223421/2000000000 : ℝ)|^4855 ≤ (36055759937869/100000000000000 : ℝ)^3831
        have hw : |(894223421/2000000000 : ℝ)|=(894223421/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1016631019/2500000000 : ℝ)|^4855 ≤ (31972119791547/100000000000000 : ℝ)^3831
        have hw : |(1016631019/2500000000 : ℝ)|=(1016631019/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2033262061/5000000000 : ℝ)|^4855 ≤ (15986060124941/50000000000000 : ℝ)^3831
        have hw : |(2033262061/5000000000 : ℝ)|=(2033262061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_box_4 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1920226431/10000000000 : ℝ)*x 0 + (5215238617/10000000000 : ℝ)*x 1 + (1303809739/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1920226431/10000000000 : ℝ)^4855 ≤ (12353711962147/100000000000000 : ℝ)^3831 := by
    have hnat : (1920226431 : ℕ)^4855*100000000000000^3831 ≤ 12353711962147^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1920226431 10000000000 12353711962147 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215238617/10000000000 : ℝ)^4855 ≤ (21911571102683/50000000000000 : ℝ)^3831 := by
    have hnat : (5215238617 : ℕ)^4855*50000000000000^3831 ≤ 21911571102683^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215238617 10000000000 21911571102683 50000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1303809739/2500000000 : ℝ)^4855 ≤ (43823145815357/100000000000000 : ℝ)^3831 := by
    have hnat : (1303809739 : ℕ)^4855*100000000000000^3831 ≤ 43823145815357^3831*2500000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303809739 2500000000 43823145815357 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1920226431/10000000000 : ℝ), (5215238617/10000000000 : ℝ), (1303809739/2500000000 : ℝ)] ![(12353711962147/100000000000000 : ℝ), (21911571102683/50000000000000 : ℝ), (43823145815357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1920226431/10000000000 : ℝ)|^4855 ≤ (12353711962147/100000000000000 : ℝ)^3831
        have hw : |(-1920226431/10000000000 : ℝ)|=(1920226431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215238617/10000000000 : ℝ)|^4855 ≤ (21911571102683/50000000000000 : ℝ)^3831
        have hw : |(5215238617/10000000000 : ℝ)|=(5215238617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1303809739/2500000000 : ℝ)|^4855 ≤ (43823145815357/100000000000000 : ℝ)^3831
        have hw : |(1303809739/2500000000 : ℝ)|=(1303809739/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_box_5 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (538660347/1000000000 : ℝ)*x 0 + (-845840821/5000000000 : ℝ)*x 1 + (1043047653/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538660347/1000000000 : ℝ)^4855 ≤ (11413986668889/25000000000000 : ℝ)^3831 := by
    have hnat : (538660347 : ℕ)^4855*25000000000000^3831 ≤ 11413986668889^3831*1000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538660347 1000000000 11413986668889 25000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (845840821/5000000000 : ℝ)^4855 ≤ (10520914846321/100000000000000 : ℝ)^3831 := by
    have hnat : (845840821 : ℕ)^4855*100000000000000^3831 ≤ 10520914846321^3831*5000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845840821 5000000000 10520914846321 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043047653/2000000000 : ℝ)^4855 ≤ (43823138456939/100000000000000 : ℝ)^3831 := by
    have hnat : (1043047653 : ℕ)^4855*100000000000000^3831 ≤ 43823138456939^3831*2000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043047653 2000000000 43823138456939 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538660347/1000000000 : ℝ), (-845840821/5000000000 : ℝ), (1043047653/2000000000 : ℝ)] ![(11413986668889/25000000000000 : ℝ), (10520914846321/100000000000000 : ℝ), (43823138456939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538660347/1000000000 : ℝ)|^4855 ≤ (11413986668889/25000000000000 : ℝ)^3831
        have hw : |(538660347/1000000000 : ℝ)|=(538660347/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-845840821/5000000000 : ℝ)|^4855 ≤ (10520914846321/100000000000000 : ℝ)^3831
        have hw : |(-845840821/5000000000 : ℝ)|=(845840821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043047653/2000000000 : ℝ)|^4855 ≤ (43823138456939/100000000000000 : ℝ)^3831
        have hw : |(1043047653/2000000000 : ℝ)|=(1043047653/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_box_6 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5386603793/10000000000 : ℝ)*x 0 + (5215237737/10000000000 : ℝ)*x 1 + (-422920479/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5386603793/10000000000 : ℝ)^4855 ≤ (45655950145017/100000000000000 : ℝ)^3831 := by
    have hnat : (5386603793 : ℕ)^4855*100000000000000^3831 ≤ 45655950145017^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386603793 10000000000 45655950145017 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215237737/10000000000 : ℝ)^4855 ≤ (21911566417149/50000000000000 : ℝ)^3831 := by
    have hnat : (5215237737 : ℕ)^4855*50000000000000^3831 ≤ 21911566417149^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215237737 10000000000 21911566417149 50000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (422920479/2500000000 : ℝ)^4855 ≤ (10520917005867/100000000000000 : ℝ)^3831 := by
    have hnat : (422920479 : ℕ)^4855*100000000000000^3831 ≤ 10520917005867^3831*2500000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422920479 2500000000 10520917005867 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5386603793/10000000000 : ℝ), (5215237737/10000000000 : ℝ), (-422920479/2500000000 : ℝ)] ![(45655950145017/100000000000000 : ℝ), (21911566417149/50000000000000 : ℝ), (10520917005867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5386603793/10000000000 : ℝ)|^4855 ≤ (45655950145017/100000000000000 : ℝ)^3831
        have hw : |(5386603793/10000000000 : ℝ)|=(5386603793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215237737/10000000000 : ℝ)|^4855 ≤ (21911566417149/50000000000000 : ℝ)^3831
        have hw : |(5215237737/10000000000 : ℝ)|=(5215237737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-422920479/2500000000 : ℝ)|^4855 ≤ (10520917005867/100000000000000 : ℝ)^3831
        have hw : |(-422920479/2500000000 : ℝ)|=(422920479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_box_7 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (977252343/2500000000 : ℝ)*x 0 + (4347246063/10000000000 : ℝ)*x 1 + (869449211/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (977252343/2500000000 : ℝ)^4855 ≤ (30410876966017/100000000000000 : ℝ)^3831 := by
    have hnat : (977252343 : ℕ)^4855*100000000000000^3831 ≤ 30410876966017^3831*2500000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      977252343 2500000000 30410876966017 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4347246063/10000000000 : ℝ)^4855 ≤ (1087330048459/3125000000000 : ℝ)^3831 := by
    have hnat : (4347246063 : ℕ)^4855*3125000000000^3831 ≤ 1087330048459^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4347246063 10000000000 1087330048459 3125000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (869449211/2000000000 : ℝ)^4855 ≤ (34794561469543/100000000000000 : ℝ)^3831 := by
    have hnat : (869449211 : ℕ)^4855*100000000000000^3831 ≤ 34794561469543^3831*2000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869449211 2000000000 34794561469543 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(977252343/2500000000 : ℝ), (4347246063/10000000000 : ℝ), (869449211/2000000000 : ℝ)] ![(30410876966017/100000000000000 : ℝ), (1087330048459/3125000000000 : ℝ), (34794561469543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(977252343/2500000000 : ℝ)|^4855 ≤ (30410876966017/100000000000000 : ℝ)^3831
        have hw : |(977252343/2500000000 : ℝ)|=(977252343/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4347246063/10000000000 : ℝ)|^4855 ≤ (1087330048459/3125000000000 : ℝ)^3831
        have hw : |(4347246063/10000000000 : ℝ)|=(4347246063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(869449211/2000000000 : ℝ)|^4855 ≤ (34794561469543/100000000000000 : ℝ)^3831
        have hw : |(869449211/2000000000 : ℝ)|=(869449211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_box_8 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-451380179/2500000000 : ℝ)*x 0 + (5074090039/10000000000 : ℝ)*x 1 + (217667323/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (451380179/2500000000 : ℝ)^4855 ≤ (5713042111671/50000000000000 : ℝ)^3831 := by
    have hnat : (451380179 : ℕ)^4855*50000000000000^3831 ≤ 5713042111671^3831*2500000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451380179 2500000000 5713042111671 50000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5074090039/10000000000 : ℝ)^4855 ≤ (42325532516709/100000000000000 : ℝ)^3831 := by
    have hnat : (5074090039 : ℕ)^4855*100000000000000^3831 ≤ 42325532516709^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5074090039 10000000000 42325532516709 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (217667323/400000000 : ℝ)^4855 ≤ (11562095812629/25000000000000 : ℝ)^3831 := by
    have hnat : (217667323 : ℕ)^4855*25000000000000^3831 ≤ 11562095812629^3831*400000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217667323 400000000 11562095812629 25000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-451380179/2500000000 : ℝ), (5074090039/10000000000 : ℝ), (217667323/400000000 : ℝ)] ![(5713042111671/50000000000000 : ℝ), (42325532516709/100000000000000 : ℝ), (11562095812629/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-451380179/2500000000 : ℝ)|^4855 ≤ (5713042111671/50000000000000 : ℝ)^3831
        have hw : |(-451380179/2500000000 : ℝ)|=(451380179/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5074090039/10000000000 : ℝ)|^4855 ≤ (42325532516709/100000000000000 : ℝ)^3831
        have hw : |(5074090039/10000000000 : ℝ)|=(5074090039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(217667323/400000000 : ℝ)|^4855 ≤ (11562095812629/25000000000000 : ℝ)^3831
        have hw : |(217667323/400000000 : ℝ)|=(217667323/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_box_9 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2615418557/5000000000 : ℝ)*x 0 + (-318934973/2000000000 : ℝ)*x 1 + (2720841843/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2615418557/5000000000 : ℝ)^4855 ≤ (43989316026067/100000000000000 : ℝ)^3831 := by
    have hnat : (2615418557 : ℕ)^4855*100000000000000^3831 ≤ 43989316026067^3831*5000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615418557 5000000000 43989316026067 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (318934973/2000000000 : ℝ)^4855 ≤ (9762294122569/100000000000000 : ℝ)^3831 := by
    have hnat : (318934973 : ℕ)^4855*100000000000000^3831 ≤ 9762294122569^3831*2000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      318934973 2000000000 9762294122569 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2720841843/5000000000 : ℝ)^4855 ≤ (46248389831361/100000000000000 : ℝ)^3831 := by
    have hnat : (2720841843 : ℕ)^4855*100000000000000^3831 ≤ 46248389831361^3831*5000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2720841843 5000000000 46248389831361 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2615418557/5000000000 : ℝ), (-318934973/2000000000 : ℝ), (2720841843/5000000000 : ℝ)] ![(43989316026067/100000000000000 : ℝ), (9762294122569/100000000000000 : ℝ), (46248389831361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2615418557/5000000000 : ℝ)|^4855 ≤ (43989316026067/100000000000000 : ℝ)^3831
        have hw : |(2615418557/5000000000 : ℝ)|=(2615418557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-318934973/2000000000 : ℝ)|^4855 ≤ (9762294122569/100000000000000 : ℝ)^3831
        have hw : |(-318934973/2000000000 : ℝ)|=(318934973/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2720841843/5000000000 : ℝ)|^4855 ≤ (46248389831361/100000000000000 : ℝ)^3831
        have hw : |(2720841843/5000000000 : ℝ)|=(2720841843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_box_10 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5230837337/10000000000 : ℝ)*x 0 + (5441683707/10000000000 : ℝ)*x 1 + (-159467453/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5230837337/10000000000 : ℝ)^4855 ≤ (43989318402677/100000000000000 : ℝ)^3831 := by
    have hnat : (5230837337 : ℕ)^4855*100000000000000^3831 ≤ 43989318402677^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230837337 10000000000 43989318402677 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5441683707/10000000000 : ℝ)^4855 ≤ (46248390057543/100000000000000 : ℝ)^3831 := by
    have hnat : (5441683707 : ℕ)^4855*100000000000000^3831 ≤ 46248390057543^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5441683707 10000000000 46248390057543 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (159467453/1000000000 : ℝ)^4855 ≤ (9762291523597/100000000000000 : ℝ)^3831 := by
    have hnat : (159467453 : ℕ)^4855*100000000000000^3831 ≤ 9762291523597^3831*1000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      159467453 1000000000 9762291523597 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5230837337/10000000000 : ℝ), (5441683707/10000000000 : ℝ), (-159467453/1000000000 : ℝ)] ![(43989318402677/100000000000000 : ℝ), (46248390057543/100000000000000 : ℝ), (9762291523597/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5230837337/10000000000 : ℝ)|^4855 ≤ (43989318402677/100000000000000 : ℝ)^3831
        have hw : |(5230837337/10000000000 : ℝ)|=(5230837337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5441683707/10000000000 : ℝ)|^4855 ≤ (46248390057543/100000000000000 : ℝ)^3831
        have hw : |(5441683707/10000000000 : ℝ)|=(5441683707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-159467453/1000000000 : ℝ)|^4855 ≤ (9762291523597/100000000000000 : ℝ)^3831
        have hw : |(-159467453/1000000000 : ℝ)|=(159467453/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_box_11 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (142294727/312500000 : ℝ)*x 0 + (125754617/312500000 : ℝ)*x 1 + (4024147591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (142294727/312500000 : ℝ)^4855 ≤ (36899041748857/100000000000000 : ℝ)^3831 := by
    have hnat : (142294727 : ℕ)^4855*100000000000000^3831 ≤ 36899041748857^3831*312500000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142294727 312500000 36899041748857 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (125754617/312500000 : ℝ)^4855 ≤ (31550479877709/100000000000000 : ℝ)^3831 := by
    have hnat : (125754617 : ℕ)^4855*100000000000000^3831 ≤ 31550479877709^3831*312500000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125754617 312500000 31550479877709 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4024147591/10000000000 : ℝ)^4855 ≤ (31550478357509/100000000000000 : ℝ)^3831 := by
    have hnat : (4024147591 : ℕ)^4855*100000000000000^3831 ≤ 31550478357509^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4024147591 10000000000 31550478357509 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(142294727/312500000 : ℝ), (125754617/312500000 : ℝ), (4024147591/10000000000 : ℝ)] ![(36899041748857/100000000000000 : ℝ), (31550479877709/100000000000000 : ℝ), (31550478357509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(142294727/312500000 : ℝ)|^4855 ≤ (36899041748857/100000000000000 : ℝ)^3831
        have hw : |(142294727/312500000 : ℝ)|=(142294727/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(125754617/312500000 : ℝ)|^4855 ≤ (31550479877709/100000000000000 : ℝ)^3831
        have hw : |(125754617/312500000 : ℝ)|=(125754617/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4024147591/10000000000 : ℝ)|^4855 ≤ (31550478357509/100000000000000 : ℝ)^3831
        have hw : |(4024147591/10000000000 : ℝ)|=(4024147591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_box_12 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1494979131/10000000000 : ℝ)*x 0 + (5547654329/10000000000 : ℝ)*x 1 + (5195389611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1494979131/10000000000 : ℝ)^4855 ≤ (562212871189/6250000000000 : ℝ)^3831 := by
    have hnat : (1494979131 : ℕ)^4855*6250000000000^3831 ≤ 562212871189^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1494979131 10000000000 562212871189 6250000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5547654329/10000000000 : ℝ)^4855 ≤ (4739271510917/10000000000000 : ℝ)^3831 := by
    have hnat : (5547654329 : ℕ)^4855*10000000000000^3831 ≤ 4739271510917^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5547654329 10000000000 4739271510917 10000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5195389611/10000000000 : ℝ)^4855 ≤ (872237578607/2000000000000 : ℝ)^3831 := by
    have hnat : (5195389611 : ℕ)^4855*2000000000000^3831 ≤ 872237578607^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195389611 10000000000 872237578607 2000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1494979131/10000000000 : ℝ), (5547654329/10000000000 : ℝ), (5195389611/10000000000 : ℝ)] ![(562212871189/6250000000000 : ℝ), (4739271510917/10000000000000 : ℝ), (872237578607/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1494979131/10000000000 : ℝ)|^4855 ≤ (562212871189/6250000000000 : ℝ)^3831
        have hw : |(-1494979131/10000000000 : ℝ)|=(1494979131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5547654329/10000000000 : ℝ)|^4855 ≤ (4739271510917/10000000000000 : ℝ)^3831
        have hw : |(5547654329/10000000000 : ℝ)|=(5547654329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5195389611/10000000000 : ℝ)|^4855 ≤ (872237578607/2000000000000 : ℝ)^3831
        have hw : |(5195389611/10000000000 : ℝ)|=(5195389611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_box_13 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5400265597/10000000000 : ℝ)*x 0 + (-849927613/5000000000 : ℝ)*x 1 + (5195389407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5400265597/10000000000 : ℝ)^4855 ≤ (45802746265649/100000000000000 : ℝ)^3831 := by
    have hnat : (5400265597 : ℕ)^4855*100000000000000^3831 ≤ 45802746265649^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400265597 10000000000 45802746265649 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (849927613/5000000000 : ℝ)^4855 ≤ (2646344238399/25000000000000 : ℝ)^3831 := by
    have hnat : (849927613 : ℕ)^4855*25000000000000^3831 ≤ 2646344238399^3831*5000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849927613 5000000000 2646344238399 25000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5195389407/10000000000 : ℝ)^4855 ≤ (43611876760179/100000000000000 : ℝ)^3831 := by
    have hnat : (5195389407 : ℕ)^4855*100000000000000^3831 ≤ 43611876760179^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195389407 10000000000 43611876760179 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5400265597/10000000000 : ℝ), (-849927613/5000000000 : ℝ), (5195389407/10000000000 : ℝ)] ![(45802746265649/100000000000000 : ℝ), (2646344238399/25000000000000 : ℝ), (43611876760179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5400265597/10000000000 : ℝ)|^4855 ≤ (45802746265649/100000000000000 : ℝ)^3831
        have hw : |(5400265597/10000000000 : ℝ)|=(5400265597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-849927613/5000000000 : ℝ)|^4855 ≤ (2646344238399/25000000000000 : ℝ)^3831
        have hw : |(-849927613/5000000000 : ℝ)|=(849927613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5195389407/10000000000 : ℝ)|^4855 ≤ (43611876760179/100000000000000 : ℝ)^3831
        have hw : |(5195389407/10000000000 : ℝ)|=(5195389407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_box_14 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2700132747/5000000000 : ℝ)*x 0 + (5195389313/10000000000 : ℝ)*x 1 + (-849927747/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2700132747/5000000000 : ℝ)^4855 ≤ (45802745158539/100000000000000 : ℝ)^3831 := by
    have hnat : (2700132747 : ℕ)^4855*100000000000000^3831 ≤ 45802745158539^3831*5000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700132747 5000000000 45802745158539 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5195389313/10000000000 : ℝ)^4855 ≤ (21805937880099/50000000000000 : ℝ)^3831 := by
    have hnat : (5195389313 : ℕ)^4855*50000000000000^3831 ≤ 21805937880099^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195389313 10000000000 21805937880099 50000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (849927747/5000000000 : ℝ)^4855 ≤ (330793095893/3125000000000 : ℝ)^3831 := by
    have hnat : (849927747 : ℕ)^4855*3125000000000^3831 ≤ 330793095893^3831*5000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849927747 5000000000 330793095893 3125000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2700132747/5000000000 : ℝ), (5195389313/10000000000 : ℝ), (-849927747/5000000000 : ℝ)] ![(45802745158539/100000000000000 : ℝ), (21805937880099/50000000000000 : ℝ), (330793095893/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2700132747/5000000000 : ℝ)|^4855 ≤ (45802745158539/100000000000000 : ℝ)^3831
        have hw : |(2700132747/5000000000 : ℝ)|=(2700132747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5195389313/10000000000 : ℝ)|^4855 ≤ (21805937880099/50000000000000 : ℝ)^3831
        have hw : |(5195389313/10000000000 : ℝ)|=(5195389313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-849927747/5000000000 : ℝ)|^4855 ≤ (330793095893/3125000000000 : ℝ)^3831
        have hw : |(-849927747/5000000000 : ℝ)|=(849927747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_box_15 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1925343219/5000000000 : ℝ)*x 0 + (109387741/250000000 : ℝ)*x 1 + (4375509721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1925343219/5000000000 : ℝ)^4855 ≤ (29837013420341/100000000000000 : ℝ)^3831 := by
    have hnat : (1925343219 : ℕ)^4855*100000000000000^3831 ≤ 29837013420341^3831*5000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1925343219 5000000000 29837013420341 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (109387741/250000000 : ℝ)^4855 ≤ (7016298573419/20000000000000 : ℝ)^3831 := by
    have hnat : (109387741 : ℕ)^4855*20000000000000^3831 ≤ 7016298573419^3831*250000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109387741 250000000 7016298573419 20000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4375509721/10000000000 : ℝ)^4855 ≤ (17540746845059/50000000000000 : ℝ)^3831 := by
    have hnat : (4375509721 : ℕ)^4855*50000000000000^3831 ≤ 17540746845059^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4375509721 10000000000 17540746845059 50000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1925343219/5000000000 : ℝ), (109387741/250000000 : ℝ), (4375509721/10000000000 : ℝ)] ![(29837013420341/100000000000000 : ℝ), (7016298573419/20000000000000 : ℝ), (17540746845059/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1925343219/5000000000 : ℝ)|^4855 ≤ (29837013420341/100000000000000 : ℝ)^3831
        have hw : |(1925343219/5000000000 : ℝ)|=(1925343219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(109387741/250000000 : ℝ)|^4855 ≤ (7016298573419/20000000000000 : ℝ)^3831
        have hw : |(109387741/250000000 : ℝ)|=(109387741/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4375509721/10000000000 : ℝ)|^4855 ≤ (17540746845059/50000000000000 : ℝ)^3831
        have hw : |(4375509721/10000000000 : ℝ)|=(4375509721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1634_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (17675869/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8149/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10583/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(16251/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58453/100000 : ℝ) ∧ (809/1000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (44033/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8149/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10583/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8149/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10583/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8149/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10583/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8149/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10583/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8149/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10583/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8149/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10583/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10583/100000 : ℝ) ^ (4851/1024 : ℝ) ≤ (1197414966461471/50000000000000000000 : ℝ) := by
    have hpowers : (10583/100000 : ℝ)^4851 ≤ (1197414966461471/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10583 : ℕ)^4851*50000000000000000000^1024 ≤ 1197414966461471^1024*100000^4851 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10583 100000 1197414966461471 50000000000000000000 4851 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10583/100000 : ℝ)) (X := (1197414966461471/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4851 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8149/50000 : ℝ) ^ (4851/1024 : ℝ) ≤ (18519966214384581/100000000000000000000 : ℝ) := by
    have hpowers : (8149/50000 : ℝ)^4851 ≤ (18519966214384581/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8149 : ℕ)^4851*100000000000000000000^1024 ≤ 18519966214384581^1024*50000^4851 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8149 50000 18519966214384581 100000000000000000000 4851 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8149/50000 : ℝ)) (X := (18519966214384581/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4851 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001197414966461471/25000000000000000000 : ℝ) ≤ (2500025275814483/2500000000000000 : ℝ) ^ (4851/1024 : ℝ) := by
    have hpowers : (25001197414966461471/25000000000000000000 : ℝ)^1024 ≤ (2500025275814483/2500000000000000 : ℝ)^4851 := by
      have hnat : (25001197414966461471 : ℕ)^1024*2500000000000000^4851 ≤ 2500025275814483^4851*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001197414966461471 25000000000000000000 2500025275814483 2500000000000000 1024 4851 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500025275814483/2500000000000000 : ℝ)) (X := (25001197414966461471/25000000000000000000 : ℝ)) (by norm_num) 4851 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100020914796147307523/100000000000000000000 : ℝ) ≤ (625027590940793/625000000000000 : ℝ) ^ (4851/1024 : ℝ) := by
    have hpowers : (100020914796147307523/100000000000000000000 : ℝ)^1024 ≤ (625027590940793/625000000000000 : ℝ)^4851 := by
      have hnat : (100020914796147307523 : ℕ)^1024*625000000000000^4851 ≤ 625027590940793^4851*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100020914796147307523 100000000000000000000 625027590940793 625000000000000 1024 4851 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625027590940793/625000000000000 : ℝ)) (X := (100020914796147307523/100000000000000000000 : ℝ)) (by norm_num) 4851 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50018519966214384581/50000000000000000000 : ℝ) ≤ (2500195451711861/2500000000000000 : ℝ) ^ (4851/1024 : ℝ) := by
    have hpowers : (50018519966214384581/50000000000000000000 : ℝ)^1024 ≤ (2500195451711861/2500000000000000 : ℝ)^4851 := by
      have hnat : (50018519966214384581 : ℕ)^1024*2500000000000000^4851 ≤ 2500195451711861^4851*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018519966214384581 50000000000000000000 2500195451711861 2500000000000000 1024 4851 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500195451711861/2500000000000000 : ℝ)) (X := (50018519966214384581/50000000000000000000 : ℝ)) (by norm_num) 4851 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1197414966461471/50000000000000000000 : ℝ) ≤ ((1587315942195313219/1587500000000000000 : ℝ)+2*(9454216521/15875000000000 : ℝ)*(10583/100000 : ℝ))^(4851/1024 : ℝ) := by
    rw [show (1587315942195313219/1587500000000000000 : ℝ)+2*(9454216521/15875000000000 : ℝ)*(10583/100000 : ℝ)=(2500025275814483/2500000000000000 : ℝ) by norm_num, show 1+2*(1197414966461471/50000000000000000000 : ℝ)=(25001197414966461471/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18519966214384581/100000000000000000000 : ℝ)+(1197414966461471/50000000000000000000 : ℝ) ≤ ((1587315942195313219/1587500000000000000 : ℝ)+(9454216521/15875000000000 : ℝ)*((8149/50000 : ℝ)+(10583/100000 : ℝ)))^(4851/1024 : ℝ) := by
    rw [show (1587315942195313219/1587500000000000000 : ℝ)+(9454216521/15875000000000 : ℝ)*((8149/50000 : ℝ)+(10583/100000 : ℝ))=(625027590940793/625000000000000 : ℝ) by norm_num, show 1+(18519966214384581/100000000000000000000 : ℝ)+(1197414966461471/50000000000000000000 : ℝ)=(100020914796147307523/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18519966214384581/100000000000000000000 : ℝ) ≤ ((1587315942195313219/1587500000000000000 : ℝ)+2*(9454216521/15875000000000 : ℝ)*(8149/50000 : ℝ))^(4851/1024 : ℝ) := by
    rw [show (1587315942195313219/1587500000000000000 : ℝ)+2*(9454216521/15875000000000 : ℝ)*(8149/50000 : ℝ)=(2500195451711861/2500000000000000 : ℝ) by norm_num, show 1+2*(18519966214384581/100000000000000000000 : ℝ)=(50018519966214384581/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1587315942195313219/1587500000000000000 : ℝ)*(X 1 0+X 2 0)+(9454216521/15875000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4851/1024 : ℝ)) (lo := (10583/100000 : ℝ)) (hi := (8149/50000 : ℝ)) (c := (1587315942195313219/1587500000000000000 : ℝ)) (alpha := (9454216521/15875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1587315942195313219/1587500000000000000 : ℝ)*(X 0 1+X 2 1)+(9454216521/15875000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4851/1024 : ℝ)) (lo := (10583/100000 : ℝ)) (hi := (8149/50000 : ℝ)) (c := (1587315942195313219/1587500000000000000 : ℝ)) (alpha := (9454216521/15875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1587315942195313219/1587500000000000000 : ℝ)*(X 0 2+X 1 2)+(9454216521/15875000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4851/1024 : ℝ)) (lo := (10583/100000 : ℝ)) (hi := (8149/50000 : ℝ)) (c := (1587315942195313219/1587500000000000000 : ℝ)) (alpha := (9454216521/15875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-69091711/500000000 : ℝ)*X 0 0+(5412030263/10000000000 : ℝ)*X 0 1+(541203039/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1312809013/2500000000 : ℝ)*X 1 0+(-50242549/312500000 : ℝ)*X 1 1+(1353007553/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5251235919/10000000000 : ℝ)*X 2 0+(5412030361/10000000000 : ℝ)*X 2 1+(-321552309/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((894223421/2000000000 : ℝ)*X 0 0+(1016631019/2500000000 : ℝ)*X 0 1+(2033262061/5000000000 : ℝ)*X 0 2+(894223421/2000000000 : ℝ)*X 1 0+(1016631019/2500000000 : ℝ)*X 1 1+(2033262061/5000000000 : ℝ)*X 1 2+(894223421/2000000000 : ℝ)*X 2 0+(1016631019/2500000000 : ℝ)*X 2 1+(2033262061/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1920226431/10000000000 : ℝ)*X 0 0+(5215238617/10000000000 : ℝ)*X 0 1+(1303809739/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((538660347/1000000000 : ℝ)*X 1 0+(-845840821/5000000000 : ℝ)*X 1 1+(1043047653/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5386603793/10000000000 : ℝ)*X 2 0+(5215237737/10000000000 : ℝ)*X 2 1+(-422920479/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((977252343/2500000000 : ℝ)*X 0 0+(4347246063/10000000000 : ℝ)*X 0 1+(869449211/2000000000 : ℝ)*X 0 2+(977252343/2500000000 : ℝ)*X 1 0+(4347246063/10000000000 : ℝ)*X 1 1+(869449211/2000000000 : ℝ)*X 1 2+(977252343/2500000000 : ℝ)*X 2 0+(4347246063/10000000000 : ℝ)*X 2 1+(869449211/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-451380179/2500000000 : ℝ)*X 0 0+(5074090039/10000000000 : ℝ)*X 0 1+(217667323/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2615418557/5000000000 : ℝ)*X 1 0+(-318934973/2000000000 : ℝ)*X 1 1+(2720841843/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5230837337/10000000000 : ℝ)*X 2 0+(5441683707/10000000000 : ℝ)*X 2 1+(-159467453/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((142294727/312500000 : ℝ)*X 0 0+(125754617/312500000 : ℝ)*X 0 1+(4024147591/10000000000 : ℝ)*X 0 2+(142294727/312500000 : ℝ)*X 1 0+(125754617/312500000 : ℝ)*X 1 1+(4024147591/10000000000 : ℝ)*X 1 2+(142294727/312500000 : ℝ)*X 2 0+(125754617/312500000 : ℝ)*X 2 1+(4024147591/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1494979131/10000000000 : ℝ)*X 0 0+(5547654329/10000000000 : ℝ)*X 0 1+(5195389611/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5400265597/10000000000 : ℝ)*X 1 0+(-849927613/5000000000 : ℝ)*X 1 1+(5195389407/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2700132747/5000000000 : ℝ)*X 2 0+(5195389313/10000000000 : ℝ)*X 2 1+(-849927747/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1925343219/5000000000 : ℝ)*X 0 0+(109387741/250000000 : ℝ)*X 0 1+(4375509721/10000000000 : ℝ)*X 0 2+(1925343219/5000000000 : ℝ)*X 1 0+(109387741/250000000 : ℝ)*X 1 1+(4375509721/10000000000 : ℝ)*X 1 2+(1925343219/5000000000 : ℝ)*X 2 0+(109387741/250000000 : ℝ)*X 2 1+(4375509721/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-16251/25000 : ℝ) ≤ (-2063784634969434046319871573/3175000000000000000000000000 : ℝ) := by norm_num
    linear_combination (124109/1250000000000 : ℝ)*(upper1) + (17442619/100000000000000 : ℝ)*(lower4) + (1516123/100000000000000 : ℝ)*(upper5) + (1728353783909717/100000000000000 : ℝ)*(major0) + (1728353783909717/100000000000000 : ℝ)*(major1) + (1728353783909717/100000000000000 : ℝ)*(major2) + (321402487/4000000000000 : ℝ)*(sp1) + (7645078599/50000000000000 : ℝ)*(sp2) + (1095680313/50000000000000 : ℝ)*(sp3) + (156285504639221/6250000000000 : ℝ)*(sp4) + (156285151607249/6250000000000 : ℝ)*(sp5) + (2500555170620961/100000000000000 : ℝ)*(sp6) + (977801945969039/100000000000000 : ℝ)*(sp7) + (2386550623/100000000000000 : ℝ)*(sp12) + (195560827465933/20000000000000 : ℝ)*(f.failure) + (2500570460778159/100000000000000 : ℝ)*(f.sum) + (5374025995347/3175000000000000000000000000 : ℝ)*base66 + (268348182091650977/158750000000000000000000000000000 : ℝ)*base68 + (268790082910849023/158750000000000000000000000000000 : ℝ)*base69 + (240362002669150977/158750000000000000000000000000000 : ℝ)*base72 + (4853739685147/3175000000000000000000000000 : ℝ)*base74 + (995255012660400977/158750000000000000000000000000000 : ℝ)*base76 + (408686982599599023/158750000000000000000000000000000 : ℝ)*base77 + (316877492768349023/158750000000000000000000000000000 : ℝ)*base79 + (9189203537697/3175000000000000000000000000 : ℝ)*base82 + (329223/200000000000000000000 : ℝ)*base90 + (329223/200000000000000000000 : ℝ)*base92 + (329223/200000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (58453/100000 : ℝ) ≤ (28999533922407730030697618451/49609375000000000000000000000 : ℝ) := by norm_num
    linear_combination (12932387/100000000000000 : ℝ)*(upper2) + (388437/4000000000000 : ℝ)*(upper3) + (1662271/25000000000000 : ℝ)*(upper5) + (18164977719269/1000000000000 : ℝ)*(major0) + (18164977719269/1000000000000 : ℝ)*(major1) + (18164977719269/1000000000000 : ℝ)*(major2) + (1292919039794377/50000000000000 : ℝ)*(sp0) + (2585829477095713/100000000000000 : ℝ)*(sp1) + (1292919601496703/50000000000000 : ℝ)*(sp2) + (513835416206947/50000000000000 : ℝ)*(sp3) + (103968027/100000000000000 : ℝ)*(sp6) + (153338999/100000000000000 : ℝ)*(sp7) + (245746643/2500000000000 : ℝ)*(sp9) + (1227372679/100000000000000 : ℝ)*(sp12) + (1027670985752893/100000000000000 : ℝ)*(f.failure) + (1292919653480717/50000000000000 : ℝ)*(f.sum) + (977362068421/127000000000000000000000000 : ℝ)*base65 + (8718222064608089/1587500000000000000000000000000 : ℝ)*base68 + (17160006311308089/1587500000000000000000000000000 : ℝ)*base70 + (5716529566608089/1587500000000000000000000000000 : ℝ)*base72 + (7948704187/25400000000000000000000000 : ℝ)*base74 + (7975133182170589/1587500000000000000000000000000 : ℝ)*base76 + (3294597685104411/1587500000000000000000000000000 : ℝ)*base77 + (5564645015158089/1587500000000000000000000000000 : ℝ)*base80 + (359649017013/127000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (3039017/1000000000000000000000 : ℝ)*base89 + (3039017/1000000000000000000000 : ℝ)*base91 + (3039017/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (809/1000 : ℝ) ≤ (16054072090143025414643035083177/19843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2561709/4000000000000 : ℝ)*(upper0) + (17782921/25000000000000 : ℝ)*(upper2) + (8630777/25000000000000 : ℝ)*(upper3) + (201986063/100000000000000 : ℝ)*(upper4) + (478883359443639/25000000000000 : ℝ)*(major0) + (478883359443639/25000000000000 : ℝ)*(major1) + (478883359443639/25000000000000 : ℝ)*(major2) + (44410753307/100000000000000 : ℝ)*(sp1) + (78820521347/100000000000000 : ℝ)*(sp2) + (16773389129/100000000000000 : ℝ)*(sp3) + (680099920046051/25000000000000 : ℝ)*(sp8) + (170022204339431/6250000000000 : ℝ)*(sp9) + (340040107457857/12500000000000 : ℝ)*(sp10) + (541841475899053/50000000000000 : ℝ)*(sp11) + (216739945037447/20000000000000 : ℝ)*(f.failure) + (680099920046051/25000000000000 : ℝ)*(f.sum) + (11090642857329/3175000000000000000000000000 : ℝ)*base65 + (192780812715936059/39687500000000000000000000000000 : ℝ)*base68 + (3172525215313941/39687500000000000000000000000000 : ℝ)*base69 + (187522710830626441/39687500000000000000000000000000 : ℝ)*base71 + (218340839651/793750000000000000000000000 : ℝ)*base73 + (22280117872186059/39687500000000000000000000000000 : ℝ)*base76 + (51878009068438941/39687500000000000000000000000000 : ℝ)*base77 + (139825857008751441/39687500000000000000000000000000 : ℝ)*base79 + (13028960913629/3175000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1266443/200000000000000000000 : ℝ)*base89 + (1266443/200000000000000000000 : ℝ)*base91 + (1266443/200000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-44033/50000 : ℝ) ≤ (-34950342760279693769930148667797/39687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11693413/25000000000000 : ℝ)*(upper3) + (31819147/50000000000000 : ℝ)*(lower4) + (126041/50000000000000 : ℝ)*(upper5) + (979400738280021/50000000000000 : ℝ)*(major0) + (979400738280021/50000000000000 : ℝ)*(major1) + (979400738280021/50000000000000 : ℝ)*(major2) + (3052720983/100000000000000 : ℝ)*(sp4) + (6974217379/12500000000000 : ℝ)*(sp5) + (80974530799/100000000000000 : ℝ)*(sp6) + (23996538561/100000000000000 : ℝ)*(sp7) + (2838776201669747/100000000000000 : ℝ)*(sp12) + (1419361730325849/50000000000000 : ℝ)*(sp13) + (283869827985993/10000000000000 : ℝ)*(sp14) + (1108154320782099/100000000000000 : ℝ)*(sp15) + (55408915866033/5000000000000 : ℝ)*(f.failure) + (283877925439073/10000000000000 : ℝ)*(f.sum) + (1914101843293/793750000000000000000000000 : ℝ)*base66 + (85061545819622599/79375000000000000000000000000000 : ℝ)*base67 + (112559552323372599/79375000000000000000000000000000 : ℝ)*base69 + (135250658256002401/79375000000000000000000000000000 : ℝ)*base72 + (9083367735603/3175000000000000000000000000 : ℝ)*base73 + (162015273256002401/79375000000000000000000000000000 : ℝ)*base76 + (542111677564622599/79375000000000000000000000000000 : ℝ)*base77 + (415912049423997599/79375000000000000000000000000000 : ℝ)*base79 + (3936720131389/1587500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (142323/50000000000000000000 : ℝ)*base90 + (142323/50000000000000000000 : ℝ)*base92 + (142323/50000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1634_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (17675869/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8149/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10583/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(16251/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58453/100000 : ℝ) else (809/1000 : ℝ) ≤ X j i ∧ X j i ≤ (44033/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1634_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1634_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (17675869/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8149/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10583/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(16251/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58453/100000 : ℝ) else (809/1000 : ℝ) ≤ X j i ∧ X j i ≤ (44033/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1634_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (17675869/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8149/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10583/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(16251/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58453/100000 : ℝ) else (809/1000 : ℝ) ≤ X j i ∧ X j i ≤ (44033/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1634_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
