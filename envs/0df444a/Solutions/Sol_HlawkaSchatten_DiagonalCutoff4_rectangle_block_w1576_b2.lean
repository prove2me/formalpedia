-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1576_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:29:11.837002+00:00
-- url     : https://prove2.me/submissions/69a67c20-47f8-4e2d-9dbb-ab24af6239bd

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
theorem support_rectangle_w1576_s6_0 (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-111090743/625000000 : ℝ)*x 0 + (5425023773/10000000000 : ℝ)*x 1 + (2610133219/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (111090743/625000000 : ℝ)^4649 ≤ (10911354916031/100000000000000 : ℝ)^3625 := by
    have hnat : (111090743 : ℕ)^4649*100000000000000^3625 ≤ 10911354916031^3625*625000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111090743 625000000 10911354916031 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5425023773/10000000000 : ℝ)^4649 ≤ (2852690837169/6250000000000 : ℝ)^3625 := by
    have hnat : (5425023773 : ℕ)^4649*6250000000000^3625 ≤ 2852690837169^3625*10000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425023773 10000000000 2852690837169 6250000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2610133219/5000000000 : ℝ)^4649 ≤ (43445591671929/100000000000000 : ℝ)^3625 := by
    have hnat : (2610133219 : ℕ)^4649*100000000000000^3625 ≤ 43445591671929^3625*5000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610133219 5000000000 43445591671929 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4649/1024 : ℝ)) 4649 3625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-111090743/625000000 : ℝ), (5425023773/10000000000 : ℝ), (2610133219/5000000000 : ℝ)] ![(10911354916031/100000000000000 : ℝ), (2852690837169/6250000000000 : ℝ), (43445591671929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-111090743/625000000 : ℝ)|^4649 ≤ (10911354916031/100000000000000 : ℝ)^3625
        have hw : |(-111090743/625000000 : ℝ)|=(111090743/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5425023773/10000000000 : ℝ)|^4649 ≤ (2852690837169/6250000000000 : ℝ)^3625
        have hw : |(5425023773/10000000000 : ℝ)|=(5425023773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2610133219/5000000000 : ℝ)|^4649 ≤ (43445591671929/100000000000000 : ℝ)^3625
        have hw : |(2610133219/5000000000 : ℝ)|=(2610133219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1576_s6_1 (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336954723/2500000000 : ℝ)*x 0 + (-941095877/5000000000 : ℝ)*x 1 + (130506651/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336954723/2500000000 : ℝ)^4649 ≤ (44811686908777/100000000000000 : ℝ)^3625 := by
    have hnat : (1336954723 : ℕ)^4649*100000000000000^3625 ≤ 44811686908777^3625*2500000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336954723 2500000000 44811686908777 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (941095877/5000000000 : ℝ)^4649 ≤ (733920353239/6250000000000 : ℝ)^3625 := by
    have hnat : (941095877 : ℕ)^4649*6250000000000^3625 ≤ 733920353239^3625*5000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      941095877 5000000000 733920353239 6250000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130506651/250000000 : ℝ)^4649 ≤ (21722793711949/50000000000000 : ℝ)^3625 := by
    have hnat : (130506651 : ℕ)^4649*50000000000000^3625 ≤ 21722793711949^3625*250000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130506651 250000000 21722793711949 50000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4649/1024 : ℝ)) 4649 3625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336954723/2500000000 : ℝ), (-941095877/5000000000 : ℝ), (130506651/250000000 : ℝ)] ![(44811686908777/100000000000000 : ℝ), (733920353239/6250000000000 : ℝ), (21722793711949/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336954723/2500000000 : ℝ)|^4649 ≤ (44811686908777/100000000000000 : ℝ)^3625
        have hw : |(1336954723/2500000000 : ℝ)|=(1336954723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-941095877/5000000000 : ℝ)|^4649 ≤ (733920353239/6250000000000 : ℝ)^3625
        have hw : |(-941095877/5000000000 : ℝ)|=(941095877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(130506651/250000000 : ℝ)|^4649 ≤ (21722793711949/50000000000000 : ℝ)^3625
        have hw : |(130506651/250000000 : ℝ)|=(130506651/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1576_s6_2 (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673909349/5000000000 : ℝ)*x 0 + (2610133121/5000000000 : ℝ)*x 1 + (-941095873/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673909349/5000000000 : ℝ)^4649 ≤ (1120292120599/2500000000000 : ℝ)^3625 := by
    have hnat : (2673909349 : ℕ)^4649*2500000000000^3625 ≤ 1120292120599^3625*5000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673909349 5000000000 1120292120599 2500000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2610133121/5000000000 : ℝ)^4649 ≤ (21722794789967/50000000000000 : ℝ)^3625 := by
    have hnat : (2610133121 : ℕ)^4649*50000000000000^3625 ≤ 21722794789967^3625*5000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610133121 5000000000 21722794789967 50000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (941095873/5000000000 : ℝ)^4649 ≤ (5871362793907/50000000000000 : ℝ)^3625 := by
    have hnat : (941095873 : ℕ)^4649*50000000000000^3625 ≤ 5871362793907^3625*5000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      941095873 5000000000 5871362793907 50000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4649/1024 : ℝ)) 4649 3625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673909349/5000000000 : ℝ), (2610133121/5000000000 : ℝ), (-941095873/5000000000 : ℝ)] ![(1120292120599/2500000000000 : ℝ), (21722794789967/50000000000000 : ℝ), (5871362793907/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673909349/5000000000 : ℝ)|^4649 ≤ (1120292120599/2500000000000 : ℝ)^3625
        have hw : |(2673909349/5000000000 : ℝ)|=(2673909349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2610133121/5000000000 : ℝ)|^4649 ≤ (21722794789967/50000000000000 : ℝ)^3625
        have hw : |(2610133121/5000000000 : ℝ)|=(2610133121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-941095873/5000000000 : ℝ)|^4649 ≤ (5871362793907/50000000000000 : ℝ)^3625
        have hw : |(-941095873/5000000000 : ℝ)|=(941095873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1576_s6_3 (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (53010891/125000000 : ℝ)*x 0 + (4003807401/10000000000 : ℝ)*x 1 + (14028523/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53010891/125000000 : ℝ)^4649 ≤ (1331305016639/4000000000000 : ℝ)^3625 := by
    have hnat : (53010891 : ℕ)^4649*4000000000000^3625 ≤ 1331305016639^3625*125000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53010891 125000000 1331305016639 4000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4003807401/10000000000 : ℝ)^4649 ≤ (15457836488567/50000000000000 : ℝ)^3625 := by
    have hnat : (4003807401 : ℕ)^4649*50000000000000^3625 ≤ 15457836488567^3625*10000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4003807401 10000000000 15457836488567 50000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (14028523/31250000 : ℝ)^4649 ≤ (35801701591907/100000000000000 : ℝ)^3625 := by
    have hnat : (14028523 : ℕ)^4649*100000000000000^3625 ≤ 35801701591907^3625*31250000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14028523 31250000 35801701591907 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4649/1024 : ℝ)) 4649 3625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53010891/125000000 : ℝ), (4003807401/10000000000 : ℝ), (14028523/31250000 : ℝ)] ![(1331305016639/4000000000000 : ℝ), (15457836488567/50000000000000 : ℝ), (35801701591907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53010891/125000000 : ℝ)|^4649 ≤ (1331305016639/4000000000000 : ℝ)^3625
        have hw : |(53010891/125000000 : ℝ)|=(53010891/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4003807401/10000000000 : ℝ)|^4649 ≤ (15457836488567/50000000000000 : ℝ)^3625
        have hw : |(4003807401/10000000000 : ℝ)|=(4003807401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(14028523/31250000 : ℝ)|^4649 ≤ (35801701591907/100000000000000 : ℝ)^3625
        have hw : |(14028523/31250000 : ℝ)|=(14028523/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1576_s6_4 (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1777478479/10000000000 : ℝ)*x 0 + (5221334017/10000000000 : ℝ)*x 1 + (5423948271/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1777478479/10000000000 : ℝ)^4649 ≤ (5455782131807/50000000000000 : ℝ)^3625 := by
    have hnat : (1777478479 : ℕ)^4649*50000000000000^3625 ≤ 5455782131807^3625*10000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1777478479 10000000000 5455782131807 50000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5221334017/10000000000 : ℝ)^4649 ≤ (10864246686469/25000000000000 : ℝ)^3625 := by
    have hnat : (5221334017 : ℕ)^4649*25000000000000^3625 ≤ 10864246686469^3625*10000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5221334017 10000000000 10864246686469 25000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5423948271/10000000000 : ℝ)^4649 ≤ (45631448969319/100000000000000 : ℝ)^3625 := by
    have hnat : (5423948271 : ℕ)^4649*100000000000000^3625 ≤ 45631448969319^3625*10000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423948271 10000000000 45631448969319 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4649/1024 : ℝ)) 4649 3625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1777478479/10000000000 : ℝ), (5221334017/10000000000 : ℝ), (5423948271/10000000000 : ℝ)] ![(5455782131807/50000000000000 : ℝ), (10864246686469/25000000000000 : ℝ), (45631448969319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1777478479/10000000000 : ℝ)|^4649 ≤ (5455782131807/50000000000000 : ℝ)^3625
        have hw : |(-1777478479/10000000000 : ℝ)|=(1777478479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5221334017/10000000000 : ℝ)|^4649 ≤ (10864246686469/25000000000000 : ℝ)^3625
        have hw : |(5221334017/10000000000 : ℝ)|=(5221334017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5423948271/10000000000 : ℝ)|^4649 ≤ (45631448969319/100000000000000 : ℝ)^3625
        have hw : |(5423948271/10000000000 : ℝ)|=(5423948271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1576_s6_5 (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (8481869/20000000 : ℝ)*x 0 + (1121649037/2500000000 : ℝ)*x 1 + (500794633/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8481869/20000000 : ℝ)^4649 ≤ (3328326172697/10000000000000 : ℝ)^3625 := by
    have hnat : (8481869 : ℕ)^4649*10000000000000^3625 ≤ 3328326172697^3625*20000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8481869 20000000 3328326172697 10000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1121649037/2500000000 : ℝ)^4649 ≤ (35775814265211/100000000000000 : ℝ)^3625 := by
    have hnat : (1121649037 : ℕ)^4649*100000000000000^3625 ≤ 35775814265211^3625*2500000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121649037 2500000000 35775814265211 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (500794633/1250000000 : ℝ)^4649 ≤ (7735230998879/25000000000000 : ℝ)^3625 := by
    have hnat : (500794633 : ℕ)^4649*25000000000000^3625 ≤ 7735230998879^3625*1250000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      500794633 1250000000 7735230998879 25000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4649/1024 : ℝ)) 4649 3625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8481869/20000000 : ℝ), (1121649037/2500000000 : ℝ), (500794633/1250000000 : ℝ)] ![(3328326172697/10000000000000 : ℝ), (35775814265211/100000000000000 : ℝ), (7735230998879/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8481869/20000000 : ℝ)|^4649 ≤ (3328326172697/10000000000000 : ℝ)^3625
        have hw : |(8481869/20000000 : ℝ)|=(8481869/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1121649037/2500000000 : ℝ)|^4649 ≤ (35775814265211/100000000000000 : ℝ)^3625
        have hw : |(1121649037/2500000000 : ℝ)|=(1121649037/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(500794633/1250000000 : ℝ)|^4649 ≤ (7735230998879/25000000000000 : ℝ)^3625
        have hw : |(500794633/1250000000 : ℝ)|=(500794633/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1576_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4212767/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (557/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (11141/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3871/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (557/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (557/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (557/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (557/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (557/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (557/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (557/5000 : ℝ) ^ (4647/1024 : ℝ) ≤ (4728061181519513/100000000000000000000 : ℝ) := by
    have hpowers : (557/5000 : ℝ)^4647 ≤ (4728061181519513/100000000000000000000 : ℝ)^1024 := by
      have hnat : (557 : ℕ)^4647*100000000000000000000^1024 ≤ 4728061181519513^1024*5000^4647 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        557 5000 4728061181519513 100000000000000000000 4647 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (557/5000 : ℝ)) (X := (4728061181519513/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4647 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3871/25000 : ℝ) ^ (4647/1024 : ℝ) ≤ (2106784782151517/10000000000000000000 : ℝ) := by
    have hpowers : (3871/25000 : ℝ)^4647 ≤ (2106784782151517/10000000000000000000 : ℝ)^1024 := by
      have hnat : (3871 : ℕ)^4647*10000000000000000000^1024 ≤ 2106784782151517^1024*25000^4647 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3871 25000 2106784782151517 10000000000000000000 4647 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3871/25000 : ℝ)) (X := (2106784782151517/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4647 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004728061181519513/50000000000000000000 : ℝ) ≤ (400008334592109/400000000000000 : ℝ) ^ (4647/1024 : ℝ) := by
    have hpowers : (50004728061181519513/50000000000000000000 : ℝ)^1024 ≤ (400008334592109/400000000000000 : ℝ)^4647 := by
      have hnat : (50004728061181519513 : ℕ)^1024*400000000000000^4647 ≤ 400008334592109^4647*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004728061181519513 50000000000000000000 400008334592109 400000000000000 1024 4647 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400008334592109/400000000000000 : ℝ)) (X := (50004728061181519513/50000000000000000000 : ℝ)) (by norm_num) 4647 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100025795909003034683/100000000000000000000 : ℝ) ≤ (5000284187163607/5000000000000000 : ℝ) ^ (4647/1024 : ℝ) := by
    have hpowers : (100025795909003034683/100000000000000000000 : ℝ)^1024 ≤ (5000284187163607/5000000000000000 : ℝ)^4647 := by
      have hnat : (100025795909003034683 : ℕ)^1024*5000000000000000^4647 ≤ 5000284187163607^4647*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100025795909003034683 100000000000000000000 5000284187163607 5000000000000000 1024 4647 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000284187163607/5000000000000000 : ℝ)) (X := (100025795909003034683/100000000000000000000 : ℝ)) (by norm_num) 4647 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5002106784782151517/5000000000000000000 : ℝ) ≤ (10000928383851703/10000000000000000 : ℝ) ^ (4647/1024 : ℝ) := by
    have hpowers : (5002106784782151517/5000000000000000000 : ℝ)^1024 ≤ (10000928383851703/10000000000000000 : ℝ)^4647 := by
      have hnat : (5002106784782151517 : ℕ)^1024*10000000000000000^4647 ≤ 10000928383851703^4647*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002106784782151517 5000000000000000000 10000928383851703 10000000000000000 1024 4647 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000928383851703/10000000000000000 : ℝ)) (X := (5002106784782151517/5000000000000000000 : ℝ)) (by norm_num) 4647 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4728061181519513/100000000000000000000 : ℝ) ≤ ((542911051556217781/543000000000000000 : ℝ)+2*(360009524489/434400000000000 : ℝ)*(557/5000 : ℝ))^(4647/1024 : ℝ) := by
    rw [show (542911051556217781/543000000000000000 : ℝ)+2*(360009524489/434400000000000 : ℝ)*(557/5000 : ℝ)=(400008334592109/400000000000000 : ℝ) by norm_num, show 1+2*(4728061181519513/100000000000000000000 : ℝ)=(50004728061181519513/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2106784782151517/10000000000000000000 : ℝ)+(4728061181519513/100000000000000000000 : ℝ) ≤ ((542911051556217781/543000000000000000 : ℝ)+(360009524489/434400000000000 : ℝ)*((3871/25000 : ℝ)+(557/5000 : ℝ)))^(4647/1024 : ℝ) := by
    rw [show (542911051556217781/543000000000000000 : ℝ)+(360009524489/434400000000000 : ℝ)*((3871/25000 : ℝ)+(557/5000 : ℝ))=(5000284187163607/5000000000000000 : ℝ) by norm_num, show 1+(2106784782151517/10000000000000000000 : ℝ)+(4728061181519513/100000000000000000000 : ℝ)=(100025795909003034683/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2106784782151517/10000000000000000000 : ℝ) ≤ ((542911051556217781/543000000000000000 : ℝ)+2*(360009524489/434400000000000 : ℝ)*(3871/25000 : ℝ))^(4647/1024 : ℝ) := by
    rw [show (542911051556217781/543000000000000000 : ℝ)+2*(360009524489/434400000000000 : ℝ)*(3871/25000 : ℝ)=(10000928383851703/10000000000000000 : ℝ) by norm_num, show 1+2*(2106784782151517/10000000000000000000 : ℝ)=(5002106784782151517/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (542911051556217781/543000000000000000 : ℝ)*(X 1 0+X 2 0)+(360009524489/434400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4647/1024 : ℝ)) (lo := (557/5000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (542911051556217781/543000000000000000 : ℝ)) (alpha := (360009524489/434400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (542911051556217781/543000000000000000 : ℝ)*(X 0 1+X 2 1)+(360009524489/434400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4647/1024 : ℝ)) (lo := (557/5000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (542911051556217781/543000000000000000 : ℝ)) (alpha := (360009524489/434400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (542911051556217781/543000000000000000 : ℝ)*(X 0 2+X 1 2)+(360009524489/434400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4647/1024 : ℝ)) (lo := (557/5000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (542911051556217781/543000000000000000 : ℝ)) (alpha := (360009524489/434400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-111090743/625000000 : ℝ)*X 0 0+(5425023773/10000000000 : ℝ)*X 0 1+(2610133219/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1576_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336954723/2500000000 : ℝ)*X 1 0+(-941095877/5000000000 : ℝ)*X 1 1+(130506651/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1576_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673909349/5000000000 : ℝ)*X 2 0+(2610133121/5000000000 : ℝ)*X 2 1+(-941095873/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1576_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((53010891/125000000 : ℝ)*X 0 0+(4003807401/10000000000 : ℝ)*X 0 1+(14028523/31250000 : ℝ)*X 0 2+(53010891/125000000 : ℝ)*X 1 0+(4003807401/10000000000 : ℝ)*X 1 1+(14028523/31250000 : ℝ)*X 1 2+(53010891/125000000 : ℝ)*X 2 0+(4003807401/10000000000 : ℝ)*X 2 1+(14028523/31250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1576_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1777478479/10000000000 : ℝ)*X 0 0+(5221334017/10000000000 : ℝ)*X 0 1+(5423948271/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1576_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((8481869/20000000 : ℝ)*X 0 0+(1121649037/2500000000 : ℝ)*X 0 1+(500794633/1250000000 : ℝ)*X 0 2+(8481869/20000000 : ℝ)*X 1 0+(1121649037/2500000000 : ℝ)*X 1 1+(500794633/1250000000 : ℝ)*X 1 2+(8481869/20000000 : ℝ)*X 2 0+(1121649037/2500000000 : ℝ)*X 2 1+(500794633/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1576_s6_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10433257722428847620758037/2262500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (656342253/100000000000000 : ℝ)*(base19) + (445068753/100000000000000 : ℝ)*(base23) + (18238807/100000000000000 : ℝ)*(lower2) + (8039823/12500000000000 : ℝ)*(upper3) + (10768987/50000000000000 : ℝ)*(upper5) + (868042827494477/25000000000000 : ℝ)*(major0) + (868042827494477/25000000000000 : ℝ)*(major1) + (868042827494477/25000000000000 : ℝ)*(major2) + (1220958643330833/25000000000000 : ℝ)*(sp0) + (2441918309097717/50000000000000 : ℝ)*(sp1) + (2441918414734467/50000000000000 : ℝ)*(sp2) + (2060500671653123/100000000000000 : ℝ)*(sp3) + (675303589/25000000000000 : ℝ)*(sp4) + (4520052179/100000000000000 : ℝ)*(sp5) + (1030252595852651/50000000000000 : ℝ)*(f.failure) + (4883837274537687/100000000000000 : ℝ)*(f.sum) + (35149253079253/5430000000000000000000000000 : ℝ)*base65 + (166481289532463213/13575000000000000000000000000000 : ℝ)*base68 + (134563859829338213/13575000000000000000000000000000 : ℝ)*base70 + (68680644102338213/13575000000000000000000000000000 : ℝ)*base72 + (1066603863283/5430000000000000000000000000 : ℝ)*base73 + (79856638992561787/13575000000000000000000000000000 : ℝ)*base75 + (65449642116638213/13575000000000000000000000000000 : ℝ)*base78 + (36589764402036787/13575000000000000000000000000000 : ℝ)*base79 + (15975181770707/5430000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (4683/125000000000000000000 : ℝ)*base90 + (4683/125000000000000000000 : ℝ)*base92 + (4683/125000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1576_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4212767/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (557/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11141/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1576_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1576_box_0 (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-393651117/2500000000 : ℝ)*x 0 + (2697974777/5000000000 : ℝ)*x 1 + (84311707/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (393651117/2500000000 : ℝ)^4649 ≤ (1167605890349/12500000000000 : ℝ)^3625 := by
    have hnat : (393651117 : ℕ)^4649*12500000000000^3625 ≤ 1167605890349^3625*2500000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393651117 2500000000 1167605890349 12500000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697974777/5000000000 : ℝ)^4649 ≤ (22664789039071/50000000000000 : ℝ)^3625 := by
    have hnat : (2697974777 : ℕ)^4649*50000000000000^3625 ≤ 22664789039071^3625*5000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697974777 5000000000 22664789039071 50000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84311707/156250000 : ℝ)^4649 ≤ (45329574781387/100000000000000 : ℝ)^3625 := by
    have hnat : (84311707 : ℕ)^4649*100000000000000^3625 ≤ 45329574781387^3625*156250000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84311707 156250000 45329574781387 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4649/1024 : ℝ)) 4649 3625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-393651117/2500000000 : ℝ), (2697974777/5000000000 : ℝ), (84311707/156250000 : ℝ)] ![(1167605890349/12500000000000 : ℝ), (22664789039071/50000000000000 : ℝ), (45329574781387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-393651117/2500000000 : ℝ)|^4649 ≤ (1167605890349/12500000000000 : ℝ)^3625
        have hw : |(-393651117/2500000000 : ℝ)|=(393651117/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697974777/5000000000 : ℝ)|^4649 ≤ (22664789039071/50000000000000 : ℝ)^3625
        have hw : |(2697974777/5000000000 : ℝ)|=(2697974777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84311707/156250000 : ℝ)|^4649 ≤ (45329574781387/100000000000000 : ℝ)^3625
        have hw : |(84311707/156250000 : ℝ)|=(84311707/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1576_box_1 (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5271141439/10000000000 : ℝ)*x 0 + (-1748132923/10000000000 : ℝ)*x 1 + (5395949761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5271141439/10000000000 : ℝ)^4649 ≤ (21994674434793/50000000000000 : ℝ)^3625 := by
    have hnat : (5271141439 : ℕ)^4649*50000000000000^3625 ≤ 21994674434793^3625*10000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271141439 10000000000 21994674434793 50000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1748132923/10000000000 : ℝ)^4649 ≤ (5340535400083/50000000000000 : ℝ)^3625 := by
    have hnat : (1748132923 : ℕ)^4649*50000000000000^3625 ≤ 5340535400083^3625*10000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1748132923 10000000000 5340535400083 50000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5395949761/10000000000 : ℝ)^4649 ≤ (453295803083/1000000000000 : ℝ)^3625 := by
    have hnat : (5395949761 : ℕ)^4649*1000000000000^3625 ≤ 453295803083^3625*10000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395949761 10000000000 453295803083 1000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4649/1024 : ℝ)) 4649 3625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5271141439/10000000000 : ℝ), (-1748132923/10000000000 : ℝ), (5395949761/10000000000 : ℝ)] ![(21994674434793/50000000000000 : ℝ), (5340535400083/50000000000000 : ℝ), (453295803083/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5271141439/10000000000 : ℝ)|^4649 ≤ (21994674434793/50000000000000 : ℝ)^3625
        have hw : |(5271141439/10000000000 : ℝ)|=(5271141439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1748132923/10000000000 : ℝ)|^4649 ≤ (5340535400083/50000000000000 : ℝ)^3625
        have hw : |(-1748132923/10000000000 : ℝ)|=(1748132923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5395949761/10000000000 : ℝ)|^4649 ≤ (453295803083/1000000000000 : ℝ)^3625
        have hw : |(5395949761/10000000000 : ℝ)|=(5395949761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1576_box_2 (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2635570831/5000000000 : ℝ)*x 0 + (2697974819/5000000000 : ℝ)*x 1 + (-437033197/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2635570831/5000000000 : ℝ)^4649 ≤ (21994675628147/50000000000000 : ℝ)^3625 := by
    have hnat : (2635570831 : ℕ)^4649*50000000000000^3625 ≤ 21994675628147^3625*5000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635570831 5000000000 21994675628147 50000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697974819/5000000000 : ℝ)^4649 ≤ (22664789491567/50000000000000 : ℝ)^3625 := by
    have hnat : (2697974819 : ℕ)^4649*50000000000000^3625 ≤ 22664789491567^3625*5000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697974819 5000000000 22664789491567 50000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (437033197/2500000000 : ℝ)^4649 ≤ (1335133717789/12500000000000 : ℝ)^3625 := by
    have hnat : (437033197 : ℕ)^4649*12500000000000^3625 ≤ 1335133717789^3625*2500000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437033197 2500000000 1335133717789 12500000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4649/1024 : ℝ)) 4649 3625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2635570831/5000000000 : ℝ), (2697974819/5000000000 : ℝ), (-437033197/2500000000 : ℝ)] ![(21994675628147/50000000000000 : ℝ), (22664789491567/50000000000000 : ℝ), (1335133717789/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2635570831/5000000000 : ℝ)|^4649 ≤ (21994675628147/50000000000000 : ℝ)^3625
        have hw : |(2635570831/5000000000 : ℝ)|=(2635570831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697974819/5000000000 : ℝ)|^4649 ≤ (22664789491567/50000000000000 : ℝ)^3625
        have hw : |(2697974819/5000000000 : ℝ)|=(2697974819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-437033197/2500000000 : ℝ)|^4649 ≤ (1335133717789/12500000000000 : ℝ)^3625
        have hw : |(-437033197/2500000000 : ℝ)|=(437033197/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1576_box_3 (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2220668343/5000000000 : ℝ)*x 0 + (2073620149/5000000000 : ℝ)*x 1 + (1036810087/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2220668343/5000000000 : ℝ)^4649 ≤ (17656816283361/50000000000000 : ℝ)^3625 := by
    have hnat : (2220668343 : ℕ)^4649*50000000000000^3625 ≤ 17656816283361^3625*5000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2220668343 5000000000 17656816283361 50000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2073620149/5000000000 : ℝ)^4649 ≤ (32343183455413/100000000000000 : ℝ)^3625 := by
    have hnat : (2073620149 : ℕ)^4649*100000000000000^3625 ≤ 32343183455413^3625*5000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073620149 5000000000 32343183455413 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036810087/2500000000 : ℝ)^4649 ≤ (64686367911/200000000000 : ℝ)^3625 := by
    have hnat : (1036810087 : ℕ)^4649*200000000000^3625 ≤ 64686367911^3625*2500000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036810087 2500000000 64686367911 200000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4649/1024 : ℝ)) 4649 3625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2220668343/5000000000 : ℝ), (2073620149/5000000000 : ℝ), (1036810087/2500000000 : ℝ)] ![(17656816283361/50000000000000 : ℝ), (32343183455413/100000000000000 : ℝ), (64686367911/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2220668343/5000000000 : ℝ)|^4649 ≤ (17656816283361/50000000000000 : ℝ)^3625
        have hw : |(2220668343/5000000000 : ℝ)|=(2220668343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2073620149/5000000000 : ℝ)|^4649 ≤ (32343183455413/100000000000000 : ℝ)^3625
        have hw : |(2073620149/5000000000 : ℝ)|=(2073620149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1036810087/2500000000 : ℝ)|^4649 ≤ (64686367911/200000000000 : ℝ)^3625
        have hw : |(1036810087/2500000000 : ℝ)|=(1036810087/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1576_box_4 (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-496420601/2500000000 : ℝ)*x 0 + (2622578487/5000000000 : ℝ)*x 1 + (5245156773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (496420601/2500000000 : ℝ)^4649 ≤ (12577125869689/100000000000000 : ℝ)^3625 := by
    have hnat : (496420601 : ℕ)^4649*100000000000000^3625 ≤ 12577125869689^3625*2500000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      496420601 2500000000 12577125869689 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622578487/5000000000 : ℝ)^4649 ≤ (8742287625457/20000000000000 : ℝ)^3625 := by
    have hnat : (2622578487 : ℕ)^4649*20000000000000^3625 ≤ 8742287625457^3625*5000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622578487 5000000000 8742287625457 20000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245156773/10000000000 : ℝ)^4649 ≤ (21855717989519/50000000000000 : ℝ)^3625 := by
    have hnat : (5245156773 : ℕ)^4649*50000000000000^3625 ≤ 21855717989519^3625*10000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245156773 10000000000 21855717989519 50000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4649/1024 : ℝ)) 4649 3625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-496420601/2500000000 : ℝ), (2622578487/5000000000 : ℝ), (5245156773/10000000000 : ℝ)] ![(12577125869689/100000000000000 : ℝ), (8742287625457/20000000000000 : ℝ), (21855717989519/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-496420601/2500000000 : ℝ)|^4649 ≤ (12577125869689/100000000000000 : ℝ)^3625
        have hw : |(-496420601/2500000000 : ℝ)|=(496420601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622578487/5000000000 : ℝ)|^4649 ≤ (8742287625457/20000000000000 : ℝ)^3625
        have hw : |(2622578487/5000000000 : ℝ)|=(2622578487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245156773/10000000000 : ℝ)|^4649 ≤ (21855717989519/50000000000000 : ℝ)^3625
        have hw : |(5245156773/10000000000 : ℝ)|=(5245156773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1576_box_5 (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2687810839/5000000000 : ℝ)*x 0 + (-905607471/5000000000 : ℝ)*x 1 + (2622578359/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2687810839/5000000000 : ℝ)^4649 ≤ (11277672012189/25000000000000 : ℝ)^3625 := by
    have hnat : (2687810839 : ℕ)^4649*25000000000000^3625 ≤ 11277672012189^3625*5000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687810839 5000000000 11277672012189 25000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (905607471/5000000000 : ℝ)^4649 ≤ (11177876546951/100000000000000 : ℝ)^3625 := by
    have hnat : (905607471 : ℕ)^4649*100000000000000^3625 ≤ 11177876546951^3625*5000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      905607471 5000000000 11177876546951 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622578359/5000000000 : ℝ)^4649 ≤ (43711435391209/100000000000000 : ℝ)^3625 := by
    have hnat : (2622578359 : ℕ)^4649*100000000000000^3625 ≤ 43711435391209^3625*5000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622578359 5000000000 43711435391209 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4649/1024 : ℝ)) 4649 3625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2687810839/5000000000 : ℝ), (-905607471/5000000000 : ℝ), (2622578359/5000000000 : ℝ)] ![(11277672012189/25000000000000 : ℝ), (11177876546951/100000000000000 : ℝ), (43711435391209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2687810839/5000000000 : ℝ)|^4649 ≤ (11277672012189/25000000000000 : ℝ)^3625
        have hw : |(2687810839/5000000000 : ℝ)|=(2687810839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-905607471/5000000000 : ℝ)|^4649 ≤ (11177876546951/100000000000000 : ℝ)^3625
        have hw : |(-905607471/5000000000 : ℝ)|=(905607471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622578359/5000000000 : ℝ)|^4649 ≤ (43711435391209/100000000000000 : ℝ)^3625
        have hw : |(2622578359/5000000000 : ℝ)|=(2622578359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1576_box_6 (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1343905337/2500000000 : ℝ)*x 0 + (5245156993/10000000000 : ℝ)*x 1 + (-90560751/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1343905337/2500000000 : ℝ)^4649 ≤ (2255534224861/5000000000000 : ℝ)^3625 := by
    have hnat : (1343905337 : ℕ)^4649*5000000000000^3625 ≤ 2255534224861^3625*2500000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343905337 2500000000 2255534224861 5000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245156993/10000000000 : ℝ)^4649 ≤ (43711438330353/100000000000000 : ℝ)^3625 := by
    have hnat : (5245156993 : ℕ)^4649*100000000000000^3625 ≤ 43711438330353^3625*10000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245156993 10000000000 43711438330353 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (90560751/500000000 : ℝ)^4649 ≤ (11177877164307/100000000000000 : ℝ)^3625 := by
    have hnat : (90560751 : ℕ)^4649*100000000000000^3625 ≤ 11177877164307^3625*500000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90560751 500000000 11177877164307 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4649/1024 : ℝ)) 4649 3625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1343905337/2500000000 : ℝ), (5245156993/10000000000 : ℝ), (-90560751/500000000 : ℝ)] ![(2255534224861/5000000000000 : ℝ), (43711438330353/100000000000000 : ℝ), (11177877164307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1343905337/2500000000 : ℝ)|^4649 ≤ (2255534224861/5000000000000 : ℝ)^3625
        have hw : |(1343905337/2500000000 : ℝ)|=(1343905337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245156993/10000000000 : ℝ)|^4649 ≤ (43711438330353/100000000000000 : ℝ)^3625
        have hw : |(5245156993/10000000000 : ℝ)|=(5245156993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-90560751/500000000 : ℝ)|^4649 ≤ (11177877164307/100000000000000 : ℝ)^3625
        have hw : |(-90560751/500000000 : ℝ)|=(90560751/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1576_box_7 (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4037688651/10000000000 : ℝ)*x 0 + (869787511/2000000000 : ℝ)*x 1 + (2174468771/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4037688651/10000000000 : ℝ)^4649 ≤ (31251591698833/100000000000000 : ℝ)^3625 := by
    have hnat : (4037688651 : ℕ)^4649*100000000000000^3625 ≤ 31251591698833^3625*10000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4037688651 10000000000 31251591698833 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (869787511/2000000000 : ℝ)^4649 ≤ (34374204204567/100000000000000 : ℝ)^3625 := by
    have hnat : (869787511 : ℕ)^4649*100000000000000^3625 ≤ 34374204204567^3625*2000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869787511 2000000000 34374204204567 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2174468771/5000000000 : ℝ)^4649 ≤ (8593551018197/25000000000000 : ℝ)^3625 := by
    have hnat : (2174468771 : ℕ)^4649*25000000000000^3625 ≤ 8593551018197^3625*5000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174468771 5000000000 8593551018197 25000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4649/1024 : ℝ)) 4649 3625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4037688651/10000000000 : ℝ), (869787511/2000000000 : ℝ), (2174468771/5000000000 : ℝ)] ![(31251591698833/100000000000000 : ℝ), (34374204204567/100000000000000 : ℝ), (8593551018197/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4037688651/10000000000 : ℝ)|^4649 ≤ (31251591698833/100000000000000 : ℝ)^3625
        have hw : |(4037688651/10000000000 : ℝ)|=(4037688651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(869787511/2000000000 : ℝ)|^4649 ≤ (34374204204567/100000000000000 : ℝ)^3625
        have hw : |(869787511/2000000000 : ℝ)|=(869787511/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2174468771/5000000000 : ℝ)|^4649 ≤ (8593551018197/25000000000000 : ℝ)^3625
        have hw : |(2174468771/5000000000 : ℝ)|=(2174468771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1576_box_8 (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1898523559/10000000000 : ℝ)*x 0 + (1284713897/2500000000 : ℝ)*x 1 + (5416199563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1898523559/10000000000 : ℝ)^4649 ≤ (11873559945837/100000000000000 : ℝ)^3625 := by
    have hnat : (1898523559 : ℕ)^4649*100000000000000^3625 ≤ 11873559945837^3625*10000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1898523559 10000000000 11873559945837 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1284713897/2500000000 : ℝ)^4649 ≤ (42578578683361/100000000000000 : ℝ)^3625 := by
    have hnat : (1284713897 : ℕ)^4649*100000000000000^3625 ≤ 42578578683361^3625*2500000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1284713897 2500000000 42578578683361 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416199563/10000000000 : ℝ)^4649 ≤ (22773930682241/50000000000000 : ℝ)^3625 := by
    have hnat : (5416199563 : ℕ)^4649*50000000000000^3625 ≤ 22773930682241^3625*10000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416199563 10000000000 22773930682241 50000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4649/1024 : ℝ)) 4649 3625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1898523559/10000000000 : ℝ), (1284713897/2500000000 : ℝ), (5416199563/10000000000 : ℝ)] ![(11873559945837/100000000000000 : ℝ), (42578578683361/100000000000000 : ℝ), (22773930682241/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1898523559/10000000000 : ℝ)|^4649 ≤ (11873559945837/100000000000000 : ℝ)^3625
        have hw : |(-1898523559/10000000000 : ℝ)|=(1898523559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1284713897/2500000000 : ℝ)|^4649 ≤ (42578578683361/100000000000000 : ℝ)^3625
        have hw : |(1284713897/2500000000 : ℝ)|=(1284713897/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416199563/10000000000 : ℝ)|^4649 ≤ (22773930682241/50000000000000 : ℝ)^3625
        have hw : |(5416199563/10000000000 : ℝ)|=(5416199563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1576_box_9 (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5257107929/10000000000 : ℝ)*x 0 + (-1739430263/10000000000 : ℝ)*x 1 + (338512501/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257107929/10000000000 : ℝ)^4649 ≤ (43839208574661/100000000000000 : ℝ)^3625 := by
    have hnat : (5257107929 : ℕ)^4649*100000000000000^3625 ≤ 43839208574661^3625*10000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257107929 10000000000 43839208574661 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1739430263/10000000000 : ℝ)^4649 ≤ (1326615645437/12500000000000 : ℝ)^3625 := by
    have hnat : (1739430263 : ℕ)^4649*12500000000000^3625 ≤ 1326615645437^3625*10000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1739430263 10000000000 1326615645437 12500000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338512501/625000000 : ℝ)^4649 ≤ (2277393312507/5000000000000 : ℝ)^3625 := by
    have hnat : (338512501 : ℕ)^4649*5000000000000^3625 ≤ 2277393312507^3625*625000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338512501 625000000 2277393312507 5000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4649/1024 : ℝ)) 4649 3625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257107929/10000000000 : ℝ), (-1739430263/10000000000 : ℝ), (338512501/625000000 : ℝ)] ![(43839208574661/100000000000000 : ℝ), (1326615645437/12500000000000 : ℝ), (2277393312507/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257107929/10000000000 : ℝ)|^4649 ≤ (43839208574661/100000000000000 : ℝ)^3625
        have hw : |(5257107929/10000000000 : ℝ)|=(5257107929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1739430263/10000000000 : ℝ)|^4649 ≤ (1326615645437/12500000000000 : ℝ)^3625
        have hw : |(-1739430263/10000000000 : ℝ)|=(1739430263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338512501/625000000 : ℝ)|^4649 ≤ (2277393312507/5000000000000 : ℝ)^3625
        have hw : |(338512501/625000000 : ℝ)|=(338512501/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1576_box_10 (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5257107539/10000000000 : ℝ)*x 0 + (5416199983/10000000000 : ℝ)*x 1 + (-1739430841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257107539/10000000000 : ℝ)^4649 ≤ (2191960220187/5000000000000 : ℝ)^3625 := by
    have hnat : (5257107539 : ℕ)^4649*5000000000000^3625 ≤ 2191960220187^3625*10000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257107539 10000000000 2191960220187 5000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5416199983/10000000000 : ℝ)^4649 ≤ (45547865894231/100000000000000 : ℝ)^3625 := by
    have hnat : (5416199983 : ℕ)^4649*100000000000000^3625 ≤ 45547865894231^3625*10000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416199983 10000000000 45547865894231 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1739430841/10000000000 : ℝ)^4649 ≤ (1326616210787/12500000000000 : ℝ)^3625 := by
    have hnat : (1739430841 : ℕ)^4649*12500000000000^3625 ≤ 1326616210787^3625*10000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1739430841 10000000000 1326616210787 12500000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4649/1024 : ℝ)) 4649 3625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257107539/10000000000 : ℝ), (5416199983/10000000000 : ℝ), (-1739430841/10000000000 : ℝ)] ![(2191960220187/5000000000000 : ℝ), (45547865894231/100000000000000 : ℝ), (1326616210787/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257107539/10000000000 : ℝ)|^4649 ≤ (2191960220187/5000000000000 : ℝ)^3625
        have hw : |(5257107539/10000000000 : ℝ)|=(5257107539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5416199983/10000000000 : ℝ)|^4649 ≤ (45547865894231/100000000000000 : ℝ)^3625
        have hw : |(5416199983/10000000000 : ℝ)|=(5416199983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1739430841/10000000000 : ℝ)|^4649 ≤ (1326616210787/12500000000000 : ℝ)^3625
        have hw : |(-1739430841/10000000000 : ℝ)|=(1739430841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1576_box_11 (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4494399963/10000000000 : ℝ)*x 0 + (1030029771/2500000000 : ℝ)*x 1 + (4120120109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4494399963/10000000000 : ℝ)^4649 ≤ (35855639036751/100000000000000 : ℝ)^3625 := by
    have hnat : (4494399963 : ℕ)^4649*100000000000000^3625 ≤ 35855639036751^3625*10000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4494399963 10000000000 35855639036751 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1030029771/2500000000 : ℝ)^4649 ≤ (16036087678227/50000000000000 : ℝ)^3625 := by
    have hnat : (1030029771 : ℕ)^4649*50000000000000^3625 ≤ 16036087678227^3625*2500000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030029771 2500000000 16036087678227 50000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4120120109/10000000000 : ℝ)^4649 ≤ (8018046397311/25000000000000 : ℝ)^3625 := by
    have hnat : (4120120109 : ℕ)^4649*25000000000000^3625 ≤ 8018046397311^3625*10000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4120120109 10000000000 8018046397311 25000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4649/1024 : ℝ)) 4649 3625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4494399963/10000000000 : ℝ), (1030029771/2500000000 : ℝ), (4120120109/10000000000 : ℝ)] ![(35855639036751/100000000000000 : ℝ), (16036087678227/50000000000000 : ℝ), (8018046397311/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4494399963/10000000000 : ℝ)|^4649 ≤ (35855639036751/100000000000000 : ℝ)^3625
        have hw : |(4494399963/10000000000 : ℝ)|=(4494399963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1030029771/2500000000 : ℝ)|^4649 ≤ (16036087678227/50000000000000 : ℝ)^3625
        have hw : |(1030029771/2500000000 : ℝ)|=(1030029771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4120120109/10000000000 : ℝ)|^4649 ≤ (8018046397311/25000000000000 : ℝ)^3625
        have hw : |(4120120109/10000000000 : ℝ)|=(4120120109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1576_box_12 (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1661398999/10000000000 : ℝ)*x 0 + (687378451/1250000000 : ℝ)*x 1 + (326881719/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1661398999/10000000000 : ℝ)^4649 ≤ (19543453639/195312500000 : ℝ)^3625 := by
    have hnat : (1661398999 : ℕ)^4649*195312500000^3625 ≤ 19543453639^3625*10000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1661398999 10000000000 19543453639 195312500000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (687378451/1250000000 : ℝ)^4649 ≤ (4644309403299/10000000000000 : ℝ)^3625 := by
    have hnat : (687378451 : ℕ)^4649*10000000000000^3625 ≤ 4644309403299^3625*1250000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      687378451 1250000000 4644309403299 10000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (326881719/625000000 : ℝ)^4649 ≤ (8710131539083/20000000000000 : ℝ)^3625 := by
    have hnat : (326881719 : ℕ)^4649*20000000000000^3625 ≤ 8710131539083^3625*625000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326881719 625000000 8710131539083 20000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4649/1024 : ℝ)) 4649 3625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1661398999/10000000000 : ℝ), (687378451/1250000000 : ℝ), (326881719/625000000 : ℝ)] ![(19543453639/195312500000 : ℝ), (4644309403299/10000000000000 : ℝ), (8710131539083/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1661398999/10000000000 : ℝ)|^4649 ≤ (19543453639/195312500000 : ℝ)^3625
        have hw : |(-1661398999/10000000000 : ℝ)|=(1661398999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(687378451/1250000000 : ℝ)|^4649 ≤ (4644309403299/10000000000000 : ℝ)^3625
        have hw : |(687378451/1250000000 : ℝ)|=(687378451/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(326881719/625000000 : ℝ)|^4649 ≤ (8710131539083/20000000000000 : ℝ)^3625
        have hw : |(326881719/625000000 : ℝ)|=(326881719/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1576_box_13 (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (673256361/1250000000 : ℝ)*x 0 + (-908670533/5000000000 : ℝ)*x 1 + (1046021409/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (673256361/1250000000 : ℝ)^4649 ≤ (45222960353193/100000000000000 : ℝ)^3625 := by
    have hnat : (673256361 : ℕ)^4649*100000000000000^3625 ≤ 45222960353193^3625*1250000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673256361 1250000000 45222960353193 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (908670533/5000000000 : ℝ)^4649 ≤ (11226386839207/100000000000000 : ℝ)^3625 := by
    have hnat : (908670533 : ℕ)^4649*100000000000000^3625 ≤ 11226386839207^3625*5000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      908670533 5000000000 11226386839207 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1046021409/2000000000 : ℝ)^4649 ≤ (43550652793697/100000000000000 : ℝ)^3625 := by
    have hnat : (1046021409 : ℕ)^4649*100000000000000^3625 ≤ 43550652793697^3625*2000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046021409 2000000000 43550652793697 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4649/1024 : ℝ)) 4649 3625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(673256361/1250000000 : ℝ), (-908670533/5000000000 : ℝ), (1046021409/2000000000 : ℝ)] ![(45222960353193/100000000000000 : ℝ), (11226386839207/100000000000000 : ℝ), (43550652793697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(673256361/1250000000 : ℝ)|^4649 ≤ (45222960353193/100000000000000 : ℝ)^3625
        have hw : |(673256361/1250000000 : ℝ)|=(673256361/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-908670533/5000000000 : ℝ)|^4649 ≤ (11226386839207/100000000000000 : ℝ)^3625
        have hw : |(-908670533/5000000000 : ℝ)|=(908670533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1046021409/2000000000 : ℝ)|^4649 ≤ (43550652793697/100000000000000 : ℝ)^3625
        have hw : |(1046021409/2000000000 : ℝ)|=(1046021409/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1576_box_14 (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1077210419/2000000000 : ℝ)*x 0 + (5230105747/10000000000 : ℝ)*x 1 + (-72693647/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1077210419/2000000000 : ℝ)^4649 ≤ (565287166879/1250000000000 : ℝ)^3625 := by
    have hnat : (1077210419 : ℕ)^4649*1250000000000^3625 ≤ 565287166879^3625*2000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077210419 2000000000 565287166879 1250000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5230105747/10000000000 : ℝ)^4649 ≤ (21775319466097/50000000000000 : ℝ)^3625 := by
    have hnat : (5230105747 : ℕ)^4649*50000000000000^3625 ≤ 21775319466097^3625*10000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230105747 10000000000 21775319466097 50000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (72693647/400000000 : ℝ)^4649 ≤ (2245277540549/20000000000000 : ℝ)^3625 := by
    have hnat : (72693647 : ℕ)^4649*20000000000000^3625 ≤ 2245277540549^3625*400000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      72693647 400000000 2245277540549 20000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4649/1024 : ℝ)) 4649 3625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1077210419/2000000000 : ℝ), (5230105747/10000000000 : ℝ), (-72693647/400000000 : ℝ)] ![(565287166879/1250000000000 : ℝ), (21775319466097/50000000000000 : ℝ), (2245277540549/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1077210419/2000000000 : ℝ)|^4649 ≤ (565287166879/1250000000000 : ℝ)^3625
        have hw : |(1077210419/2000000000 : ℝ)|=(1077210419/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5230105747/10000000000 : ℝ)|^4649 ≤ (21775319466097/50000000000000 : ℝ)^3625
        have hw : |(5230105747/10000000000 : ℝ)|=(5230105747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-72693647/400000000 : ℝ)|^4649 ≤ (2245277540549/20000000000000 : ℝ)^3625
        have hw : |(-72693647/400000000 : ℝ)|=(72693647/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1576_box_15 (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (399654011/1000000000 : ℝ)*x 0 + (546130263/1250000000 : ℝ)*x 1 + (4369042987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (399654011/1000000000 : ℝ)^4649 ≤ (30843725062367/100000000000000 : ℝ)^3625 := by
    have hnat : (399654011 : ℕ)^4649*100000000000000^3625 ≤ 30843725062367^3625*1000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399654011 1000000000 30843725062367 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (546130263/1250000000 : ℝ)^4649 ≤ (34578132981293/100000000000000 : ℝ)^3625 := by
    have hnat : (546130263 : ℕ)^4649*100000000000000^3625 ≤ 34578132981293^3625*1250000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546130263 1250000000 34578132981293 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4369042987/10000000000 : ℝ)^4649 ≤ (432226774297/1250000000000 : ℝ)^3625 := by
    have hnat : (4369042987 : ℕ)^4649*1250000000000^3625 ≤ 432226774297^3625*10000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4369042987 10000000000 432226774297 1250000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4649/1024 : ℝ)) 4649 3625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(399654011/1000000000 : ℝ), (546130263/1250000000 : ℝ), (4369042987/10000000000 : ℝ)] ![(30843725062367/100000000000000 : ℝ), (34578132981293/100000000000000 : ℝ), (432226774297/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(399654011/1000000000 : ℝ)|^4649 ≤ (30843725062367/100000000000000 : ℝ)^3625
        have hw : |(399654011/1000000000 : ℝ)|=(399654011/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(546130263/1250000000 : ℝ)|^4649 ≤ (34578132981293/100000000000000 : ℝ)^3625
        have hw : |(546130263/1250000000 : ℝ)|=(546130263/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4369042987/10000000000 : ℝ)|^4649 ≤ (432226774297/1250000000000 : ℝ)^3625
        have hw : |(4369042987/10000000000 : ℝ)|=(4369042987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1576_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4212767/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11141/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(63839/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58931/100000 : ℝ) ∧ (4049/5000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (86403/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11141/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11141/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11141/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11141/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11141/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11141/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11141/100000 : ℝ) ^ (4647/1024 : ℝ) ≤ (4729987550954653/100000000000000000000 : ℝ) := by
    have hpowers : (11141/100000 : ℝ)^4647 ≤ (4729987550954653/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11141 : ℕ)^4647*100000000000000000000^1024 ≤ 4729987550954653^1024*100000^4647 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11141 100000 4729987550954653 100000000000000000000 4647 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11141/100000 : ℝ)) (X := (4729987550954653/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4647 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3871/25000 : ℝ) ^ (4647/1024 : ℝ) ≤ (2106784782151517/10000000000000000000 : ℝ) := by
    have hpowers : (3871/25000 : ℝ)^4647 ≤ (2106784782151517/10000000000000000000 : ℝ)^1024 := by
      have hnat : (3871 : ℕ)^4647*10000000000000000000^1024 ≤ 2106784782151517^1024*25000^4647 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3871 25000 2106784782151517 10000000000000000000 4647 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3871/25000 : ℝ)) (X := (2106784782151517/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4647 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004729987550954653/50000000000000000000 : ℝ) ≤ (10000208449694347/10000000000000000 : ℝ) ^ (4647/1024 : ℝ) := by
    have hpowers : (50004729987550954653/50000000000000000000 : ℝ)^1024 ≤ (10000208449694347/10000000000000000 : ℝ)^4647 := by
      have hnat : (50004729987550954653 : ℕ)^1024*10000000000000000^4647 ≤ 10000208449694347^4647*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004729987550954653 50000000000000000000 10000208449694347 10000000000000000 1024 4647 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000208449694347/10000000000000000 : ℝ)) (X := (50004729987550954653/50000000000000000000 : ℝ)) (by norm_num) 4647 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100025797835372469823/100000000000000000000 : ℝ) ≤ (500028420838381/500000000000000 : ℝ) ^ (4647/1024 : ℝ) := by
    have hpowers : (100025797835372469823/100000000000000000000 : ℝ)^1024 ≤ (500028420838381/500000000000000 : ℝ)^4647 := by
      have hnat : (100025797835372469823 : ℕ)^1024*500000000000000^4647 ≤ 500028420838381^4647*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100025797835372469823 100000000000000000000 500028420838381 500000000000000 1024 4647 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500028420838381/500000000000000 : ℝ)) (X := (100025797835372469823/100000000000000000000 : ℝ)) (by norm_num) 4647 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5002106784782151517/5000000000000000000 : ℝ) ≤ (10000928383840893/10000000000000000 : ℝ) ^ (4647/1024 : ℝ) := by
    have hpowers : (5002106784782151517/5000000000000000000 : ℝ)^1024 ≤ (10000928383840893/10000000000000000 : ℝ)^4647 := by
      have hnat : (5002106784782151517 : ℕ)^1024*10000000000000000^4647 ≤ 10000928383840893^4647*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002106784782151517 5000000000000000000 10000928383840893 10000000000000000 1024 4647 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000928383840893/10000000000000000 : ℝ)) (X := (5002106784782151517/5000000000000000000 : ℝ)) (by norm_num) 4647 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4729987550954653/100000000000000000000 : ℝ) ≤ ((8684576902139176007/8686000000000000000 : ℝ)+2*(359967073273/434300000000000 : ℝ)*(11141/100000 : ℝ))^(4647/1024 : ℝ) := by
    rw [show (8684576902139176007/8686000000000000000 : ℝ)+2*(359967073273/434300000000000 : ℝ)*(11141/100000 : ℝ)=(10000208449694347/10000000000000000 : ℝ) by norm_num, show 1+2*(4729987550954653/100000000000000000000 : ℝ)=(50004729987550954653/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2106784782151517/10000000000000000000 : ℝ)+(4729987550954653/100000000000000000000 : ℝ) ≤ ((8684576902139176007/8686000000000000000 : ℝ)+(359967073273/434300000000000 : ℝ)*((3871/25000 : ℝ)+(11141/100000 : ℝ)))^(4647/1024 : ℝ) := by
    rw [show (8684576902139176007/8686000000000000000 : ℝ)+(359967073273/434300000000000 : ℝ)*((3871/25000 : ℝ)+(11141/100000 : ℝ))=(500028420838381/500000000000000 : ℝ) by norm_num, show 1+(2106784782151517/10000000000000000000 : ℝ)+(4729987550954653/100000000000000000000 : ℝ)=(100025797835372469823/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2106784782151517/10000000000000000000 : ℝ) ≤ ((8684576902139176007/8686000000000000000 : ℝ)+2*(359967073273/434300000000000 : ℝ)*(3871/25000 : ℝ))^(4647/1024 : ℝ) := by
    rw [show (8684576902139176007/8686000000000000000 : ℝ)+2*(359967073273/434300000000000 : ℝ)*(3871/25000 : ℝ)=(10000928383840893/10000000000000000 : ℝ) by norm_num, show 1+2*(2106784782151517/10000000000000000000 : ℝ)=(5002106784782151517/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8684576902139176007/8686000000000000000 : ℝ)*(X 1 0+X 2 0)+(359967073273/434300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4647/1024 : ℝ)) (lo := (11141/100000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (8684576902139176007/8686000000000000000 : ℝ)) (alpha := (359967073273/434300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8684576902139176007/8686000000000000000 : ℝ)*(X 0 1+X 2 1)+(359967073273/434300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4647/1024 : ℝ)) (lo := (11141/100000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (8684576902139176007/8686000000000000000 : ℝ)) (alpha := (359967073273/434300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8684576902139176007/8686000000000000000 : ℝ)*(X 0 2+X 1 2)+(359967073273/434300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4647/1024 : ℝ)) (lo := (11141/100000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (8684576902139176007/8686000000000000000 : ℝ)) (alpha := (359967073273/434300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-393651117/2500000000 : ℝ)*X 0 0+(2697974777/5000000000 : ℝ)*X 0 1+(84311707/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1576_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5271141439/10000000000 : ℝ)*X 1 0+(-1748132923/10000000000 : ℝ)*X 1 1+(5395949761/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1576_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2635570831/5000000000 : ℝ)*X 2 0+(2697974819/5000000000 : ℝ)*X 2 1+(-437033197/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1576_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2220668343/5000000000 : ℝ)*X 0 0+(2073620149/5000000000 : ℝ)*X 0 1+(1036810087/2500000000 : ℝ)*X 0 2+(2220668343/5000000000 : ℝ)*X 1 0+(2073620149/5000000000 : ℝ)*X 1 1+(1036810087/2500000000 : ℝ)*X 1 2+(2220668343/5000000000 : ℝ)*X 2 0+(2073620149/5000000000 : ℝ)*X 2 1+(1036810087/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1576_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-496420601/2500000000 : ℝ)*X 0 0+(2622578487/5000000000 : ℝ)*X 0 1+(5245156773/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1576_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2687810839/5000000000 : ℝ)*X 1 0+(-905607471/5000000000 : ℝ)*X 1 1+(2622578359/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1576_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1343905337/2500000000 : ℝ)*X 2 0+(5245156993/10000000000 : ℝ)*X 2 1+(-90560751/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1576_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4037688651/10000000000 : ℝ)*X 0 0+(869787511/2000000000 : ℝ)*X 0 1+(2174468771/5000000000 : ℝ)*X 0 2+(4037688651/10000000000 : ℝ)*X 1 0+(869787511/2000000000 : ℝ)*X 1 1+(2174468771/5000000000 : ℝ)*X 1 2+(4037688651/10000000000 : ℝ)*X 2 0+(869787511/2000000000 : ℝ)*X 2 1+(2174468771/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1576_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1898523559/10000000000 : ℝ)*X 0 0+(1284713897/2500000000 : ℝ)*X 0 1+(5416199563/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1576_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5257107929/10000000000 : ℝ)*X 1 0+(-1739430263/10000000000 : ℝ)*X 1 1+(338512501/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1576_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5257107539/10000000000 : ℝ)*X 2 0+(5416199983/10000000000 : ℝ)*X 2 1+(-1739430841/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1576_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4494399963/10000000000 : ℝ)*X 0 0+(1030029771/2500000000 : ℝ)*X 0 1+(4120120109/10000000000 : ℝ)*X 0 2+(4494399963/10000000000 : ℝ)*X 1 0+(1030029771/2500000000 : ℝ)*X 1 1+(4120120109/10000000000 : ℝ)*X 1 2+(4494399963/10000000000 : ℝ)*X 2 0+(1030029771/2500000000 : ℝ)*X 2 1+(4120120109/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1576_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1661398999/10000000000 : ℝ)*X 0 0+(687378451/1250000000 : ℝ)*X 0 1+(326881719/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1576_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((673256361/1250000000 : ℝ)*X 1 0+(-908670533/5000000000 : ℝ)*X 1 1+(1046021409/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1576_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1077210419/2000000000 : ℝ)*X 2 0+(5230105747/10000000000 : ℝ)*X 2 1+(-72693647/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1576_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((399654011/1000000000 : ℝ)*X 0 0+(546130263/1250000000 : ℝ)*X 0 1+(4369042987/10000000000 : ℝ)*X 0 2+(399654011/1000000000 : ℝ)*X 1 0+(546130263/1250000000 : ℝ)*X 1 1+(4369042987/10000000000 : ℝ)*X 1 2+(399654011/1000000000 : ℝ)*X 2 0+(546130263/1250000000 : ℝ)*X 2 1+(4369042987/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1576_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-63839/100000 : ℝ) ≤ (-69310819674482849663626460335029/108575000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2347/48828125000 : ℝ)*(upper1) + (1840971/20000000000000 : ℝ)*(upper2) + (10532021/20000000000000 : ℝ)*(upper3) + (383159/781250000000 : ℝ)*(lower4) + (579094761937049/25000000000000 : ℝ)*(major0) + (579094761937049/25000000000000 : ℝ)*(major1) + (579094761937049/25000000000000 : ℝ)*(major2) + (4369581961/100000000000000 : ℝ)*(sp1) + (833616267/50000000000000 : ℝ)*(sp3) + (1639709246994269/50000000000000 : ℝ)*(sp4) + (3279414124406577/100000000000000 : ℝ)*(sp5) + (655882870840351/20000000000000 : ℝ)*(sp6) + (137461687192961/10000000000000 : ℝ)*(sp7) + (4139786783/100000000000000 : ℝ)*(sp14) + (42956829348817/3125000000000 : ℝ)*(f.failure) + (1639709246994269/50000000000000 : ℝ)*(f.sum) + (31161703005061/10857500000000000000000000000 : ℝ)*base66 + (1411415856890623343/217150000000000000000000000000000 : ℝ)*base67 + (1490152352098176657/217150000000000000000000000000000 : ℝ)*base70 + (1972610971791873343/217150000000000000000000000000000 : ℝ)*base71 + (19761355928167/21715000000000000000000000000 : ℝ)*base74 + (13078954429319126657/217150000000000000000000000000000 : ℝ)*base76 + (1284990721905873343/217150000000000000000000000000000 : ℝ)*base77 + (949472530732023343/217150000000000000000000000000000 : ℝ)*base79 + (100323293285297/21715000000000000000000000000 : ℝ)*base82 + (65861/7812500000000000000 : ℝ)*base90 + (65861/7812500000000000000 : ℝ)*base92 + (65861/7812500000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (58931/100000 : ℝ) ≤ (31993620294192579848830882241823/54287500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (66984929/100000000000000 : ℝ)*(upper0) + (3354371/12500000000000 : ℝ)*(upper3) + (94975823/100000000000000 : ℝ)*(upper4) + (299628034765937/12500000000000 : ℝ)*(major0) + (299628034765937/12500000000000 : ℝ)*(major1) + (299628034765937/12500000000000 : ℝ)*(major2) + (335192496569077/10000000000000 : ℝ)*(sp0) + (837979644999381/25000000000000 : ℝ)*(sp1) + (209494790243403/6250000000000 : ℝ)*(sp2) + (711237462514569/50000000000000 : ℝ)*(sp3) + (2310089107/25000000000000 : ℝ)*(sp5) + (11176459503/100000000000000 : ℝ)*(sp6) + (2854663181/100000000000000 : ℝ)*(sp8) + (1251630701/100000000000000 : ℝ)*(sp11) + (1422476176659839/100000000000000 : ℝ)*(f.failure) + (104747744386061/3125000000000 : ℝ)*(f.sum) + (1033120224377/339296875000000000000000000 : ℝ)*base65 + (831225967865093559/108575000000000000000000000000000 : ℝ)*base67 + (430124480914093559/108575000000000000000000000000000 : ℝ)*base69 + (128100680847468559/108575000000000000000000000000000 : ℝ)*base71 + (1332249039823/5428750000000000000000000000 : ℝ)*base74 + (49846963643781441/108575000000000000000000000000000 : ℝ)*base76 + (118294251992468559/108575000000000000000000000000000 : ℝ)*base77 + (853254604314531441/108575000000000000000000000000000 : ℝ)*base80 + (116506738014127/21715000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (35487/250000000000000000000 : ℝ)*base90 + (35487/250000000000000000000 : ℝ)*base92 + (35487/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (4049/5000 : ℝ) ≤ (175853017808976101604592826065377/217150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (48037151/100000000000000 : ℝ)*(upper0) + (126414427/100000000000000 : ℝ)*(lower1) + (8558459/5000000000000 : ℝ)*(upper2) + (103410241/50000000000000 : ℝ)*(lower5) + (1291305956443363/50000000000000 : ℝ)*(major0) + (1291305956443363/50000000000000 : ℝ)*(major1) + (1291305956443363/50000000000000 : ℝ)*(major2) + (3537388893/100000000000000 : ℝ)*(sp0) + (1360583503/6250000000000 : ℝ)*(sp1) + (3605823781/20000000000000 : ℝ)*(sp3) + (2253509981223/62500000000 : ℝ)*(sp8) + (1802798869004823/50000000000000 : ℝ)*(sp9) + (1802809753672847/50000000000000 : ℝ)*(sp10) + (766296098234207/50000000000000 : ℝ)*(sp11) + (38315255639683/2500000000000 : ℝ)*(f.failure) + (1802809753672847/50000000000000 : ℝ)*(f.sum) + (35515513434389/10857500000000000000000000000 : ℝ)*base65 + (2530556928157571541/434300000000000000000000000000000 : ℝ)*base67 + (3749398883226971541/434300000000000000000000000000000 : ℝ)*base69 + (1718132711801428459/434300000000000000000000000000000 : ℝ)*base72 + (51637501663219/10857500000000000000000000000 : ℝ)*base73 + (1381656953826971541/434300000000000000000000000000000 : ℝ)*base75 + (420535888299428459/434300000000000000000000000000000 : ℝ)*base78 + (9083526753113571541/434300000000000000000000000000000 : ℝ)*base79 + (77242242861309/10857500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (57861/6250000000000000000 : ℝ)*base89 + (57861/6250000000000000000 : ℝ)*base91 + (57861/6250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-86403/100000 : ℝ) ≤ (-187618804624233067518390494493363/217150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (43607943/20000000000000 : ℝ)*(lower0) + (229887337/50000000000000 : ℝ)*(lower1) + (5054767/2500000000000 : ℝ)*(lower2) + (1311630205611101/50000000000000 : ℝ)*(major0) + (1311630205611101/50000000000000 : ℝ)*(major1) + (1311630205611101/50000000000000 : ℝ)*(major2) + (1544294977/20000000000000 : ℝ)*(sp0) + (504005752129/100000000000000 : ℝ)*(sp5) + (148077821059/20000000000000 : ℝ)*(sp6) + (62144648551/100000000000000 : ℝ)*(sp7) + (58102825802263/1562500000000 : ℝ)*(sp12) + (929521141766897/25000000000000 : ℝ)*(sp13) + (1858924091857211/50000000000000 : ℝ)*(sp14) + (389167572472609/25000000000000 : ℝ)*(sp15) + (1556732434538987/100000000000000 : ℝ)*(f.failure) + (3718588572819717/100000000000000 : ℝ)*(f.sum) + (1625043415351/21715000000000000000000000000 : ℝ)*base65 + (2087543951085013707/434300000000000000000000000000000 : ℝ)*base67 + (2968214673780913707/434300000000000000000000000000000 : ℝ)*base69 + (2088486394245413707/434300000000000000000000000000000 : ℝ)*base71 + (57261617799299/21715000000000000000000000000 : ℝ)*base74 + (1423994022582713707/434300000000000000000000000000000 : ℝ)*base75 + (2667763923406213707/434300000000000000000000000000000 : ℝ)*base77 + (1063686902696113707/434300000000000000000000000000000 : ℝ)*base79 + (15042076556007/10857500000000000000000000000 : ℝ)*base82 + (352971/250000000000000000000 : ℝ)*base90 + (352971/250000000000000000000 : ℝ)*base92 + (352971/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1576_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4212767/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11141/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63839/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58931/100000 : ℝ) else (4049/5000 : ℝ) ≤ X j i ∧ X j i ≤ (86403/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1576_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1576_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4212767/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (557/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63839/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58931/100000 : ℝ) else (4049/5000 : ℝ) ≤ X j i ∧ X j i ≤ (86403/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1576_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1576_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4212767/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (557/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63839/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58931/100000 : ℝ) else (4049/5000 : ℝ) ≤ X j i ∧ X j i ≤ (86403/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1576_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
