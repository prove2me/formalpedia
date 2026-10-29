-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1606_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:50:20.011707+00:00
-- url     : https://prove2.me/submissions/cc5cd5aa-7c82-4817-bfa4-aab08d6b7757

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
theorem support_rectangle_w1606_box_0 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1439483539/10000000000 : ℝ)*x 0 + (1354780541/2500000000 : ℝ)*x 1 + (1083824433/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1439483539/10000000000 : ℝ)^4743 ≤ (8441603523347/100000000000000 : ℝ)^3719 := by
    have hnat : (1439483539 : ℕ)^4743*100000000000000^3719 ≤ 8441603523347^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1439483539 10000000000 8441603523347 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1354780541/2500000000 : ℝ)^4743 ≤ (11444799555437/25000000000000 : ℝ)^3719 := by
    have hnat : (1354780541 : ℕ)^4743*25000000000000^3719 ≤ 11444799555437^3719*2500000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354780541 2500000000 11444799555437 25000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083824433/2000000000 : ℝ)^4743 ≤ (22889599116261/50000000000000 : ℝ)^3719 := by
    have hnat : (1083824433 : ℕ)^4743*50000000000000^3719 ≤ 22889599116261^3719*2000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083824433 2000000000 22889599116261 50000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1439483539/10000000000 : ℝ), (1354780541/2500000000 : ℝ), (1083824433/2000000000 : ℝ)] ![(8441603523347/100000000000000 : ℝ), (11444799555437/25000000000000 : ℝ), (22889599116261/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1439483539/10000000000 : ℝ)|^4743 ≤ (8441603523347/100000000000000 : ℝ)^3719
        have hw : |(-1439483539/10000000000 : ℝ)|=(1439483539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1354780541/2500000000 : ℝ)|^4743 ≤ (11444799555437/25000000000000 : ℝ)^3719
        have hw : |(1354780541/2500000000 : ℝ)|=(1354780541/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1083824433/2000000000 : ℝ)|^4743 ≤ (22889599116261/50000000000000 : ℝ)^3719
        have hw : |(1083824433/2000000000 : ℝ)|=(1083824433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_box_1 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2625553583/5000000000 : ℝ)*x 0 + (-837674389/5000000000 : ℝ)*x 1 + (5419122179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2625553583/5000000000 : ℝ)^4743 ≤ (8795366926499/20000000000000 : ℝ)^3719 := by
    have hnat : (2625553583 : ℕ)^4743*20000000000000^3719 ≤ 8795366926499^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625553583 5000000000 8795366926499 20000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (837674389/5000000000 : ℝ)^4743 ≤ (81951735701/800000000000 : ℝ)^3719 := by
    have hnat : (837674389 : ℕ)^4743*800000000000^3719 ≤ 81951735701^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      837674389 5000000000 81951735701 800000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5419122179/10000000000 : ℝ)^4743 ≤ (22889599191677/50000000000000 : ℝ)^3719 := by
    have hnat : (5419122179 : ℕ)^4743*50000000000000^3719 ≤ 22889599191677^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419122179 10000000000 22889599191677 50000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2625553583/5000000000 : ℝ), (-837674389/5000000000 : ℝ), (5419122179/10000000000 : ℝ)] ![(8795366926499/20000000000000 : ℝ), (81951735701/800000000000 : ℝ), (22889599191677/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2625553583/5000000000 : ℝ)|^4743 ≤ (8795366926499/20000000000000 : ℝ)^3719
        have hw : |(2625553583/5000000000 : ℝ)|=(2625553583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-837674389/5000000000 : ℝ)|^4743 ≤ (81951735701/800000000000 : ℝ)^3719
        have hw : |(-837674389/5000000000 : ℝ)|=(837674389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5419122179/10000000000 : ℝ)|^4743 ≤ (22889599191677/50000000000000 : ℝ)^3719
        have hw : |(5419122179/10000000000 : ℝ)|=(5419122179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_box_2 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (210044287/400000000 : ℝ)*x 0 + (1083824433/2000000000 : ℝ)*x 1 + (-837674393/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210044287/400000000 : ℝ)^4743 ≤ (21988417364311/50000000000000 : ℝ)^3719 := by
    have hnat : (210044287 : ℕ)^4743*50000000000000^3719 ≤ 21988417364311^3719*400000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210044287 400000000 21988417364311 50000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083824433/2000000000 : ℝ)^4743 ≤ (22889599116261/50000000000000 : ℝ)^3719 := by
    have hnat : (1083824433 : ℕ)^4743*50000000000000^3719 ≤ 22889599116261^3719*2000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083824433 2000000000 22889599116261 50000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (837674393/5000000000 : ℝ)^4743 ≤ (1024396702501/10000000000000 : ℝ)^3719 := by
    have hnat : (837674393 : ℕ)^4743*10000000000000^3719 ≤ 1024396702501^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      837674393 5000000000 1024396702501 10000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210044287/400000000 : ℝ), (1083824433/2000000000 : ℝ), (-837674393/5000000000 : ℝ)] ![(21988417364311/50000000000000 : ℝ), (22889599116261/50000000000000 : ℝ), (1024396702501/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210044287/400000000 : ℝ)|^4743 ≤ (21988417364311/50000000000000 : ℝ)^3719
        have hw : |(210044287/400000000 : ℝ)|=(210044287/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083824433/2000000000 : ℝ)|^4743 ≤ (22889599116261/50000000000000 : ℝ)^3719
        have hw : |(1083824433/2000000000 : ℝ)|=(1083824433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-837674393/5000000000 : ℝ)|^4743 ≤ (1024396702501/10000000000000 : ℝ)^3719
        have hw : |(-837674393/5000000000 : ℝ)|=(837674393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_box_3 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4496071799/10000000000 : ℝ)*x 0 + (4088565811/10000000000 : ℝ)*x 1 + (4088565811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4496071799/10000000000 : ℝ)^4743 ≤ (1761624759/4882812500 : ℝ)^3719 := by
    have hnat : (4496071799 : ℕ)^4743*4882812500^3719 ≤ 1761624759^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4496071799 10000000000 1761624759 4882812500 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4088565811/10000000000 : ℝ)^4743 ≤ (31960962458049/100000000000000 : ℝ)^3719 := by
    have hnat : (4088565811 : ℕ)^4743*100000000000000^3719 ≤ 31960962458049^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4088565811 10000000000 31960962458049 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4088565811/10000000000 : ℝ)^4743 ≤ (31960962458049/100000000000000 : ℝ)^3719 := by
    have hnat : (4088565811 : ℕ)^4743*100000000000000^3719 ≤ 31960962458049^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4088565811 10000000000 31960962458049 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4496071799/10000000000 : ℝ), (4088565811/10000000000 : ℝ), (4088565811/10000000000 : ℝ)] ![(1761624759/4882812500 : ℝ), (31960962458049/100000000000000 : ℝ), (31960962458049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4496071799/10000000000 : ℝ)|^4743 ≤ (1761624759/4882812500 : ℝ)^3719
        have hw : |(4496071799/10000000000 : ℝ)|=(4496071799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4088565811/10000000000 : ℝ)|^4743 ≤ (31960962458049/100000000000000 : ℝ)^3719
        have hw : |(4088565811/10000000000 : ℝ)|=(4088565811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4088565811/10000000000 : ℝ)|^4743 ≤ (31960962458049/100000000000000 : ℝ)^3719
        have hw : |(4088565811/10000000000 : ℝ)|=(4088565811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_box_4 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1000048579/5000000000 : ℝ)*x 0 + (651733421/1250000000 : ℝ)*x 1 + (5213867183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1000048579/5000000000 : ℝ)^4743 ≤ (12841049488921/100000000000000 : ℝ)^3719 := by
    have hnat : (1000048579 : ℕ)^4743*100000000000000^3719 ≤ 12841049488921^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000048579 5000000000 12841049488921 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (651733421/1250000000 : ℝ)^4743 ≤ (2178973811861/5000000000000 : ℝ)^3719 := by
    have hnat : (651733421 : ℕ)^4743*5000000000000^3719 ≤ 2178973811861^3719*1250000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651733421 1250000000 2178973811861 5000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5213867183/10000000000 : ℝ)^4743 ≤ (21789737132579/50000000000000 : ℝ)^3719 := by
    have hnat : (5213867183 : ℕ)^4743*50000000000000^3719 ≤ 21789737132579^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5213867183 10000000000 21789737132579 50000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1000048579/5000000000 : ℝ), (651733421/1250000000 : ℝ), (5213867183/10000000000 : ℝ)] ![(12841049488921/100000000000000 : ℝ), (2178973811861/5000000000000 : ℝ), (21789737132579/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1000048579/5000000000 : ℝ)|^4743 ≤ (12841049488921/100000000000000 : ℝ)^3719
        have hw : |(-1000048579/5000000000 : ℝ)|=(1000048579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(651733421/1250000000 : ℝ)|^4743 ≤ (2178973811861/5000000000000 : ℝ)^3719
        have hw : |(651733421/1250000000 : ℝ)|=(651733421/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5213867183/10000000000 : ℝ)|^4743 ≤ (21789737132579/50000000000000 : ℝ)^3719
        have hw : |(5213867183/10000000000 : ℝ)|=(5213867183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_box_5 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5392849413/10000000000 : ℝ)*x 0 + (-1761969171/10000000000 : ℝ)*x 1 + (208554693/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5392849413/10000000000 : ℝ)^4743 ≤ (45496331779179/100000000000000 : ℝ)^3719 := by
    have hnat : (5392849413 : ℕ)^4743*100000000000000^3719 ≤ 45496331779179^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392849413 10000000000 45496331779179 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1761969171/10000000000 : ℝ)^4743 ≤ (5462096217101/50000000000000 : ℝ)^3719 := by
    have hnat : (1761969171 : ℕ)^4743*50000000000000^3719 ≤ 5462096217101^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1761969171 10000000000 5462096217101 50000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208554693/400000000 : ℝ)^4743 ≤ (43579475778849/100000000000000 : ℝ)^3719 := by
    have hnat : (208554693 : ℕ)^4743*100000000000000^3719 ≤ 43579475778849^3719*400000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208554693 400000000 43579475778849 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5392849413/10000000000 : ℝ), (-1761969171/10000000000 : ℝ), (208554693/400000000 : ℝ)] ![(45496331779179/100000000000000 : ℝ), (5462096217101/50000000000000 : ℝ), (43579475778849/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5392849413/10000000000 : ℝ)|^4743 ≤ (45496331779179/100000000000000 : ℝ)^3719
        have hw : |(5392849413/10000000000 : ℝ)|=(5392849413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1761969171/10000000000 : ℝ)|^4743 ≤ (5462096217101/50000000000000 : ℝ)^3719
        have hw : |(-1761969171/10000000000 : ℝ)|=(1761969171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(208554693/400000000 : ℝ)|^4743 ≤ (43579475778849/100000000000000 : ℝ)^3719
        have hw : |(208554693/400000000 : ℝ)|=(208554693/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_box_6 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42131637/78125000 : ℝ)*x 0 + (5213867119/10000000000 : ℝ)*x 1 + (-1761969281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42131637/78125000 : ℝ)^4743 ≤ (2843520818911/6250000000000 : ℝ)^3719 := by
    have hnat : (42131637 : ℕ)^4743*6250000000000^3719 ≤ 2843520818911^3719*78125000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42131637 78125000 2843520818911 6250000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5213867119/10000000000 : ℝ)^4743 ≤ (43579473582931/100000000000000 : ℝ)^3719 := by
    have hnat : (5213867119 : ℕ)^4743*100000000000000^3719 ≤ 43579473582931^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5213867119 10000000000 43579473582931 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1761969281/10000000000 : ℝ)^4743 ≤ (2184838660797/20000000000000 : ℝ)^3719 := by
    have hnat : (1761969281 : ℕ)^4743*20000000000000^3719 ≤ 2184838660797^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1761969281 10000000000 2184838660797 20000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42131637/78125000 : ℝ), (5213867119/10000000000 : ℝ), (-1761969281/10000000000 : ℝ)] ![(2843520818911/6250000000000 : ℝ), (43579473582931/100000000000000 : ℝ), (2184838660797/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42131637/78125000 : ℝ)|^4743 ≤ (2843520818911/6250000000000 : ℝ)^3719
        have hw : |(42131637/78125000 : ℝ)|=(42131637/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5213867119/10000000000 : ℝ)|^4743 ≤ (43579473582931/100000000000000 : ℝ)^3719
        have hw : |(5213867119/10000000000 : ℝ)|=(5213867119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1761969281/10000000000 : ℝ)|^4743 ≤ (2184838660797/20000000000000 : ℝ)^3719
        have hw : |(-1761969281/10000000000 : ℝ)|=(1761969281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_box_7 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3929845621/10000000000 : ℝ)*x 0 + (17075521/39062500 : ℝ)*x 1 + (2185666627/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3929845621/10000000000 : ℝ)^4743 ≤ (15193565140559/50000000000000 : ℝ)^3719 := by
    have hnat : (3929845621 : ℕ)^4743*50000000000000^3719 ≤ 15193565140559^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3929845621 10000000000 15193565140559 50000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17075521/39062500 : ℝ)^4743 ≤ (8701608868663/25000000000000 : ℝ)^3719 := by
    have hnat : (17075521 : ℕ)^4743*25000000000000^3719 ≤ 8701608868663^3719*39062500^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17075521 39062500 8701608868663 25000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2185666627/5000000000 : ℝ)^4743 ≤ (34806434235763/100000000000000 : ℝ)^3719 := by
    have hnat : (2185666627 : ℕ)^4743*100000000000000^3719 ≤ 34806434235763^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185666627 5000000000 34806434235763 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3929845621/10000000000 : ℝ), (17075521/39062500 : ℝ), (2185666627/5000000000 : ℝ)] ![(15193565140559/50000000000000 : ℝ), (8701608868663/25000000000000 : ℝ), (34806434235763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3929845621/10000000000 : ℝ)|^4743 ≤ (15193565140559/50000000000000 : ℝ)^3719
        have hw : |(3929845621/10000000000 : ℝ)|=(3929845621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(17075521/39062500 : ℝ)|^4743 ≤ (8701608868663/25000000000000 : ℝ)^3719
        have hw : |(17075521/39062500 : ℝ)|=(17075521/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2185666627/5000000000 : ℝ)|^4743 ≤ (34806434235763/100000000000000 : ℝ)^3719
        have hw : |(2185666627/5000000000 : ℝ)|=(2185666627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_box_8 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-94047553/500000000 : ℝ)*x 0 + (2533679809/5000000000 : ℝ)*x 1 + (5449115121/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (94047553/500000000 : ℝ)^4743 ≤ (593680170723/5000000000000 : ℝ)^3719 := by
    have hnat : (94047553 : ℕ)^4743*5000000000000^3719 ≤ 593680170723^3719*500000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94047553 500000000 593680170723 5000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2533679809/5000000000 : ℝ)^4743 ≤ (10505954090721/25000000000000 : ℝ)^3719 := by
    have hnat : (2533679809 : ℕ)^4743*25000000000000^3719 ≤ 10505954090721^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2533679809 5000000000 10505954090721 25000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5449115121/10000000000 : ℝ)^4743 ≤ (46102580205869/100000000000000 : ℝ)^3719 := by
    have hnat : (5449115121 : ℕ)^4743*100000000000000^3719 ≤ 46102580205869^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5449115121 10000000000 46102580205869 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-94047553/500000000 : ℝ), (2533679809/5000000000 : ℝ), (5449115121/10000000000 : ℝ)] ![(593680170723/5000000000000 : ℝ), (10505954090721/25000000000000 : ℝ), (46102580205869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-94047553/500000000 : ℝ)|^4743 ≤ (593680170723/5000000000000 : ℝ)^3719
        have hw : |(-94047553/500000000 : ℝ)|=(94047553/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2533679809/5000000000 : ℝ)|^4743 ≤ (10505954090721/25000000000000 : ℝ)^3719
        have hw : |(2533679809/5000000000 : ℝ)|=(2533679809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5449115121/10000000000 : ℝ)|^4743 ≤ (46102580205869/100000000000000 : ℝ)^3719
        have hw : |(5449115121/10000000000 : ℝ)|=(5449115121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_box_9 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5230389347/10000000000 : ℝ)*x 0 + (-166222571/1000000000 : ℝ)*x 1 + (681139431/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5230389347/10000000000 : ℝ)^4743 ≤ (43755673971139/100000000000000 : ℝ)^3719 := by
    have hnat : (5230389347 : ℕ)^4743*100000000000000^3719 ≤ 43755673971139^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230389347 10000000000 43755673971139 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (166222571/1000000000 : ℝ)^4743 ≤ (2535435569351/25000000000000 : ℝ)^3719 := by
    have hnat : (166222571 : ℕ)^4743*25000000000000^3719 ≤ 2535435569351^3719*1000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166222571 1000000000 2535435569351 25000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (681139431/1250000000 : ℝ)^4743 ≤ (23051291867119/50000000000000 : ℝ)^3719 := by
    have hnat : (681139431 : ℕ)^4743*50000000000000^3719 ≤ 23051291867119^3719*1250000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681139431 1250000000 23051291867119 50000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5230389347/10000000000 : ℝ), (-166222571/1000000000 : ℝ), (681139431/1250000000 : ℝ)] ![(43755673971139/100000000000000 : ℝ), (2535435569351/25000000000000 : ℝ), (23051291867119/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5230389347/10000000000 : ℝ)|^4743 ≤ (43755673971139/100000000000000 : ℝ)^3719
        have hw : |(5230389347/10000000000 : ℝ)|=(5230389347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-166222571/1000000000 : ℝ)|^4743 ≤ (2535435569351/25000000000000 : ℝ)^3719
        have hw : |(-166222571/1000000000 : ℝ)|=(166222571/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(681139431/1250000000 : ℝ)|^4743 ≤ (23051291867119/50000000000000 : ℝ)^3719
        have hw : |(681139431/1250000000 : ℝ)|=(681139431/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_box_10 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1307597497/2500000000 : ℝ)*x 0 + (1362278961/2500000000 : ℝ)*x 1 + (-1662224281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1307597497/2500000000 : ℝ)^4743 ≤ (1750227232401/4000000000000 : ℝ)^3719 := by
    have hnat : (1307597497 : ℕ)^4743*4000000000000^3719 ≤ 1750227232401^3719*2500000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307597497 2500000000 1750227232401 4000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1362278961/2500000000 : ℝ)^4743 ≤ (11525647001781/25000000000000 : ℝ)^3719 := by
    have hnat : (1362278961 : ℕ)^4743*25000000000000^3719 ≤ 11525647001781^3719*2500000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1362278961 2500000000 11525647001781 25000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1662224281/10000000000 : ℝ)^4743 ≤ (2028346231599/20000000000000 : ℝ)^3719 := by
    have hnat : (1662224281 : ℕ)^4743*20000000000000^3719 ≤ 2028346231599^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1662224281 10000000000 2028346231599 20000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1307597497/2500000000 : ℝ), (1362278961/2500000000 : ℝ), (-1662224281/10000000000 : ℝ)] ![(1750227232401/4000000000000 : ℝ), (11525647001781/25000000000000 : ℝ), (2028346231599/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1307597497/2500000000 : ℝ)|^4743 ≤ (1750227232401/4000000000000 : ℝ)^3719
        have hw : |(1307597497/2500000000 : ℝ)|=(1307597497/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1362278961/2500000000 : ℝ)|^4743 ≤ (11525647001781/25000000000000 : ℝ)^3719
        have hw : |(1362278961/2500000000 : ℝ)|=(1362278961/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1662224281/10000000000 : ℝ)|^4743 ≤ (2028346231599/20000000000000 : ℝ)^3719
        have hw : |(-1662224281/10000000000 : ℝ)|=(1662224281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_box_11 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (572051777/1250000000 : ℝ)*x 0 + (4047171693/10000000000 : ℝ)*x 1 + (2023585149/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (572051777/1250000000 : ℝ)^4743 ≤ (4612787202673/12500000000000 : ℝ)^3719 := by
    have hnat : (572051777 : ℕ)^4743*12500000000000^3719 ≤ 4612787202673^3719*1250000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      572051777 1250000000 4612787202673 12500000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4047171693/10000000000 : ℝ)^4743 ≤ (7887214529147/25000000000000 : ℝ)^3719 := by
    have hnat : (4047171693 : ℕ)^4743*25000000000000^3719 ≤ 7887214529147^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4047171693 10000000000 7887214529147 25000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2023585149/5000000000 : ℝ)^4743 ≤ (7887211061993/25000000000000 : ℝ)^3719 := by
    have hnat : (2023585149 : ℕ)^4743*25000000000000^3719 ≤ 7887211061993^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2023585149 5000000000 7887211061993 25000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(572051777/1250000000 : ℝ), (4047171693/10000000000 : ℝ), (2023585149/5000000000 : ℝ)] ![(4612787202673/12500000000000 : ℝ), (7887214529147/25000000000000 : ℝ), (7887211061993/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(572051777/1250000000 : ℝ)|^4743 ≤ (4612787202673/12500000000000 : ℝ)^3719
        have hw : |(572051777/1250000000 : ℝ)|=(572051777/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4047171693/10000000000 : ℝ)|^4743 ≤ (7887214529147/25000000000000 : ℝ)^3719
        have hw : |(4047171693/10000000000 : ℝ)|=(4047171693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2023585149/5000000000 : ℝ)|^4743 ≤ (7887211061993/25000000000000 : ℝ)^3719
        have hw : |(2023585149/5000000000 : ℝ)|=(2023585149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_box_12 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1557469433/10000000000 : ℝ)*x 0 + (5559637799/10000000000 : ℝ)*x 1 + (5193996021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1557469433/10000000000 : ℝ)^4743 ≤ (2333447562167/25000000000000 : ℝ)^3719 := by
    have hnat : (1557469433 : ℕ)^4743*25000000000000^3719 ≤ 2333447562167^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1557469433 10000000000 2333447562167 25000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5559637799/10000000000 : ℝ)^4743 ≤ (23649223396021/50000000000000 : ℝ)^3719 := by
    have hnat : (5559637799 : ℕ)^4743*50000000000000^3719 ≤ 23649223396021^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5559637799 10000000000 23649223396021 50000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5193996021/10000000000 : ℝ)^4743 ≤ (43367762939849/100000000000000 : ℝ)^3719 := by
    have hnat : (5193996021 : ℕ)^4743*100000000000000^3719 ≤ 43367762939849^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5193996021 10000000000 43367762939849 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1557469433/10000000000 : ℝ), (5559637799/10000000000 : ℝ), (5193996021/10000000000 : ℝ)] ![(2333447562167/25000000000000 : ℝ), (23649223396021/50000000000000 : ℝ), (43367762939849/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1557469433/10000000000 : ℝ)|^4743 ≤ (2333447562167/25000000000000 : ℝ)^3719
        have hw : |(-1557469433/10000000000 : ℝ)|=(1557469433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5559637799/10000000000 : ℝ)|^4743 ≤ (23649223396021/50000000000000 : ℝ)^3719
        have hw : |(5559637799/10000000000 : ℝ)|=(5559637799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5193996021/10000000000 : ℝ)|^4743 ≤ (43367762939849/100000000000000 : ℝ)^3719
        have hw : |(5193996021/10000000000 : ℝ)|=(5193996021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_box_13 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5406578693/10000000000 : ℝ)*x 0 + (-885025757/5000000000 : ℝ)*x 1 + (5193995549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5406578693/10000000000 : ℝ)^4743 ≤ (9128820261859/20000000000000 : ℝ)^3719 := by
    have hnat : (5406578693 : ℕ)^4743*20000000000000^3719 ≤ 9128820261859^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406578693 10000000000 9128820261859 20000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (885025757/5000000000 : ℝ)^4743 ≤ (2747035188317/25000000000000 : ℝ)^3719 := by
    have hnat : (885025757 : ℕ)^4743*25000000000000^3719 ≤ 2747035188317^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      885025757 5000000000 2747035188317 25000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5193995549/10000000000 : ℝ)^4743 ≤ (43367757913711/100000000000000 : ℝ)^3719 := by
    have hnat : (5193995549 : ℕ)^4743*100000000000000^3719 ≤ 43367757913711^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5193995549 10000000000 43367757913711 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5406578693/10000000000 : ℝ), (-885025757/5000000000 : ℝ), (5193995549/10000000000 : ℝ)] ![(9128820261859/20000000000000 : ℝ), (2747035188317/25000000000000 : ℝ), (43367757913711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5406578693/10000000000 : ℝ)|^4743 ≤ (9128820261859/20000000000000 : ℝ)^3719
        have hw : |(5406578693/10000000000 : ℝ)|=(5406578693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-885025757/5000000000 : ℝ)|^4743 ≤ (2747035188317/25000000000000 : ℝ)^3719
        have hw : |(-885025757/5000000000 : ℝ)|=(885025757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5193995549/10000000000 : ℝ)|^4743 ≤ (43367757913711/100000000000000 : ℝ)^3719
        have hw : |(5193995549/10000000000 : ℝ)|=(5193995549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_box_14 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5406579729/10000000000 : ℝ)*x 0 + (1298498851/2500000000 : ℝ)*x 1 + (-1770050301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5406579729/10000000000 : ℝ)^4743 ≤ (45644112463763/100000000000000 : ℝ)^3719 := by
    have hnat : (5406579729 : ℕ)^4743*100000000000000^3719 ≤ 45644112463763^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406579729 10000000000 45644112463763 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1298498851/2500000000 : ℝ)^4743 ≤ (8673551273933/20000000000000 : ℝ)^3719 := by
    have hnat : (1298498851 : ℕ)^4743*20000000000000^3719 ≤ 8673551273933^3719*2500000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298498851 2500000000 8673551273933 20000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1770050301/10000000000 : ℝ)^4743 ≤ (5494065574923/50000000000000 : ℝ)^3719 := by
    have hnat : (1770050301 : ℕ)^4743*50000000000000^3719 ≤ 5494065574923^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1770050301 10000000000 5494065574923 50000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5406579729/10000000000 : ℝ), (1298498851/2500000000 : ℝ), (-1770050301/10000000000 : ℝ)] ![(45644112463763/100000000000000 : ℝ), (8673551273933/20000000000000 : ℝ), (5494065574923/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5406579729/10000000000 : ℝ)|^4743 ≤ (45644112463763/100000000000000 : ℝ)^3719
        have hw : |(5406579729/10000000000 : ℝ)|=(5406579729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1298498851/2500000000 : ℝ)|^4743 ≤ (8673551273933/20000000000000 : ℝ)^3719
        have hw : |(1298498851/2500000000 : ℝ)|=(1298498851/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1770050301/10000000000 : ℝ)|^4743 ≤ (5494065574923/50000000000000 : ℝ)^3719
        have hw : |(-1770050301/10000000000 : ℝ)|=(1770050301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_box_15 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3873405261/10000000000 : ℝ)*x 0 + (4398659777/10000000000 : ℝ)*x 1 + (4398660953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3873405261/10000000000 : ℝ)^4743 ≤ (14915825180773/50000000000000 : ℝ)^3719 := by
    have hnat : (3873405261 : ℕ)^4743*50000000000000^3719 ≤ 14915825180773^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3873405261 10000000000 14915825180773 50000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4398659777/10000000000 : ℝ)^4743 ≤ (35084168832017/100000000000000 : ℝ)^3719 := by
    have hnat : (4398659777 : ℕ)^4743*100000000000000^3719 ≤ 35084168832017^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4398659777 10000000000 35084168832017 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4398660953/10000000000 : ℝ)^4743 ≤ (35084180794603/100000000000000 : ℝ)^3719 := by
    have hnat : (4398660953 : ℕ)^4743*100000000000000^3719 ≤ 35084180794603^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4398660953 10000000000 35084180794603 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3873405261/10000000000 : ℝ), (4398659777/10000000000 : ℝ), (4398660953/10000000000 : ℝ)] ![(14915825180773/50000000000000 : ℝ), (35084168832017/100000000000000 : ℝ), (35084180794603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3873405261/10000000000 : ℝ)|^4743 ≤ (14915825180773/50000000000000 : ℝ)^3719
        have hw : |(3873405261/10000000000 : ℝ)|=(3873405261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4398659777/10000000000 : ℝ)|^4743 ≤ (35084168832017/100000000000000 : ℝ)^3719
        have hw : |(4398659777/10000000000 : ℝ)|=(4398659777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4398660953/10000000000 : ℝ)|^4743 ≤ (35084180794603/100000000000000 : ℝ)^3719
        have hw : |(4398660953/10000000000 : ℝ)|=(4398660953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1606_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34444033/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4087/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10409/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(32453/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58151/100000 : ℝ) ∧ (80353/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (87783/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4087/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10409/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4087/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10409/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4087/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10409/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4087/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10409/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4087/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10409/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4087/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10409/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10409/100000 : ℝ) ^ (4739/1024 : ℝ) ≤ (2835554375908387/100000000000000000000 : ℝ) := by
    have hpowers : (10409/100000 : ℝ)^4739 ≤ (2835554375908387/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10409 : ℕ)^4739*100000000000000000000^1024 ≤ 2835554375908387^1024*100000^4739 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10409 100000 2835554375908387 100000000000000000000 4739 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10409/100000 : ℝ)) (X := (2835554375908387/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4739 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4087/25000 : ℝ) ^ (4739/1024 : ℝ) ≤ (5726768337432287/25000000000000000000 : ℝ) := by
    have hpowers : (4087/25000 : ℝ)^4739 ≤ (5726768337432287/25000000000000000000 : ℝ)^1024 := by
      have hnat : (4087 : ℕ)^4739*25000000000000000000^1024 ≤ 5726768337432287^1024*25000^4739 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4087 25000 5726768337432287 25000000000000000000 4739 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4087/25000 : ℝ)) (X := (5726768337432287/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4739 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002835554375908387/50000000000000000000 : ℝ) ≤ (5000061269110367/5000000000000000 : ℝ) ^ (4739/1024 : ℝ) := by
    have hpowers : (50002835554375908387/50000000000000000000 : ℝ)^1024 ≤ (5000061269110367/5000000000000000 : ℝ)^4739 := by
      have hnat : (50002835554375908387 : ℕ)^1024*5000000000000000^4739 ≤ 5000061269110367^4739*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002835554375908387 50000000000000000000 5000061269110367 5000000000000000 1024 4739 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000061269110367/5000000000000000 : ℝ)) (X := (50002835554375908387/50000000000000000000 : ℝ)) (by norm_num) 4739 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20005148525545127507/20000000000000000000 : ℝ) ≤ (5000278094444031/5000000000000000 : ℝ) ^ (4739/1024 : ℝ) := by
    have hpowers : (20005148525545127507/20000000000000000000 : ℝ)^1024 ≤ (5000278094444031/5000000000000000 : ℝ)^4739 := by
      have hnat : (20005148525545127507 : ℕ)^1024*5000000000000000^4739 ≤ 5000278094444031^4739*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20005148525545127507 20000000000000000000 5000278094444031 5000000000000000 1024 4739 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000278094444031/5000000000000000 : ℝ)) (X := (20005148525545127507/20000000000000000000 : ℝ)) (by norm_num) 4739 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12505726768337432287/12500000000000000000 : ℝ) ≤ (1000098983955539/1000000000000000 : ℝ) ^ (4739/1024 : ℝ) := by
    have hpowers : (12505726768337432287/12500000000000000000 : ℝ)^1024 ≤ (1000098983955539/1000000000000000 : ℝ)^4739 := by
      have hnat : (12505726768337432287 : ℕ)^1024*1000000000000000^4739 ≤ 1000098983955539^4739*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505726768337432287 12500000000000000000 1000098983955539 1000000000000000 1024 4739 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000098983955539/1000000000000000 : ℝ)) (X := (12505726768337432287/12500000000000000000 : ℝ)) (by norm_num) 4739 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2835554375908387/100000000000000000000 : ℝ) ≤ ((29690850007450252461/29695000000000000000 : ℝ)+2*(6775791677/9279687500000 : ℝ)*(10409/100000 : ℝ))^(4739/1024 : ℝ) := by
    rw [show (29690850007450252461/29695000000000000000 : ℝ)+2*(6775791677/9279687500000 : ℝ)*(10409/100000 : ℝ)=(5000061269110367/5000000000000000 : ℝ) by norm_num, show 1+2*(2835554375908387/100000000000000000000 : ℝ)=(50002835554375908387/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5726768337432287/25000000000000000000 : ℝ)+(2835554375908387/100000000000000000000 : ℝ) ≤ ((29690850007450252461/29695000000000000000 : ℝ)+(6775791677/9279687500000 : ℝ)*((4087/25000 : ℝ)+(10409/100000 : ℝ)))^(4739/1024 : ℝ) := by
    rw [show (29690850007450252461/29695000000000000000 : ℝ)+(6775791677/9279687500000 : ℝ)*((4087/25000 : ℝ)+(10409/100000 : ℝ))=(5000278094444031/5000000000000000 : ℝ) by norm_num, show 1+(5726768337432287/25000000000000000000 : ℝ)+(2835554375908387/100000000000000000000 : ℝ)=(20005148525545127507/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5726768337432287/25000000000000000000 : ℝ) ≤ ((29690850007450252461/29695000000000000000 : ℝ)+2*(6775791677/9279687500000 : ℝ)*(4087/25000 : ℝ))^(4739/1024 : ℝ) := by
    rw [show (29690850007450252461/29695000000000000000 : ℝ)+2*(6775791677/9279687500000 : ℝ)*(4087/25000 : ℝ)=(1000098983955539/1000000000000000 : ℝ) by norm_num, show 1+2*(5726768337432287/25000000000000000000 : ℝ)=(12505726768337432287/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (29690850007450252461/29695000000000000000 : ℝ)*(X 1 0+X 2 0)+(6775791677/9279687500000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4739/1024 : ℝ)) (lo := (10409/100000 : ℝ)) (hi := (4087/25000 : ℝ)) (c := (29690850007450252461/29695000000000000000 : ℝ)) (alpha := (6775791677/9279687500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (29690850007450252461/29695000000000000000 : ℝ)*(X 0 1+X 2 1)+(6775791677/9279687500000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4739/1024 : ℝ)) (lo := (10409/100000 : ℝ)) (hi := (4087/25000 : ℝ)) (c := (29690850007450252461/29695000000000000000 : ℝ)) (alpha := (6775791677/9279687500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (29690850007450252461/29695000000000000000 : ℝ)*(X 0 2+X 1 2)+(6775791677/9279687500000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4739/1024 : ℝ)) (lo := (10409/100000 : ℝ)) (hi := (4087/25000 : ℝ)) (c := (29690850007450252461/29695000000000000000 : ℝ)) (alpha := (6775791677/9279687500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1439483539/10000000000 : ℝ)*X 0 0+(1354780541/2500000000 : ℝ)*X 0 1+(1083824433/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2625553583/5000000000 : ℝ)*X 1 0+(-837674389/5000000000 : ℝ)*X 1 1+(5419122179/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((210044287/400000000 : ℝ)*X 2 0+(1083824433/2000000000 : ℝ)*X 2 1+(-837674393/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4496071799/10000000000 : ℝ)*X 0 0+(4088565811/10000000000 : ℝ)*X 0 1+(4088565811/10000000000 : ℝ)*X 0 2+(4496071799/10000000000 : ℝ)*X 1 0+(4088565811/10000000000 : ℝ)*X 1 1+(4088565811/10000000000 : ℝ)*X 1 2+(4496071799/10000000000 : ℝ)*X 2 0+(4088565811/10000000000 : ℝ)*X 2 1+(4088565811/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1000048579/5000000000 : ℝ)*X 0 0+(651733421/1250000000 : ℝ)*X 0 1+(5213867183/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5392849413/10000000000 : ℝ)*X 1 0+(-1761969171/10000000000 : ℝ)*X 1 1+(208554693/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((42131637/78125000 : ℝ)*X 2 0+(5213867119/10000000000 : ℝ)*X 2 1+(-1761969281/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3929845621/10000000000 : ℝ)*X 0 0+(17075521/39062500 : ℝ)*X 0 1+(2185666627/5000000000 : ℝ)*X 0 2+(3929845621/10000000000 : ℝ)*X 1 0+(17075521/39062500 : ℝ)*X 1 1+(2185666627/5000000000 : ℝ)*X 1 2+(3929845621/10000000000 : ℝ)*X 2 0+(17075521/39062500 : ℝ)*X 2 1+(2185666627/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-94047553/500000000 : ℝ)*X 0 0+(2533679809/5000000000 : ℝ)*X 0 1+(5449115121/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5230389347/10000000000 : ℝ)*X 1 0+(-166222571/1000000000 : ℝ)*X 1 1+(681139431/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1307597497/2500000000 : ℝ)*X 2 0+(1362278961/2500000000 : ℝ)*X 2 1+(-1662224281/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((572051777/1250000000 : ℝ)*X 0 0+(4047171693/10000000000 : ℝ)*X 0 1+(2023585149/5000000000 : ℝ)*X 0 2+(572051777/1250000000 : ℝ)*X 1 0+(4047171693/10000000000 : ℝ)*X 1 1+(2023585149/5000000000 : ℝ)*X 1 2+(572051777/1250000000 : ℝ)*X 2 0+(4047171693/10000000000 : ℝ)*X 2 1+(2023585149/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1557469433/10000000000 : ℝ)*X 0 0+(5559637799/10000000000 : ℝ)*X 0 1+(5193996021/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5406578693/10000000000 : ℝ)*X 1 0+(-885025757/5000000000 : ℝ)*X 1 1+(5193995549/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5406579729/10000000000 : ℝ)*X 2 0+(1298498851/2500000000 : ℝ)*X 2 1+(-1770050301/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3873405261/10000000000 : ℝ)*X 0 0+(4398659777/10000000000 : ℝ)*X 0 1+(4398660953/10000000000 : ℝ)*X 0 2+(3873405261/10000000000 : ℝ)*X 1 0+(4398659777/10000000000 : ℝ)*X 1 1+(4398660953/10000000000 : ℝ)*X 1 2+(3873405261/10000000000 : ℝ)*X 2 0+(4398659777/10000000000 : ℝ)*X 2 1+(4398660953/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-32453/50000 : ℝ) ≤ (-963661672514912773259681201020509/1484750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (174811/2500000000000 : ℝ)*(lower0) + (7767709/100000000000000 : ℝ)*(upper3) + (2598879/100000000000000 : ℝ)*(lower4) + (60301/1562500000000 : ℝ)*(lower5) + (1673877360127641/100000000000000 : ℝ)*(major0) + (1673877360127641/100000000000000 : ℝ)*(major1) + (1673877360127641/100000000000000 : ℝ)*(major2) + (1131895267/50000000000000 : ℝ)*(sp2) + (599361964934569/25000000000000 : ℝ)*(sp4) + (299681122086289/12500000000000 : ℝ)*(sp5) + (1198723356449889/50000000000000 : ℝ)*(sp6) + (971931663803183/100000000000000 : ℝ)*(sp7) + (279238009/25000000000000 : ℝ)*(sp8) + (873593319/10000000000000 : ℝ)*(sp15) + (971940399736373/100000000000000 : ℝ)*(f.failure) + (299681122086289/12500000000000 : ℝ)*(f.sum) + (56111870864927/29695000000000000000000000000 : ℝ)*base66 + (30975068774043774501/2969500000000000000000000000000000 : ℝ)*base67 + (17690071680984774501/2969500000000000000000000000000000 : ℝ)*base69 + (4402151082511274501/2969500000000000000000000000000000 : ℝ)*base71 + (139383529537239/14847500000000000000000000000 : ℝ)*base73 + (13603675810332774501/2969500000000000000000000000000000 : ℝ)*base75 + (7269804353372274501/2969500000000000000000000000000000 : ℝ)*base77 + (17176022385261774501/2969500000000000000000000000000000 : ℝ)*base79 + (4175509596351/14847500000000000000000000000 : ℝ)*base82 + (2912309/2000000000000000000000 : ℝ)*base89 + (2912309/2000000000000000000000 : ℝ)*base91 + (2912309/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (58151/100000 : ℝ) ≤ (431715242457361509621618960601977/742375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6722313/100000000000000 : ℝ)*(upper2) + (1110693/50000000000000 : ℝ)*(upper3) + (3239659/50000000000000 : ℝ)*(upper4) + (1779351/100000000000000 : ℝ)*(upper5) + (879053615624973/50000000000000 : ℝ)*(major0) + (879053615624973/50000000000000 : ℝ)*(major1) + (879053615624973/50000000000000 : ℝ)*(major2) + (1237990685241757/50000000000000 : ℝ)*(sp0) + (2475981307705299/100000000000000 : ℝ)*(sp1) + (1237990389503191/50000000000000 : ℝ)*(sp2) + (510424325528299/50000000000000 : ℝ)*(sp3) + (16940381/20000000000000 : ℝ)*(sp5) + (613400823/100000000000000 : ℝ)*(sp10) + (2192369/10000000000000 : ℝ)*(sp12) + (510424325528299/50000000000000 : ℝ)*(f.failure) + (618995348101801/25000000000000 : ℝ)*(f.sum) + (39227460680009/14847500000000000000000000000 : ℝ)*base65 + (6224747086590491447/1484750000000000000000000000000000 : ℝ)*base68 + (8336897046506991447/1484750000000000000000000000000000 : ℝ)*base70 + (4531910290181241447/1484750000000000000000000000000000 : ℝ)*base72 + (209491246257407/29695000000000000000000000000 : ℝ)*base74 + (5577274396480491447/1484750000000000000000000000000000 : ℝ)*base76 + (19211405742412491447/1484750000000000000000000000000000 : ℝ)*base78 + (10638959371541491447/1484750000000000000000000000000000 : ℝ)*base80 + (38378564890503/29695000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (13189867/1000000000000000000000 : ℝ)*base89 + (13189867/1000000000000000000000 : ℝ)*base91 + (13189867/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (80353/100000 : ℝ) ≤ (596541568358383732852123267841811/742375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (100103497/100000000000000 : ℝ)*(lower3) + (98528243/25000000000000 : ℝ)*(upper4) + (20102963/100000000000000 : ℝ)*(lower5) + (932215609327961/50000000000000 : ℝ)*(major0) + (932215609327961/50000000000000 : ℝ)*(major1) + (932215609327961/50000000000000 : ℝ)*(major2) + (5677905777/100000000000000 : ℝ)*(sp0) + (33806014829/50000000000000 : ℝ)*(sp1) + (44200132129/25000000000000 : ℝ)*(sp2) + (72977974949/100000000000000 : ℝ)*(sp3) + (163717849156863/6250000000000 : ℝ)*(sp8) + (1309711826192963/50000000000000 : ℝ)*(sp9) + (2619314463887069/100000000000000 : ℝ)*(sp10) + (541256459679693/50000000000000 : ℝ)*(sp11) + (216517179466867/20000000000000 : ℝ)*(f.failure) + (81859102012987/3125000000000 : ℝ)*(f.sum) + (830276616677/927968750000000000000000000 : ℝ)*base66 + (6906121105019012021/1484750000000000000000000000000000 : ℝ)*base67 + (3234578253416762021/1484750000000000000000000000000000 : ℝ)*base69 + (12338004344606012021/1484750000000000000000000000000000 : ℝ)*base71 + (72632341778919/29695000000000000000000000000 : ℝ)*base74 + (13645473531686012021/1484750000000000000000000000000000 : ℝ)*base75 + (6386372207416512021/1484750000000000000000000000000000 : ℝ)*base77 + (6282075328980012021/1484750000000000000000000000000000 : ℝ)*base79 + (38064340987763/14847500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (1354611/400000000000000000000 : ℝ)*base89 + (1354611/400000000000000000000 : ℝ)*base91 + (1354611/400000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-87783/100000 : ℝ) ≤ (-325831083111406866069488031463707/371187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1184633/10000000000000 : ℝ)*(lower0) + (7514931/2000000000000 : ℝ)*(lower1) + (56218703/12500000000000 : ℝ)*(lower2) + (476568898831257/25000000000000 : ℝ)*(major0) + (476568898831257/25000000000000 : ℝ)*(major1) + (476568898831257/25000000000000 : ℝ)*(major2) + (8997157103/100000000000000 : ℝ)*(sp0) + (355974576393/100000000000000 : ℝ)*(sp5) + (23475011053/10000000000000 : ℝ)*(sp6) + (13890271541/25000000000000 : ℝ)*(sp7) + (68372987828939/2500000000000 : ℝ)*(sp12) + (2734572535738269/100000000000000 : ℝ)*(sp13) + (683673440051033/25000000000000 : ℝ)*(sp14) + (1106827361320181/100000000000000 : ℝ)*(sp15) + (138360365300793/12500000000000 : ℝ)*(f.failure) + (1367464255157331/50000000000000 : ℝ)*(f.sum) + (726164165093/927968750000000000000000000 : ℝ)*base66 + (5796748307620601523/742375000000000000000000000000000 : ℝ)*base68 + (5205102359304226523/742375000000000000000000000000000 : ℝ)*base70 + (88002727388351523/742375000000000000000000000000000 : ℝ)*base72 + (28423169028257/3711875000000000000000000000 : ℝ)*base74 + (2349532164340351523/742375000000000000000000000000000 : ℝ)*base76 + (3442531498950601523/742375000000000000000000000000000 : ℝ)*base78 + (2394095557742351523/742375000000000000000000000000000 : ℝ)*base80 + (48589311991281/29695000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (981831/250000000000000000000 : ℝ)*base90 + (981831/250000000000000000000 : ℝ)*base92 + (981831/250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1606_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34444033/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4087/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10409/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(32453/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58151/100000 : ℝ) else (80353/100000 : ℝ) ≤ X j i ∧ X j i ≤ (87783/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1606_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1606_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34444033/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4087/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10409/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(32453/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58151/100000 : ℝ) else (80353/100000 : ℝ) ≤ X j i ∧ X j i ≤ (87783/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1606_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34444033/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4087/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10409/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(32453/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58151/100000 : ℝ) else (80353/100000 : ℝ) ≤ X j i ∧ X j i ≤ (87783/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1606_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
