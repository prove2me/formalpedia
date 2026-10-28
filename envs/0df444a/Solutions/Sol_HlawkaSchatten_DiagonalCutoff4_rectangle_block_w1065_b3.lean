-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1065_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:06:47.921973+00:00
-- url     : https://prove2.me/submissions/13fd0902-1178-4366-ab2a-9e3c5bbcd181

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
theorem support_rectangle_w1065_s9_0 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-275533001/1250000000 : ℝ)*x 0 + (215773857/400000000 : ℝ)*x 1 + (5264460331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (275533001/1250000000 : ℝ)^4129 ≤ (836677517007/6250000000000 : ℝ)^3105 := by
    have hnat : (275533001 : ℕ)^4129*6250000000000^3105 ≤ 836677517007^3105*1250000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275533001 1250000000 836677517007 6250000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215773857/400000000 : ℝ)^4129 ≤ (44008317409731/100000000000000 : ℝ)^3105 := by
    have hnat : (215773857 : ℕ)^4129*100000000000000^3105 ≤ 44008317409731^3105*400000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215773857 400000000 44008317409731 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264460331/10000000000 : ℝ)^4129 ≤ (21302421154833/50000000000000 : ℝ)^3105 := by
    have hnat : (5264460331 : ℕ)^4129*50000000000000^3105 ≤ 21302421154833^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264460331 10000000000 21302421154833 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-275533001/1250000000 : ℝ), (215773857/400000000 : ℝ), (5264460331/10000000000 : ℝ)] ![(836677517007/6250000000000 : ℝ), (44008317409731/100000000000000 : ℝ), (21302421154833/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-275533001/1250000000 : ℝ)|^4129 ≤ (836677517007/6250000000000 : ℝ)^3105
        have hw : |(-275533001/1250000000 : ℝ)|=(275533001/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(215773857/400000000 : ℝ)|^4129 ≤ (44008317409731/100000000000000 : ℝ)^3105
        have hw : |(215773857/400000000 : ℝ)|=(215773857/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264460331/10000000000 : ℝ)|^4129 ≤ (21302421154833/50000000000000 : ℝ)^3105
        have hw : |(5264460331/10000000000 : ℝ)|=(5264460331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s9_1 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1068994659/2000000000 : ℝ)*x 0 + (-1135082437/5000000000 : ℝ)*x 1 + (5264460559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068994659/2000000000 : ℝ)^4129 ≤ (21736745669461/50000000000000 : ℝ)^3105 := by
    have hnat : (1068994659 : ℕ)^4129*50000000000000^3105 ≤ 21736745669461^3105*2000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068994659 2000000000 21736745669461 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1135082437/5000000000 : ℝ)^4129 ≤ (13921663885737/100000000000000 : ℝ)^3105 := by
    have hnat : (1135082437 : ℕ)^4129*100000000000000^3105 ≤ 13921663885737^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1135082437 5000000000 13921663885737 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264460559/10000000000 : ℝ)^4129 ≤ (2662802797711/6250000000000 : ℝ)^3105 := by
    have hnat : (5264460559 : ℕ)^4129*6250000000000^3105 ≤ 2662802797711^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264460559 10000000000 2662802797711 6250000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068994659/2000000000 : ℝ), (-1135082437/5000000000 : ℝ), (5264460559/10000000000 : ℝ)] ![(21736745669461/50000000000000 : ℝ), (13921663885737/100000000000000 : ℝ), (2662802797711/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068994659/2000000000 : ℝ)|^4129 ≤ (21736745669461/50000000000000 : ℝ)^3105
        have hw : |(1068994659/2000000000 : ℝ)|=(1068994659/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1135082437/5000000000 : ℝ)|^4129 ≤ (13921663885737/100000000000000 : ℝ)^3105
        have hw : |(-1135082437/5000000000 : ℝ)|=(1135082437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264460559/10000000000 : ℝ)|^4129 ≤ (2662802797711/6250000000000 : ℝ)^3105
        have hw : |(5264460559/10000000000 : ℝ)|=(5264460559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s9_2 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (41757613/78125000 : ℝ)*x 0 + (2632229971/5000000000 : ℝ)*x 1 + (-2270164137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41757613/78125000 : ℝ)^4129 ≤ (21736751991349/50000000000000 : ℝ)^3105 := by
    have hnat : (41757613 : ℕ)^4129*50000000000000^3105 ≤ 21736751991349^3105*78125000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41757613 78125000 21736751991349 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632229971/5000000000 : ℝ)^4129 ≤ (42604838123293/100000000000000 : ℝ)^3105 := by
    have hnat : (2632229971 : ℕ)^4129*100000000000000^3105 ≤ 42604838123293^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632229971 5000000000 42604838123293 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2270164137/10000000000 : ℝ)^4129 ≤ (6960828937799/50000000000000 : ℝ)^3105 := by
    have hnat : (2270164137 : ℕ)^4129*50000000000000^3105 ≤ 6960828937799^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2270164137 10000000000 6960828937799 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41757613/78125000 : ℝ), (2632229971/5000000000 : ℝ), (-2270164137/10000000000 : ℝ)] ![(21736751991349/50000000000000 : ℝ), (42604838123293/100000000000000 : ℝ), (6960828937799/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41757613/78125000 : ℝ)|^4129 ≤ (21736751991349/50000000000000 : ℝ)^3105
        have hw : |(41757613/78125000 : ℝ)|=(41757613/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632229971/5000000000 : ℝ)|^4129 ≤ (42604838123293/100000000000000 : ℝ)^3105
        have hw : |(2632229971/5000000000 : ℝ)|=(2632229971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2270164137/10000000000 : ℝ)|^4129 ≤ (6960828937799/50000000000000 : ℝ)^3105
        have hw : |(-2270164137/10000000000 : ℝ)|=(2270164137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s9_3 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4375637109/10000000000 : ℝ)*x 0 + (1062564973/2500000000 : ℝ)*x 1 + (4504765539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4375637109/10000000000 : ℝ)^4129 ≤ (16658276772269/50000000000000 : ℝ)^3105 := by
    have hnat : (4375637109 : ℕ)^4129*50000000000000^3105 ≤ 16658276772269^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4375637109 10000000000 16658276772269 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1062564973/2500000000 : ℝ)^4129 ≤ (4006640695793/12500000000000 : ℝ)^3105 := by
    have hnat : (1062564973 : ℕ)^4129*12500000000000^3105 ≤ 4006640695793^3105*2500000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062564973 2500000000 4006640695793 12500000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4504765539/10000000000 : ℝ)^4129 ≤ (34630320872873/100000000000000 : ℝ)^3105 := by
    have hnat : (4504765539 : ℕ)^4129*100000000000000^3105 ≤ 34630320872873^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4504765539 10000000000 34630320872873 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4375637109/10000000000 : ℝ), (1062564973/2500000000 : ℝ), (4504765539/10000000000 : ℝ)] ![(16658276772269/50000000000000 : ℝ), (4006640695793/12500000000000 : ℝ), (34630320872873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4375637109/10000000000 : ℝ)|^4129 ≤ (16658276772269/50000000000000 : ℝ)^3105
        have hw : |(4375637109/10000000000 : ℝ)|=(4375637109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1062564973/2500000000 : ℝ)|^4129 ≤ (4006640695793/12500000000000 : ℝ)^3105
        have hw : |(1062564973/2500000000 : ℝ)|=(1062564973/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4504765539/10000000000 : ℝ)|^4129 ≤ (34630320872873/100000000000000 : ℝ)^3105
        have hw : |(4504765539/10000000000 : ℝ)|=(4504765539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s9_4 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-551067307/2500000000 : ℝ)*x 0 + (5264785613/10000000000 : ℝ)*x 1 + (2697009927/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (551067307/2500000000 : ℝ)^4129 ≤ (3346720607247/25000000000000 : ℝ)^3105 := by
    have hnat : (551067307 : ℕ)^4129*25000000000000^3105 ≤ 3346720607247^3105*2500000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551067307 2500000000 3346720607247 25000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264785613/10000000000 : ℝ)^4129 ≤ (426083429931/1000000000000 : ℝ)^3105 := by
    have hnat : (5264785613 : ℕ)^4129*1000000000000^3105 ≤ 426083429931^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264785613 10000000000 426083429931 1000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697009927/5000000000 : ℝ)^4129 ≤ (22002387280989/50000000000000 : ℝ)^3105 := by
    have hnat : (2697009927 : ℕ)^4129*50000000000000^3105 ≤ 22002387280989^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697009927 5000000000 22002387280989 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-551067307/2500000000 : ℝ), (5264785613/10000000000 : ℝ), (2697009927/5000000000 : ℝ)] ![(3346720607247/25000000000000 : ℝ), (426083429931/1000000000000 : ℝ), (22002387280989/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-551067307/2500000000 : ℝ)|^4129 ≤ (3346720607247/25000000000000 : ℝ)^3105
        have hw : |(-551067307/2500000000 : ℝ)|=(551067307/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264785613/10000000000 : ℝ)|^4129 ≤ (426083429931/1000000000000 : ℝ)^3105
        have hw : |(5264785613/10000000000 : ℝ)|=(5264785613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697009927/5000000000 : ℝ)|^4129 ≤ (22002387280989/50000000000000 : ℝ)^3105
        have hw : |(2697009927/5000000000 : ℝ)|=(2697009927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s9_5 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (664032627/1250000000 : ℝ)*x 0 + (-2140604663/10000000000 : ℝ)*x 1 + (5394019757/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664032627/1250000000 : ℝ)^4129 ≤ (21560018242197/50000000000000 : ℝ)^3105 := by
    have hnat : (664032627 : ℕ)^4129*50000000000000^3105 ≤ 21560018242197^3105*1250000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664032627 1250000000 21560018242197 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2140604663/10000000000 : ℝ)^4129 ≤ (12875189999083/100000000000000 : ℝ)^3105 := by
    have hnat : (2140604663 : ℕ)^4129*100000000000000^3105 ≤ 12875189999083^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140604663 10000000000 12875189999083 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394019757/10000000000 : ℝ)^4129 ≤ (44004773509671/100000000000000 : ℝ)^3105 := by
    have hnat : (5394019757 : ℕ)^4129*100000000000000^3105 ≤ 44004773509671^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394019757 10000000000 44004773509671 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664032627/1250000000 : ℝ), (-2140604663/10000000000 : ℝ), (5394019757/10000000000 : ℝ)] ![(21560018242197/50000000000000 : ℝ), (12875189999083/100000000000000 : ℝ), (44004773509671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664032627/1250000000 : ℝ)|^4129 ≤ (21560018242197/50000000000000 : ℝ)^3105
        have hw : |(664032627/1250000000 : ℝ)|=(664032627/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2140604663/10000000000 : ℝ)|^4129 ≤ (12875189999083/100000000000000 : ℝ)^3105
        have hw : |(-2140604663/10000000000 : ℝ)|=(2140604663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394019757/10000000000 : ℝ)|^4129 ≤ (44004773509671/100000000000000 : ℝ)^3105
        have hw : |(5394019757/10000000000 : ℝ)|=(5394019757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s9_6 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312260963/10000000000 : ℝ)*x 0 + (5394019801/10000000000 : ℝ)*x 1 + (-85624187/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312260963/10000000000 : ℝ)^4129 ≤ (43120035912311/100000000000000 : ℝ)^3105 := by
    have hnat : (5312260963 : ℕ)^4129*100000000000000^3105 ≤ 43120035912311^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312260963 10000000000 43120035912311 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394019801/10000000000 : ℝ)^4129 ≤ (22002386993503/50000000000000 : ℝ)^3105 := by
    have hnat : (5394019801 : ℕ)^4129*50000000000000^3105 ≤ 22002386993503^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394019801 10000000000 22002386993503 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (85624187/400000000 : ℝ)^4129 ≤ (1609398761883/12500000000000 : ℝ)^3105 := by
    have hnat : (85624187 : ℕ)^4129*12500000000000^3105 ≤ 1609398761883^3105*400000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85624187 400000000 1609398761883 12500000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312260963/10000000000 : ℝ), (5394019801/10000000000 : ℝ), (-85624187/400000000 : ℝ)] ![(43120035912311/100000000000000 : ℝ), (22002386993503/50000000000000 : ℝ), (1609398761883/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312260963/10000000000 : ℝ)|^4129 ≤ (43120035912311/100000000000000 : ℝ)^3105
        have hw : |(5312260963/10000000000 : ℝ)|=(5312260963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394019801/10000000000 : ℝ)|^4129 ≤ (22002386993503/50000000000000 : ℝ)^3105
        have hw : |(5394019801/10000000000 : ℝ)|=(5394019801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-85624187/400000000 : ℝ)|^4129 ≤ (1609398761883/12500000000000 : ℝ)^3105
        have hw : |(-85624187/400000000 : ℝ)|=(85624187/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1065_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29594717/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7001/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9/80 : ℝ)*pair X i i ≤ pair X i h) :
    (11251/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7001/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7001/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9/80 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7001/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9/80 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7001/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9/80 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7001/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9/80 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7001/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9/80 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7001/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9/80 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
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
  have hpowlo : (9/80 : ℝ) ^ (8257/2048 : ℝ) ≤ (7472489371962847/50000000000000000000 : ℝ) := by
    have hpowers : (9/80 : ℝ)^8257 ≤ (7472489371962847/50000000000000000000 : ℝ)^2048 := by
      have hnat : (9 : ℕ)^8257*50000000000000000000^2048 ≤ 7472489371962847^2048*80^8257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9 80 7472489371962847 50000000000000000000 8257 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9/80 : ℝ)) (X := (7472489371962847/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7001/50000 : ℝ) ^ (8257/2048 : ℝ) ≤ (4514106974374721/12500000000000000000 : ℝ) := by
    have hpowers : (7001/50000 : ℝ)^8257 ≤ (4514106974374721/12500000000000000000 : ℝ)^2048 := by
      have hnat : (7001 : ℕ)^8257*12500000000000000000^2048 ≤ 4514106974374721^2048*50000^8257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7001 50000 4514106974374721 12500000000000000000 8257 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7001/50000 : ℝ)) (X := (4514106974374721/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007472489371962847/25000000000000000000 : ℝ) ≤ (2500185320802791/2500000000000000 : ℝ) ^ (8257/2048 : ℝ) := by
    have hpowers : (25007472489371962847/25000000000000000000 : ℝ)^2048 ≤ (2500185320802791/2500000000000000 : ℝ)^8257 := by
      have hnat : (25007472489371962847 : ℕ)^2048*2500000000000000^8257 ≤ 2500185320802791^8257*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007472489371962847 25000000000000000000 2500185320802791 2500000000000000 2048 8257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500185320802791/2500000000000000 : ℝ)) (X := (25007472489371962847/25000000000000000000 : ℝ)) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025528917269461731/50000000000000000000 : ℝ) ≤ (10001266154506143/10000000000000000 : ℝ) ^ (8257/2048 : ℝ) := by
    have hpowers : (50025528917269461731/50000000000000000000 : ℝ)^2048 ≤ (10001266154506143/10000000000000000 : ℝ)^8257 := by
      have hnat : (50025528917269461731 : ℕ)^2048*10000000000000000^8257 ≤ 10001266154506143^8257*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025528917269461731 50000000000000000000 10001266154506143 10000000000000000 2048 8257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001266154506143/10000000000000000 : ℝ)) (X := (50025528917269461731/50000000000000000000 : ℝ)) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254514106974374721/6250000000000000000 : ℝ) ≤ (5000895512900561/5000000000000000 : ℝ) ^ (8257/2048 : ℝ) := by
    have hpowers : (6254514106974374721/6250000000000000000 : ℝ)^2048 ≤ (5000895512900561/5000000000000000 : ℝ)^8257 := by
      have hnat : (6254514106974374721 : ℕ)^2048*5000000000000000^8257 ≤ 5000895512900561^8257*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254514106974374721 6250000000000000000 5000895512900561 5000000000000000 2048 8257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000895512900561/5000000000000000 : ℝ)) (X := (6254514106974374721/6250000000000000000 : ℝ)) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7472489371962847/50000000000000000000 : ℝ) ≤ ((6877557601815023957/6880000000000000000 : ℝ)+2*(524871294979/275200000000000 : ℝ)*(9/80 : ℝ))^(8257/2048 : ℝ) := by
    rw [show (6877557601815023957/6880000000000000000 : ℝ)+2*(524871294979/275200000000000 : ℝ)*(9/80 : ℝ)=(2500185320802791/2500000000000000 : ℝ) by norm_num, show 1+2*(7472489371962847/50000000000000000000 : ℝ)=(25007472489371962847/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4514106974374721/12500000000000000000 : ℝ)+(7472489371962847/50000000000000000000 : ℝ) ≤ ((6877557601815023957/6880000000000000000 : ℝ)+(524871294979/275200000000000 : ℝ)*((7001/50000 : ℝ)+(9/80 : ℝ)))^(8257/2048 : ℝ) := by
    rw [show (6877557601815023957/6880000000000000000 : ℝ)+(524871294979/275200000000000 : ℝ)*((7001/50000 : ℝ)+(9/80 : ℝ))=(10001266154506143/10000000000000000 : ℝ) by norm_num, show 1+(4514106974374721/12500000000000000000 : ℝ)+(7472489371962847/50000000000000000000 : ℝ)=(50025528917269461731/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4514106974374721/12500000000000000000 : ℝ) ≤ ((6877557601815023957/6880000000000000000 : ℝ)+2*(524871294979/275200000000000 : ℝ)*(7001/50000 : ℝ))^(8257/2048 : ℝ) := by
    rw [show (6877557601815023957/6880000000000000000 : ℝ)+2*(524871294979/275200000000000 : ℝ)*(7001/50000 : ℝ)=(5000895512900561/5000000000000000 : ℝ) by norm_num, show 1+2*(4514106974374721/12500000000000000000 : ℝ)=(6254514106974374721/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6877557601815023957/6880000000000000000 : ℝ)*(X 1 0+X 2 0)+(524871294979/275200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8257/2048 : ℝ)) (lo := (9/80 : ℝ)) (hi := (7001/50000 : ℝ)) (c := (6877557601815023957/6880000000000000000 : ℝ)) (alpha := (524871294979/275200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6877557601815023957/6880000000000000000 : ℝ)*(X 0 1+X 2 1)+(524871294979/275200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8257/2048 : ℝ)) (lo := (9/80 : ℝ)) (hi := (7001/50000 : ℝ)) (c := (6877557601815023957/6880000000000000000 : ℝ)) (alpha := (524871294979/275200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6877557601815023957/6880000000000000000 : ℝ)*(X 0 2+X 1 2)+(524871294979/275200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8257/2048 : ℝ)) (lo := (9/80 : ℝ)) (hi := (7001/50000 : ℝ)) (c := (6877557601815023957/6880000000000000000 : ℝ)) (alpha := (524871294979/275200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-275533001/1250000000 : ℝ)*X 0 0+(215773857/400000000 : ℝ)*X 0 1+(5264460331/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068994659/2000000000 : ℝ)*X 1 0+(-1135082437/5000000000 : ℝ)*X 1 1+(5264460559/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((41757613/78125000 : ℝ)*X 2 0+(2632229971/5000000000 : ℝ)*X 2 1+(-2270164137/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4375637109/10000000000 : ℝ)*X 0 0+(1062564973/2500000000 : ℝ)*X 0 1+(4504765539/10000000000 : ℝ)*X 0 2+(4375637109/10000000000 : ℝ)*X 1 0+(1062564973/2500000000 : ℝ)*X 1 1+(4504765539/10000000000 : ℝ)*X 1 2+(4375637109/10000000000 : ℝ)*X 2 0+(1062564973/2500000000 : ℝ)*X 2 1+(4504765539/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-551067307/2500000000 : ℝ)*X 0 0+(5264785613/10000000000 : ℝ)*X 0 1+(2697009927/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((664032627/1250000000 : ℝ)*X 1 0+(-2140604663/10000000000 : ℝ)*X 1 1+(5394019757/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s9_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312260963/10000000000 : ℝ)*X 2 0+(5394019801/10000000000 : ℝ)*X 2 1+(-85624187/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s9_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (560792729288581434920537751/172000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (54060201/50000000000000 : ℝ)*(base8) + (92991041/25000000000000 : ℝ)*(base21) + (526081979/100000000000000 : ℝ)*(lower2) + (562099167/100000000000000 : ℝ)*(upper4) + (5814122795735219/100000000000000 : ℝ)*(major0) + (5814122795735219/100000000000000 : ℝ)*(major1) + (5814122795735219/100000000000000 : ℝ)*(major2) + (1924759989040443/25000000000000 : ℝ)*(sp0) + (1924764501611883/25000000000000 : ℝ)*(sp1) + (7699062223143491/100000000000000 : ℝ)*(sp2) + (3929162624353001/100000000000000 : ℝ)*(sp3) + (21397077237/50000000000000 : ℝ)*(sp4) + (6212997279/25000000000000 : ℝ)*(sp5) + (20263328993/100000000000000 : ℝ)*(sp6) + (3929162624353001/100000000000000 : ℝ)*(f.failure) + (962385357304581/12500000000000 : ℝ)*(f.sum) + (542355954718041/13760000000000000000000000000 : ℝ)*base65 + (2629764241103333417/688000000000000000000000000000000 : ℝ)*base68 + (6070379447552666583/688000000000000000000000000000000 : ℝ)*base69 + (11176269597408666583/688000000000000000000000000000000 : ℝ)*base71 + (39218854774759/13760000000000000000000000000 : ℝ)*base74 + (8300695279616666583/688000000000000000000000000000000 : ℝ)*base75 + (113137144247952666583/688000000000000000000000000000000 : ℝ)*base77 + (4675226944832666583/688000000000000000000000000000000 : ℝ)*base79 + (32739421873319/13760000000000000000000000000 : ℝ)*base82 + (7304283/2000000000000000000000 : ℝ)*base90 + (7304283/2000000000000000000000 : ℝ)*base92 + (7304283/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1065_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29594717/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7001/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9/80 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11251/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7001/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1065_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1065_box_0 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-207476639/1000000000 : ℝ)*x 0 + (672172631/1250000000 : ℝ)*x 1 + (5377380889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (207476639/1000000000 : ℝ)^4129 ≤ (617564084971/5000000000000 : ℝ)^3105 := by
    have hnat : (207476639 : ℕ)^4129*5000000000000^3105 ≤ 617564084971^3105*1000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207476639 1000000000 617564084971 5000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (672172631/1250000000 : ℝ)^4129 ≤ (21912180000839/50000000000000 : ℝ)^3105 := by
    have hnat : (672172631 : ℕ)^4129*50000000000000^3105 ≤ 21912180000839^3105*1250000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672172631 1250000000 21912180000839 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5377380889/10000000000 : ℝ)^4129 ≤ (1095608956963/2500000000000 : ℝ)^3105 := by
    have hnat : (5377380889 : ℕ)^4129*2500000000000^3105 ≤ 1095608956963^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377380889 10000000000 1095608956963 2500000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-207476639/1000000000 : ℝ), (672172631/1250000000 : ℝ), (5377380889/10000000000 : ℝ)] ![(617564084971/5000000000000 : ℝ), (21912180000839/50000000000000 : ℝ), (1095608956963/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-207476639/1000000000 : ℝ)|^4129 ≤ (617564084971/5000000000000 : ℝ)^3105
        have hw : |(-207476639/1000000000 : ℝ)|=(207476639/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(672172631/1250000000 : ℝ)|^4129 ≤ (21912180000839/50000000000000 : ℝ)^3105
        have hw : |(672172631/1250000000 : ℝ)|=(672172631/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5377380889/10000000000 : ℝ)|^4129 ≤ (1095608956963/2500000000000 : ℝ)^3105
        have hw : |(5377380889/10000000000 : ℝ)|=(5377380889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_box_1 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647596613/5000000000 : ℝ)*x 0 + (-1093012093/5000000000 : ℝ)*x 1 + (5377380997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647596613/5000000000 : ℝ)^4129 ≤ (21467952093821/50000000000000 : ℝ)^3105 := by
    have hnat : (2647596613 : ℕ)^4129*50000000000000^3105 ≤ 21467952093821^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647596613 5000000000 21467952093821 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1093012093/5000000000 : ℝ)^4129 ≤ (13239736348263/100000000000000 : ℝ)^3105 := by
    have hnat : (1093012093 : ℕ)^4129*100000000000000^3105 ≤ 13239736348263^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093012093 5000000000 13239736348263 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5377380997/10000000000 : ℝ)^4129 ≤ (43824359448967/100000000000000 : ℝ)^3105 := by
    have hnat : (5377380997 : ℕ)^4129*100000000000000^3105 ≤ 43824359448967^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377380997 10000000000 43824359448967 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647596613/5000000000 : ℝ), (-1093012093/5000000000 : ℝ), (5377380997/10000000000 : ℝ)] ![(21467952093821/50000000000000 : ℝ), (13239736348263/100000000000000 : ℝ), (43824359448967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647596613/5000000000 : ℝ)|^4129 ≤ (21467952093821/50000000000000 : ℝ)^3105
        have hw : |(2647596613/5000000000 : ℝ)|=(2647596613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1093012093/5000000000 : ℝ)|^4129 ≤ (13239736348263/100000000000000 : ℝ)^3105
        have hw : |(-1093012093/5000000000 : ℝ)|=(1093012093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5377380997/10000000000 : ℝ)|^4129 ≤ (43824359448967/100000000000000 : ℝ)^3105
        have hw : |(5377380997/10000000000 : ℝ)|=(5377380997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_box_2 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295193263/10000000000 : ℝ)*x 0 + (2688690457/5000000000 : ℝ)*x 1 + (-273253031/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295193263/10000000000 : ℝ)^4129 ≤ (42935904586597/100000000000000 : ℝ)^3105 := by
    have hnat : (5295193263 : ℕ)^4129*100000000000000^3105 ≤ 42935904586597^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295193263 10000000000 42935904586597 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2688690457/5000000000 : ℝ)^4129 ≤ (43824358549457/100000000000000 : ℝ)^3105 := by
    have hnat : (2688690457 : ℕ)^4129*100000000000000^3105 ≤ 43824358549457^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688690457 5000000000 43824358549457 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (273253031/1250000000 : ℝ)^4129 ≤ (6619868423803/50000000000000 : ℝ)^3105 := by
    have hnat : (273253031 : ℕ)^4129*50000000000000^3105 ≤ 6619868423803^3105*1250000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273253031 1250000000 6619868423803 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295193263/10000000000 : ℝ), (2688690457/5000000000 : ℝ), (-273253031/1250000000 : ℝ)] ![(42935904586597/100000000000000 : ℝ), (43824358549457/100000000000000 : ℝ), (6619868423803/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295193263/10000000000 : ℝ)|^4129 ≤ (42935904586597/100000000000000 : ℝ)^3105
        have hw : |(5295193263/10000000000 : ℝ)|=(5295193263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2688690457/5000000000 : ℝ)|^4129 ≤ (43824358549457/100000000000000 : ℝ)^3105
        have hw : |(2688690457/5000000000 : ℝ)|=(2688690457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-273253031/1250000000 : ℝ)|^4129 ≤ (6619868423803/50000000000000 : ℝ)^3105
        have hw : |(-273253031/1250000000 : ℝ)|=(273253031/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_box_3 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2242016891/5000000000 : ℝ)*x 0 + (4323602237/10000000000 : ℝ)*x 1 + (432360203/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2242016891/5000000000 : ℝ)^4129 ≤ (6883709274087/20000000000000 : ℝ)^3105 := by
    have hnat : (2242016891 : ℕ)^4129*20000000000000^3105 ≤ 6883709274087^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242016891 5000000000 6883709274087 20000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4323602237/10000000000 : ℝ)^4129 ≤ (16395363923351/50000000000000 : ℝ)^3105 := by
    have hnat : (4323602237 : ℕ)^4129*50000000000000^3105 ≤ 16395363923351^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4323602237 10000000000 16395363923351 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (432360203/1000000000 : ℝ)^4129 ≤ (16395362879523/50000000000000 : ℝ)^3105 := by
    have hnat : (432360203 : ℕ)^4129*50000000000000^3105 ≤ 16395362879523^3105*1000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432360203 1000000000 16395362879523 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2242016891/5000000000 : ℝ), (4323602237/10000000000 : ℝ), (432360203/1000000000 : ℝ)] ![(6883709274087/20000000000000 : ℝ), (16395363923351/50000000000000 : ℝ), (16395362879523/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2242016891/5000000000 : ℝ)|^4129 ≤ (6883709274087/20000000000000 : ℝ)^3105
        have hw : |(2242016891/5000000000 : ℝ)|=(2242016891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4323602237/10000000000 : ℝ)|^4129 ≤ (16395363923351/50000000000000 : ℝ)^3105
        have hw : |(4323602237/10000000000 : ℝ)|=(4323602237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(432360203/1000000000 : ℝ)|^4129 ≤ (16395362879523/50000000000000 : ℝ)^3105
        have hw : |(432360203/1000000000 : ℝ)|=(432360203/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_box_4 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-583785373/2500000000 : ℝ)*x 0 + (8448123/16000000 : ℝ)*x 1 + (2640038409/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (583785373/2500000000 : ℝ)^4129 ≤ (2890804950237/20000000000000 : ℝ)^3105 := by
    have hnat : (583785373 : ℕ)^4129*20000000000000^3105 ≤ 2890804950237^3105*2500000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      583785373 2500000000 2890804950237 20000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8448123/16000000 : ℝ)^4129 ≤ (42772987927611/100000000000000 : ℝ)^3105 := by
    have hnat : (8448123 : ℕ)^4129*100000000000000^3105 ≤ 42772987927611^3105*16000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8448123 16000000 42772987927611 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2640038409/5000000000 : ℝ)^4129 ≤ (2673311707099/6250000000000 : ℝ)^3105 := by
    have hnat : (2640038409 : ℕ)^4129*6250000000000^3105 ≤ 2673311707099^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640038409 5000000000 2673311707099 6250000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-583785373/2500000000 : ℝ), (8448123/16000000 : ℝ), (2640038409/5000000000 : ℝ)] ![(2890804950237/20000000000000 : ℝ), (42772987927611/100000000000000 : ℝ), (2673311707099/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-583785373/2500000000 : ℝ)|^4129 ≤ (2890804950237/20000000000000 : ℝ)^3105
        have hw : |(-583785373/2500000000 : ℝ)|=(583785373/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8448123/16000000 : ℝ)|^4129 ≤ (42772987927611/100000000000000 : ℝ)^3105
        have hw : |(8448123/16000000 : ℝ)|=(8448123/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2640038409/5000000000 : ℝ)|^4129 ≤ (2673311707099/6250000000000 : ℝ)^3105
        have hw : |(2640038409/5000000000 : ℝ)|=(2640038409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_box_5 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5364058743/10000000000 : ℝ)*x 0 + (-2224063021/10000000000 : ℝ)*x 1 + (5280076799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364058743/10000000000 : ℝ)^4129 ≤ (21840019444793/50000000000000 : ℝ)^3105 := by
    have hnat : (5364058743 : ℕ)^4129*50000000000000^3105 ≤ 21840019444793^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364058743 10000000000 21840019444793 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2224063021/10000000000 : ℝ)^4129 ≤ (13546973984021/100000000000000 : ℝ)^3105 := by
    have hnat : (2224063021 : ℕ)^4129*100000000000000^3105 ≤ 13546973984021^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2224063021 10000000000 13546973984021 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5280076799/10000000000 : ℝ)^4129 ≤ (10693246777227/25000000000000 : ℝ)^3105 := by
    have hnat : (5280076799 : ℕ)^4129*25000000000000^3105 ≤ 10693246777227^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280076799 10000000000 10693246777227 25000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364058743/10000000000 : ℝ), (-2224063021/10000000000 : ℝ), (5280076799/10000000000 : ℝ)] ![(21840019444793/50000000000000 : ℝ), (13546973984021/100000000000000 : ℝ), (10693246777227/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364058743/10000000000 : ℝ)|^4129 ≤ (21840019444793/50000000000000 : ℝ)^3105
        have hw : |(5364058743/10000000000 : ℝ)|=(5364058743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2224063021/10000000000 : ℝ)|^4129 ≤ (13546973984021/100000000000000 : ℝ)^3105
        have hw : |(-2224063021/10000000000 : ℝ)|=(2224063021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5280076799/10000000000 : ℝ)|^4129 ≤ (10693246777227/25000000000000 : ℝ)^3105
        have hw : |(5280076799/10000000000 : ℝ)|=(5280076799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_box_6 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1341014659/2500000000 : ℝ)*x 0 + (1320019259/2500000000 : ℝ)*x 1 + (-44481257/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1341014659/2500000000 : ℝ)^4129 ≤ (10920009432731/25000000000000 : ℝ)^3105 := by
    have hnat : (1341014659 : ℕ)^4129*25000000000000^3105 ≤ 10920009432731^3105*2500000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1341014659 2500000000 10920009432731 25000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1320019259/2500000000 : ℝ)^4129 ≤ (2673311853873/6250000000000 : ℝ)^3105 := by
    have hnat : (1320019259 : ℕ)^4129*6250000000000^3105 ≤ 2673311853873^3105*2500000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320019259 2500000000 2673311853873 6250000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (44481257/200000000 : ℝ)^4129 ≤ (13546972598941/100000000000000 : ℝ)^3105 := by
    have hnat : (44481257 : ℕ)^4129*100000000000000^3105 ≤ 13546972598941^3105*200000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44481257 200000000 13546972598941 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1341014659/2500000000 : ℝ), (1320019259/2500000000 : ℝ), (-44481257/200000000 : ℝ)] ![(10920009432731/25000000000000 : ℝ), (2673311853873/6250000000000 : ℝ), (13546972598941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1341014659/2500000000 : ℝ)|^4129 ≤ (10920009432731/25000000000000 : ℝ)^3105
        have hw : |(1341014659/2500000000 : ℝ)|=(1341014659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1320019259/2500000000 : ℝ)|^4129 ≤ (2673311853873/6250000000000 : ℝ)^3105
        have hw : |(1320019259/2500000000 : ℝ)|=(1320019259/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-44481257/200000000 : ℝ)|^4129 ≤ (13546972598941/100000000000000 : ℝ)^3105
        have hw : |(-44481257/200000000 : ℝ)|=(44481257/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_box_7 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4266912591/10000000000 : ℝ)*x 0 + (4432141301/10000000000 : ℝ)*x 1 + (2216070613/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4266912591/10000000000 : ℝ)^4129 ≤ (32220235803781/100000000000000 : ℝ)^3105 := by
    have hnat : (4266912591 : ℕ)^4129*100000000000000^3105 ≤ 32220235803781^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4266912591 10000000000 32220235803781 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4432141301/10000000000 : ℝ)^4129 ≤ (33889882472187/100000000000000 : ℝ)^3105 := by
    have hnat : (4432141301 : ℕ)^4129*100000000000000^3105 ≤ 33889882472187^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4432141301 10000000000 33889882472187 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2216070613/5000000000 : ℝ)^4129 ≤ (33889881709579/100000000000000 : ℝ)^3105 := by
    have hnat : (2216070613 : ℕ)^4129*100000000000000^3105 ≤ 33889881709579^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2216070613 5000000000 33889881709579 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4266912591/10000000000 : ℝ), (4432141301/10000000000 : ℝ), (2216070613/5000000000 : ℝ)] ![(32220235803781/100000000000000 : ℝ), (33889882472187/100000000000000 : ℝ), (33889881709579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4266912591/10000000000 : ℝ)|^4129 ≤ (32220235803781/100000000000000 : ℝ)^3105
        have hw : |(4266912591/10000000000 : ℝ)|=(4266912591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4432141301/10000000000 : ℝ)|^4129 ≤ (33889882472187/100000000000000 : ℝ)^3105
        have hw : |(4432141301/10000000000 : ℝ)|=(4432141301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2216070613/5000000000 : ℝ)|^4129 ≤ (33889881709579/100000000000000 : ℝ)^3105
        have hw : |(2216070613/5000000000 : ℝ)|=(2216070613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_box_8 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2280787103/10000000000 : ℝ)*x 0 + (1303513033/2500000000 : ℝ)*x 1 + (336686331/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2280787103/10000000000 : ℝ)^4129 ≤ (14008353543081/100000000000000 : ℝ)^3105 := by
    have hnat : (2280787103 : ℕ)^4129*100000000000000^3105 ≤ 14008353543081^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2280787103 10000000000 14008353543081 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1303513033/2500000000 : ℝ)^4129 ≤ (42063213398687/100000000000000 : ℝ)^3105 := by
    have hnat : (1303513033 : ℕ)^4129*100000000000000^3105 ≤ 42063213398687^3105*2500000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303513033 2500000000 42063213398687 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (336686331/625000000 : ℝ)^4129 ≤ (351427464413/800000000000 : ℝ)^3105 := by
    have hnat : (336686331 : ℕ)^4129*800000000000^3105 ≤ 351427464413^3105*625000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336686331 625000000 351427464413 800000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2280787103/10000000000 : ℝ), (1303513033/2500000000 : ℝ), (336686331/625000000 : ℝ)] ![(14008353543081/100000000000000 : ℝ), (42063213398687/100000000000000 : ℝ), (351427464413/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2280787103/10000000000 : ℝ)|^4129 ≤ (14008353543081/100000000000000 : ℝ)^3105
        have hw : |(-2280787103/10000000000 : ℝ)|=(2280787103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1303513033/2500000000 : ℝ)|^4129 ≤ (42063213398687/100000000000000 : ℝ)^3105
        have hw : |(1303513033/2500000000 : ℝ)|=(1303513033/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(336686331/625000000 : ℝ)|^4129 ≤ (351427464413/800000000000 : ℝ)^3105
        have hw : |(336686331/625000000 : ℝ)|=(336686331/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_box_9 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644197763/5000000000 : ℝ)*x 0 + (-1091099761/5000000000 : ℝ)*x 1 + (2693490749/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644197763/5000000000 : ℝ)^4129 ≤ (21431311533363/50000000000000 : ℝ)^3105 := by
    have hnat : (2644197763 : ℕ)^4129*50000000000000^3105 ≤ 21431311533363^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644197763 5000000000 21431311533363 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1091099761/5000000000 : ℝ)^4129 ≤ (3302235419127/25000000000000 : ℝ)^3105 := by
    have hnat : (1091099761 : ℕ)^4129*25000000000000^3105 ≤ 3302235419127^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091099761 5000000000 3302235419127 25000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693490749/5000000000 : ℝ)^4129 ≤ (43928435242083/100000000000000 : ℝ)^3105 := by
    have hnat : (2693490749 : ℕ)^4129*100000000000000^3105 ≤ 43928435242083^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693490749 5000000000 43928435242083 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644197763/5000000000 : ℝ), (-1091099761/5000000000 : ℝ), (2693490749/5000000000 : ℝ)] ![(21431311533363/50000000000000 : ℝ), (3302235419127/25000000000000 : ℝ), (43928435242083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644197763/5000000000 : ℝ)|^4129 ≤ (21431311533363/50000000000000 : ℝ)^3105
        have hw : |(2644197763/5000000000 : ℝ)|=(2644197763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1091099761/5000000000 : ℝ)|^4129 ≤ (3302235419127/25000000000000 : ℝ)^3105
        have hw : |(-1091099761/5000000000 : ℝ)|=(1091099761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693490749/5000000000 : ℝ)|^4129 ≤ (43928435242083/100000000000000 : ℝ)^3105
        have hw : |(2693490749/5000000000 : ℝ)|=(2693490749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_box_10 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (264419773/500000000 : ℝ)*x 0 + (1346745137/2500000000 : ℝ)*x 1 + (-218220089/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264419773/500000000 : ℝ)^4129 ≤ (42862622355379/100000000000000 : ℝ)^3105 := by
    have hnat : (264419773 : ℕ)^4129*100000000000000^3105 ≤ 42862622355379^3105*500000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264419773 500000000 42862622355379 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1346745137/2500000000 : ℝ)^4129 ≤ (1757136997617/4000000000000 : ℝ)^3105 := by
    have hnat : (1346745137 : ℕ)^4129*4000000000000^3105 ≤ 1757136997617^3105*2500000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346745137 2500000000 1757136997617 4000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (218220089/1000000000 : ℝ)^4129 ≤ (165111908599/1250000000000 : ℝ)^3105 := by
    have hnat : (218220089 : ℕ)^4129*1250000000000^3105 ≤ 165111908599^3105*1000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218220089 1000000000 165111908599 1250000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264419773/500000000 : ℝ), (1346745137/2500000000 : ℝ), (-218220089/1000000000 : ℝ)] ![(42862622355379/100000000000000 : ℝ), (1757136997617/4000000000000 : ℝ), (165111908599/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264419773/500000000 : ℝ)|^4129 ≤ (42862622355379/100000000000000 : ℝ)^3105
        have hw : |(264419773/500000000 : ℝ)|=(264419773/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1346745137/2500000000 : ℝ)|^4129 ≤ (1757136997617/4000000000000 : ℝ)^3105
        have hw : |(1346745137/2500000000 : ℝ)|=(1346745137/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-218220089/1000000000 : ℝ)|^4129 ≤ (165111908599/1250000000000 : ℝ)^3105
        have hw : |(-218220089/1000000000 : ℝ)|=(218220089/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_box_11 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1126295729/2500000000 : ℝ)*x 0 + (4312886431/10000000000 : ℝ)*x 1 + (4312887657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1126295729/2500000000 : ℝ)^4129 ≤ (34634587677427/100000000000000 : ℝ)^3105 := by
    have hnat : (1126295729 : ℕ)^4129*100000000000000^3105 ≤ 34634587677427^3105*2500000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126295729 2500000000 34634587677427 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4312886431/10000000000 : ℝ)^4129 ≤ (32682699974783/100000000000000 : ℝ)^3105 := by
    have hnat : (4312886431 : ℕ)^4129*100000000000000^3105 ≤ 32682699974783^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4312886431 10000000000 32682699974783 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4312887657/10000000000 : ℝ)^4129 ≤ (817067808231/2500000000000 : ℝ)^3105 := by
    have hnat : (4312887657 : ℕ)^4129*2500000000000^3105 ≤ 817067808231^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4312887657 10000000000 817067808231 2500000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1126295729/2500000000 : ℝ), (4312886431/10000000000 : ℝ), (4312887657/10000000000 : ℝ)] ![(34634587677427/100000000000000 : ℝ), (32682699974783/100000000000000 : ℝ), (817067808231/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1126295729/2500000000 : ℝ)|^4129 ≤ (34634587677427/100000000000000 : ℝ)^3105
        have hw : |(1126295729/2500000000 : ℝ)|=(1126295729/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4312886431/10000000000 : ℝ)|^4129 ≤ (32682699974783/100000000000000 : ℝ)^3105
        have hw : |(4312886431/10000000000 : ℝ)|=(4312886431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4312887657/10000000000 : ℝ)|^4129 ≤ (817067808231/2500000000000 : ℝ)^3105
        have hw : |(4312887657/10000000000 : ℝ)|=(4312887657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_box_12 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-133093109/625000000 : ℝ)*x 0 + (2721034531/5000000000 : ℝ)*x 1 + (1054415431/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133093109/625000000 : ℝ)^4129 ≤ (3196591295461/25000000000000 : ℝ)^3105 := by
    have hnat : (133093109 : ℕ)^4129*25000000000000^3105 ≤ 3196591295461^3105*625000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133093109 625000000 3196591295461 25000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2721034531/5000000000 : ℝ)^4129 ≤ (22263400777971/50000000000000 : ℝ)^3105 := by
    have hnat : (2721034531 : ℕ)^4129*50000000000000^3105 ≤ 22263400777971^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721034531 5000000000 22263400777971 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054415431/2000000000 : ℝ)^4129 ≤ (8537366650121/20000000000000 : ℝ)^3105 := by
    have hnat : (1054415431 : ℕ)^4129*20000000000000^3105 ≤ 8537366650121^3105*2000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054415431 2000000000 8537366650121 20000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-133093109/625000000 : ℝ), (2721034531/5000000000 : ℝ), (1054415431/2000000000 : ℝ)] ![(3196591295461/25000000000000 : ℝ), (22263400777971/50000000000000 : ℝ), (8537366650121/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-133093109/625000000 : ℝ)|^4129 ≤ (3196591295461/25000000000000 : ℝ)^3105
        have hw : |(-133093109/625000000 : ℝ)|=(133093109/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2721034531/5000000000 : ℝ)|^4129 ≤ (22263400777971/50000000000000 : ℝ)^3105
        have hw : |(2721034531/5000000000 : ℝ)|=(2721034531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1054415431/2000000000 : ℝ)|^4129 ≤ (8537366650121/20000000000000 : ℝ)^3105
        have hw : |(1054415431/2000000000 : ℝ)|=(1054415431/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_box_13 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (671214789/1250000000 : ℝ)*x 0 + (-2227131921/10000000000 : ℝ)*x 1 + (5272076649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671214789/1250000000 : ℝ)^4129 ≤ (21870667411477/50000000000000 : ℝ)^3105 := by
    have hnat : (671214789 : ℕ)^4129*50000000000000^3105 ≤ 21870667411477^3105*1250000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671214789 1250000000 21870667411477 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2227131921/10000000000 : ℝ)^4129 ≤ (3392959338573/25000000000000 : ℝ)^3105 := by
    have hnat : (2227131921 : ℕ)^4129*25000000000000^3105 ≤ 3392959338573^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2227131921 10000000000 3392959338573 25000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5272076649/10000000000 : ℝ)^4129 ≤ (42686827802493/100000000000000 : ℝ)^3105 := by
    have hnat : (5272076649 : ℕ)^4129*100000000000000^3105 ≤ 42686827802493^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272076649 10000000000 42686827802493 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671214789/1250000000 : ℝ), (-2227131921/10000000000 : ℝ), (5272076649/10000000000 : ℝ)] ![(21870667411477/50000000000000 : ℝ), (3392959338573/25000000000000 : ℝ), (42686827802493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671214789/1250000000 : ℝ)|^4129 ≤ (21870667411477/50000000000000 : ℝ)^3105
        have hw : |(671214789/1250000000 : ℝ)|=(671214789/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2227131921/10000000000 : ℝ)|^4129 ≤ (3392959338573/25000000000000 : ℝ)^3105
        have hw : |(-2227131921/10000000000 : ℝ)|=(2227131921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5272076649/10000000000 : ℝ)|^4129 ≤ (42686827802493/100000000000000 : ℝ)^3105
        have hw : |(5272076649/10000000000 : ℝ)|=(5272076649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_box_14 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5369718083/10000000000 : ℝ)*x 0 + (659009621/1250000000 : ℝ)*x 1 + (-556782951/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369718083/10000000000 : ℝ)^4129 ≤ (2187066617117/5000000000000 : ℝ)^3105 := by
    have hnat : (5369718083 : ℕ)^4129*5000000000000^3105 ≤ 2187066617117^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369718083 10000000000 2187066617117 5000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (659009621/1250000000 : ℝ)^4129 ≤ (10671707809293/25000000000000 : ℝ)^3105 := by
    have hnat : (659009621 : ℕ)^4129*25000000000000^3105 ≤ 10671707809293^3105*1250000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659009621 1250000000 10671707809293 25000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (556782951/2500000000 : ℝ)^4129 ≤ (424119887693/3125000000000 : ℝ)^3105 := by
    have hnat : (556782951 : ℕ)^4129*3125000000000^3105 ≤ 424119887693^3105*2500000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      556782951 2500000000 424119887693 3125000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369718083/10000000000 : ℝ), (659009621/1250000000 : ℝ), (-556782951/2500000000 : ℝ)] ![(2187066617117/5000000000000 : ℝ), (10671707809293/25000000000000 : ℝ), (424119887693/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369718083/10000000000 : ℝ)|^4129 ≤ (2187066617117/5000000000000 : ℝ)^3105
        have hw : |(5369718083/10000000000 : ℝ)|=(5369718083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(659009621/1250000000 : ℝ)|^4129 ≤ (10671707809293/25000000000000 : ℝ)^3105
        have hw : |(659009621/1250000000 : ℝ)|=(659009621/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-556782951/2500000000 : ℝ)|^4129 ≤ (424119887693/3125000000000 : ℝ)^3105
        have hw : |(-556782951/2500000000 : ℝ)|=(556782951/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_box_15 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2124414913/5000000000 : ℝ)*x 0 + (1110265229/2500000000 : ℝ)*x 1 + (4441060813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2124414913/5000000000 : ℝ)^4129 ≤ (16019392436321/50000000000000 : ℝ)^3105 := by
    have hnat : (2124414913 : ℕ)^4129*50000000000000^3105 ≤ 16019392436321^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124414913 5000000000 16019392436321 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1110265229/2500000000 : ℝ)^4129 ≤ (33980608079557/100000000000000 : ℝ)^3105 := by
    have hnat : (1110265229 : ℕ)^4129*100000000000000^3105 ≤ 33980608079557^3105*2500000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1110265229 2500000000 33980608079557 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4441060813/10000000000 : ℝ)^4129 ≤ (8495151757887/25000000000000 : ℝ)^3105 := by
    have hnat : (4441060813 : ℕ)^4129*25000000000000^3105 ≤ 8495151757887^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4441060813 10000000000 8495151757887 25000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2124414913/5000000000 : ℝ), (1110265229/2500000000 : ℝ), (4441060813/10000000000 : ℝ)] ![(16019392436321/50000000000000 : ℝ), (33980608079557/100000000000000 : ℝ), (8495151757887/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2124414913/5000000000 : ℝ)|^4129 ≤ (16019392436321/50000000000000 : ℝ)^3105
        have hw : |(2124414913/5000000000 : ℝ)|=(2124414913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1110265229/2500000000 : ℝ)|^4129 ≤ (33980608079557/100000000000000 : ℝ)^3105
        have hw : |(1110265229/2500000000 : ℝ)|=(1110265229/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4441060813/10000000000 : ℝ)|^4129 ≤ (8495151757887/25000000000000 : ℝ)^3105
        have hw : |(4441060813/10000000000 : ℝ)|=(4441060813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1065_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29594717/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7001/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11251/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(3889/6250 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(1481/2500 : ℝ) ∧ (79569/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (1659/2000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7001/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11251/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7001/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11251/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7001/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11251/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7001/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11251/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7001/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11251/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7001/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11251/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11251/100000 : ℝ) ^ (8257/2048 : ℝ) ≤ (598013415934081/4000000000000000000 : ℝ) := by
    have hpowers : (11251/100000 : ℝ)^8257 ≤ (598013415934081/4000000000000000000 : ℝ)^2048 := by
      have hnat : (11251 : ℕ)^8257*4000000000000000000^2048 ≤ 598013415934081^2048*100000^8257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11251 100000 598013415934081 4000000000000000000 8257 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11251/100000 : ℝ)) (X := (598013415934081/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7001/50000 : ℝ) ^ (8257/2048 : ℝ) ≤ (4514106974374721/12500000000000000000 : ℝ) := by
    have hpowers : (7001/50000 : ℝ)^8257 ≤ (4514106974374721/12500000000000000000 : ℝ)^2048 := by
      have hnat : (7001 : ℕ)^8257*12500000000000000000^2048 ≤ 4514106974374721^2048*50000^8257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7001 50000 4514106974374721 12500000000000000000 8257 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7001/50000 : ℝ)) (X := (4514106974374721/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000598013415934081/2000000000000000000 : ℝ) ≤ (10000741548875757/10000000000000000 : ℝ) ^ (8257/2048 : ℝ) := by
    have hpowers : (2000598013415934081/2000000000000000000 : ℝ)^2048 ≤ (10000741548875757/10000000000000000 : ℝ)^8257 := by
      have hnat : (2000598013415934081 : ℕ)^2048*10000000000000000^8257 ≤ 10000741548875757^8257*2000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000598013415934081 2000000000000000000 10000741548875757 10000000000000000 2048 8257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000741548875757/10000000000000000 : ℝ)) (X := (2000598013415934081/2000000000000000000 : ℝ)) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051063191193349793/100000000000000000000 : ℝ) ≤ (10001266287317309/10000000000000000 : ℝ) ^ (8257/2048 : ℝ) := by
    have hpowers : (100051063191193349793/100000000000000000000 : ℝ)^2048 ≤ (10001266287317309/10000000000000000 : ℝ)^8257 := by
      have hnat : (100051063191193349793 : ℕ)^2048*10000000000000000^8257 ≤ 10001266287317309^8257*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051063191193349793 100000000000000000000 10001266287317309 10000000000000000 2048 8257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001266287317309/10000000000000000 : ℝ)) (X := (100051063191193349793/100000000000000000000 : ℝ)) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254514106974374721/6250000000000000000 : ℝ) ≤ (10001791025758861/10000000000000000 : ℝ) ^ (8257/2048 : ℝ) := by
    have hpowers : (6254514106974374721/6250000000000000000 : ℝ)^2048 ≤ (10001791025758861/10000000000000000 : ℝ)^8257 := by
      have hnat : (6254514106974374721 : ℕ)^2048*10000000000000000^8257 ≤ 10001791025758861^8257*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254514106974374721 6250000000000000000 10001791025758861 10000000000000000 2048 8257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001791025758861/10000000000000000 : ℝ)) (X := (6254514106974374721/6250000000000000000 : ℝ)) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(598013415934081/4000000000000000000 : ℝ) ≤ ((27500232336545404403/27510000000000000000 : ℝ)+2*(32796152597/17193750000000 : ℝ)*(11251/100000 : ℝ))^(8257/2048 : ℝ) := by
    rw [show (27500232336545404403/27510000000000000000 : ℝ)+2*(32796152597/17193750000000 : ℝ)*(11251/100000 : ℝ)=(10000741548875757/10000000000000000 : ℝ) by norm_num, show 1+2*(598013415934081/4000000000000000000 : ℝ)=(2000598013415934081/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4514106974374721/12500000000000000000 : ℝ)+(598013415934081/4000000000000000000 : ℝ) ≤ ((27500232336545404403/27510000000000000000 : ℝ)+(32796152597/17193750000000 : ℝ)*((7001/50000 : ℝ)+(11251/100000 : ℝ)))^(8257/2048 : ℝ) := by
    rw [show (27500232336545404403/27510000000000000000 : ℝ)+(32796152597/17193750000000 : ℝ)*((7001/50000 : ℝ)+(11251/100000 : ℝ))=(10001266287317309/10000000000000000 : ℝ) by norm_num, show 1+(4514106974374721/12500000000000000000 : ℝ)+(598013415934081/4000000000000000000 : ℝ)=(100051063191193349793/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4514106974374721/12500000000000000000 : ℝ) ≤ ((27500232336545404403/27510000000000000000 : ℝ)+2*(32796152597/17193750000000 : ℝ)*(7001/50000 : ℝ))^(8257/2048 : ℝ) := by
    rw [show (27500232336545404403/27510000000000000000 : ℝ)+2*(32796152597/17193750000000 : ℝ)*(7001/50000 : ℝ)=(10001791025758861/10000000000000000 : ℝ) by norm_num, show 1+2*(4514106974374721/12500000000000000000 : ℝ)=(6254514106974374721/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27500232336545404403/27510000000000000000 : ℝ)*(X 1 0+X 2 0)+(32796152597/17193750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8257/2048 : ℝ)) (lo := (11251/100000 : ℝ)) (hi := (7001/50000 : ℝ)) (c := (27500232336545404403/27510000000000000000 : ℝ)) (alpha := (32796152597/17193750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27500232336545404403/27510000000000000000 : ℝ)*(X 0 1+X 2 1)+(32796152597/17193750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8257/2048 : ℝ)) (lo := (11251/100000 : ℝ)) (hi := (7001/50000 : ℝ)) (c := (27500232336545404403/27510000000000000000 : ℝ)) (alpha := (32796152597/17193750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27500232336545404403/27510000000000000000 : ℝ)*(X 0 2+X 1 2)+(32796152597/17193750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8257/2048 : ℝ)) (lo := (11251/100000 : ℝ)) (hi := (7001/50000 : ℝ)) (c := (27500232336545404403/27510000000000000000 : ℝ)) (alpha := (32796152597/17193750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-207476639/1000000000 : ℝ)*X 0 0+(672172631/1250000000 : ℝ)*X 0 1+(5377380889/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2647596613/5000000000 : ℝ)*X 1 0+(-1093012093/5000000000 : ℝ)*X 1 1+(5377380997/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5295193263/10000000000 : ℝ)*X 2 0+(2688690457/5000000000 : ℝ)*X 2 1+(-273253031/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2242016891/5000000000 : ℝ)*X 0 0+(4323602237/10000000000 : ℝ)*X 0 1+(432360203/1000000000 : ℝ)*X 0 2+(2242016891/5000000000 : ℝ)*X 1 0+(4323602237/10000000000 : ℝ)*X 1 1+(432360203/1000000000 : ℝ)*X 1 2+(2242016891/5000000000 : ℝ)*X 2 0+(4323602237/10000000000 : ℝ)*X 2 1+(432360203/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-583785373/2500000000 : ℝ)*X 0 0+(8448123/16000000 : ℝ)*X 0 1+(2640038409/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5364058743/10000000000 : ℝ)*X 1 0+(-2224063021/10000000000 : ℝ)*X 1 1+(5280076799/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1341014659/2500000000 : ℝ)*X 2 0+(1320019259/2500000000 : ℝ)*X 2 1+(-44481257/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4266912591/10000000000 : ℝ)*X 0 0+(4432141301/10000000000 : ℝ)*X 0 1+(2216070613/5000000000 : ℝ)*X 0 2+(4266912591/10000000000 : ℝ)*X 1 0+(4432141301/10000000000 : ℝ)*X 1 1+(2216070613/5000000000 : ℝ)*X 1 2+(4266912591/10000000000 : ℝ)*X 2 0+(4432141301/10000000000 : ℝ)*X 2 1+(2216070613/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2280787103/10000000000 : ℝ)*X 0 0+(1303513033/2500000000 : ℝ)*X 0 1+(336686331/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2644197763/5000000000 : ℝ)*X 1 0+(-1091099761/5000000000 : ℝ)*X 1 1+(2693490749/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((264419773/500000000 : ℝ)*X 2 0+(1346745137/2500000000 : ℝ)*X 2 1+(-218220089/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1126295729/2500000000 : ℝ)*X 0 0+(4312886431/10000000000 : ℝ)*X 0 1+(4312887657/10000000000 : ℝ)*X 0 2+(1126295729/2500000000 : ℝ)*X 1 0+(4312886431/10000000000 : ℝ)*X 1 1+(4312887657/10000000000 : ℝ)*X 1 2+(1126295729/2500000000 : ℝ)*X 2 0+(4312886431/10000000000 : ℝ)*X 2 1+(4312887657/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-133093109/625000000 : ℝ)*X 0 0+(2721034531/5000000000 : ℝ)*X 0 1+(1054415431/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((671214789/1250000000 : ℝ)*X 1 0+(-2227131921/10000000000 : ℝ)*X 1 1+(5272076649/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5369718083/10000000000 : ℝ)*X 2 0+(659009621/1250000000 : ℝ)*X 2 1+(-556782951/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2124414913/5000000000 : ℝ)*X 0 0+(1110265229/2500000000 : ℝ)*X 0 1+(4441060813/10000000000 : ℝ)*X 0 2+(2124414913/5000000000 : ℝ)*X 1 0+(1110265229/2500000000 : ℝ)*X 1 1+(4441060813/10000000000 : ℝ)*X 1 2+(2124414913/5000000000 : ℝ)*X 2 0+(1110265229/2500000000 : ℝ)*X 2 1+(4441060813/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-3889/6250 : ℝ) ≤ (-17830474981770949436379158595497/28656250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6936357/20000000000000 : ℝ)*(upper1) + (722927/2500000000000 : ℝ)*(upper4) + (2851731/5000000000000 : ℝ)*(upper5) + (240988165876933/6250000000000 : ℝ)*(major0) + (240988165876933/6250000000000 : ℝ)*(major1) + (240988165876933/6250000000000 : ℝ)*(major2) + (2461546953/50000000000000 : ℝ)*(sp1) + (955961231/50000000000000 : ℝ)*(sp3) + (5126612599888867/100000000000000 : ℝ)*(sp4) + (5126614490819869/100000000000000 : ℝ)*(sp5) + (5126531297941671/100000000000000 : ℝ)*(sp6) + (1302870314620923/50000000000000 : ℝ)*(sp7) + (1703506227/25000000000000 : ℝ)*(sp8) + (11014496513/12500000000000 : ℝ)*(sp14) + (2605742541164309/100000000000000 : ℝ)*(f.failure) + (205064776556551/4000000000000 : ℝ)*(f.sum) + (20968901375923/6877500000000000000000000000 : ℝ)*base65 + (2144934717280248499/171937500000000000000000000000000 : ℝ)*base67 + (2261703764895310999/171937500000000000000000000000000 : ℝ)*base69 + (1984215095150748499/171937500000000000000000000000000 : ℝ)*base71 + (62277442392131/13755000000000000000000000000 : ℝ)*base73 + (633641738339748499/171937500000000000000000000000000 : ℝ)*base75 + (1337122817918560999/171937500000000000000000000000000 : ℝ)*base77 + (2098801591180435999/171937500000000000000000000000000 : ℝ)*base79 + (3151590891347/6877500000000000000000000000 : ℝ)*base82 + (15355553/2000000000000000000000 : ℝ)*base89 + (15355553/2000000000000000000000 : ℝ)*base91 + (15355553/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (1481/2500 : ℝ) ≤ (9700962442329385611792647093679/16375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1593199/5000000000000 : ℝ)*(upper3) + (22078323/100000000000000 : ℝ)*(upper4) + (28317667/50000000000000 : ℝ)*(lower5) + (979676323403183/25000000000000 : ℝ)*(major0) + (979676323403183/25000000000000 : ℝ)*(major1) + (979676323403183/25000000000000 : ℝ)*(major2) + (2584707108982519/50000000000000 : ℝ)*(sp0) + (1292353586318149/25000000000000 : ℝ)*(sp1) + (5169413916680743/100000000000000 : ℝ)*(sp2) + (662061196861691/25000000000000 : ℝ)*(sp3) + (2230352769/100000000000000 : ℝ)*(sp5) + (1329472311/50000000000000 : ℝ)*(sp6) + (1717909399/100000000000000 : ℝ)*(sp7) + (294707541/12500000000000 : ℝ)*(sp8) + (662061626339041/25000000000000 : ℝ)*(f.failure) + (1033883315125073/20000000000000 : ℝ)*(f.sum) + (4238480829007/1965000000000000000000000000 : ℝ)*base65 + (261934040724252107/98250000000000000000000000000000 : ℝ)*base67 + (239269762459002107/98250000000000000000000000000000 : ℝ)*base69 + (1083358074982002107/98250000000000000000000000000000 : ℝ)*base71 + (1728563526911/982500000000000000000000000 : ℝ)*base73 + (373972401511752107/98250000000000000000000000000000 : ℝ)*base75 + (1088374136573502107/98250000000000000000000000000000 : ℝ)*base77 + (650078488978752107/98250000000000000000000000000000 : ℝ)*base79 + (4457921048351/982500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (4446397/500000000000000000000 : ℝ)*base89 + (4446397/500000000000000000000 : ℝ)*base91 + (4446397/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (79569/100000 : ℝ) ≤ (13029849551738985042626722929271/16375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (771095611/100000000000000 : ℝ)*(upper0) + (249237661/100000000000000 : ℝ)*(upper2) + (161632339/100000000000000 : ℝ)*(lower3) + (310397517/25000000000000 : ℝ)*(lower5) + (2193449447601901/50000000000000 : ℝ)*(major0) + (2193449447601901/50000000000000 : ℝ)*(major1) + (2193449447601901/50000000000000 : ℝ)*(major2) + (62101105449/20000000000000 : ℝ)*(sp1) + (10113407033/6250000000000 : ℝ)*(sp3) + (459745017/25000000000000 : ℝ)*(sp4) + (578262207958619/10000000000000 : ℝ)*(sp8) + (5782313413039013/100000000000000 : ℝ)*(sp9) + (2891311959283129/50000000000000 : ℝ)*(sp10) + (370561023819603/12500000000000 : ℝ)*(sp11) + (370581250633669/12500000000000 : ℝ)*(f.failure) + (2891311959283129/50000000000000 : ℝ)*(f.sum) + (8283582032533/6877500000000000000000000000 : ℝ)*base66 + (12848033774701770103/1375500000000000000000000000000000 : ℝ)*base67 + (4141869506095770103/1375500000000000000000000000000000 : ℝ)*base69 + (11537081824687770103/1375500000000000000000000000000000 : ℝ)*base71 + (150008767771/3438750000000000000000000000 : ℝ)*base73 + (2833522963533270103/1375500000000000000000000000000000 : ℝ)*base75 + (596603219548229897/1375500000000000000000000000000000 : ℝ)*base78 + (40887374586799770103/1375500000000000000000000000000000 : ℝ)*base79 + (9520937231941/3438750000000000000000000000 : ℝ)*base81 + (273327/250000000000000000000 : ℝ)*base90 + (273327/250000000000000000000 : ℝ)*base92 + (273327/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-1659/2000 : ℝ) ≤ (-23769696682202899811973277176619/28656250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26872937/100000000000000 : ℝ)*(upper1) + (24053959/25000000000000 : ℝ)*(upper3) + (22023767/25000000000000 : ℝ)*(upper5) + (276346159492223/6250000000000 : ℝ)*(major0) + (276346159492223/6250000000000 : ℝ)*(major1) + (276346159492223/6250000000000 : ℝ)*(major2) + (35253034149/100000000000000 : ℝ)*(sp4) + (246999801669/50000000000000 : ℝ)*(sp5) + (255978031609/100000000000000 : ℝ)*(sp6) + (412697092073/100000000000000 : ℝ)*(sp7) + (5882631723272891/100000000000000 : ℝ)*(sp12) + (5882172976703703/100000000000000 : ℝ)*(sp13) + (735301374784429/12500000000000 : ℝ)*(sp14) + (2987646659498881/100000000000000 : ℝ)*(sp15) + (1494029678295477/50000000000000 : ℝ)*(f.failure) + (5882666976307041/100000000000000 : ℝ)*(f.sum) + (45656624585399/13755000000000000000000000000 : ℝ)*base66 + (114820040672682869/171937500000000000000000000000000 : ℝ)*base67 + (7560079991413182869/171937500000000000000000000000000 : ℝ)*base69 + (1426365354392495369/171937500000000000000000000000000 : ℝ)*base71 + (8144805835063/1719375000000000000000000000 : ℝ)*base74 + (2581777812263192131/171937500000000000000000000000000 : ℝ)*base76 + (1351698278066870369/171937500000000000000000000000000 : ℝ)*base77 + (352141315998129631/171937500000000000000000000000000 : ℝ)*base80 + (631501872238921/13755000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (4195009/1000000000000000000000 : ℝ)*base89 + (4195009/1000000000000000000000 : ℝ)*base91 + (4195009/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1065_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29594717/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7001/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11251/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(1481/2500 : ℝ) else (79569/100000 : ℝ) ≤ X j i ∧ X j i ≤ (1659/2000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1065_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1065_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29594717/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7001/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9/80 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(1481/2500 : ℝ) else (79569/100000 : ℝ) ≤ X j i ∧ X j i ≤ (1659/2000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1065_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1065_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29594717/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7001/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9/80 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(1481/2500 : ℝ) else (79569/100000 : ℝ) ≤ X j i ∧ X j i ≤ (1659/2000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1065_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
