-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1082_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:50:45.638641+00:00
-- url     : https://prove2.me/submissions/7a531351-1bd0-4d98-9057-81ee74bcffe2

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
theorem support_rectangle_w1082_s3_0 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1095693033/5000000000 : ℝ)*x 0 + (108713809/200000000 : ℝ)*x 1 + (261304563/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1095693033/5000000000 : ℝ)^8275 ≤ (6650552547451/50000000000000 : ℝ)^6227 := by
    have hnat : (1095693033 : ℕ)^8275*50000000000000^6227 ≤ 6650552547451^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095693033 5000000000 6650552547451 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108713809/200000000 : ℝ)^8275 ≤ (2780113803541/6250000000000 : ℝ)^6227 := by
    have hnat : (108713809 : ℕ)^8275*6250000000000^6227 ≤ 2780113803541^6227*200000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108713809 200000000 2780113803541 6250000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (261304563/500000000 : ℝ)^8275 ≤ (42217074036943/100000000000000 : ℝ)^6227 := by
    have hnat : (261304563 : ℕ)^8275*100000000000000^6227 ≤ 42217074036943^6227*500000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261304563 500000000 42217074036943 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1095693033/5000000000 : ℝ), (108713809/200000000 : ℝ), (261304563/500000000 : ℝ)] ![(6650552547451/50000000000000 : ℝ), (2780113803541/6250000000000 : ℝ), (42217074036943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1095693033/5000000000 : ℝ)|^8275 ≤ (6650552547451/50000000000000 : ℝ)^6227
        have hw : |(-1095693033/5000000000 : ℝ)|=(1095693033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(108713809/200000000 : ℝ)|^8275 ≤ (2780113803541/6250000000000 : ℝ)^6227
        have hw : |(108713809/200000000 : ℝ)|=(108713809/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(261304563/500000000 : ℝ)|^8275 ≤ (42217074036943/100000000000000 : ℝ)^6227
        have hw : |(261304563/500000000 : ℝ)|=(261304563/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s3_1 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5355281777/10000000000 : ℝ)*x 0 + (-459735021/2000000000 : ℝ)*x 1 + (5226091249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355281777/10000000000 : ℝ)^8275 ≤ (2725595966859/6250000000000 : ℝ)^6227 := by
    have hnat : (5355281777 : ℕ)^8275*6250000000000^6227 ≤ 2725595966859^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355281777 10000000000 2725595966859 6250000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (459735021/2000000000 : ℝ)^8275 ≤ (14173390595183/100000000000000 : ℝ)^6227 := by
    have hnat : (459735021 : ℕ)^8275*100000000000000^6227 ≤ 14173390595183^6227*2000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      459735021 2000000000 14173390595183 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5226091249/10000000000 : ℝ)^8275 ≤ (21108536959429/50000000000000 : ℝ)^6227 := by
    have hnat : (5226091249 : ℕ)^8275*50000000000000^6227 ≤ 21108536959429^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226091249 10000000000 21108536959429 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355281777/10000000000 : ℝ), (-459735021/2000000000 : ℝ), (5226091249/10000000000 : ℝ)] ![(2725595966859/6250000000000 : ℝ), (14173390595183/100000000000000 : ℝ), (21108536959429/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355281777/10000000000 : ℝ)|^8275 ≤ (2725595966859/6250000000000 : ℝ)^6227
        have hw : |(5355281777/10000000000 : ℝ)|=(5355281777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-459735021/2000000000 : ℝ)|^8275 ≤ (14173390595183/100000000000000 : ℝ)^6227
        have hw : |(-459735021/2000000000 : ℝ)|=(459735021/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5226091249/10000000000 : ℝ)|^8275 ≤ (21108536959429/50000000000000 : ℝ)^6227
        have hw : |(5226091249/10000000000 : ℝ)|=(5226091249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s3_2 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2677640853/5000000000 : ℝ)*x 0 + (326630729/625000000 : ℝ)*x 1 + (-459734931/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677640853/5000000000 : ℝ)^8275 ≤ (5451191837677/12500000000000 : ℝ)^6227 := by
    have hnat : (2677640853 : ℕ)^8275*12500000000000^6227 ≤ 5451191837677^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677640853 5000000000 5451191837677 12500000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (326630729/625000000 : ℝ)^8275 ≤ (8443415674773/20000000000000 : ℝ)^6227 := by
    have hnat : (326630729 : ℕ)^8275*20000000000000^6227 ≤ 8443415674773^6227*625000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326630729 625000000 8443415674773 20000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (459734931/2000000000 : ℝ)^8275 ≤ (14173386907973/100000000000000 : ℝ)^6227 := by
    have hnat : (459734931 : ℕ)^8275*100000000000000^6227 ≤ 14173386907973^6227*2000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      459734931 2000000000 14173386907973 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677640853/5000000000 : ℝ), (326630729/625000000 : ℝ), (-459734931/2000000000 : ℝ)] ![(5451191837677/12500000000000 : ℝ), (8443415674773/20000000000000 : ℝ), (14173386907973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677640853/5000000000 : ℝ)|^8275 ≤ (5451191837677/12500000000000 : ℝ)^6227
        have hw : |(2677640853/5000000000 : ℝ)|=(2677640853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(326630729/625000000 : ℝ)|^8275 ≤ (8443415674773/20000000000000 : ℝ)^6227
        have hw : |(326630729/625000000 : ℝ)|=(326630729/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-459734931/2000000000 : ℝ)|^8275 ≤ (14173386907973/100000000000000 : ℝ)^6227
        have hw : |(-459734931/2000000000 : ℝ)|=(459734931/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s3_3 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (34964143/80000000 : ℝ)*x 0 + (4169367269/10000000000 : ℝ)*x 1 + (916291313/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34964143/80000000 : ℝ)^8275 ≤ (16644764587211/50000000000000 : ℝ)^6227 := by
    have hnat : (34964143 : ℕ)^8275*50000000000000^6227 ≤ 16644764587211^6227*80000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34964143 80000000 16644764587211 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4169367269/10000000000 : ℝ)^8275 ≤ (31269065703613/100000000000000 : ℝ)^6227 := by
    have hnat : (4169367269 : ℕ)^8275*100000000000000^6227 ≤ 31269065703613^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4169367269 10000000000 31269065703613 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (916291313/2000000000 : ℝ)^8275 ≤ (17720702555197/50000000000000 : ℝ)^6227 := by
    have hnat : (916291313 : ℕ)^8275*50000000000000^6227 ≤ 17720702555197^6227*2000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      916291313 2000000000 17720702555197 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(34964143/80000000 : ℝ), (4169367269/10000000000 : ℝ), (916291313/2000000000 : ℝ)] ![(16644764587211/50000000000000 : ℝ), (31269065703613/100000000000000 : ℝ), (17720702555197/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(34964143/80000000 : ℝ)|^8275 ≤ (16644764587211/50000000000000 : ℝ)^6227
        have hw : |(34964143/80000000 : ℝ)|=(34964143/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4169367269/10000000000 : ℝ)|^8275 ≤ (31269065703613/100000000000000 : ℝ)^6227
        have hw : |(4169367269/10000000000 : ℝ)|=(4169367269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(916291313/2000000000 : ℝ)|^8275 ≤ (17720702555197/50000000000000 : ℝ)^6227
        have hw : |(916291313/2000000000 : ℝ)|=(916291313/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s3_4 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-17531263/80000000 : ℝ)*x 0 + (5226940269/10000000000 : ℝ)*x 1 + (5434836129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17531263/80000000 : ℝ)^8275 ≤ (6650640503241/50000000000000 : ℝ)^6227 := by
    have hnat : (17531263 : ℕ)^8275*50000000000000^6227 ≤ 6650640503241^6227*80000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17531263 80000000 6650640503241 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5226940269/10000000000 : ℝ)^8275 ≤ (21113094177431/50000000000000 : ℝ)^6227 := by
    have hnat : (5226940269 : ℕ)^8275*50000000000000^6227 ≤ 21113094177431^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226940269 10000000000 21113094177431 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5434836129/10000000000 : ℝ)^8275 ≤ (44472530618797/100000000000000 : ℝ)^6227 := by
    have hnat : (5434836129 : ℕ)^8275*100000000000000^6227 ≤ 44472530618797^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434836129 10000000000 44472530618797 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-17531263/80000000 : ℝ), (5226940269/10000000000 : ℝ), (5434836129/10000000000 : ℝ)] ![(6650640503241/50000000000000 : ℝ), (21113094177431/50000000000000 : ℝ), (44472530618797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-17531263/80000000 : ℝ)|^8275 ≤ (6650640503241/50000000000000 : ℝ)^6227
        have hw : |(-17531263/80000000 : ℝ)|=(17531263/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5226940269/10000000000 : ℝ)|^8275 ≤ (21113094177431/50000000000000 : ℝ)^6227
        have hw : |(5226940269/10000000000 : ℝ)|=(5226940269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5434836129/10000000000 : ℝ)|^8275 ≤ (44472530618797/100000000000000 : ℝ)^6227
        have hw : |(5434836129/10000000000 : ℝ)|=(5434836129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s3_5 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5302418761/10000000000 : ℝ)*x 0 + (-2089930533/10000000000 : ℝ)*x 1 + (1358709033/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302418761/10000000000 : ℝ)^8275 ≤ (168118781029/390625000000 : ℝ)^6227 := by
    have hnat : (5302418761 : ℕ)^8275*390625000000^6227 ≤ 168118781029^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302418761 10000000000 168118781029 390625000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2089930533/10000000000 : ℝ)^8275 ≤ (12489061385429/100000000000000 : ℝ)^6227 := by
    have hnat : (2089930533 : ℕ)^8275*100000000000000^6227 ≤ 12489061385429^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2089930533 10000000000 12489061385429 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358709033/2500000000 : ℝ)^8275 ≤ (44472530651419/100000000000000 : ℝ)^6227 := by
    have hnat : (1358709033 : ℕ)^8275*100000000000000^6227 ≤ 44472530651419^6227*2500000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358709033 2500000000 44472530651419 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302418761/10000000000 : ℝ), (-2089930533/10000000000 : ℝ), (1358709033/2500000000 : ℝ)] ![(168118781029/390625000000 : ℝ), (12489061385429/100000000000000 : ℝ), (44472530651419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302418761/10000000000 : ℝ)|^8275 ≤ (168118781029/390625000000 : ℝ)^6227
        have hw : |(5302418761/10000000000 : ℝ)|=(5302418761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2089930533/10000000000 : ℝ)|^8275 ≤ (12489061385429/100000000000000 : ℝ)^6227
        have hw : |(-2089930533/10000000000 : ℝ)|=(2089930533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358709033/2500000000 : ℝ)|^8275 ≤ (44472530651419/100000000000000 : ℝ)^6227
        have hw : |(1358709033/2500000000 : ℝ)|=(1358709033/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s3_6 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2651209537/5000000000 : ℝ)*x 0 + (1358709107/2500000000 : ℝ)*x 1 + (-2089929703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651209537/5000000000 : ℝ)^8275 ≤ (43038411319527/100000000000000 : ℝ)^6227 := by
    have hnat : (2651209537 : ℕ)^8275*100000000000000^6227 ≤ 43038411319527^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651209537 5000000000 43038411319527 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1358709107/2500000000 : ℝ)^8275 ≤ (22236266935081/50000000000000 : ℝ)^6227 := by
    have hnat : (1358709107 : ℕ)^8275*50000000000000^6227 ≤ 22236266935081^6227*2500000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358709107 2500000000 22236266935081 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2089929703/10000000000 : ℝ)^8275 ≤ (12489054794219/100000000000000 : ℝ)^6227 := by
    have hnat : (2089929703 : ℕ)^8275*100000000000000^6227 ≤ 12489054794219^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2089929703 10000000000 12489054794219 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651209537/5000000000 : ℝ), (1358709107/2500000000 : ℝ), (-2089929703/10000000000 : ℝ)] ![(43038411319527/100000000000000 : ℝ), (22236266935081/50000000000000 : ℝ), (12489054794219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651209537/5000000000 : ℝ)|^8275 ≤ (43038411319527/100000000000000 : ℝ)^6227
        have hw : |(2651209537/5000000000 : ℝ)|=(2651209537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1358709107/2500000000 : ℝ)|^8275 ≤ (22236266935081/50000000000000 : ℝ)^6227
        have hw : |(1358709107/2500000000 : ℝ)|=(1358709107/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2089929703/10000000000 : ℝ)|^8275 ≤ (12489054794219/100000000000000 : ℝ)^6227
        have hw : |(-2089929703/10000000000 : ℝ)|=(2089929703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s3_7 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (43705593/100000000 : ℝ)*x 0 + (4579787923/10000000000 : ℝ)*x 1 + (4171046161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43705593/100000000 : ℝ)^8275 ≤ (16644974238283/50000000000000 : ℝ)^6227 := by
    have hnat : (43705593 : ℕ)^8275*50000000000000^6227 ≤ 16644974238283^6227*100000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43705593 100000000 16644974238283 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4579787923/10000000000 : ℝ)^8275 ≤ (8856063091153/25000000000000 : ℝ)^6227 := by
    have hnat : (4579787923 : ℕ)^8275*25000000000000^6227 ≤ 8856063091153^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4579787923 10000000000 8856063091153 25000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4171046161/10000000000 : ℝ)^8275 ≤ (31285799150253/100000000000000 : ℝ)^6227 := by
    have hnat : (4171046161 : ℕ)^8275*100000000000000^6227 ≤ 31285799150253^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171046161 10000000000 31285799150253 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(43705593/100000000 : ℝ), (4579787923/10000000000 : ℝ), (4171046161/10000000000 : ℝ)] ![(16644974238283/50000000000000 : ℝ), (8856063091153/25000000000000 : ℝ), (31285799150253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(43705593/100000000 : ℝ)|^8275 ≤ (16644974238283/50000000000000 : ℝ)^6227
        have hw : |(43705593/100000000 : ℝ)|=(43705593/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4579787923/10000000000 : ℝ)|^8275 ≤ (8856063091153/25000000000000 : ℝ)^6227
        have hw : |(4579787923/10000000000 : ℝ)|=(4579787923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4171046161/10000000000 : ℝ)|^8275 ≤ (31285799150253/100000000000000 : ℝ)^6227
        have hw : |(4171046161/10000000000 : ℝ)|=(4171046161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1082_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18538049/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16689/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (879/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (10449/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14883/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16689/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (879/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16689/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (879/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16689/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (879/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16689/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (879/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16689/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (879/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16689/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (879/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (879/10000 : ℝ) ^ (4137/1024 : ℝ) ≤ (1083187901361439/20000000000000000000 : ℝ) := by
    have hpowers : (879/10000 : ℝ)^4137 ≤ (1083187901361439/20000000000000000000 : ℝ)^1024 := by
      have hnat : (879 : ℕ)^4137*20000000000000000000^1024 ≤ 1083187901361439^1024*10000^4137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        879 10000 1083187901361439 20000000000000000000 4137 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (879/10000 : ℝ)) (X := (1083187901361439/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16689/100000 : ℝ) ^ (4137/1024 : ℝ) ≤ (9026057802992831/12500000000000000000 : ℝ) := by
    have hpowers : (16689/100000 : ℝ)^4137 ≤ (9026057802992831/12500000000000000000 : ℝ)^1024 := by
      have hnat : (16689 : ℕ)^4137*12500000000000000000^1024 ≤ 9026057802992831^1024*100000^4137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16689 100000 9026057802992831 12500000000000000000 4137 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16689/100000 : ℝ)) (X := (9026057802992831/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001083187901361439/10000000000000000000 : ℝ) ≤ (2500067025574719/2500000000000000 : ℝ) ^ (4137/1024 : ℝ) := by
    have hpowers : (10001083187901361439/10000000000000000000 : ℝ)^1024 ≤ (2500067025574719/2500000000000000 : ℝ)^4137 := by
      have hnat : (10001083187901361439 : ℕ)^1024*2500000000000000^4137 ≤ 2500067025574719^4137*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001083187901361439 10000000000000000000 2500067025574719 2500000000000000 1024 4137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500067025574719/2500000000000000 : ℝ)) (X := (10001083187901361439/10000000000000000000 : ℝ)) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100077624401930749843/100000000000000000000 : ℝ) ≤ (10001920816619711/10000000000000000 : ℝ) ^ (4137/1024 : ℝ) := by
    have hpowers : (100077624401930749843/100000000000000000000 : ℝ)^1024 ≤ (10001920816619711/10000000000000000 : ℝ)^4137 := by
      have hnat : (100077624401930749843 : ℕ)^1024*10000000000000000^4137 ≤ 10001920816619711^4137*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100077624401930749843 100000000000000000000 10001920816619711 10000000000000000 1024 4137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001920816619711/10000000000000000 : ℝ)) (X := (100077624401930749843/100000000000000000000 : ℝ)) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6259026057802992831/6250000000000000000 : ℝ) ≤ (5001786765470273/5000000000000000 : ℝ) ^ (4137/1024 : ℝ) := by
    have hpowers : (6259026057802992831/6250000000000000000 : ℝ)^1024 ≤ (5001786765470273/5000000000000000 : ℝ)^4137 := by
      have hnat : (6259026057802992831 : ℕ)^1024*5000000000000000^4137 ≤ 5001786765470273^4137*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6259026057802992831 6250000000000000000 5001786765470273 5000000000000000 1024 4137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001786765470273/5000000000000000 : ℝ)) (X := (6259026057802992831/6250000000000000000 : ℝ)) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1083187901361439/20000000000000000000 : ℝ) ≤ ((1645063812964552963/1645625000000000000 : ℝ)+2*(330542864167/157980000000000 : ℝ)*(879/10000 : ℝ))^(4137/1024 : ℝ) := by
    rw [show (1645063812964552963/1645625000000000000 : ℝ)+2*(330542864167/157980000000000 : ℝ)*(879/10000 : ℝ)=(2500067025574719/2500000000000000 : ℝ) by norm_num, show 1+2*(1083187901361439/20000000000000000000 : ℝ)=(10001083187901361439/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9026057802992831/12500000000000000000 : ℝ)+(1083187901361439/20000000000000000000 : ℝ) ≤ ((1645063812964552963/1645625000000000000 : ℝ)+(330542864167/157980000000000 : ℝ)*((16689/100000 : ℝ)+(879/10000 : ℝ)))^(4137/1024 : ℝ) := by
    rw [show (1645063812964552963/1645625000000000000 : ℝ)+(330542864167/157980000000000 : ℝ)*((16689/100000 : ℝ)+(879/10000 : ℝ))=(10001920816619711/10000000000000000 : ℝ) by norm_num, show 1+(9026057802992831/12500000000000000000 : ℝ)+(1083187901361439/20000000000000000000 : ℝ)=(100077624401930749843/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9026057802992831/12500000000000000000 : ℝ) ≤ ((1645063812964552963/1645625000000000000 : ℝ)+2*(330542864167/157980000000000 : ℝ)*(16689/100000 : ℝ))^(4137/1024 : ℝ) := by
    rw [show (1645063812964552963/1645625000000000000 : ℝ)+2*(330542864167/157980000000000 : ℝ)*(16689/100000 : ℝ)=(5001786765470273/5000000000000000 : ℝ) by norm_num, show 1+2*(9026057802992831/12500000000000000000 : ℝ)=(6259026057802992831/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1645063812964552963/1645625000000000000 : ℝ)*(X 1 0+X 2 0)+(330542864167/157980000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4137/1024 : ℝ)) (lo := (879/10000 : ℝ)) (hi := (16689/100000 : ℝ)) (c := (1645063812964552963/1645625000000000000 : ℝ)) (alpha := (330542864167/157980000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1645063812964552963/1645625000000000000 : ℝ)*(X 0 1+X 2 1)+(330542864167/157980000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4137/1024 : ℝ)) (lo := (879/10000 : ℝ)) (hi := (16689/100000 : ℝ)) (c := (1645063812964552963/1645625000000000000 : ℝ)) (alpha := (330542864167/157980000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1645063812964552963/1645625000000000000 : ℝ)*(X 0 2+X 1 2)+(330542864167/157980000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4137/1024 : ℝ)) (lo := (879/10000 : ℝ)) (hi := (16689/100000 : ℝ)) (c := (1645063812964552963/1645625000000000000 : ℝ)) (alpha := (330542864167/157980000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1095693033/5000000000 : ℝ)*X 0 0+(108713809/200000000 : ℝ)*X 0 1+(261304563/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5355281777/10000000000 : ℝ)*X 1 0+(-459735021/2000000000 : ℝ)*X 1 1+(5226091249/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2677640853/5000000000 : ℝ)*X 2 0+(326630729/625000000 : ℝ)*X 2 1+(-459734931/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((34964143/80000000 : ℝ)*X 0 0+(4169367269/10000000000 : ℝ)*X 0 1+(916291313/2000000000 : ℝ)*X 0 2+(34964143/80000000 : ℝ)*X 1 0+(4169367269/10000000000 : ℝ)*X 1 1+(916291313/2000000000 : ℝ)*X 1 2+(34964143/80000000 : ℝ)*X 2 0+(4169367269/10000000000 : ℝ)*X 2 1+(916291313/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-17531263/80000000 : ℝ)*X 0 0+(5226940269/10000000000 : ℝ)*X 0 1+(5434836129/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5302418761/10000000000 : ℝ)*X 1 0+(-2089930533/10000000000 : ℝ)*X 1 1+(1358709033/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2651209537/5000000000 : ℝ)*X 2 0+(1358709107/2500000000 : ℝ)*X 2 1+(-2089929703/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((43705593/100000000 : ℝ)*X 0 0+(4579787923/10000000000 : ℝ)*X 0 1+(4171046161/10000000000 : ℝ)*X 0 2+(43705593/100000000 : ℝ)*X 1 0+(4579787923/10000000000 : ℝ)*X 1 1+(4171046161/10000000000 : ℝ)*X 1 2+(43705593/100000000 : ℝ)*X 2 0+(4579787923/10000000000 : ℝ)*X 2 1+(4171046161/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (48107373166761640055421003/41140625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (164239757/25000000000000 : ℝ)*(base19) + (153516207/50000000000000 : ℝ)*(base23) + (86286941/50000000000000 : ℝ)*(lower2) + (897411/2500000000000 : ℝ)*(upper5) + (1799428055070973/50000000000000 : ℝ)*(major0) + (1799428055070973/50000000000000 : ℝ)*(major1) + (1799428055070973/50000000000000 : ℝ)*(major2) + (2385512603077003/50000000000000 : ℝ)*(sp0) + (477103932216189/10000000000000 : ℝ)*(sp1) + (4771043276257883/100000000000000 : ℝ)*(sp2) + (1213331627649181/50000000000000 : ℝ)*(sp3) + (18377136291/100000000000000 : ℝ)*(sp4) + (3604169379/100000000000000 : ℝ)*(sp5) + (5342717229/100000000000000 : ℝ)*(sp7) + (303333574751949/12500000000000 : ℝ)*(f.failure) + (4771043583290297/100000000000000 : ℝ)*(f.sum) + (11516873688311/7899000000000000000000000000 : ℝ)*base65 + (402194010433452253/246843750000000000000000000000000 : ℝ)*base68 + (559233817728235247/246843750000000000000000000000000 : ℝ)*base69 + (862956176615483503/246843750000000000000000000000000 : ℝ)*base72 + (681364728493/789900000000000000000000000 : ℝ)*base74 + (5231231270835703997/246843750000000000000000000000000 : ℝ)*base75 + (1562039180989172747/246843750000000000000000000000000 : ℝ)*base77 + (1698954224305078997/246843750000000000000000000000000 : ℝ)*base79 + (772476715073/987375000000000000000000000 : ℝ)*base82 + (2782501/156250000000000000000 : ℝ)*base89 + (2782501/156250000000000000000 : ℝ)*base91 + (2782501/156250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9719334856936679091751/2633000000000000000000000000 : ℝ) := by norm_num
    linear_combination (785840199/100000000000000 : ℝ)*(base19) + (16423451/1000000000000 : ℝ)*(base23) + (40806049/25000000000000 : ℝ)*(upper2) + (8763833/6250000000000 : ℝ)*(upper3) + (22224853/20000000000000 : ℝ)*(upper5) + (725663411100461/20000000000000 : ℝ)*(major0) + (725663411100461/20000000000000 : ℝ)*(major1) + (725663411100461/20000000000000 : ℝ)*(major2) + (1053777353/10000000000000 : ℝ)*(sp1) + (296739419/800000000000 : ℝ)*(sp2) + (4810100202566047/100000000000000 : ℝ)*(sp4) + (2405044439476159/50000000000000 : ℝ)*(sp5) + (1202515366948393/25000000000000 : ℝ)*(sp6) + (1223266892696713/50000000000000 : ℝ)*(sp7) + (1223266892696713/50000000000000 : ℝ)*(f.failure) + (4810100202566047/100000000000000 : ℝ)*(f.sum) + (4244882908589/789900000000000000000000000 : ℝ)*base66 + (932952921262745921/98737500000000000000000000000000 : ℝ)*base68 + (756790415307354079/98737500000000000000000000000000 : ℝ)*base69 + (648739176731908421/98737500000000000000000000000000 : ℝ)*base72 + (31866984123611/7899000000000000000000000000 : ℝ)*base74 + (707018729122141579/98737500000000000000000000000000 : ℝ)*base75 + (746380025978533421/98737500000000000000000000000000 : ℝ)*base78 + (1268271660355666579/98737500000000000000000000000000 : ℝ)*base79 + (26286441277/12342187500000000000000000 : ℝ)*base81 + (1482937/625000000000000000000 : ℝ)*base89 + (1482937/625000000000000000000 : ℝ)*base91 + (1482937/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1082_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18538049/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16689/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (879/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10449/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14883/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1082_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1082_s4_0 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-548728251/2500000000 : ℝ)*x 0 + (2702468381/5000000000 : ℝ)*x 1 + (5254540049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (548728251/2500000000 : ℝ)^8275 ≤ (3332390221731/25000000000000 : ℝ)^6227 := by
    have hnat : (548728251 : ℕ)^8275*25000000000000^6227 ≤ 3332390221731^6227*2500000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548728251 2500000000 3332390221731 25000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2702468381/5000000000 : ℝ)^8275 ≤ (44147695513529/100000000000000 : ℝ)^6227 := by
    have hnat : (2702468381 : ℕ)^8275*100000000000000^6227 ≤ 44147695513529^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702468381 5000000000 44147695513529 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254540049/10000000000 : ℝ)^8275 ≤ (42522743592463/100000000000000 : ℝ)^6227 := by
    have hnat : (5254540049 : ℕ)^8275*100000000000000^6227 ≤ 42522743592463^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254540049 10000000000 42522743592463 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-548728251/2500000000 : ℝ), (2702468381/5000000000 : ℝ), (5254540049/10000000000 : ℝ)] ![(3332390221731/25000000000000 : ℝ), (44147695513529/100000000000000 : ℝ), (42522743592463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-548728251/2500000000 : ℝ)|^8275 ≤ (3332390221731/25000000000000 : ℝ)^6227
        have hw : |(-548728251/2500000000 : ℝ)|=(548728251/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2702468381/5000000000 : ℝ)|^8275 ≤ (44147695513529/100000000000000 : ℝ)^6227
        have hw : |(2702468381/5000000000 : ℝ)|=(2702468381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254540049/10000000000 : ℝ)|^8275 ≤ (42522743592463/100000000000000 : ℝ)^6227
        have hw : |(5254540049/10000000000 : ℝ)|=(5254540049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s4_1 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5347649829/10000000000 : ℝ)*x 0 + (-45427867/200000000 : ℝ)*x 1 + (2627270211/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347649829/10000000000 : ℝ)^8275 ≤ (680108836757/1562500000000 : ℝ)^6227 := by
    have hnat : (5347649829 : ℕ)^8275*1562500000000^6227 ≤ 680108836757^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347649829 10000000000 680108836757 1562500000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (45427867/200000000 : ℝ)^8275 ≤ (13950286833759/100000000000000 : ℝ)^6227 := by
    have hnat : (45427867 : ℕ)^8275*100000000000000^6227 ≤ 13950286833759^6227*200000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45427867 200000000 13950286833759 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627270211/5000000000 : ℝ)^8275 ≤ (21261373801879/50000000000000 : ℝ)^6227 := by
    have hnat : (2627270211 : ℕ)^8275*50000000000000^6227 ≤ 21261373801879^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627270211 5000000000 21261373801879 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347649829/10000000000 : ℝ), (-45427867/200000000 : ℝ), (2627270211/5000000000 : ℝ)] ![(680108836757/1562500000000 : ℝ), (13950286833759/100000000000000 : ℝ), (21261373801879/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347649829/10000000000 : ℝ)|^8275 ≤ (680108836757/1562500000000 : ℝ)^6227
        have hw : |(5347649829/10000000000 : ℝ)|=(5347649829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-45427867/200000000 : ℝ)|^8275 ≤ (13950286833759/100000000000000 : ℝ)^6227
        have hw : |(-45427867/200000000 : ℝ)|=(45427867/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627270211/5000000000 : ℝ)|^8275 ≤ (21261373801879/50000000000000 : ℝ)^6227
        have hw : |(2627270211/5000000000 : ℝ)|=(2627270211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s4_2 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336912507/2500000000 : ℝ)*x 0 + (2627270089/5000000000 : ℝ)*x 1 + (-2271393407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336912507/2500000000 : ℝ)^8275 ≤ (1088174192623/2500000000000 : ℝ)^6227 := by
    have hnat : (1336912507 : ℕ)^8275*2500000000000^6227 ≤ 1088174192623^6227*2500000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336912507 2500000000 1088174192623 2500000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2627270089/5000000000 : ℝ)^8275 ≤ (42522744979747/100000000000000 : ℝ)^6227 := by
    have hnat : (2627270089 : ℕ)^8275*100000000000000^6227 ≤ 42522744979747^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627270089 5000000000 42522744979747 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2271393407/10000000000 : ℝ)^8275 ≤ (558011491959/4000000000000 : ℝ)^6227 := by
    have hnat : (2271393407 : ℕ)^8275*4000000000000^6227 ≤ 558011491959^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2271393407 10000000000 558011491959 4000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336912507/2500000000 : ℝ), (2627270089/5000000000 : ℝ), (-2271393407/10000000000 : ℝ)] ![(1088174192623/2500000000000 : ℝ), (42522744979747/100000000000000 : ℝ), (558011491959/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336912507/2500000000 : ℝ)|^8275 ≤ (1088174192623/2500000000000 : ℝ)^6227
        have hw : |(1336912507/2500000000 : ℝ)|=(1336912507/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2627270089/5000000000 : ℝ)|^8275 ≤ (42522744979747/100000000000000 : ℝ)^6227
        have hw : |(2627270089/5000000000 : ℝ)|=(2627270089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2271393407/10000000000 : ℝ)|^8275 ≤ (558011491959/4000000000000 : ℝ)^6227
        have hw : |(-2271393407/10000000000 : ℝ)|=(2271393407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s4_3 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (874523183/2000000000 : ℝ)*x 0 + (2113645519/5000000000 : ℝ)*x 1 + (4522983919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (874523183/2000000000 : ℝ)^8275 ≤ (33310767092011/100000000000000 : ℝ)^6227 := by
    have hnat : (874523183 : ℕ)^8275*100000000000000^6227 ≤ 33310767092011^6227*2000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874523183 2000000000 33310767092011 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2113645519/5000000000 : ℝ)^8275 ≤ (6369533211557/20000000000000 : ℝ)^6227 := by
    have hnat : (2113645519 : ℕ)^8275*20000000000000^6227 ≤ 6369533211557^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113645519 5000000000 6369533211557 20000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4522983919/10000000000 : ℝ)^8275 ≤ (34841566846129/100000000000000 : ℝ)^6227 := by
    have hnat : (4522983919 : ℕ)^8275*100000000000000^6227 ≤ 34841566846129^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4522983919 10000000000 34841566846129 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(874523183/2000000000 : ℝ), (2113645519/5000000000 : ℝ), (4522983919/10000000000 : ℝ)] ![(33310767092011/100000000000000 : ℝ), (6369533211557/20000000000000 : ℝ), (34841566846129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(874523183/2000000000 : ℝ)|^8275 ≤ (33310767092011/100000000000000 : ℝ)^6227
        have hw : |(874523183/2000000000 : ℝ)|=(874523183/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2113645519/5000000000 : ℝ)|^8275 ≤ (6369533211557/20000000000000 : ℝ)^6227
        have hw : |(2113645519/5000000000 : ℝ)|=(2113645519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4522983919/10000000000 : ℝ)|^8275 ≤ (34841566846129/100000000000000 : ℝ)^6227
        have hw : |(4522983919/10000000000 : ℝ)|=(4522983919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s4_4 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2194920203/10000000000 : ℝ)*x 0 + (2627489197/5000000000 : ℝ)*x 1 + (2702248551/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2194920203/10000000000 : ℝ)^8275 ≤ (1666202373097/12500000000000 : ℝ)^6227 := by
    have hnat : (2194920203 : ℕ)^8275*12500000000000^6227 ≤ 1666202373097^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2194920203 10000000000 1666202373097 12500000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2627489197/5000000000 : ℝ)^8275 ≤ (10631864420217/25000000000000 : ℝ)^6227 := by
    have hnat : (2627489197 : ℕ)^8275*25000000000000^6227 ≤ 10631864420217^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627489197 5000000000 10631864420217 25000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2702248551/5000000000 : ℝ)^8275 ≤ (11035730830943/25000000000000 : ℝ)^6227 := by
    have hnat : (2702248551 : ℕ)^8275*25000000000000^6227 ≤ 11035730830943^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702248551 5000000000 11035730830943 25000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2194920203/10000000000 : ℝ), (2627489197/5000000000 : ℝ), (2702248551/5000000000 : ℝ)] ![(1666202373097/12500000000000 : ℝ), (10631864420217/25000000000000 : ℝ), (11035730830943/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2194920203/10000000000 : ℝ)|^8275 ≤ (1666202373097/12500000000000 : ℝ)^6227
        have hw : |(-2194920203/10000000000 : ℝ)|=(2194920203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2627489197/5000000000 : ℝ)|^8275 ≤ (10631864420217/25000000000000 : ℝ)^6227
        have hw : |(2627489197/5000000000 : ℝ)|=(2627489197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2702248551/5000000000 : ℝ)|^8275 ≤ (11035730830943/25000000000000 : ℝ)^6227
        have hw : |(2702248551/5000000000 : ℝ)|=(2702248551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s4_5 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1327430581/2500000000 : ℝ)*x 0 + (-2121436103/10000000000 : ℝ)*x 1 + (5404497153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327430581/2500000000 : ℝ)^8275 ≤ (10779300997139/25000000000000 : ℝ)^6227 := by
    have hnat : (1327430581 : ℕ)^8275*25000000000000^6227 ≤ 10779300997139^6227*2500000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327430581 2500000000 10779300997139 25000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2121436103/10000000000 : ℝ)^8275 ≤ (12739872115397/100000000000000 : ℝ)^6227 := by
    have hnat : (2121436103 : ℕ)^8275*100000000000000^6227 ≤ 12739872115397^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121436103 10000000000 12739872115397 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5404497153/10000000000 : ℝ)^8275 ≤ (11035730969333/25000000000000 : ℝ)^6227 := by
    have hnat : (5404497153 : ℕ)^8275*25000000000000^6227 ≤ 11035730969333^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404497153 10000000000 11035730969333 25000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327430581/2500000000 : ℝ), (-2121436103/10000000000 : ℝ), (5404497153/10000000000 : ℝ)] ![(10779300997139/25000000000000 : ℝ), (12739872115397/100000000000000 : ℝ), (11035730969333/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327430581/2500000000 : ℝ)|^8275 ≤ (10779300997139/25000000000000 : ℝ)^6227
        have hw : |(1327430581/2500000000 : ℝ)|=(1327430581/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2121436103/10000000000 : ℝ)|^8275 ≤ (12739872115397/100000000000000 : ℝ)^6227
        have hw : |(-2121436103/10000000000 : ℝ)|=(2121436103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5404497153/10000000000 : ℝ)|^8275 ≤ (11035730969333/25000000000000 : ℝ)^6227
        have hw : |(5404497153/10000000000 : ℝ)|=(5404497153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s4_6 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (663715277/1250000000 : ℝ)*x 0 + (337781063/625000000 : ℝ)*x 1 + (-2121436447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663715277/1250000000 : ℝ)^8275 ≤ (5389650352889/12500000000000 : ℝ)^6227 := by
    have hnat : (663715277 : ℕ)^8275*12500000000000^6227 ≤ 5389650352889^6227*1250000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663715277 1250000000 5389650352889 12500000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337781063/625000000 : ℝ)^8275 ≤ (11035730575871/25000000000000 : ℝ)^6227 := by
    have hnat : (337781063 : ℕ)^8275*25000000000000^6227 ≤ 11035730575871^6227*625000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337781063 625000000 11035730575871 25000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2121436447/10000000000 : ℝ)^8275 ≤ (3184968715163/25000000000000 : ℝ)^6227 := by
    have hnat : (2121436447 : ℕ)^8275*25000000000000^6227 ≤ 3184968715163^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121436447 10000000000 3184968715163 25000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663715277/1250000000 : ℝ), (337781063/625000000 : ℝ), (-2121436447/10000000000 : ℝ)] ![(5389650352889/12500000000000 : ℝ), (11035730575871/25000000000000 : ℝ), (3184968715163/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663715277/1250000000 : ℝ)|^8275 ≤ (5389650352889/12500000000000 : ℝ)^6227
        have hw : |(663715277/1250000000 : ℝ)|=(663715277/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337781063/625000000 : ℝ)|^8275 ≤ (11035730575871/25000000000000 : ℝ)^6227
        have hw : |(337781063/625000000 : ℝ)|=(337781063/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2121436447/10000000000 : ℝ)|^8275 ≤ (3184968715163/25000000000000 : ℝ)^6227
        have hw : |(-2121436447/10000000000 : ℝ)|=(2121436447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s4_7 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4372631467/10000000000 : ℝ)*x 0 + (4522122637/10000000000 : ℝ)*x 1 + (4228155903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4372631467/10000000000 : ℝ)^8275 ≤ (3331092453341/10000000000000 : ℝ)^6227 := by
    have hnat : (4372631467 : ℕ)^8275*10000000000000^6227 ≤ 3331092453341^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4372631467 10000000000 3331092453341 10000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4522122637/10000000000 : ℝ)^8275 ≤ (34832750400351/100000000000000 : ℝ)^6227 := by
    have hnat : (4522122637 : ℕ)^8275*100000000000000^6227 ≤ 34832750400351^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4522122637 10000000000 34832750400351 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4228155903/10000000000 : ℝ)^8275 ≤ (7964081263407/25000000000000 : ℝ)^6227 := by
    have hnat : (4228155903 : ℕ)^8275*25000000000000^6227 ≤ 7964081263407^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4228155903 10000000000 7964081263407 25000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4372631467/10000000000 : ℝ), (4522122637/10000000000 : ℝ), (4228155903/10000000000 : ℝ)] ![(3331092453341/10000000000000 : ℝ), (34832750400351/100000000000000 : ℝ), (7964081263407/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4372631467/10000000000 : ℝ)|^8275 ≤ (3331092453341/10000000000000 : ℝ)^6227
        have hw : |(4372631467/10000000000 : ℝ)|=(4372631467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4522122637/10000000000 : ℝ)|^8275 ≤ (34832750400351/100000000000000 : ℝ)^6227
        have hw : |(4522122637/10000000000 : ℝ)|=(4522122637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4228155903/10000000000 : ℝ)|^8275 ≤ (7964081263407/25000000000000 : ℝ)^6227
        have hw : |(4228155903/10000000000 : ℝ)|=(4228155903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1082_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18538049/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14883/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10449/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (691/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14241/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14883/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10449/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14883/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10449/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14883/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10449/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14883/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10449/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14883/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10449/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14883/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10449/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10449/100000 : ℝ) ^ (4137/1024 : ℝ) ≤ (10889892396274117/100000000000000000000 : ℝ) := by
    have hpowers : (10449/100000 : ℝ)^4137 ≤ (10889892396274117/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10449 : ℕ)^4137*100000000000000000000^1024 ≤ 10889892396274117^1024*100000^4137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10449 100000 10889892396274117 100000000000000000000 4137 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10449/100000 : ℝ)) (X := (10889892396274117/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14883/100000 : ℝ) ^ (4137/1024 : ℝ) ≤ (45460816280274157/100000000000000000000 : ℝ) := by
    have hpowers : (14883/100000 : ℝ)^4137 ≤ (45460816280274157/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14883 : ℕ)^4137*100000000000000000000^1024 ≤ 45460816280274157^1024*100000^4137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14883 100000 45460816280274157 100000000000000000000 4137 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14883/100000 : ℝ)) (X := (45460816280274157/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010889892396274117/50000000000000000000 : ℝ) ≤ (10000539054201207/10000000000000000 : ℝ) ^ (4137/1024 : ℝ) := by
    have hpowers : (50010889892396274117/50000000000000000000 : ℝ)^1024 ≤ (10000539054201207/10000000000000000 : ℝ)^4137 := by
      have hnat : (50010889892396274117 : ℕ)^1024*10000000000000000^4137 ≤ 10000539054201207^4137*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010889892396274117 50000000000000000000 10000539054201207 10000000000000000 1024 4137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000539054201207/10000000000000000 : ℝ)) (X := (50010889892396274117/50000000000000000000 : ℝ)) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50028175354338274137/50000000000000000000 : ℝ) ≤ (2500348627603841/2500000000000000 : ℝ) ^ (4137/1024 : ℝ) := by
    have hpowers : (50028175354338274137/50000000000000000000 : ℝ)^1024 ≤ (2500348627603841/2500000000000000 : ℝ)^4137 := by
      have hnat : (50028175354338274137 : ℕ)^1024*2500000000000000^4137 ≤ 2500348627603841^4137*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028175354338274137 50000000000000000000 2500348627603841 2500000000000000 1024 4137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500348627603841/2500000000000000 : ℝ)) (X := (50028175354338274137/50000000000000000000 : ℝ)) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50045460816280274157/50000000000000000000 : ℝ) ≤ (10002249966629521/10000000000000000 : ℝ) ^ (4137/1024 : ℝ) := by
    have hpowers : (50045460816280274157/50000000000000000000 : ℝ)^1024 ≤ (10002249966629521/10000000000000000 : ℝ)^4137 := by
      have hnat : (50045460816280274157 : ℕ)^1024*10000000000000000^4137 ≤ 10002249966629521^4137*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50045460816280274157 50000000000000000000 10002249966629521 10000000000000000 1024 4137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002249966629521/10000000000000000 : ℝ)) (X := (50045460816280274157/50000000000000000000 : ℝ)) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10889892396274117/100000000000000000000 : ℝ) ≤ ((3693709403530391571/3695000000000000000 : ℝ)+2*(855456214157/443400000000000 : ℝ)*(10449/100000 : ℝ))^(4137/1024 : ℝ) := by
    rw [show (3693709403530391571/3695000000000000000 : ℝ)+2*(855456214157/443400000000000 : ℝ)*(10449/100000 : ℝ)=(10000539054201207/10000000000000000 : ℝ) by norm_num, show 1+2*(10889892396274117/100000000000000000000 : ℝ)=(50010889892396274117/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(45460816280274157/100000000000000000000 : ℝ)+(10889892396274117/100000000000000000000 : ℝ) ≤ ((3693709403530391571/3695000000000000000 : ℝ)+(855456214157/443400000000000 : ℝ)*((14883/100000 : ℝ)+(10449/100000 : ℝ)))^(4137/1024 : ℝ) := by
    rw [show (3693709403530391571/3695000000000000000 : ℝ)+(855456214157/443400000000000 : ℝ)*((14883/100000 : ℝ)+(10449/100000 : ℝ))=(2500348627603841/2500000000000000 : ℝ) by norm_num, show 1+(45460816280274157/100000000000000000000 : ℝ)+(10889892396274117/100000000000000000000 : ℝ)=(50028175354338274137/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(45460816280274157/100000000000000000000 : ℝ) ≤ ((3693709403530391571/3695000000000000000 : ℝ)+2*(855456214157/443400000000000 : ℝ)*(14883/100000 : ℝ))^(4137/1024 : ℝ) := by
    rw [show (3693709403530391571/3695000000000000000 : ℝ)+2*(855456214157/443400000000000 : ℝ)*(14883/100000 : ℝ)=(10002249966629521/10000000000000000 : ℝ) by norm_num, show 1+2*(45460816280274157/100000000000000000000 : ℝ)=(50045460816280274157/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3693709403530391571/3695000000000000000 : ℝ)*(X 1 0+X 2 0)+(855456214157/443400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4137/1024 : ℝ)) (lo := (10449/100000 : ℝ)) (hi := (14883/100000 : ℝ)) (c := (3693709403530391571/3695000000000000000 : ℝ)) (alpha := (855456214157/443400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3693709403530391571/3695000000000000000 : ℝ)*(X 0 1+X 2 1)+(855456214157/443400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4137/1024 : ℝ)) (lo := (10449/100000 : ℝ)) (hi := (14883/100000 : ℝ)) (c := (3693709403530391571/3695000000000000000 : ℝ)) (alpha := (855456214157/443400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3693709403530391571/3695000000000000000 : ℝ)*(X 0 2+X 1 2)+(855456214157/443400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4137/1024 : ℝ)) (lo := (10449/100000 : ℝ)) (hi := (14883/100000 : ℝ)) (c := (3693709403530391571/3695000000000000000 : ℝ)) (alpha := (855456214157/443400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-548728251/2500000000 : ℝ)*X 0 0+(2702468381/5000000000 : ℝ)*X 0 1+(5254540049/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347649829/10000000000 : ℝ)*X 1 0+(-45427867/200000000 : ℝ)*X 1 1+(2627270211/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336912507/2500000000 : ℝ)*X 2 0+(2627270089/5000000000 : ℝ)*X 2 1+(-2271393407/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((874523183/2000000000 : ℝ)*X 0 0+(2113645519/5000000000 : ℝ)*X 0 1+(4522983919/10000000000 : ℝ)*X 0 2+(874523183/2000000000 : ℝ)*X 1 0+(2113645519/5000000000 : ℝ)*X 1 1+(4522983919/10000000000 : ℝ)*X 1 2+(874523183/2000000000 : ℝ)*X 2 0+(2113645519/5000000000 : ℝ)*X 2 1+(4522983919/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2194920203/10000000000 : ℝ)*X 0 0+(2627489197/5000000000 : ℝ)*X 0 1+(2702248551/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1327430581/2500000000 : ℝ)*X 1 0+(-2121436103/10000000000 : ℝ)*X 1 1+(5404497153/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((663715277/1250000000 : ℝ)*X 2 0+(337781063/625000000 : ℝ)*X 2 1+(-2121436447/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4372631467/10000000000 : ℝ)*X 0 0+(4522122637/10000000000 : ℝ)*X 0 1+(4228155903/10000000000 : ℝ)*X 0 2+(4372631467/10000000000 : ℝ)*X 1 0+(4522122637/10000000000 : ℝ)*X 1 1+(4228155903/10000000000 : ℝ)*X 1 2+(4372631467/10000000000 : ℝ)*X 2 0+(4522122637/10000000000 : ℝ)*X 2 1+(4228155903/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (683022303936615081328681099/184750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1722331393/100000000000000 : ℝ)*(base19) + (1456227089/100000000000000 : ℝ)*(base23) + (450909291/100000000000000 : ℝ)*(upper3) + (137310869/50000000000000 : ℝ)*(upper4) + (44422307/100000000000000 : ℝ)*(upper5) + (5015550507767923/100000000000000 : ℝ)*(major0) + (5015550507767923/100000000000000 : ℝ)*(major1) + (5015550507767923/100000000000000 : ℝ)*(major2) + (207785314518993/3125000000000 : ℝ)*(sp0) + (6649169316020227/100000000000000 : ℝ)*(sp1) + (1662292395531133/25000000000000 : ℝ)*(sp2) + (845475822667337/25000000000000 : ℝ)*(sp3) + (10243435961/25000000000000 : ℝ)*(sp4) + (26563281251/100000000000000 : ℝ)*(sp7) + (1690964926975299/50000000000000 : ℝ)*(f.failure) + (6649171038351621/100000000000000 : ℝ)*(f.sum) + (86137495200259/22170000000000000000000000000 : ℝ)*base66 + (15412449383746406099/1108500000000000000000000000000000 : ℝ)*base67 + (8535758098693406099/1108500000000000000000000000000000 : ℝ)*base69 + (8468121152172093901/1108500000000000000000000000000000 : ℝ)*base72 + (5802116038459/22170000000000000000000000000 : ℝ)*base74 + (8628205666303593901/1108500000000000000000000000000000 : ℝ)*base76 + (17305300100032593901/1108500000000000000000000000000000 : ℝ)*base78 + (5504367919261593901/1108500000000000000000000000000000 : ℝ)*base80 + (187428560463941/22170000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (4098349/625000000000000000000 : ℝ)*base90 + (4098349/625000000000000000000 : ℝ)*base92 + (4098349/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (36416084336897391543773/3695000000000000000000000000 : ℝ) := by norm_num
    linear_combination (144526141/6250000000000 : ℝ)*(base19) + (322624231/12500000000000 : ℝ)*(base23) + (103150231/100000000000000 : ℝ)*(upper3) + (61066543/25000000000000 : ℝ)*(lower4) + (10892943/6250000000000 : ℝ)*(upper5) + (2522465728449611/50000000000000 : ℝ)*(major0) + (2522465728449611/50000000000000 : ℝ)*(major1) + (2522465728449611/50000000000000 : ℝ)*(major2) + (13252244841/20000000000000 : ℝ)*(sp1) + (14625414297/25000000000000 : ℝ)*(sp2) + (6688121484519641/100000000000000 : ℝ)*(sp4) + (334402645543859/5000000000000 : ℝ)*(sp5) + (3344030200934303/50000000000000 : ℝ)*(sp6) + (170087055038101/5000000000000 : ℝ)*(sp7) + (170087055038101/5000000000000 : ℝ)*(f.failure) + (6688121484519641/100000000000000 : ℝ)*(f.sum) + (24428236238741/5542500000000000000000000000 : ℝ)*base65 + (4720021737591561643/554250000000000000000000000000000 : ℝ)*base67 + (1732557398687438357/554250000000000000000000000000000 : ℝ)*base70 + (3678376862969811643/554250000000000000000000000000000 : ℝ)*base71 + (38927591054677/11085000000000000000000000000 : ℝ)*base73 + (3381284172573561643/554250000000000000000000000000000 : ℝ)*base75 + (2074003697583938357/554250000000000000000000000000000 : ℝ)*base78 + (2895924052779938357/554250000000000000000000000000000 : ℝ)*base80 + (7023959680343/11085000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (545051/62500000000000000000 : ℝ)*base90 + (545051/62500000000000000000 : ℝ)*base92 + (545051/62500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1082_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18538049/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14883/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10449/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (691/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14241/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1082_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1082_s5_0 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-8576937/39062500 : ℝ)*x 0 + (1349136369/2500000000 : ℝ)*x 1 + (105248359/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8576937/39062500 : ℝ)^8275 ≤ (533435168313/4000000000000 : ℝ)^6227 := by
    have hnat : (8576937 : ℕ)^8275*4000000000000^6227 ≤ 533435168313^6227*39062500^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8576937 39062500 533435168313 4000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1349136369/2500000000 : ℝ)^8275 ≤ (44056636246233/100000000000000 : ℝ)^6227 := by
    have hnat : (1349136369 : ℕ)^8275*100000000000000^6227 ≤ 44056636246233^6227*2500000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349136369 2500000000 44056636246233 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105248359/200000000 : ℝ)^8275 ≤ (21303742263677/50000000000000 : ℝ)^6227 := by
    have hnat : (105248359 : ℕ)^8275*50000000000000^6227 ≤ 21303742263677^6227*200000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105248359 200000000 21303742263677 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-8576937/39062500 : ℝ), (1349136369/2500000000 : ℝ), (105248359/200000000 : ℝ)] ![(533435168313/4000000000000 : ℝ), (44056636246233/100000000000000 : ℝ), (21303742263677/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-8576937/39062500 : ℝ)|^8275 ≤ (533435168313/4000000000000 : ℝ)^6227
        have hw : |(-8576937/39062500 : ℝ)|=(8576937/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1349136369/2500000000 : ℝ)|^8275 ≤ (44056636246233/100000000000000 : ℝ)^6227
        have hw : |(1349136369/2500000000 : ℝ)|=(1349136369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(105248359/200000000 : ℝ)|^8275 ≤ (21303742263677/50000000000000 : ℝ)^6227
        have hw : |(105248359/200000000 : ℝ)|=(105248359/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s5_1 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345557679/10000000000 : ℝ)*x 0 + (-565945137/2500000000 : ℝ)*x 1 + (5262417047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345557679/10000000000 : ℝ)^8275 ≤ (21752168690987/50000000000000 : ℝ)^6227 := by
    have hnat : (5345557679 : ℕ)^8275*50000000000000^6227 ≤ 21752168690987^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345557679 10000000000 21752168690987 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (565945137/2500000000 : ℝ)^8275 ≤ (277763755981/2000000000000 : ℝ)^6227 := by
    have hnat : (565945137 : ℕ)^8275*2000000000000^6227 ≤ 277763755981^6227*2500000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565945137 2500000000 277763755981 2000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5262417047/10000000000 : ℝ)^8275 ≤ (42607474811579/100000000000000 : ℝ)^6227 := by
    have hnat : (5262417047 : ℕ)^8275*100000000000000^6227 ≤ 42607474811579^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262417047 10000000000 42607474811579 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345557679/10000000000 : ℝ), (-565945137/2500000000 : ℝ), (5262417047/10000000000 : ℝ)] ![(21752168690987/50000000000000 : ℝ), (277763755981/2000000000000 : ℝ), (42607474811579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345557679/10000000000 : ℝ)|^8275 ≤ (21752168690987/50000000000000 : ℝ)^6227
        have hw : |(5345557679/10000000000 : ℝ)|=(5345557679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-565945137/2500000000 : ℝ)|^8275 ≤ (277763755981/2000000000000 : ℝ)^6227
        have hw : |(-565945137/2500000000 : ℝ)|=(565945137/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5262417047/10000000000 : ℝ)|^8275 ≤ (42607474811579/100000000000000 : ℝ)^6227
        have hw : |(5262417047/10000000000 : ℝ)|=(5262417047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s5_2 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336389401/2500000000 : ℝ)*x 0 + (657802237/1250000000 : ℝ)*x 1 + (-90551181/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336389401/2500000000 : ℝ)^8275 ≤ (8700867314169/20000000000000 : ℝ)^6227 := by
    have hnat : (1336389401 : ℕ)^8275*20000000000000^6227 ≤ 8700867314169^6227*2500000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336389401 2500000000 8700867314169 20000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (657802237/1250000000 : ℝ)^8275 ≤ (5325935493293/12500000000000 : ℝ)^6227 := by
    have hnat : (657802237 : ℕ)^8275*12500000000000^6227 ≤ 5325935493293^6227*1250000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657802237 1250000000 5325935493293 12500000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (90551181/400000000 : ℝ)^8275 ≤ (13888179458859/100000000000000 : ℝ)^6227 := by
    have hnat : (90551181 : ℕ)^8275*100000000000000^6227 ≤ 13888179458859^6227*400000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90551181 400000000 13888179458859 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336389401/2500000000 : ℝ), (657802237/1250000000 : ℝ), (-90551181/400000000 : ℝ)] ![(8700867314169/20000000000000 : ℝ), (5325935493293/12500000000000 : ℝ), (13888179458859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336389401/2500000000 : ℝ)|^8275 ≤ (8700867314169/20000000000000 : ℝ)^6227
        have hw : |(1336389401/2500000000 : ℝ)|=(1336389401/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(657802237/1250000000 : ℝ)|^8275 ≤ (5325935493293/12500000000000 : ℝ)^6227
        have hw : |(657802237/1250000000 : ℝ)|=(657802237/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-90551181/400000000 : ℝ)|^8275 ≤ (13888179458859/100000000000000 : ℝ)^6227
        have hw : |(-90551181/400000000 : ℝ)|=(90551181/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s5_3 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1093267989/2500000000 : ℝ)*x 0 + (848644881/2000000000 : ℝ)*x 1 + (450693091/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093267989/2500000000 : ℝ)^8275 ≤ (33315383920881/100000000000000 : ℝ)^6227 := by
    have hnat : (1093267989 : ℕ)^8275*100000000000000^6227 ≤ 33315383920881^6227*2500000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093267989 2500000000 33315383920881 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (848644881/2000000000 : ℝ)^8275 ≤ (2000455234509/6250000000000 : ℝ)^6227 := by
    have hnat : (848644881 : ℕ)^8275*6250000000000^6227 ≤ 2000455234509^6227*2000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848644881 2000000000 2000455234509 6250000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (450693091/1000000000 : ℝ)^8275 ≤ (4334666539711/12500000000000 : ℝ)^6227 := by
    have hnat : (450693091 : ℕ)^8275*12500000000000^6227 ≤ 4334666539711^6227*1000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450693091 1000000000 4334666539711 12500000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1093267989/2500000000 : ℝ), (848644881/2000000000 : ℝ), (450693091/1000000000 : ℝ)] ![(33315383920881/100000000000000 : ℝ), (2000455234509/6250000000000 : ℝ), (4334666539711/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1093267989/2500000000 : ℝ)|^8275 ≤ (33315383920881/100000000000000 : ℝ)^6227
        have hw : |(1093267989/2500000000 : ℝ)|=(1093267989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(848644881/2000000000 : ℝ)|^8275 ≤ (2000455234509/6250000000000 : ℝ)^6227
        have hw : |(848644881/2000000000 : ℝ)|=(848644881/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(450693091/1000000000 : ℝ)|^8275 ≤ (4334666539711/12500000000000 : ℝ)^6227
        have hw : |(450693091/1000000000 : ℝ)|=(450693091/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s5_4 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2195701583/10000000000 : ℝ)*x 0 + (5262766351/10000000000 : ℝ)*x 1 + (5396195691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2195701583/10000000000 : ℝ)^8275 ≤ (333398132563/2500000000000 : ℝ)^6227 := by
    have hnat : (2195701583 : ℕ)^8275*2500000000000^6227 ≤ 333398132563^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2195701583 10000000000 333398132563 2500000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5262766351/10000000000 : ℝ)^8275 ≤ (21305616584023/50000000000000 : ℝ)^6227 := by
    have hnat : (5262766351 : ℕ)^8275*50000000000000^6227 ≤ 21305616584023^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262766351 10000000000 21305616584023 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396195691/10000000000 : ℝ)^8275 ≤ (44052841513589/100000000000000 : ℝ)^6227 := by
    have hnat : (5396195691 : ℕ)^8275*100000000000000^6227 ≤ 44052841513589^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396195691 10000000000 44052841513589 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2195701583/10000000000 : ℝ), (5262766351/10000000000 : ℝ), (5396195691/10000000000 : ℝ)] ![(333398132563/2500000000000 : ℝ), (21305616584023/50000000000000 : ℝ), (44052841513589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2195701583/10000000000 : ℝ)|^8275 ≤ (333398132563/2500000000000 : ℝ)^6227
        have hw : |(-2195701583/10000000000 : ℝ)|=(2195701583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5262766351/10000000000 : ℝ)|^8275 ≤ (21305616584023/50000000000000 : ℝ)^6227
        have hw : |(5262766351/10000000000 : ℝ)|=(5262766351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5396195691/10000000000 : ℝ)|^8275 ≤ (44052841513589/100000000000000 : ℝ)^6227
        have hw : |(5396195691/10000000000 : ℝ)|=(5396195691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s5_5 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (663966357/1250000000 : ℝ)*x 0 + (-532500569/2500000000 : ℝ)*x 1 + (5396195679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663966357/1250000000 : ℝ)^8275 ≤ (2696179982261/6250000000000 : ℝ)^6227 := by
    have hnat : (663966357 : ℕ)^8275*6250000000000^6227 ≤ 2696179982261^6227*1250000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663966357 1250000000 2696179982261 6250000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (532500569/2500000000 : ℝ)^8275 ≤ (6404139444961/50000000000000 : ℝ)^6227 := by
    have hnat : (532500569 : ℕ)^8275*50000000000000^6227 ≤ 6404139444961^6227*2500000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532500569 2500000000 6404139444961 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396195679/10000000000 : ℝ)^8275 ≤ (8810568276681/20000000000000 : ℝ)^6227 := by
    have hnat : (5396195679 : ℕ)^8275*20000000000000^6227 ≤ 8810568276681^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396195679 10000000000 8810568276681 20000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663966357/1250000000 : ℝ), (-532500569/2500000000 : ℝ), (5396195679/10000000000 : ℝ)] ![(2696179982261/6250000000000 : ℝ), (6404139444961/50000000000000 : ℝ), (8810568276681/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663966357/1250000000 : ℝ)|^8275 ≤ (2696179982261/6250000000000 : ℝ)^6227
        have hw : |(663966357/1250000000 : ℝ)|=(663966357/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-532500569/2500000000 : ℝ)|^8275 ≤ (6404139444961/50000000000000 : ℝ)^6227
        have hw : |(-532500569/2500000000 : ℝ)|=(532500569/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5396195679/10000000000 : ℝ)|^8275 ≤ (8810568276681/20000000000000 : ℝ)^6227
        have hw : |(5396195679/10000000000 : ℝ)|=(5396195679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s5_6 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (531173087/1000000000 : ℝ)*x 0 + (5396195663/10000000000 : ℝ)*x 1 + (-2130002279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531173087/1000000000 : ℝ)^8275 ≤ (43138879867271/100000000000000 : ℝ)^6227 := by
    have hnat : (531173087 : ℕ)^8275*100000000000000^6227 ≤ 43138879867271^6227*1000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531173087 1000000000 43138879867271 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396195663/10000000000 : ℝ)^8275 ≤ (44052841209827/100000000000000 : ℝ)^6227 := by
    have hnat : (5396195663 : ℕ)^8275*100000000000000^6227 ≤ 44052841209827^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396195663 10000000000 44052841209827 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2130002279/10000000000 : ℝ)^8275 ≤ (2561655782779/20000000000000 : ℝ)^6227 := by
    have hnat : (2130002279 : ℕ)^8275*20000000000000^6227 ≤ 2561655782779^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130002279 10000000000 2561655782779 20000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531173087/1000000000 : ℝ), (5396195663/10000000000 : ℝ), (-2130002279/10000000000 : ℝ)] ![(43138879867271/100000000000000 : ℝ), (44052841209827/100000000000000 : ℝ), (2561655782779/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531173087/1000000000 : ℝ)|^8275 ≤ (43138879867271/100000000000000 : ℝ)^6227
        have hw : |(531173087/1000000000 : ℝ)|=(531173087/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396195663/10000000000 : ℝ)|^8275 ≤ (44052841209827/100000000000000 : ℝ)^6227
        have hw : |(5396195663/10000000000 : ℝ)|=(5396195663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2130002279/10000000000 : ℝ)|^8275 ≤ (2561655782779/20000000000000 : ℝ)^6227
        have hw : |(-2130002279/10000000000 : ℝ)|=(2130002279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s5_7 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4373082777/10000000000 : ℝ)*x 0 + (901249183/2000000000 : ℝ)*x 1 + (4243912153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4373082777/10000000000 : ℝ)^8275 ≤ (16657746735759/50000000000000 : ℝ)^6227 := by
    have hnat : (4373082777 : ℕ)^8275*50000000000000^6227 ≤ 16657746735759^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4373082777 10000000000 16657746735759 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (901249183/2000000000 : ℝ)^8275 ≤ (3467032857047/10000000000000 : ℝ)^6227 := by
    have hnat : (901249183 : ℕ)^8275*10000000000000^6227 ≤ 3467032857047^6227*2000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901249183 2000000000 3467032857047 10000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4243912153/10000000000 : ℝ)^8275 ≤ (32014177936101/100000000000000 : ℝ)^6227 := by
    have hnat : (4243912153 : ℕ)^8275*100000000000000^6227 ≤ 32014177936101^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4243912153 10000000000 32014177936101 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4373082777/10000000000 : ℝ), (901249183/2000000000 : ℝ), (4243912153/10000000000 : ℝ)] ![(16657746735759/50000000000000 : ℝ), (3467032857047/10000000000000 : ℝ), (32014177936101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4373082777/10000000000 : ℝ)|^8275 ≤ (16657746735759/50000000000000 : ℝ)^6227
        have hw : |(4373082777/10000000000 : ℝ)|=(4373082777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(901249183/2000000000 : ℝ)|^8275 ≤ (3467032857047/10000000000000 : ℝ)^6227
        have hw : |(901249183/2000000000 : ℝ)|=(901249183/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4243912153/10000000000 : ℝ)|^8275 ≤ (32014177936101/100000000000000 : ℝ)^6227
        have hw : |(4243912153/10000000000 : ℝ)|=(4243912153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1082_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18538049/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14241/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (691/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (1403/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2813/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14241/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (691/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14241/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (691/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14241/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (691/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14241/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (691/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14241/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (691/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14241/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (691/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (691/6250 : ℝ) ^ (4137/1024 : ℝ) ≤ (3420099102259603/25000000000000000000 : ℝ) := by
    have hpowers : (691/6250 : ℝ)^4137 ≤ (3420099102259603/25000000000000000000 : ℝ)^1024 := by
      have hnat : (691 : ℕ)^4137*25000000000000000000^1024 ≤ 3420099102259603^1024*6250^4137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        691 6250 3420099102259603 25000000000000000000 4137 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (691/6250 : ℝ)) (X := (3420099102259603/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14241/100000 : ℝ) ^ (4137/1024 : ℝ) ≤ (38042627110563551/100000000000000000000 : ℝ) := by
    have hpowers : (14241/100000 : ℝ)^4137 ≤ (38042627110563551/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14241 : ℕ)^4137*100000000000000000000^1024 ≤ 38042627110563551^1024*100000^4137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14241 100000 38042627110563551 100000000000000000000 4137 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14241/100000 : ℝ)) (X := (38042627110563551/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503420099102259603/12500000000000000000 : ℝ) ≤ (2000135434218691/2000000000000000 : ℝ) ^ (4137/1024 : ℝ) := by
    have hpowers : (12503420099102259603/12500000000000000000 : ℝ)^1024 ≤ (2000135434218691/2000000000000000 : ℝ)^4137 := by
      have hnat : (12503420099102259603 : ℕ)^1024*2000000000000000^4137 ≤ 2000135434218691^4137*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503420099102259603 12500000000000000000 2000135434218691 2000000000000000 1024 4137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000135434218691/2000000000000000 : ℝ)) (X := (12503420099102259603/12500000000000000000 : ℝ)) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051723023519601963/100000000000000000000 : ℝ) ≤ (10001280011414521/10000000000000000 : ℝ) ^ (4137/1024 : ℝ) := by
    have hpowers : (100051723023519601963/100000000000000000000 : ℝ)^1024 ≤ (10001280011414521/10000000000000000 : ℝ)^4137 := by
      have hnat : (100051723023519601963 : ℕ)^1024*10000000000000000^4137 ≤ 10001280011414521^4137*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051723023519601963 100000000000000000000 10001280011414521 10000000000000000 1024 4137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001280011414521/10000000000000000 : ℝ)) (X := (100051723023519601963/100000000000000000000 : ℝ)) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50038042627110563551/50000000000000000000 : ℝ) ≤ (10001882851735587/10000000000000000 : ℝ) ^ (4137/1024 : ℝ) := by
    have hpowers : (50038042627110563551/50000000000000000000 : ℝ)^1024 ≤ (10001882851735587/10000000000000000 : ℝ)^4137 := by
      have hnat : (50038042627110563551 : ℕ)^1024*10000000000000000^4137 ≤ 10001882851735587^4137*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50038042627110563551 50000000000000000000 10001882851735587 10000000000000000 1024 4137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001882851735587/10000000000000000 : ℝ)) (X := (50038042627110563551/50000000000000000000 : ℝ)) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3420099102259603/25000000000000000000 : ℝ) ≤ ((31838826784753242783/31850000000000000000 : ℝ)+2*(301420160533/159250000000000 : ℝ)*(691/6250 : ℝ))^(4137/1024 : ℝ) := by
    rw [show (31838826784753242783/31850000000000000000 : ℝ)+2*(301420160533/159250000000000 : ℝ)*(691/6250 : ℝ)=(2000135434218691/2000000000000000 : ℝ) by norm_num, show 1+2*(3420099102259603/25000000000000000000 : ℝ)=(12503420099102259603/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(38042627110563551/100000000000000000000 : ℝ)+(3420099102259603/25000000000000000000 : ℝ) ≤ ((31838826784753242783/31850000000000000000 : ℝ)+(301420160533/159250000000000 : ℝ)*((14241/100000 : ℝ)+(691/6250 : ℝ)))^(4137/1024 : ℝ) := by
    rw [show (31838826784753242783/31850000000000000000 : ℝ)+(301420160533/159250000000000 : ℝ)*((14241/100000 : ℝ)+(691/6250 : ℝ))=(10001280011414521/10000000000000000 : ℝ) by norm_num, show 1+(38042627110563551/100000000000000000000 : ℝ)+(3420099102259603/25000000000000000000 : ℝ)=(100051723023519601963/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(38042627110563551/100000000000000000000 : ℝ) ≤ ((31838826784753242783/31850000000000000000 : ℝ)+2*(301420160533/159250000000000 : ℝ)*(14241/100000 : ℝ))^(4137/1024 : ℝ) := by
    rw [show (31838826784753242783/31850000000000000000 : ℝ)+2*(301420160533/159250000000000 : ℝ)*(14241/100000 : ℝ)=(10001882851735587/10000000000000000 : ℝ) by norm_num, show 1+2*(38042627110563551/100000000000000000000 : ℝ)=(50038042627110563551/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (31838826784753242783/31850000000000000000 : ℝ)*(X 1 0+X 2 0)+(301420160533/159250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4137/1024 : ℝ)) (lo := (691/6250 : ℝ)) (hi := (14241/100000 : ℝ)) (c := (31838826784753242783/31850000000000000000 : ℝ)) (alpha := (301420160533/159250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (31838826784753242783/31850000000000000000 : ℝ)*(X 0 1+X 2 1)+(301420160533/159250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4137/1024 : ℝ)) (lo := (691/6250 : ℝ)) (hi := (14241/100000 : ℝ)) (c := (31838826784753242783/31850000000000000000 : ℝ)) (alpha := (301420160533/159250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (31838826784753242783/31850000000000000000 : ℝ)*(X 0 2+X 1 2)+(301420160533/159250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4137/1024 : ℝ)) (lo := (691/6250 : ℝ)) (hi := (14241/100000 : ℝ)) (c := (31838826784753242783/31850000000000000000 : ℝ)) (alpha := (301420160533/159250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-8576937/39062500 : ℝ)*X 0 0+(1349136369/2500000000 : ℝ)*X 0 1+(105248359/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345557679/10000000000 : ℝ)*X 1 0+(-565945137/2500000000 : ℝ)*X 1 1+(5262417047/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336389401/2500000000 : ℝ)*X 2 0+(657802237/1250000000 : ℝ)*X 2 1+(-90551181/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1093267989/2500000000 : ℝ)*X 0 0+(848644881/2000000000 : ℝ)*X 0 1+(450693091/1000000000 : ℝ)*X 0 2+(1093267989/2500000000 : ℝ)*X 1 0+(848644881/2000000000 : ℝ)*X 1 1+(450693091/1000000000 : ℝ)*X 1 2+(1093267989/2500000000 : ℝ)*X 2 0+(848644881/2000000000 : ℝ)*X 2 1+(450693091/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2195701583/10000000000 : ℝ)*X 0 0+(5262766351/10000000000 : ℝ)*X 0 1+(5396195691/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((663966357/1250000000 : ℝ)*X 1 0+(-532500569/2500000000 : ℝ)*X 1 1+(5396195679/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((531173087/1000000000 : ℝ)*X 2 0+(5396195663/10000000000 : ℝ)*X 2 1+(-2130002279/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4373082777/10000000000 : ℝ)*X 0 0+(901249183/2000000000 : ℝ)*X 0 1+(4243912153/10000000000 : ℝ)*X 0 2+(4373082777/10000000000 : ℝ)*X 1 0+(901249183/2000000000 : ℝ)*X 1 1+(4243912153/10000000000 : ℝ)*X 1 2+(4373082777/10000000000 : ℝ)*X 2 0+(901249183/2000000000 : ℝ)*X 2 1+(4243912153/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (64181248004889712799757573/28437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1803882309/100000000000000 : ℝ)*(base19) + (207586663/12500000000000 : ℝ)*(base23) + (177953201/100000000000000 : ℝ)*(lower2) + (5154219/6250000000000 : ℝ)*(upper5) + (1405981377149861/25000000000000 : ℝ)*(major0) + (1405981377149861/25000000000000 : ℝ)*(major1) + (1405981377149861/25000000000000 : ℝ)*(major2) + (7455640533179739/100000000000000 : ℝ)*(sp0) + (1863913071501583/25000000000000 : ℝ)*(sp1) + (1863924734789973/25000000000000 : ℝ)*(sp2) + (948030471297929/25000000000000 : ℝ)*(sp3) + (60066673457/100000000000000 : ℝ)*(sp4) + (9301992911/20000000000000 : ℝ)*(sp5) + (28456923199/100000000000000 : ℝ)*(sp7) + (1896075171057457/50000000000000 : ℝ)*(f.failure) + (1863925149963299/25000000000000 : ℝ)*(f.sum) + (4980600773231/995312500000000000000000000 : ℝ)*base66 + (6921713248425303163/796250000000000000000000000000000 : ℝ)*base67 + (2519883514305303163/796250000000000000000000000000000 : ℝ)*base69 + (3894487344158446837/796250000000000000000000000000000 : ℝ)*base72 + (4150517449479/15925000000000000000000000000 : ℝ)*base73 + (16260363189500303163/796250000000000000000000000000000 : ℝ)*base75 + (1259331346316553163/796250000000000000000000000000000 : ℝ)*base77 + (9735285666104053163/796250000000000000000000000000000 : ℝ)*base79 + (36418639146671/15925000000000000000000000000 : ℝ)*base82 + (5318607/625000000000000000000 : ℝ)*base90 + (5318607/625000000000000000000 : ℝ)*base92 + (5318607/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14731848139829744192670011601/1592500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (857034271/50000000000000 : ℝ)*(base19) + (1894529613/100000000000000 : ℝ)*(base23) + (44266277/25000000000000 : ℝ)*(upper3) + (1867909/2500000000000 : ℝ)*(lower4) + (194332853/100000000000000 : ℝ)*(upper5) + (5653269959947451/100000000000000 : ℝ)*(major0) + (5653269959947451/100000000000000 : ℝ)*(major1) + (5653269959947451/100000000000000 : ℝ)*(major2) + (22539660327/50000000000000 : ℝ)*(sp1) + (48227028197/100000000000000 : ℝ)*(sp2) + (3747301316329227/50000000000000 : ℝ)*(sp4) + (7494555839269259/100000000000000 : ℝ)*(sp5) + (7494552511100643/100000000000000 : ℝ)*(sp6) + (59561515294961/1562500000000 : ℝ)*(sp7) + (59561515294961/1562500000000 : ℝ)*(f.failure) + (3747301316329227/50000000000000 : ℝ)*(f.sum) + (963925776269/248828125000000000000000000 : ℝ)*base65 + (9269644351288403867/3185000000000000000000000000000000 : ℝ)*base68 + (16966314404991596133/3185000000000000000000000000000000 : ℝ)*base69 + (46846141716871596133/3185000000000000000000000000000000 : ℝ)*base71 + (30224427959967/7962500000000000000000000000 : ℝ)*base74 + (145413043733403867/3185000000000000000000000000000000 : ℝ)*base76 + (1363858781691596133/3185000000000000000000000000000000 : ℝ)*base77 + (59158031206316596133/3185000000000000000000000000000000 : ℝ)*base79 + (10774841191371/3981250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (104697/39062500000000000000 : ℝ)*base90 + (104697/39062500000000000000 : ℝ)*base92 + (104697/39062500000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1082_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18538049/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14241/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (691/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1403/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2813/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1082_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1082_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18538049/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16689/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (879/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1403/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2813/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1082_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1082_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1082_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18538049/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16689/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (879/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1403/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2813/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1082_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
