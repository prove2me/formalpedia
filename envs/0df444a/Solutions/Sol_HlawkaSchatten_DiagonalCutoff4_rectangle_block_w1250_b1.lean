-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1250_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:23:09.836488+00:00
-- url     : https://prove2.me/submissions/69ea203f-6835-4a62-8d2b-4cc2b38c2faa

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
theorem support_rectangle_w1250_s3_0 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-16511759/78125000 : ℝ)*x 0 + (2709478773/5000000000 : ℝ)*x 1 + (5241234041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16511759/78125000 : ℝ)^8443 ≤ (2569599770707/20000000000000 : ℝ)^6395 := by
    have hnat : (16511759 : ℕ)^8443*20000000000000^6395 ≤ 2569599770707^6395*78125000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16511759 78125000 2569599770707 20000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2709478773/5000000000 : ℝ)^8443 ≤ (22267538887513/50000000000000 : ℝ)^6395 := by
    have hnat : (2709478773 : ℕ)^8443*50000000000000^6395 ≤ 22267538887513^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709478773 5000000000 22267538887513 50000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5241234041/10000000000 : ℝ)^8443 ≤ (21308461681303/50000000000000 : ℝ)^6395 := by
    have hnat : (5241234041 : ℕ)^8443*50000000000000^6395 ≤ 21308461681303^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241234041 10000000000 21308461681303 50000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-16511759/78125000 : ℝ), (2709478773/5000000000 : ℝ), (5241234041/10000000000 : ℝ)] ![(2569599770707/20000000000000 : ℝ), (22267538887513/50000000000000 : ℝ), (21308461681303/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-16511759/78125000 : ℝ)|^8443 ≤ (2569599770707/20000000000000 : ℝ)^6395
        have hw : |(-16511759/78125000 : ℝ)|=(16511759/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2709478773/5000000000 : ℝ)|^8443 ≤ (22267538887513/50000000000000 : ℝ)^6395
        have hw : |(2709478773/5000000000 : ℝ)|=(2709478773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5241234041/10000000000 : ℝ)|^8443 ≤ (21308461681303/50000000000000 : ℝ)^6395
        have hw : |(5241234041/10000000000 : ℝ)|=(5241234041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s3_1 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5351313147/10000000000 : ℝ)*x 0 + (-275519447/1250000000 : ℝ)*x 1 + (2620617071/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351313147/10000000000 : ℝ)^8443 ≤ (10950646341889/25000000000000 : ℝ)^6395 := by
    have hnat : (5351313147 : ℕ)^8443*25000000000000^6395 ≤ 10950646341889^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351313147 10000000000 10950646341889 25000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (275519447/1250000000 : ℝ)^8443 ≤ (2716098035151/20000000000000 : ℝ)^6395 := by
    have hnat : (275519447 : ℕ)^8443*20000000000000^6395 ≤ 2716098035151^6395*1250000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275519447 1250000000 2716098035151 20000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2620617071/5000000000 : ℝ)^8443 ≤ (332944722241/781250000000 : ℝ)^6395 := by
    have hnat : (2620617071 : ℕ)^8443*781250000000^6395 ≤ 332944722241^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620617071 5000000000 332944722241 781250000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351313147/10000000000 : ℝ), (-275519447/1250000000 : ℝ), (2620617071/5000000000 : ℝ)] ![(10950646341889/25000000000000 : ℝ), (2716098035151/20000000000000 : ℝ), (332944722241/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351313147/10000000000 : ℝ)|^8443 ≤ (10950646341889/25000000000000 : ℝ)^6395
        have hw : |(5351313147/10000000000 : ℝ)|=(5351313147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-275519447/1250000000 : ℝ)|^8443 ≤ (2716098035151/20000000000000 : ℝ)^6395
        have hw : |(-275519447/1250000000 : ℝ)|=(275519447/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2620617071/5000000000 : ℝ)|^8443 ≤ (332944722241/781250000000 : ℝ)^6395
        have hw : |(2620617071/5000000000 : ℝ)|=(2620617071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s3_2 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1070262619/2000000000 : ℝ)*x 0 + (26206173/50000000 : ℝ)*x 1 + (-2204155041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070262619/2000000000 : ℝ)^8443 ≤ (10950646201401/25000000000000 : ℝ)^6395 := by
    have hnat : (1070262619 : ℕ)^8443*25000000000000^6395 ≤ 10950646201401^6395*2000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070262619 2000000000 10950646201401 25000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (26206173/50000000 : ℝ)^8443 ≤ (42616929363509/100000000000000 : ℝ)^6395 := by
    have hnat : (26206173 : ℕ)^8443*100000000000000^6395 ≤ 42616929363509^6395*50000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26206173 50000000 42616929363509 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2204155041/10000000000 : ℝ)^8443 ≤ (3395121455953/25000000000000 : ℝ)^6395 := by
    have hnat : (2204155041 : ℕ)^8443*25000000000000^6395 ≤ 3395121455953^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2204155041 10000000000 3395121455953 25000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070262619/2000000000 : ℝ), (26206173/50000000 : ℝ), (-2204155041/10000000000 : ℝ)] ![(10950646201401/25000000000000 : ℝ), (42616929363509/100000000000000 : ℝ), (3395121455953/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070262619/2000000000 : ℝ)|^8443 ≤ (10950646201401/25000000000000 : ℝ)^6395
        have hw : |(1070262619/2000000000 : ℝ)|=(1070262619/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(26206173/50000000 : ℝ)|^8443 ≤ (42616929363509/100000000000000 : ℝ)^6395
        have hw : |(26206173/50000000 : ℝ)|=(26206173/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2204155041/10000000000 : ℝ)|^8443 ≤ (3395121455953/25000000000000 : ℝ)^6395
        have hw : |(-2204155041/10000000000 : ℝ)|=(2204155041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s3_3 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2174008583/5000000000 : ℝ)*x 0 + (4171111041/10000000000 : ℝ)*x 1 + (4532191109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2174008583/5000000000 : ℝ)^8443 ≤ (33300745194411/100000000000000 : ℝ)^6395 := by
    have hnat : (2174008583 : ℕ)^8443*100000000000000^6395 ≤ 33300745194411^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174008583 5000000000 33300745194411 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4171111041/10000000000 : ℝ)^8443 ≤ (1260948333681/4000000000000 : ℝ)^6395 := by
    have hnat : (4171111041 : ℕ)^8443*4000000000000^6395 ≤ 1260948333681^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171111041 10000000000 1260948333681 4000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4532191109/10000000000 : ℝ)^8443 ≤ (17587773228747/50000000000000 : ℝ)^6395 := by
    have hnat : (4532191109 : ℕ)^8443*50000000000000^6395 ≤ 17587773228747^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4532191109 10000000000 17587773228747 50000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2174008583/5000000000 : ℝ), (4171111041/10000000000 : ℝ), (4532191109/10000000000 : ℝ)] ![(33300745194411/100000000000000 : ℝ), (1260948333681/4000000000000 : ℝ), (17587773228747/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2174008583/5000000000 : ℝ)|^8443 ≤ (33300745194411/100000000000000 : ℝ)^6395
        have hw : |(2174008583/5000000000 : ℝ)|=(2174008583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4171111041/10000000000 : ℝ)|^8443 ≤ (1260948333681/4000000000000 : ℝ)^6395
        have hw : |(4171111041/10000000000 : ℝ)|=(4171111041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4532191109/10000000000 : ℝ)|^8443 ≤ (17587773228747/50000000000000 : ℝ)^6395
        have hw : |(4532191109/10000000000 : ℝ)|=(4532191109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s3_4 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2113519459/10000000000 : ℝ)*x 0 + (5241876829/10000000000 : ℝ)*x 1 + (2709155489/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2113519459/10000000000 : ℝ)^8443 ≤ (12848113678803/100000000000000 : ℝ)^6395 := by
    have hnat : (2113519459 : ℕ)^8443*100000000000000^6395 ≤ 12848113678803^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113519459 10000000000 12848113678803 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5241876829/10000000000 : ℝ)^8443 ≤ (42623823870701/100000000000000 : ℝ)^6395 := by
    have hnat : (5241876829 : ℕ)^8443*100000000000000^6395 ≤ 42623823870701^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241876829 10000000000 42623823870701 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2709155489/5000000000 : ℝ)^8443 ≤ (44528062436773/100000000000000 : ℝ)^6395 := by
    have hnat : (2709155489 : ℕ)^8443*100000000000000^6395 ≤ 44528062436773^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709155489 5000000000 44528062436773 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2113519459/10000000000 : ℝ), (5241876829/10000000000 : ℝ), (2709155489/5000000000 : ℝ)] ![(12848113678803/100000000000000 : ℝ), (42623823870701/100000000000000 : ℝ), (44528062436773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2113519459/10000000000 : ℝ)|^8443 ≤ (12848113678803/100000000000000 : ℝ)^6395
        have hw : |(-2113519459/10000000000 : ℝ)|=(2113519459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5241876829/10000000000 : ℝ)|^8443 ≤ (42623823870701/100000000000000 : ℝ)^6395
        have hw : |(5241876829/10000000000 : ℝ)|=(5241876829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2709155489/5000000000 : ℝ)|^8443 ≤ (44528062436773/100000000000000 : ℝ)^6395
        have hw : |(2709155489/5000000000 : ℝ)|=(2709155489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s3_5 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5305947683/10000000000 : ℝ)*x 0 + (-405415701/2000000000 : ℝ)*x 1 + (5418310861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305947683/10000000000 : ℝ)^8443 ≤ (43312998337187/100000000000000 : ℝ)^6395 := by
    have hnat : (5305947683 : ℕ)^8443*100000000000000^6395 ≤ 43312998337187^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305947683 10000000000 43312998337187 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (405415701/2000000000 : ℝ)^8443 ≤ (3039735119837/25000000000000 : ℝ)^6395 := by
    have hnat : (405415701 : ℕ)^8443*25000000000000^6395 ≤ 3039735119837^6395*2000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      405415701 2000000000 3039735119837 25000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5418310861/10000000000 : ℝ)^8443 ≤ (22264030583667/50000000000000 : ℝ)^6395 := by
    have hnat : (5418310861 : ℕ)^8443*50000000000000^6395 ≤ 22264030583667^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418310861 10000000000 22264030583667 50000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305947683/10000000000 : ℝ), (-405415701/2000000000 : ℝ), (5418310861/10000000000 : ℝ)] ![(43312998337187/100000000000000 : ℝ), (3039735119837/25000000000000 : ℝ), (22264030583667/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305947683/10000000000 : ℝ)|^8443 ≤ (43312998337187/100000000000000 : ℝ)^6395
        have hw : |(5305947683/10000000000 : ℝ)|=(5305947683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-405415701/2000000000 : ℝ)|^8443 ≤ (3039735119837/25000000000000 : ℝ)^6395
        have hw : |(-405415701/2000000000 : ℝ)|=(405415701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5418310861/10000000000 : ℝ)|^8443 ≤ (22264030583667/50000000000000 : ℝ)^6395
        have hw : |(5418310861/10000000000 : ℝ)|=(5418310861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s3_6 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1061189493/2000000000 : ℝ)*x 0 + (1354577789/2500000000 : ℝ)*x 1 + (-1013539199/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061189493/2000000000 : ℝ)^8443 ≤ (43312995987727/100000000000000 : ℝ)^6395 := by
    have hnat : (1061189493 : ℕ)^8443*100000000000000^6395 ≤ 43312995987727^6395*2000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061189493 2000000000 43312995987727 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1354577789/2500000000 : ℝ)^8443 ≤ (44528064368057/100000000000000 : ℝ)^6395 := by
    have hnat : (1354577789 : ℕ)^8443*100000000000000^6395 ≤ 44528064368057^6395*2500000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354577789 2500000000 44528064368057 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1013539199/5000000000 : ℝ)^8443 ≤ (6079469815997/50000000000000 : ℝ)^6395 := by
    have hnat : (1013539199 : ℕ)^8443*50000000000000^6395 ≤ 6079469815997^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1013539199 5000000000 6079469815997 50000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061189493/2000000000 : ℝ), (1354577789/2500000000 : ℝ), (-1013539199/5000000000 : ℝ)] ![(43312995987727/100000000000000 : ℝ), (44528064368057/100000000000000 : ℝ), (6079469815997/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061189493/2000000000 : ℝ)|^8443 ≤ (43312995987727/100000000000000 : ℝ)^6395
        have hw : |(1061189493/2000000000 : ℝ)|=(1061189493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1354577789/2500000000 : ℝ)|^8443 ≤ (44528064368057/100000000000000 : ℝ)^6395
        have hw : |(1354577789/2500000000 : ℝ)|=(1354577789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1013539199/5000000000 : ℝ)|^8443 ≤ (6079469815997/50000000000000 : ℝ)^6395
        have hw : |(-1013539199/5000000000 : ℝ)|=(1013539199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s3_7 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4348045059/10000000000 : ℝ)*x 0 + (1132721387/2500000000 : ℝ)*x 1 + (521552923/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4348045059/10000000000 : ℝ)^8443 ≤ (666020544739/2000000000000 : ℝ)^6395 := by
    have hnat : (4348045059 : ℕ)^8443*2000000000000^6395 ≤ 666020544739^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4348045059 10000000000 666020544739 2000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1132721387/2500000000 : ℝ)^8443 ≤ (35162169233071/100000000000000 : ℝ)^6395 := by
    have hnat : (1132721387 : ℕ)^8443*100000000000000^6395 ≤ 35162169233071^6395*2500000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132721387 2500000000 35162169233071 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521552923/1250000000 : ℝ)^8443 ≤ (7884200877143/25000000000000 : ℝ)^6395 := by
    have hnat : (521552923 : ℕ)^8443*25000000000000^6395 ≤ 7884200877143^6395*1250000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521552923 1250000000 7884200877143 25000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4348045059/10000000000 : ℝ), (1132721387/2500000000 : ℝ), (521552923/1250000000 : ℝ)] ![(666020544739/2000000000000 : ℝ), (35162169233071/100000000000000 : ℝ), (7884200877143/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4348045059/10000000000 : ℝ)|^8443 ≤ (666020544739/2000000000000 : ℝ)^6395
        have hw : |(4348045059/10000000000 : ℝ)|=(4348045059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1132721387/2500000000 : ℝ)|^8443 ≤ (35162169233071/100000000000000 : ℝ)^6395
        have hw : |(1132721387/2500000000 : ℝ)|=(1132721387/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(521552923/1250000000 : ℝ)|^8443 ≤ (7884200877143/25000000000000 : ℝ)^6395
        have hw : |(521552923/1250000000 : ℝ)|=(521552923/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1250_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151585227/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8101/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2383/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2733/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14693/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8101/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2383/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8101/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2383/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8101/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2383/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8101/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2383/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8101/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2383/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8101/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2383/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2383/25000 : ℝ) ^ (4221/1024 : ℝ) ≤ (6196191201073037/100000000000000000000 : ℝ) := by
    have hpowers : (2383/25000 : ℝ)^4221 ≤ (6196191201073037/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2383 : ℕ)^4221*100000000000000000000^1024 ≤ 6196191201073037^1024*25000^4221 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2383 25000 6196191201073037 100000000000000000000 4221 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2383/25000 : ℝ)) (X := (6196191201073037/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8101/50000 : ℝ) ^ (4221/1024 : ℝ) ≤ (1103611716186011/2000000000000000000 : ℝ) := by
    have hpowers : (8101/50000 : ℝ)^4221 ≤ (1103611716186011/2000000000000000000 : ℝ)^1024 := by
      have hnat : (8101 : ℕ)^4221*2000000000000000000^1024 ≤ 1103611716186011^1024*50000^4221 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8101 50000 1103611716186011 2000000000000000000 4221 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8101/50000 : ℝ)) (X := (1103611716186011/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006196191201073037/50000000000000000000 : ℝ) ≤ (5000150310401429/5000000000000000 : ℝ) ^ (4221/1024 : ℝ) := by
    have hpowers : (50006196191201073037/50000000000000000000 : ℝ)^1024 ≤ (5000150310401429/5000000000000000 : ℝ)^4221 := by
      have hnat : (50006196191201073037 : ℕ)^1024*5000000000000000^4221 ≤ 5000150310401429^4221*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006196191201073037 50000000000000000000 5000150310401429 5000000000000000 1024 4221 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000150310401429/5000000000000000 : ℝ)) (X := (50006196191201073037/50000000000000000000 : ℝ)) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100061376777010373587/100000000000000000000 : ℝ) ≤ (10001488633414269/10000000000000000 : ℝ) ^ (4221/1024 : ℝ) := by
    have hpowers : (100061376777010373587/100000000000000000000 : ℝ)^1024 ≤ (10001488633414269/10000000000000000 : ℝ)^4221 := by
      have hnat : (100061376777010373587 : ℕ)^1024*10000000000000000^4221 ≤ 10001488633414269^4221*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100061376777010373587 100000000000000000000 10001488633414269 10000000000000000 1024 4221 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001488633414269/10000000000000000 : ℝ)) (X := (100061376777010373587/100000000000000000000 : ℝ)) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1001103611716186011/1000000000000000000 : ℝ) ≤ (125033458075321/125000000000000 : ℝ) ^ (4221/1024 : ℝ) := by
    have hpowers : (1001103611716186011/1000000000000000000 : ℝ)^1024 ≤ (125033458075321/125000000000000 : ℝ)^4221 := by
      have hnat : (1001103611716186011 : ℕ)^1024*125000000000000^4221 ≤ 125033458075321^4221*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1001103611716186011 1000000000000000000 125033458075321 125000000000000 1024 4221 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125033458075321/125000000000000 : ℝ)) (X := (1001103611716186011/1000000000000000000 : ℝ)) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6196191201073037/100000000000000000000 : ℝ) ≤ ((16669839217082780889/16675000000000000000 : ℝ)+2*(1188012611411/667000000000000 : ℝ)*(2383/25000 : ℝ))^(4221/1024 : ℝ) := by
    rw [show (16669839217082780889/16675000000000000000 : ℝ)+2*(1188012611411/667000000000000 : ℝ)*(2383/25000 : ℝ)=(5000150310401429/5000000000000000 : ℝ) by norm_num, show 1+2*(6196191201073037/100000000000000000000 : ℝ)=(50006196191201073037/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1103611716186011/2000000000000000000 : ℝ)+(6196191201073037/100000000000000000000 : ℝ) ≤ ((16669839217082780889/16675000000000000000 : ℝ)+(1188012611411/667000000000000 : ℝ)*((8101/50000 : ℝ)+(2383/25000 : ℝ)))^(4221/1024 : ℝ) := by
    rw [show (16669839217082780889/16675000000000000000 : ℝ)+(1188012611411/667000000000000 : ℝ)*((8101/50000 : ℝ)+(2383/25000 : ℝ))=(10001488633414269/10000000000000000 : ℝ) by norm_num, show 1+(1103611716186011/2000000000000000000 : ℝ)+(6196191201073037/100000000000000000000 : ℝ)=(100061376777010373587/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1103611716186011/2000000000000000000 : ℝ) ≤ ((16669839217082780889/16675000000000000000 : ℝ)+2*(1188012611411/667000000000000 : ℝ)*(8101/50000 : ℝ))^(4221/1024 : ℝ) := by
    rw [show (16669839217082780889/16675000000000000000 : ℝ)+2*(1188012611411/667000000000000 : ℝ)*(8101/50000 : ℝ)=(125033458075321/125000000000000 : ℝ) by norm_num, show 1+2*(1103611716186011/2000000000000000000 : ℝ)=(1001103611716186011/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16669839217082780889/16675000000000000000 : ℝ)*(X 1 0+X 2 0)+(1188012611411/667000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4221/1024 : ℝ)) (lo := (2383/25000 : ℝ)) (hi := (8101/50000 : ℝ)) (c := (16669839217082780889/16675000000000000000 : ℝ)) (alpha := (1188012611411/667000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16669839217082780889/16675000000000000000 : ℝ)*(X 0 1+X 2 1)+(1188012611411/667000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4221/1024 : ℝ)) (lo := (2383/25000 : ℝ)) (hi := (8101/50000 : ℝ)) (c := (16669839217082780889/16675000000000000000 : ℝ)) (alpha := (1188012611411/667000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16669839217082780889/16675000000000000000 : ℝ)*(X 0 2+X 1 2)+(1188012611411/667000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4221/1024 : ℝ)) (lo := (2383/25000 : ℝ)) (hi := (8101/50000 : ℝ)) (c := (16669839217082780889/16675000000000000000 : ℝ)) (alpha := (1188012611411/667000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-16511759/78125000 : ℝ)*X 0 0+(2709478773/5000000000 : ℝ)*X 0 1+(5241234041/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351313147/10000000000 : ℝ)*X 1 0+(-275519447/1250000000 : ℝ)*X 1 1+(2620617071/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070262619/2000000000 : ℝ)*X 2 0+(26206173/50000000 : ℝ)*X 2 1+(-2204155041/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2174008583/5000000000 : ℝ)*X 0 0+(4171111041/10000000000 : ℝ)*X 0 1+(4532191109/10000000000 : ℝ)*X 0 2+(2174008583/5000000000 : ℝ)*X 1 0+(4171111041/10000000000 : ℝ)*X 1 1+(4532191109/10000000000 : ℝ)*X 1 2+(2174008583/5000000000 : ℝ)*X 2 0+(4171111041/10000000000 : ℝ)*X 2 1+(4532191109/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2113519459/10000000000 : ℝ)*X 0 0+(5241876829/10000000000 : ℝ)*X 0 1+(2709155489/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305947683/10000000000 : ℝ)*X 1 0+(-405415701/2000000000 : ℝ)*X 1 1+(5418310861/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061189493/2000000000 : ℝ)*X 2 0+(1354577789/2500000000 : ℝ)*X 2 1+(-1013539199/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4348045059/10000000000 : ℝ)*X 0 0+(1132721387/2500000000 : ℝ)*X 0 1+(521552923/1250000000 : ℝ)*X 0 2+(4348045059/10000000000 : ℝ)*X 1 0+(1132721387/2500000000 : ℝ)*X 1 1+(521552923/1250000000 : ℝ)*X 1 2+(4348045059/10000000000 : ℝ)*X 2 0+(1132721387/2500000000 : ℝ)*X 2 1+(521552923/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2625668605471218144205303863/833750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (141993/1562500000000 : ℝ)*(base8) + (10613777/10000000000000 : ℝ)*(lower2) + (54962771/50000000000000 : ℝ)*(lower3) + (9524809/12500000000000 : ℝ)*(lower4) + (4198117615080411/100000000000000 : ℝ)*(major0) + (4198117615080411/100000000000000 : ℝ)*(major1) + (4198117615080411/100000000000000 : ℝ)*(major2) + (1406683908205993/25000000000000 : ℝ)*(sp0) + (1125349065602561/20000000000000 : ℝ)*(sp1) + (2813379188622173/50000000000000 : ℝ)*(sp2) + (173092083693223/6250000000000 : ℝ)*(sp3) + (11367666411/50000000000000 : ℝ)*(sp4) + (13049231541/100000000000000 : ℝ)*(sp5) + (1704425319/50000000000000 : ℝ)*(sp7) + (1384738373971103/50000000000000 : ℝ)*(f.failure) + (2813379188622173/50000000000000 : ℝ)*(f.sum) + (156099789544879/33350000000000000000000000000 : ℝ)*base66 + (88024324149092090379/1667500000000000000000000000000000 : ℝ)*base67 + (24954667396917090379/1667500000000000000000000000000000 : ℝ)*base69 + (6711377873162909621/1667500000000000000000000000000000 : ℝ)*base72 + (115201188519471/33350000000000000000000000000 : ℝ)*base73 + (5028535404964590379/1667500000000000000000000000000000 : ℝ)*base75 + (53541771421522909621/1667500000000000000000000000000000 : ℝ)*base78 + (2472407151217090379/1667500000000000000000000000000000 : ℝ)*base79 + (75762068425379/33350000000000000000000000000 : ℝ)*base82 + (10304619/5000000000000000000000 : ℝ)*base90 + (10304619/5000000000000000000000 : ℝ)*base92 + (10304619/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (209058765906024629079500241/208437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (205276611/25000000000000 : ℝ)*(base19) + (944308687/100000000000000 : ℝ)*(base23) + (76024547/50000000000000 : ℝ)*(upper2) + (64958041/100000000000000 : ℝ)*(upper3) + (12210271/20000000000000 : ℝ)*(upper5) + (2114381372994223/50000000000000 : ℝ)*(major0) + (2114381372994223/50000000000000 : ℝ)*(major1) + (2114381372994223/50000000000000 : ℝ)*(major2) + (276641413/2000000000000 : ℝ)*(sp1) + (10980771563/50000000000000 : ℝ)*(sp2) + (1133566454853621/20000000000000 : ℝ)*(sp4) + (5667817621091011/100000000000000 : ℝ)*(sp5) + (1416952342104073/25000000000000 : ℝ)*(sp6) + (557938636855219/20000000000000 : ℝ)*(sp7) + (557938636855219/20000000000000 : ℝ)*(f.failure) + (1133566454853621/20000000000000 : ℝ)*(f.sum) + (78844489966903/16675000000000000000000000000 : ℝ)*base65 + (16025167194705620753/833750000000000000000000000000000 : ℝ)*base68 + (1578237393899370753/833750000000000000000000000000000 : ℝ)*base70 + (8186552815356870753/833750000000000000000000000000000 : ℝ)*base72 + (38542573736111/8337500000000000000000000000 : ℝ)*base74 + (3804471688933120753/833750000000000000000000000000000 : ℝ)*base76 + (555840771893120753/833750000000000000000000000000000 : ℝ)*base78 + (2445835268583129247/833750000000000000000000000000000 : ℝ)*base79 + (6830620980497/16675000000000000000000000000 : ℝ)*base82 + (18249713/2000000000000000000000 : ℝ)*base89 + (18249713/2000000000000000000000 : ℝ)*base91 + (18249713/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1250_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151585227/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8101/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2383/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2733/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14693/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1250_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1250_s4_0 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-528937117/2500000000 : ℝ)*x 0 + (5397167519/10000000000 : ℝ)*x 1 + (210462151/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528937117/2500000000 : ℝ)^8443 ≤ (2573201264387/20000000000000 : ℝ)^6395 := by
    have hnat : (528937117 : ℕ)^8443*20000000000000^6395 ≤ 2573201264387^6395*2500000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528937117 2500000000 2573201264387 20000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5397167519/10000000000 : ℝ)^8443 ≤ (2768675080721/6250000000000 : ℝ)^6395 := by
    have hnat : (5397167519 : ℕ)^8443*6250000000000^6395 ≤ 2768675080721^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397167519 10000000000 2768675080721 6250000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210462151/400000000 : ℝ)^8443 ≤ (42835192375607/100000000000000 : ℝ)^6395 := by
    have hnat : (210462151 : ℕ)^8443*100000000000000^6395 ≤ 42835192375607^6395*400000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210462151 400000000 42835192375607 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-528937117/2500000000 : ℝ), (5397167519/10000000000 : ℝ), (210462151/400000000 : ℝ)] ![(2573201264387/20000000000000 : ℝ), (2768675080721/6250000000000 : ℝ), (42835192375607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-528937117/2500000000 : ℝ)|^8443 ≤ (2573201264387/20000000000000 : ℝ)^6395
        have hw : |(-528937117/2500000000 : ℝ)|=(528937117/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5397167519/10000000000 : ℝ)|^8443 ≤ (2768675080721/6250000000000 : ℝ)^6395
        have hw : |(5397167519/10000000000 : ℝ)|=(5397167519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210462151/400000000 : ℝ)|^8443 ≤ (42835192375607/100000000000000 : ℝ)^6395
        have hw : |(210462151/400000000 : ℝ)|=(210462151/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s4_1 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668226987/1250000000 : ℝ)*x 0 + (-2184597243/10000000000 : ℝ)*x 1 + (328847111/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668226987/1250000000 : ℝ)^8443 ≤ (10935796913557/25000000000000 : ℝ)^6395 := by
    have hnat : (668226987 : ℕ)^8443*25000000000000^6395 ≤ 10935796913557^6395*1250000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668226987 1250000000 10935796913557 25000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2184597243/10000000000 : ℝ)^8443 ≤ (6710809973121/50000000000000 : ℝ)^6395 := by
    have hnat : (2184597243 : ℕ)^8443*50000000000000^6395 ≤ 6710809973121^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184597243 10000000000 6710809973121 50000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (328847111/625000000 : ℝ)^8443 ≤ (10708798096589/25000000000000 : ℝ)^6395 := by
    have hnat : (328847111 : ℕ)^8443*25000000000000^6395 ≤ 10708798096589^6395*625000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328847111 625000000 10708798096589 25000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668226987/1250000000 : ℝ), (-2184597243/10000000000 : ℝ), (328847111/625000000 : ℝ)] ![(10935796913557/25000000000000 : ℝ), (6710809973121/50000000000000 : ℝ), (10708798096589/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668226987/1250000000 : ℝ)|^8443 ≤ (10935796913557/25000000000000 : ℝ)^6395
        have hw : |(668226987/1250000000 : ℝ)|=(668226987/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2184597243/10000000000 : ℝ)|^8443 ≤ (6710809973121/50000000000000 : ℝ)^6395
        have hw : |(-2184597243/10000000000 : ℝ)|=(2184597243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(328847111/625000000 : ℝ)|^8443 ≤ (10708798096589/25000000000000 : ℝ)^6395
        have hw : |(328847111/625000000 : ℝ)|=(328847111/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s4_2 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336453989/2500000000 : ℝ)*x 0 + (1315388427/2500000000 : ℝ)*x 1 + (-2184597253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336453989/2500000000 : ℝ)^8443 ≤ (43743188302421/100000000000000 : ℝ)^6395 := by
    have hnat : (1336453989 : ℕ)^8443*100000000000000^6395 ≤ 43743188302421^6395*2500000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336453989 2500000000 43743188302421 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315388427/2500000000 : ℝ)^8443 ≤ (21417595827733/50000000000000 : ℝ)^6395 := by
    have hnat : (1315388427 : ℕ)^8443*50000000000000^6395 ≤ 21417595827733^6395*2500000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315388427 2500000000 21417595827733 50000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2184597253/10000000000 : ℝ)^8443 ≤ (2684324005471/20000000000000 : ℝ)^6395 := by
    have hnat : (2184597253 : ℕ)^8443*20000000000000^6395 ≤ 2684324005471^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184597253 10000000000 2684324005471 20000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336453989/2500000000 : ℝ), (1315388427/2500000000 : ℝ), (-2184597253/10000000000 : ℝ)] ![(43743188302421/100000000000000 : ℝ), (21417595827733/50000000000000 : ℝ), (2684324005471/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336453989/2500000000 : ℝ)|^8443 ≤ (43743188302421/100000000000000 : ℝ)^6395
        have hw : |(1336453989/2500000000 : ℝ)|=(1336453989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1315388427/2500000000 : ℝ)|^8443 ≤ (21417595827733/50000000000000 : ℝ)^6395
        have hw : |(1315388427/2500000000 : ℝ)|=(1315388427/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2184597253/10000000000 : ℝ)|^8443 ≤ (2684324005471/20000000000000 : ℝ)^6395
        have hw : |(-2184597253/10000000000 : ℝ)|=(2184597253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s4_3 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4349362693/10000000000 : ℝ)*x 0 + (263357251/625000000 : ℝ)*x 1 + (280577697/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4349362693/10000000000 : ℝ)^8443 ≤ (6662870253989/20000000000000 : ℝ)^6395 := by
    have hnat : (4349362693 : ℕ)^8443*20000000000000^6395 ≤ 6662870253989^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4349362693 10000000000 6662870253989 20000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263357251/625000000 : ℝ)^8443 ≤ (31949512803021/100000000000000 : ℝ)^6395 := by
    have hnat : (263357251 : ℕ)^8443*100000000000000^6395 ≤ 31949512803021^6395*625000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263357251 625000000 31949512803021 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (280577697/625000000 : ℝ)^8443 ≤ (34736135910837/100000000000000 : ℝ)^6395 := by
    have hnat : (280577697 : ℕ)^8443*100000000000000^6395 ≤ 34736135910837^6395*625000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280577697 625000000 34736135910837 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4349362693/10000000000 : ℝ), (263357251/625000000 : ℝ), (280577697/625000000 : ℝ)] ![(6662870253989/20000000000000 : ℝ), (31949512803021/100000000000000 : ℝ), (34736135910837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4349362693/10000000000 : ℝ)|^8443 ≤ (6662870253989/20000000000000 : ℝ)^6395
        have hw : |(4349362693/10000000000 : ℝ)|=(4349362693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(263357251/625000000 : ℝ)|^8443 ≤ (31949512803021/100000000000000 : ℝ)^6395
        have hw : |(263357251/625000000 : ℝ)|=(263357251/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(280577697/625000000 : ℝ)|^8443 ≤ (34736135910837/100000000000000 : ℝ)^6395
        have hw : |(280577697/625000000 : ℝ)|=(280577697/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s4_4 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2115754811/10000000000 : ℝ)*x 0 + (5261928561/10000000000 : ℝ)*x 1 + (2698395533/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2115754811/10000000000 : ℝ)^8443 ≤ (12866057246917/100000000000000 : ℝ)^6395 := by
    have hnat : (2115754811 : ℕ)^8443*100000000000000^6395 ≤ 12866057246917^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115754811 10000000000 12866057246917 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5261928561/10000000000 : ℝ)^8443 ≤ (2677451297707/6250000000000 : ℝ)^6395 := by
    have hnat : (5261928561 : ℕ)^8443*6250000000000^6395 ≤ 2677451297707^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261928561 10000000000 2677451297707 6250000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698395533/5000000000 : ℝ)^8443 ≤ (4429472196727/10000000000000 : ℝ)^6395 := by
    have hnat : (2698395533 : ℕ)^8443*10000000000000^6395 ≤ 4429472196727^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698395533 5000000000 4429472196727 10000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2115754811/10000000000 : ℝ), (5261928561/10000000000 : ℝ), (2698395533/5000000000 : ℝ)] ![(12866057246917/100000000000000 : ℝ), (2677451297707/6250000000000 : ℝ), (4429472196727/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2115754811/10000000000 : ℝ)|^8443 ≤ (12866057246917/100000000000000 : ℝ)^6395
        have hw : |(-2115754811/10000000000 : ℝ)|=(2115754811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5261928561/10000000000 : ℝ)|^8443 ≤ (2677451297707/6250000000000 : ℝ)^6395
        have hw : |(5261928561/10000000000 : ℝ)|=(5261928561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698395533/5000000000 : ℝ)|^8443 ≤ (4429472196727/10000000000000 : ℝ)^6395
        have hw : |(2698395533/5000000000 : ℝ)|=(2698395533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s4_5 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311196657/10000000000 : ℝ)*x 0 + (-256169993/1250000000 : ℝ)*x 1 + (2698395499/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311196657/10000000000 : ℝ)^8443 ≤ (43369577266037/100000000000000 : ℝ)^6395 := by
    have hnat : (5311196657 : ℕ)^8443*100000000000000^6395 ≤ 43369577266037^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311196657 10000000000 43369577266037 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (256169993/1250000000 : ℝ)^8443 ≤ (3083925371759/25000000000000 : ℝ)^6395 := by
    have hnat : (256169993 : ℕ)^8443*25000000000000^6395 ≤ 3083925371759^6395*1250000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256169993 1250000000 3083925371759 25000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698395499/5000000000 : ℝ)^8443 ≤ (2768420076901/6250000000000 : ℝ)^6395 := by
    have hnat : (2698395499 : ℕ)^8443*6250000000000^6395 ≤ 2768420076901^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698395499 5000000000 2768420076901 6250000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311196657/10000000000 : ℝ), (-256169993/1250000000 : ℝ), (2698395499/5000000000 : ℝ)] ![(43369577266037/100000000000000 : ℝ), (3083925371759/25000000000000 : ℝ), (2768420076901/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311196657/10000000000 : ℝ)|^8443 ≤ (43369577266037/100000000000000 : ℝ)^6395
        have hw : |(5311196657/10000000000 : ℝ)|=(5311196657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-256169993/1250000000 : ℝ)|^8443 ≤ (3083925371759/25000000000000 : ℝ)^6395
        have hw : |(-256169993/1250000000 : ℝ)|=(256169993/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698395499/5000000000 : ℝ)|^8443 ≤ (2768420076901/6250000000000 : ℝ)^6395
        have hw : |(2698395499/5000000000 : ℝ)|=(2698395499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s4_6 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1327799031/2500000000 : ℝ)*x 0 + (2698395839/5000000000 : ℝ)*x 1 + (-2049359741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327799031/2500000000 : ℝ)^8443 ≤ (5421196439987/12500000000000 : ℝ)^6395 := by
    have hnat : (1327799031 : ℕ)^8443*12500000000000^6395 ≤ 5421196439987^6395*2500000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327799031 2500000000 5421196439987 12500000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2698395839/5000000000 : ℝ)^8443 ≤ (44294728598957/100000000000000 : ℝ)^6395 := by
    have hnat : (2698395839 : ℕ)^8443*100000000000000^6395 ≤ 44294728598957^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698395839 5000000000 44294728598957 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2049359741/10000000000 : ℝ)^8443 ≤ (61678499369/500000000000 : ℝ)^6395 := by
    have hnat : (2049359741 : ℕ)^8443*500000000000^6395 ≤ 61678499369^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2049359741 10000000000 61678499369 500000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327799031/2500000000 : ℝ), (2698395839/5000000000 : ℝ), (-2049359741/10000000000 : ℝ)] ![(5421196439987/12500000000000 : ℝ), (44294728598957/100000000000000 : ℝ), (61678499369/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327799031/2500000000 : ℝ)|^8443 ≤ (5421196439987/12500000000000 : ℝ)^6395
        have hw : |(1327799031/2500000000 : ℝ)|=(1327799031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2698395839/5000000000 : ℝ)|^8443 ≤ (44294728598957/100000000000000 : ℝ)^6395
        have hw : |(2698395839/5000000000 : ℝ)|=(2698395839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2049359741/10000000000 : ℝ)|^8443 ≤ (61678499369/500000000000 : ℝ)^6395
        have hw : |(-2049359741/10000000000 : ℝ)|=(2049359741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s4_7 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1087343809/2500000000 : ℝ)*x 0 + (4488481979/10000000000 : ℝ)*x 1 + (4214480073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087343809/2500000000 : ℝ)^8443 ≤ (33314478112097/100000000000000 : ℝ)^6395 := by
    have hnat : (1087343809 : ℕ)^8443*100000000000000^6395 ≤ 33314478112097^6395*2500000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087343809 2500000000 33314478112097 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4488481979/10000000000 : ℝ)^8443 ≤ (6945672053971/20000000000000 : ℝ)^6395 := by
    have hnat : (4488481979 : ℕ)^8443*20000000000000^6395 ≤ 6945672053971^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4488481979 10000000000 6945672053971 20000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4214480073/10000000000 : ℝ)^8443 ≤ (31957161607957/100000000000000 : ℝ)^6395 := by
    have hnat : (4214480073 : ℕ)^8443*100000000000000^6395 ≤ 31957161607957^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4214480073 10000000000 31957161607957 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1087343809/2500000000 : ℝ), (4488481979/10000000000 : ℝ), (4214480073/10000000000 : ℝ)] ![(33314478112097/100000000000000 : ℝ), (6945672053971/20000000000000 : ℝ), (31957161607957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1087343809/2500000000 : ℝ)|^8443 ≤ (33314478112097/100000000000000 : ℝ)^6395
        have hw : |(1087343809/2500000000 : ℝ)|=(1087343809/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4488481979/10000000000 : ℝ)|^8443 ≤ (6945672053971/20000000000000 : ℝ)^6395
        have hw : |(4488481979/10000000000 : ℝ)|=(4488481979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4214480073/10000000000 : ℝ)|^8443 ≤ (31957161607957/100000000000000 : ℝ)^6395
        have hw : |(4214480073/10000000000 : ℝ)|=(4214480073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1250_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151585227/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14693/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2733/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2273/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14237/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14693/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2733/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14693/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2733/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14693/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2733/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14693/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2733/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14693/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2733/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14693/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2733/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2733/25000 : ℝ) ^ (4221/1024 : ℝ) ≤ (10900646465841001/100000000000000000000 : ℝ) := by
    have hpowers : (2733/25000 : ℝ)^4221 ≤ (10900646465841001/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2733 : ℕ)^4221*100000000000000000000^1024 ≤ 10900646465841001^1024*25000^4221 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2733 25000 10900646465841001 100000000000000000000 4221 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2733/25000 : ℝ)) (X := (10900646465841001/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14693/100000 : ℝ) ^ (4221/1024 : ℝ) ≤ (3687829467648519/10000000000000000000 : ℝ) := by
    have hpowers : (14693/100000 : ℝ)^4221 ≤ (3687829467648519/10000000000000000000 : ℝ)^1024 := by
      have hnat : (14693 : ℕ)^4221*10000000000000000000^1024 ≤ 3687829467648519^1024*100000^4221 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14693 100000 3687829467648519 10000000000000000000 4221 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14693/100000 : ℝ)) (X := (3687829467648519/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010900646465841001/50000000000000000000 : ℝ) ≤ (10000528848164959/10000000000000000 : ℝ) ^ (4221/1024 : ℝ) := by
    have hpowers : (50010900646465841001/50000000000000000000 : ℝ)^1024 ≤ (10000528848164959/10000000000000000 : ℝ)^4221 := by
      have hnat : (50010900646465841001 : ℕ)^1024*10000000000000000^4221 ≤ 10000528848164959^4221*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010900646465841001 50000000000000000000 10000528848164959 10000000000000000 1024 4221 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000528848164959/10000000000000000 : ℝ)) (X := (50010900646465841001/50000000000000000000 : ℝ)) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047778941142326191/100000000000000000000 : ℝ) ≤ (10001158890917271/10000000000000000 : ℝ) ^ (4221/1024 : ℝ) := by
    have hpowers : (100047778941142326191/100000000000000000000 : ℝ)^1024 ≤ (10001158890917271/10000000000000000 : ℝ)^4221 := by
      have hnat : (100047778941142326191 : ℕ)^1024*10000000000000000^4221 ≤ 10001158890917271^4221*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047778941142326191 100000000000000000000 10001158890917271 10000000000000000 1024 4221 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001158890917271/10000000000000000 : ℝ)) (X := (100047778941142326191/100000000000000000000 : ℝ)) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003687829467648519/5000000000000000000 : ℝ) ≤ (10001788933669583/10000000000000000 : ℝ) ^ (4221/1024 : ℝ) := by
    have hpowers : (5003687829467648519/5000000000000000000 : ℝ)^1024 ≤ (10001788933669583/10000000000000000 : ℝ)^4221 := by
      have hnat : (5003687829467648519 : ℕ)^1024*10000000000000000^4221 ≤ 10001788933669583^4221*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003687829467648519 5000000000000000000 10001788933669583 10000000000000000 1024 4221 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001788933669583/10000000000000000 : ℝ)) (X := (5003687829467648519/5000000000000000000 : ℝ)) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10900646465841001/100000000000000000000 : ℝ) ≤ ((37598213743211861231/37610000000000000000 : ℝ)+2*(78755344039/47012500000000 : ℝ)*(2733/25000 : ℝ))^(4221/1024 : ℝ) := by
    rw [show (37598213743211861231/37610000000000000000 : ℝ)+2*(78755344039/47012500000000 : ℝ)*(2733/25000 : ℝ)=(10000528848164959/10000000000000000 : ℝ) by norm_num, show 1+2*(10900646465841001/100000000000000000000 : ℝ)=(50010900646465841001/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3687829467648519/10000000000000000000 : ℝ)+(10900646465841001/100000000000000000000 : ℝ) ≤ ((37598213743211861231/37610000000000000000 : ℝ)+(78755344039/47012500000000 : ℝ)*((14693/100000 : ℝ)+(2733/25000 : ℝ)))^(4221/1024 : ℝ) := by
    rw [show (37598213743211861231/37610000000000000000 : ℝ)+(78755344039/47012500000000 : ℝ)*((14693/100000 : ℝ)+(2733/25000 : ℝ))=(10001158890917271/10000000000000000 : ℝ) by norm_num, show 1+(3687829467648519/10000000000000000000 : ℝ)+(10900646465841001/100000000000000000000 : ℝ)=(100047778941142326191/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3687829467648519/10000000000000000000 : ℝ) ≤ ((37598213743211861231/37610000000000000000 : ℝ)+2*(78755344039/47012500000000 : ℝ)*(14693/100000 : ℝ))^(4221/1024 : ℝ) := by
    rw [show (37598213743211861231/37610000000000000000 : ℝ)+2*(78755344039/47012500000000 : ℝ)*(14693/100000 : ℝ)=(10001788933669583/10000000000000000 : ℝ) by norm_num, show 1+2*(3687829467648519/10000000000000000000 : ℝ)=(5003687829467648519/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (37598213743211861231/37610000000000000000 : ℝ)*(X 1 0+X 2 0)+(78755344039/47012500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4221/1024 : ℝ)) (lo := (2733/25000 : ℝ)) (hi := (14693/100000 : ℝ)) (c := (37598213743211861231/37610000000000000000 : ℝ)) (alpha := (78755344039/47012500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (37598213743211861231/37610000000000000000 : ℝ)*(X 0 1+X 2 1)+(78755344039/47012500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4221/1024 : ℝ)) (lo := (2733/25000 : ℝ)) (hi := (14693/100000 : ℝ)) (c := (37598213743211861231/37610000000000000000 : ℝ)) (alpha := (78755344039/47012500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (37598213743211861231/37610000000000000000 : ℝ)*(X 0 2+X 1 2)+(78755344039/47012500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4221/1024 : ℝ)) (lo := (2733/25000 : ℝ)) (hi := (14693/100000 : ℝ)) (c := (37598213743211861231/37610000000000000000 : ℝ)) (alpha := (78755344039/47012500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-528937117/2500000000 : ℝ)*X 0 0+(5397167519/10000000000 : ℝ)*X 0 1+(210462151/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668226987/1250000000 : ℝ)*X 1 0+(-2184597243/10000000000 : ℝ)*X 1 1+(328847111/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336453989/2500000000 : ℝ)*X 2 0+(1315388427/2500000000 : ℝ)*X 2 1+(-2184597253/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4349362693/10000000000 : ℝ)*X 0 0+(263357251/625000000 : ℝ)*X 0 1+(280577697/625000000 : ℝ)*X 0 2+(4349362693/10000000000 : ℝ)*X 1 0+(263357251/625000000 : ℝ)*X 1 1+(280577697/625000000 : ℝ)*X 1 2+(4349362693/10000000000 : ℝ)*X 2 0+(263357251/625000000 : ℝ)*X 2 1+(280577697/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2115754811/10000000000 : ℝ)*X 0 0+(5261928561/10000000000 : ℝ)*X 0 1+(2698395533/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311196657/10000000000 : ℝ)*X 1 0+(-256169993/1250000000 : ℝ)*X 1 1+(2698395499/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1327799031/2500000000 : ℝ)*X 2 0+(2698395839/5000000000 : ℝ)*X 2 1+(-2049359741/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1087343809/2500000000 : ℝ)*X 0 0+(4488481979/10000000000 : ℝ)*X 0 1+(4214480073/10000000000 : ℝ)*X 0 2+(1087343809/2500000000 : ℝ)*X 1 0+(4488481979/10000000000 : ℝ)*X 1 1+(4214480073/10000000000 : ℝ)*X 1 2+(1087343809/2500000000 : ℝ)*X 2 0+(4488481979/10000000000 : ℝ)*X 2 1+(4214480073/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10175212385053023762246419031/1880500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1125589741/100000000000000 : ℝ)*(base19) + (1149389459/100000000000000 : ℝ)*(base23) + (162590317/100000000000000 : ℝ)*(upper3) + (6304147/20000000000000 : ℝ)*(upper4) + (7494417/6250000000000 : ℝ)*(upper5) + (5501686953212911/100000000000000 : ℝ)*(major0) + (5501686953212911/100000000000000 : ℝ)*(major1) + (5501686953212911/100000000000000 : ℝ)*(major2) + (368695573681709/5000000000000 : ℝ)*(sp0) + (737393781840567/10000000000000 : ℝ)*(sp1) + (57608889020359/781250000000 : ℝ)*(sp2) + (72588398082849/2000000000000 : ℝ)*(sp3) + (2747036123/10000000000000 : ℝ)*(sp4) + (14877924347/100000000000000 : ℝ)*(sp7) + (1814717391033399/50000000000000 : ℝ)*(f.failure) + (7373938943995411/100000000000000 : ℝ)*(f.sum) + (19763612162943/4701250000000000000000000000 : ℝ)*base65 + (89715689313509753441/3761000000000000000000000000000000 : ℝ)*base67 + (44048765863981753441/3761000000000000000000000000000000 : ℝ)*base69 + (90137268457570753441/3761000000000000000000000000000000 : ℝ)*base71 + (148544957593317/18805000000000000000000000000 : ℝ)*base73 + (56522087612341753441/3761000000000000000000000000000000 : ℝ)*base75 + (64293031199858753441/3761000000000000000000000000000000 : ℝ)*base77 + (86570814204783753441/3761000000000000000000000000000000 : ℝ)*base79 + (40159786900857/18805000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1996573/5000000000000000000000 : ℝ)*base89 + (1996573/5000000000000000000000 : ℝ)*base91 + (1996573/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27498730090065274551154911/9402500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (38231061/4000000000000 : ℝ)*(base19) + (425329381/100000000000000 : ℝ)*(base23) + (21124959/20000000000000 : ℝ)*(upper2) + (194771173/50000000000000 : ℝ)*(upper3) + (34701477/50000000000000 : ℝ)*(upper4) + (14771639/50000000000000 : ℝ)*(upper5) + (27661373016073/500000000000 : ℝ)*(major0) + (27661373016073/500000000000 : ℝ)*(major1) + (27661373016073/500000000000 : ℝ)*(major2) + (1394852643/6250000000000 : ℝ)*(sp2) + (3707467905200763/50000000000000 : ℝ)*(sp4) + (7414934854625001/100000000000000 : ℝ)*(sp5) + (3707456533714929/50000000000000 : ℝ)*(sp6) + (1824806649270183/50000000000000 : ℝ)*(sp7) + (1824806649270183/50000000000000 : ℝ)*(f.failure) + (3707467905200763/50000000000000 : ℝ)*(f.sum) + (246459901717/75220000000000000000000000 : ℝ)*base65 + (200283069824165863/18805000000000000000000000000000 : ℝ)*base67 + (28331183459795863/18805000000000000000000000000000 : ℝ)*base69 + (158242710524399137/18805000000000000000000000000000 : ℝ)*base72 + (1512806329547/376100000000000000000000000 : ℝ)*base73 + (134764097913214137/18805000000000000000000000000000 : ℝ)*base76 + (224582031510885863/18805000000000000000000000000000 : ℝ)*base77 + (121118880126855863/18805000000000000000000000000000 : ℝ)*base79 + (3514738549949/940250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (74386541/5000000000000000000000 : ℝ)*base89 + (74386541/5000000000000000000000 : ℝ)*base91 + (74386541/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1250_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151585227/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14693/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2733/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2273/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1250_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1250_s5_0 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-423237139/2000000000 : ℝ)*x 0 + (107844291/200000000 : ℝ)*x 1 + (5266219279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (423237139/2000000000 : ℝ)^8443 ≤ (6434758363809/50000000000000 : ℝ)^6395 := by
    have hnat : (423237139 : ℕ)^8443*50000000000000^6395 ≤ 6434758363809^6395*2000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423237139 2000000000 6434758363809 50000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107844291/200000000 : ℝ)^8443 ≤ (44245137161813/100000000000000 : ℝ)^6395 := by
    have hnat : (107844291 : ℕ)^8443*100000000000000^6395 ≤ 44245137161813^6395*200000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107844291 200000000 44245137161813 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266219279/10000000000 : ℝ)^8443 ≤ (42885346096829/100000000000000 : ℝ)^6395 := by
    have hnat : (5266219279 : ℕ)^8443*100000000000000^6395 ≤ 42885346096829^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266219279 10000000000 42885346096829 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-423237139/2000000000 : ℝ), (107844291/200000000 : ℝ), (5266219279/10000000000 : ℝ)] ![(6434758363809/50000000000000 : ℝ), (44245137161813/100000000000000 : ℝ), (42885346096829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-423237139/2000000000 : ℝ)|^8443 ≤ (6434758363809/50000000000000 : ℝ)^6395
        have hw : |(-423237139/2000000000 : ℝ)|=(423237139/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(107844291/200000000 : ℝ)|^8443 ≤ (44245137161813/100000000000000 : ℝ)^6395
        have hw : |(107844291/200000000 : ℝ)|=(107844291/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266219279/10000000000 : ℝ)|^8443 ≤ (42885346096829/100000000000000 : ℝ)^6395
        have hw : |(5266219279/10000000000 : ℝ)|=(5266219279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s5_1 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068912351/2000000000 : ℝ)*x 0 + (-87203313/400000000 : ℝ)*x 1 + (1316554823/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068912351/2000000000 : ℝ)^8443 ≤ (10932409854813/25000000000000 : ℝ)^6395 := by
    have hnat : (1068912351 : ℕ)^8443*25000000000000^6395 ≤ 10932409854813^6395*2000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068912351 2000000000 10932409854813 25000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (87203313/400000000 : ℝ)^8443 ≤ (2677002865229/20000000000000 : ℝ)^6395 := by
    have hnat : (87203313 : ℕ)^8443*20000000000000^6395 ≤ 2677002865229^6395*400000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87203313 400000000 2677002865229 20000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316554823/2500000000 : ℝ)^8443 ≤ (42885346236597/100000000000000 : ℝ)^6395 := by
    have hnat : (1316554823 : ℕ)^8443*100000000000000^6395 ≤ 42885346236597^6395*2500000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316554823 2500000000 42885346236597 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068912351/2000000000 : ℝ), (-87203313/400000000 : ℝ), (1316554823/2500000000 : ℝ)] ![(10932409854813/25000000000000 : ℝ), (2677002865229/20000000000000 : ℝ), (42885346236597/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068912351/2000000000 : ℝ)|^8443 ≤ (10932409854813/25000000000000 : ℝ)^6395
        have hw : |(1068912351/2000000000 : ℝ)|=(1068912351/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-87203313/400000000 : ℝ)|^8443 ≤ (2677002865229/20000000000000 : ℝ)^6395
        have hw : |(-87203313/400000000 : ℝ)|=(87203313/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316554823/2500000000 : ℝ)|^8443 ≤ (42885346236597/100000000000000 : ℝ)^6395
        have hw : |(1316554823/2500000000 : ℝ)|=(1316554823/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s5_2 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344561809/10000000000 : ℝ)*x 0 + (2633109649/5000000000 : ℝ)*x 1 + (-436016549/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344561809/10000000000 : ℝ)^8443 ≤ (43729640002581/100000000000000 : ℝ)^6395 := by
    have hnat : (5344561809 : ℕ)^8443*100000000000000^6395 ≤ 43729640002581^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344561809 10000000000 43729640002581 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633109649/5000000000 : ℝ)^8443 ≤ (21442673150553/50000000000000 : ℝ)^6395 := by
    have hnat : (2633109649 : ℕ)^8443*50000000000000^6395 ≤ 21442673150553^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633109649 5000000000 21442673150553 50000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (436016549/2000000000 : ℝ)^8443 ≤ (1673126709709/12500000000000 : ℝ)^6395 := by
    have hnat : (436016549 : ℕ)^8443*12500000000000^6395 ≤ 1673126709709^6395*2000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436016549 2000000000 1673126709709 12500000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344561809/10000000000 : ℝ), (2633109649/5000000000 : ℝ), (-436016549/2000000000 : ℝ)] ![(43729640002581/100000000000000 : ℝ), (21442673150553/50000000000000 : ℝ), (1673126709709/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344561809/10000000000 : ℝ)|^8443 ≤ (43729640002581/100000000000000 : ℝ)^6395
        have hw : |(5344561809/10000000000 : ℝ)|=(5344561809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633109649/5000000000 : ℝ)|^8443 ≤ (21442673150553/50000000000000 : ℝ)^6395
        have hw : |(2633109649/5000000000 : ℝ)|=(2633109649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-436016549/2000000000 : ℝ)|^8443 ≤ (1673126709709/12500000000000 : ℝ)^6395
        have hw : |(-436016549/2000000000 : ℝ)|=(436016549/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s5_3 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4349619459/10000000000 : ℝ)*x 0 + (4223454239/10000000000 : ℝ)*x 1 + (895887867/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4349619459/10000000000 : ℝ)^8443 ≤ (16658473930621/50000000000000 : ℝ)^6395 := by
    have hnat : (4349619459 : ℕ)^8443*50000000000000^6395 ≤ 16658473930621^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4349619459 10000000000 16658473930621 50000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4223454239/10000000000 : ℝ)^8443 ≤ (32047033216693/100000000000000 : ℝ)^6395 := by
    have hnat : (4223454239 : ℕ)^8443*100000000000000^6395 ≤ 32047033216693^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4223454239 10000000000 32047033216693 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (895887867/2000000000 : ℝ)^8443 ≤ (17318009453591/50000000000000 : ℝ)^6395 := by
    have hnat : (895887867 : ℕ)^8443*50000000000000^6395 ≤ 17318009453591^6395*2000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895887867 2000000000 17318009453591 50000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4349619459/10000000000 : ℝ), (4223454239/10000000000 : ℝ), (895887867/2000000000 : ℝ)] ![(16658473930621/50000000000000 : ℝ), (32047033216693/100000000000000 : ℝ), (17318009453591/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4349619459/10000000000 : ℝ)|^8443 ≤ (16658473930621/50000000000000 : ℝ)^6395
        have hw : |(4349619459/10000000000 : ℝ)|=(4349619459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4223454239/10000000000 : ℝ)|^8443 ≤ (32047033216693/100000000000000 : ℝ)^6395
        have hw : |(4223454239/10000000000 : ℝ)|=(4223454239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(895887867/2000000000 : ℝ)|^8443 ≤ (17318009453591/50000000000000 : ℝ)^6395
        have hw : |(895887867/2000000000 : ℝ)|=(895887867/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s5_4 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-529047533/2500000000 : ℝ)*x 0 + (5266543087/10000000000 : ℝ)*x 1 + (539188989/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529047533/2500000000 : ℝ)^8443 ≤ (12869552352569/100000000000000 : ℝ)^6395 := by
    have hnat : (529047533 : ℕ)^8443*100000000000000^6395 ≤ 12869552352569^6395*2500000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529047533 2500000000 12869552352569 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266543087/10000000000 : ℝ)^8443 ≤ (21444413765033/50000000000000 : ℝ)^6395 := by
    have hnat : (5266543087 : ℕ)^8443*50000000000000^6395 ≤ 21444413765033^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266543087 10000000000 21444413765033 50000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539188989/1000000000 : ℝ)^8443 ≤ (4424162010633/10000000000000 : ℝ)^6395 := by
    have hnat : (539188989 : ℕ)^8443*10000000000000^6395 ≤ 4424162010633^6395*1000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539188989 1000000000 4424162010633 10000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-529047533/2500000000 : ℝ), (5266543087/10000000000 : ℝ), (539188989/1000000000 : ℝ)] ![(12869552352569/100000000000000 : ℝ), (21444413765033/50000000000000 : ℝ), (4424162010633/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-529047533/2500000000 : ℝ)|^8443 ≤ (12869552352569/100000000000000 : ℝ)^6395
        have hw : |(-529047533/2500000000 : ℝ)|=(529047533/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266543087/10000000000 : ℝ)|^8443 ≤ (21444413765033/50000000000000 : ℝ)^6395
        have hw : |(5266543087/10000000000 : ℝ)|=(5266543087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539188989/1000000000 : ℝ)|^8443 ≤ (4424162010633/10000000000000 : ℝ)^6395
        have hw : |(539188989/1000000000 : ℝ)|=(539188989/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s5_5 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312396483/10000000000 : ℝ)*x 0 + (-1027206281/5000000000 : ℝ)*x 1 + (539188959/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312396483/10000000000 : ℝ)^8443 ≤ (43382512760209/100000000000000 : ℝ)^6395 := by
    have hnat : (5312396483 : ℕ)^8443*100000000000000^6395 ≤ 43382512760209^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312396483 10000000000 43382512760209 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1027206281/5000000000 : ℝ)^8443 ≤ (1546983794871/12500000000000 : ℝ)^6395 := by
    have hnat : (1027206281 : ℕ)^8443*12500000000000^6395 ≤ 1546983794871^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027206281 5000000000 1546983794871 12500000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539188959/1000000000 : ℝ)^8443 ≤ (44241616856449/100000000000000 : ℝ)^6395 := by
    have hnat : (539188959 : ℕ)^8443*100000000000000^6395 ≤ 44241616856449^6395*1000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539188959 1000000000 44241616856449 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312396483/10000000000 : ℝ), (-1027206281/5000000000 : ℝ), (539188959/1000000000 : ℝ)] ![(43382512760209/100000000000000 : ℝ), (1546983794871/12500000000000 : ℝ), (44241616856449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312396483/10000000000 : ℝ)|^8443 ≤ (43382512760209/100000000000000 : ℝ)^6395
        have hw : |(5312396483/10000000000 : ℝ)|=(5312396483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1027206281/5000000000 : ℝ)|^8443 ≤ (1546983794871/12500000000000 : ℝ)^6395
        have hw : |(-1027206281/5000000000 : ℝ)|=(1027206281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539188959/1000000000 : ℝ)|^8443 ≤ (44241616856449/100000000000000 : ℝ)^6395
        have hw : |(539188959/1000000000 : ℝ)|=(539188959/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s5_6 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328099111/2500000000 : ℝ)*x 0 + (5391889851/10000000000 : ℝ)*x 1 + (-2054412259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328099111/2500000000 : ℝ)^8443 ≤ (43382512339729/100000000000000 : ℝ)^6395 := by
    have hnat : (1328099111 : ℕ)^8443*100000000000000^6395 ≤ 43382512339729^6395*2500000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328099111 2500000000 43382512339729 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391889851/10000000000 : ℝ)^8443 ≤ (22120809841923/50000000000000 : ℝ)^6395 := by
    have hnat : (5391889851 : ℕ)^8443*50000000000000^6395 ≤ 22120809841923^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391889851 10000000000 22120809841923 50000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2054412259/10000000000 : ℝ)^8443 ≤ (2475173589827/20000000000000 : ℝ)^6395 := by
    have hnat : (2054412259 : ℕ)^8443*20000000000000^6395 ≤ 2475173589827^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2054412259 10000000000 2475173589827 20000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328099111/2500000000 : ℝ), (5391889851/10000000000 : ℝ), (-2054412259/10000000000 : ℝ)] ![(43382512339729/100000000000000 : ℝ), (22120809841923/50000000000000 : ℝ), (2475173589827/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328099111/2500000000 : ℝ)|^8443 ≤ (43382512339729/100000000000000 : ℝ)^6395
        have hw : |(1328099111/2500000000 : ℝ)|=(1328099111/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391889851/10000000000 : ℝ)|^8443 ≤ (22120809841923/50000000000000 : ℝ)^6395
        have hw : |(5391889851/10000000000 : ℝ)|=(5391889851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2054412259/10000000000 : ℝ)|^8443 ≤ (2475173589827/20000000000000 : ℝ)^6395
        have hw : |(-2054412259/10000000000 : ℝ)|=(2054412259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s5_7 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4349629509/10000000000 : ℝ)*x 0 + (4478781861/10000000000 : ℝ)*x 1 + (4224114043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4349629509/10000000000 : ℝ)^8443 ≤ (33317049494631/100000000000000 : ℝ)^6395 := by
    have hnat : (4349629509 : ℕ)^8443*100000000000000^6395 ≤ 33317049494631^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4349629509 10000000000 33317049494631 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4478781861/10000000000 : ℝ)^8443 ≤ (3462930726299/10000000000000 : ℝ)^6395 := by
    have hnat : (4478781861 : ℕ)^8443*10000000000000^6395 ≤ 3462930726299^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4478781861 10000000000 3462930726299 10000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4224114043/10000000000 : ℝ)^8443 ≤ (16026821613111/50000000000000 : ℝ)^6395 := by
    have hnat : (4224114043 : ℕ)^8443*50000000000000^6395 ≤ 16026821613111^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224114043 10000000000 16026821613111 50000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4349629509/10000000000 : ℝ), (4478781861/10000000000 : ℝ), (4224114043/10000000000 : ℝ)] ![(33317049494631/100000000000000 : ℝ), (3462930726299/10000000000000 : ℝ), (16026821613111/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4349629509/10000000000 : ℝ)|^8443 ≤ (33317049494631/100000000000000 : ℝ)^6395
        have hw : |(4349629509/10000000000 : ℝ)|=(4349629509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4478781861/10000000000 : ℝ)|^8443 ≤ (3462930726299/10000000000000 : ℝ)^6395
        have hw : |(4478781861/10000000000 : ℝ)|=(4478781861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4224114043/10000000000 : ℝ)|^8443 ≤ (16026821613111/50000000000000 : ℝ)^6395
        have hw : |(4224114043/10000000000 : ℝ)|=(4224114043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1250_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151585227/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2273/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (1433/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14133/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2273/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2273/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2273/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2273/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2273/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2273/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2273/20000 : ℝ) ^ (4221/1024 : ℝ) ≤ (1599192851046939/12500000000000000000 : ℝ) := by
    have hpowers : (2273/20000 : ℝ)^4221 ≤ (1599192851046939/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2273 : ℕ)^4221*12500000000000000000^1024 ≤ 1599192851046939^1024*20000^4221 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2273 20000 1599192851046939 12500000000000000000 4221 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2273/20000 : ℝ)) (X := (1599192851046939/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14237/100000 : ℝ) ^ (4221/1024 : ℝ) ≤ (32384073018913273/100000000000000000000 : ℝ) := by
    have hpowers : (14237/100000 : ℝ)^4221 ≤ (32384073018913273/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14237 : ℕ)^4221*100000000000000000000^1024 ≤ 32384073018913273^1024*100000^4221 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14237 100000 32384073018913273 100000000000000000000 4221 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14237/100000 : ℝ)) (X := (32384073018913273/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251599192851046939/6250000000000000000 : ℝ) ≤ (2000124134741489/2000000000000000 : ℝ) ^ (4221/1024 : ℝ) := by
    have hpowers : (6251599192851046939/6250000000000000000 : ℝ)^1024 ≤ (2000124134741489/2000000000000000 : ℝ)^4221 := by
      have hnat : (6251599192851046939 : ℕ)^1024*2000000000000000^4221 ≤ 2000124134741489^4221*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251599192851046939 6250000000000000000 2000124134741489 2000000000000000 1024 4221 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000124134741489/2000000000000000 : ℝ)) (X := (6251599192851046939/6250000000000000000 : ℝ)) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009035523165457757/20000000000000000000 : ℝ) ≤ (10001095805871353/10000000000000000 : ℝ) ^ (4221/1024 : ℝ) := by
    have hpowers : (20009035523165457757/20000000000000000000 : ℝ)^1024 ≤ (10001095805871353/10000000000000000 : ℝ)^4221 := by
      have hnat : (20009035523165457757 : ℕ)^1024*10000000000000000^4221 ≤ 10001095805871353^4221*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009035523165457757 20000000000000000000 10001095805871353 10000000000000000 1024 4221 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001095805871353/10000000000000000 : ℝ)) (X := (20009035523165457757/20000000000000000000 : ℝ)) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032384073018913273/50000000000000000000 : ℝ) ≤ (10001570938035261/10000000000000000 : ℝ) ^ (4221/1024 : ℝ) := by
    have hpowers : (50032384073018913273/50000000000000000000 : ℝ)^1024 ≤ (10001570938035261/10000000000000000 : ℝ)^4221 := by
      have hnat : (50032384073018913273 : ℕ)^1024*10000000000000000^4221 ≤ 10001570938035261^4221*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032384073018913273 50000000000000000000 10001570938035261 10000000000000000 1024 4221 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001570938035261/10000000000000000 : ℝ)) (X := (50032384073018913273/50000000000000000000 : ℝ)) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1599192851046939/12500000000000000000 : ℝ) ≤ ((71777457052005383/71800000000000000 : ℝ)+2*(118783040977/71800000000000 : ℝ)*(2273/20000 : ℝ))^(4221/1024 : ℝ) := by
    rw [show (71777457052005383/71800000000000000 : ℝ)+2*(118783040977/71800000000000 : ℝ)*(2273/20000 : ℝ)=(2000124134741489/2000000000000000 : ℝ) by norm_num, show 1+2*(1599192851046939/12500000000000000000 : ℝ)=(6251599192851046939/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32384073018913273/100000000000000000000 : ℝ)+(1599192851046939/12500000000000000000 : ℝ) ≤ ((71777457052005383/71800000000000000 : ℝ)+(118783040977/71800000000000 : ℝ)*((14237/100000 : ℝ)+(2273/20000 : ℝ)))^(4221/1024 : ℝ) := by
    rw [show (71777457052005383/71800000000000000 : ℝ)+(118783040977/71800000000000 : ℝ)*((14237/100000 : ℝ)+(2273/20000 : ℝ))=(10001095805871353/10000000000000000 : ℝ) by norm_num, show 1+(32384073018913273/100000000000000000000 : ℝ)+(1599192851046939/12500000000000000000 : ℝ)=(20009035523165457757/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32384073018913273/100000000000000000000 : ℝ) ≤ ((71777457052005383/71800000000000000 : ℝ)+2*(118783040977/71800000000000 : ℝ)*(14237/100000 : ℝ))^(4221/1024 : ℝ) := by
    rw [show (71777457052005383/71800000000000000 : ℝ)+2*(118783040977/71800000000000 : ℝ)*(14237/100000 : ℝ)=(10001570938035261/10000000000000000 : ℝ) by norm_num, show 1+2*(32384073018913273/100000000000000000000 : ℝ)=(50032384073018913273/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (71777457052005383/71800000000000000 : ℝ)*(X 1 0+X 2 0)+(118783040977/71800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4221/1024 : ℝ)) (lo := (2273/20000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (71777457052005383/71800000000000000 : ℝ)) (alpha := (118783040977/71800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (71777457052005383/71800000000000000 : ℝ)*(X 0 1+X 2 1)+(118783040977/71800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4221/1024 : ℝ)) (lo := (2273/20000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (71777457052005383/71800000000000000 : ℝ)) (alpha := (118783040977/71800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (71777457052005383/71800000000000000 : ℝ)*(X 0 2+X 1 2)+(118783040977/71800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4221/1024 : ℝ)) (lo := (2273/20000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (71777457052005383/71800000000000000 : ℝ)) (alpha := (118783040977/71800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-423237139/2000000000 : ℝ)*X 0 0+(107844291/200000000 : ℝ)*X 0 1+(5266219279/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068912351/2000000000 : ℝ)*X 1 0+(-87203313/400000000 : ℝ)*X 1 1+(1316554823/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344561809/10000000000 : ℝ)*X 2 0+(2633109649/5000000000 : ℝ)*X 2 1+(-436016549/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4349619459/10000000000 : ℝ)*X 0 0+(4223454239/10000000000 : ℝ)*X 0 1+(895887867/2000000000 : ℝ)*X 0 2+(4349619459/10000000000 : ℝ)*X 1 0+(4223454239/10000000000 : ℝ)*X 1 1+(895887867/2000000000 : ℝ)*X 1 2+(4349619459/10000000000 : ℝ)*X 2 0+(4223454239/10000000000 : ℝ)*X 2 1+(895887867/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-529047533/2500000000 : ℝ)*X 0 0+(5266543087/10000000000 : ℝ)*X 0 1+(539188989/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312396483/10000000000 : ℝ)*X 1 0+(-1027206281/5000000000 : ℝ)*X 1 1+(539188959/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328099111/2500000000 : ℝ)*X 2 0+(5391889851/10000000000 : ℝ)*X 2 1+(-2054412259/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4349629509/10000000000 : ℝ)*X 0 0+(4478781861/10000000000 : ℝ)*X 0 1+(4224114043/10000000000 : ℝ)*X 0 2+(4349629509/10000000000 : ℝ)*X 1 0+(4478781861/10000000000 : ℝ)*X 1 1+(4224114043/10000000000 : ℝ)*X 1 2+(4349629509/10000000000 : ℝ)*X 2 0+(4478781861/10000000000 : ℝ)*X 2 1+(4224114043/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (33645756809336950972854669/3590000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (958825003/50000000000000 : ℝ)*(base19) + (1822448839/100000000000000 : ℝ)*(base23) + (93740177/100000000000000 : ℝ)*(lower2) + (104856309/50000000000000 : ℝ)*(upper3) + (224975873/100000000000000 : ℝ)*(upper5) + (5921721942946519/100000000000000 : ℝ)*(major0) + (5921721942946519/100000000000000 : ℝ)*(major1) + (5921721942946519/100000000000000 : ℝ)*(major2) + (3968428743105011/50000000000000 : ℝ)*(sp0) + (7936911936459209/100000000000000 : ℝ)*(sp1) + (7936912031660377/100000000000000 : ℝ)*(sp2) + (1953251484640503/50000000000000 : ℝ)*(sp3) + (28183949597/50000000000000 : ℝ)*(sp4) + (26750100237/100000000000000 : ℝ)*(sp7) + (1953264859690621/50000000000000 : ℝ)*(f.failure) + (248028557940913/3125000000000 : ℝ)*(f.sum) + (554016753553/3590000000000000000000000000 : ℝ)*base65 + (56232080849245223/7180000000000000000000000000000 : ℝ)*base68 + (147699425774645223/7180000000000000000000000000000 : ℝ)*base70 + (35048955691414777/7180000000000000000000000000000 : ℝ)*base71 + (6130920727877/3590000000000000000000000000 : ℝ)*base74 + (100443548113954777/7180000000000000000000000000000 : ℝ)*base75 + (26190342069774777/7180000000000000000000000000000 : ℝ)*base77 + (12110294168514777/7180000000000000000000000000000 : ℝ)*base79 + (27634677057177/3590000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (15944033/5000000000000000000000 : ℝ)*base90 + (15944033/5000000000000000000000 : ℝ)*base92 + (15944033/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9889541093124421005993/3590000000000000000000000000 : ℝ) := by norm_num
    linear_combination (107579221/100000000000000 : ℝ)*(base8) + (98497349/50000000000000 : ℝ)*(lower2) + (1953747/12500000000000 : ℝ)*(lower3) + (171934147/100000000000000 : ℝ)*(lower4) + (5952297543367447/100000000000000 : ℝ)*(major0) + (5952297543367447/100000000000000 : ℝ)*(major1) + (5952297543367447/100000000000000 : ℝ)*(major2) + (6592684187/50000000000000 : ℝ)*(sp0) + (3492845961/20000000000000 : ℝ)*(sp2) + (202080373/2500000000000 : ℝ)*(sp3) + (1595576283030891/20000000000000 : ℝ)*(sp4) + (159557894162041/2000000000000 : ℝ)*(sp5) + (3988938621936123/50000000000000 : ℝ)*(sp6) + (1963346101796503/50000000000000 : ℝ)*(sp7) + (1963350143403963/50000000000000 : ℝ)*(f.failure) + (159557894162041/2000000000000 : ℝ)*(f.sum) + (39658293819241/3590000000000000000000000000 : ℝ)*base66 + (66780391029893799/7180000000000000000000000000000 : ℝ)*base68 + (252884191887033799/7180000000000000000000000000000 : ℝ)*base70 + (452542966168433799/7180000000000000000000000000000 : ℝ)*base72 + (12469713849579/3590000000000000000000000000 : ℝ)*base73 + (23732364588246201/7180000000000000000000000000000 : ℝ)*base75 + (65722929941146201/7180000000000000000000000000000 : ℝ)*base77 + (123233943881926201/7180000000000000000000000000000 : ℝ)*base79 + (41271475837509/3590000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (65945399/5000000000000000000000 : ℝ)*base90 + (65945399/5000000000000000000000 : ℝ)*base92 + (65945399/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1250_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151585227/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2273/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1433/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14133/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1250_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1250_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151585227/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8101/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2383/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1433/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14133/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1250_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1250_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1250_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151585227/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8101/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2383/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1433/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14133/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1250_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
