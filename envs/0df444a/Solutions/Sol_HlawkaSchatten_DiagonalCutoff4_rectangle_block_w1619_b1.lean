-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1619_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:53:47.792484+00:00
-- url     : https://prove2.me/submissions/9c7426f2-2906-428d-8839-601cc28a2ac0

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
theorem support_rectangle_w1619_s3_0 (p : ℝ) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-210224871/1250000000 : ℝ)*x 0 + (5457136667/10000000000 : ℝ)*x 1 + (2590632267/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210224871/1250000000 : ℝ)^4795 ≤ (2591052018831/25000000000000 : ℝ)^3771 := by
    have hnat : (210224871 : ℕ)^4795*25000000000000^3771 ≤ 2591052018831^3771*1250000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210224871 1250000000 2591052018831 25000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5457136667/10000000000 : ℝ)^4795 ≤ (4629548942293/10000000000000 : ℝ)^3771 := by
    have hnat : (5457136667 : ℕ)^4795*10000000000000^3771 ≤ 4629548942293^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457136667 10000000000 4629548942293 10000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2590632267/5000000000 : ℝ)^4795 ≤ (21670151244967/50000000000000 : ℝ)^3771 := by
    have hnat : (2590632267 : ℕ)^4795*50000000000000^3771 ≤ 21670151244967^3771*5000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590632267 5000000000 21670151244967 50000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4795/1024 : ℝ)) 4795 3771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-210224871/1250000000 : ℝ), (5457136667/10000000000 : ℝ), (2590632267/5000000000 : ℝ)] ![(2591052018831/25000000000000 : ℝ), (4629548942293/10000000000000 : ℝ), (21670151244967/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-210224871/1250000000 : ℝ)|^4795 ≤ (2591052018831/25000000000000 : ℝ)^3771
        have hw : |(-210224871/1250000000 : ℝ)|=(210224871/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5457136667/10000000000 : ℝ)|^4795 ≤ (4629548942293/10000000000000 : ℝ)^3771
        have hw : |(5457136667/10000000000 : ℝ)|=(5457136667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2590632267/5000000000 : ℝ)|^4795 ≤ (21670151244967/50000000000000 : ℝ)^3771
        have hw : |(2590632267/5000000000 : ℝ)|=(2590632267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1619_s3_1 (p : ℝ) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669049531/1250000000 : ℝ)*x 0 + (-364801581/2000000000 : ℝ)*x 1 + (207250589/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669049531/1250000000 : ℝ)^4795 ≤ (45168599009753/100000000000000 : ℝ)^3771 := by
    have hnat : (669049531 : ℕ)^4795*100000000000000^3771 ≤ 45168599009753^3771*1250000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669049531 1250000000 45168599009753 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (364801581/2000000000 : ℝ)^4795 ≤ (1436387057177/12500000000000 : ℝ)^3771 := by
    have hnat : (364801581 : ℕ)^4795*12500000000000^3771 ≤ 1436387057177^3771*2000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      364801581 2000000000 1436387057177 12500000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207250589/400000000 : ℝ)^4795 ≤ (2708769032591/6250000000000 : ℝ)^3771 := by
    have hnat : (207250589 : ℕ)^4795*6250000000000^3771 ≤ 2708769032591^3771*400000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207250589 400000000 2708769032591 6250000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4795/1024 : ℝ)) 4795 3771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669049531/1250000000 : ℝ), (-364801581/2000000000 : ℝ), (207250589/400000000 : ℝ)] ![(45168599009753/100000000000000 : ℝ), (1436387057177/12500000000000 : ℝ), (2708769032591/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669049531/1250000000 : ℝ)|^4795 ≤ (45168599009753/100000000000000 : ℝ)^3771
        have hw : |(669049531/1250000000 : ℝ)|=(669049531/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-364801581/2000000000 : ℝ)|^4795 ≤ (1436387057177/12500000000000 : ℝ)^3771
        have hw : |(-364801581/2000000000 : ℝ)|=(364801581/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(207250589/400000000 : ℝ)|^4795 ≤ (2708769032591/6250000000000 : ℝ)^3771
        have hw : |(207250589/400000000 : ℝ)|=(207250589/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1619_s3_2 (p : ℝ) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352396293/10000000000 : ℝ)*x 0 + (2590632451/5000000000 : ℝ)*x 1 + (-182400761/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352396293/10000000000 : ℝ)^4795 ≤ (22584299746313/50000000000000 : ℝ)^3771 := by
    have hnat : (5352396293 : ℕ)^4795*50000000000000^3771 ≤ 22584299746313^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352396293 10000000000 22584299746313 50000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2590632451/5000000000 : ℝ)^4795 ≤ (43340306404071/100000000000000 : ℝ)^3771 := by
    have hnat : (2590632451 : ℕ)^4795*100000000000000^3771 ≤ 43340306404071^3771*5000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590632451 5000000000 43340306404071 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (182400761/1000000000 : ℝ)^4795 ≤ (11491094094279/100000000000000 : ℝ)^3771 := by
    have hnat : (182400761 : ℕ)^4795*100000000000000^3771 ≤ 11491094094279^3771*1000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182400761 1000000000 11491094094279 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4795/1024 : ℝ)) 4795 3771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352396293/10000000000 : ℝ), (2590632451/5000000000 : ℝ), (-182400761/1000000000 : ℝ)] ![(22584299746313/50000000000000 : ℝ), (43340306404071/100000000000000 : ℝ), (11491094094279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352396293/10000000000 : ℝ)|^4795 ≤ (22584299746313/50000000000000 : ℝ)^3771
        have hw : |(5352396293/10000000000 : ℝ)|=(5352396293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2590632451/5000000000 : ℝ)|^4795 ≤ (43340306404071/100000000000000 : ℝ)^3771
        have hw : |(2590632451/5000000000 : ℝ)|=(2590632451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-182400761/1000000000 : ℝ)|^4795 ≤ (11491094094279/100000000000000 : ℝ)^3771
        have hw : |(-182400761/1000000000 : ℝ)|=(182400761/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1619_s3_3 (p : ℝ) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (525641057/1250000000 : ℝ)*x 0 + (3872776579/10000000000 : ℝ)*x 1 + (4558728069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525641057/1250000000 : ℝ)^4795 ≤ (16618355022797/50000000000000 : ℝ)^3771 := by
    have hnat : (525641057 : ℕ)^4795*50000000000000^3771 ≤ 16618355022797^3771*1250000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525641057 1250000000 16618355022797 50000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3872776579/10000000000 : ℝ)^4795 ≤ (598661841867/2000000000000 : ℝ)^3771 := by
    have hnat : (3872776579 : ℕ)^4795*2000000000000^3771 ≤ 598661841867^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3872776579 10000000000 598661841867 2000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4558728069/10000000000 : ℝ)^4795 ≤ (36830197844011/100000000000000 : ℝ)^3771 := by
    have hnat : (4558728069 : ℕ)^4795*100000000000000^3771 ≤ 36830197844011^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4558728069 10000000000 36830197844011 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4795/1024 : ℝ)) 4795 3771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525641057/1250000000 : ℝ), (3872776579/10000000000 : ℝ), (4558728069/10000000000 : ℝ)] ![(16618355022797/50000000000000 : ℝ), (598661841867/2000000000000 : ℝ), (36830197844011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525641057/1250000000 : ℝ)|^4795 ≤ (16618355022797/50000000000000 : ℝ)^3771
        have hw : |(525641057/1250000000 : ℝ)|=(525641057/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3872776579/10000000000 : ℝ)|^4795 ≤ (598661841867/2000000000000 : ℝ)^3771
        have hw : |(3872776579/10000000000 : ℝ)|=(3872776579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4558728069/10000000000 : ℝ)|^4795 ≤ (36830197844011/100000000000000 : ℝ)^3771
        have hw : |(4558728069/10000000000 : ℝ)|=(4558728069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1619_s3_4 (p : ℝ) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-42046713/250000000 : ℝ)*x 0 + (1036665719/2000000000 : ℝ)*x 1 + (2727525367/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42046713/250000000 : ℝ)^4795 ≤ (647797067967/6250000000000 : ℝ)^3771 := by
    have hnat : (42046713 : ℕ)^4795*6250000000000^3771 ≤ 647797067967^3771*250000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42046713 250000000 647797067967 6250000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036665719/2000000000 : ℝ)^4795 ≤ (2710141095727/6250000000000 : ℝ)^3771 := by
    have hnat : (1036665719 : ℕ)^4795*6250000000000^3771 ≤ 2710141095727^3771*2000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036665719 2000000000 2710141095727 6250000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2727525367/5000000000 : ℝ)^4795 ≤ (46272989359537/100000000000000 : ℝ)^3771 := by
    have hnat : (2727525367 : ℕ)^4795*100000000000000^3771 ≤ 46272989359537^3771*5000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2727525367 5000000000 46272989359537 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4795/1024 : ℝ)) 4795 3771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-42046713/250000000 : ℝ), (1036665719/2000000000 : ℝ), (2727525367/5000000000 : ℝ)] ![(647797067967/6250000000000 : ℝ), (2710141095727/6250000000000 : ℝ), (46272989359537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-42046713/250000000 : ℝ)|^4795 ≤ (647797067967/6250000000000 : ℝ)^3771
        have hw : |(-42046713/250000000 : ℝ)|=(42046713/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036665719/2000000000 : ℝ)|^4795 ≤ (2710141095727/6250000000000 : ℝ)^3771
        have hw : |(1036665719/2000000000 : ℝ)|=(1036665719/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2727525367/5000000000 : ℝ)|^4795 ≤ (46272989359537/100000000000000 : ℝ)^3771
        have hw : |(2727525367/5000000000 : ℝ)|=(2727525367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1619_s3_5 (p : ℝ) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (263950893/500000000 : ℝ)*x 0 + (-96888873/625000000 : ℝ)*x 1 + (5455049799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (263950893/500000000 : ℝ)^4795 ≤ (5547835233963/12500000000000 : ℝ)^3771 := by
    have hnat : (263950893 : ℕ)^4795*12500000000000^3771 ≤ 5547835233963^3771*500000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263950893 500000000 5547835233963 12500000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (96888873/625000000 : ℝ)^4795 ≤ (9344338836001/100000000000000 : ℝ)^3771 := by
    have hnat : (96888873 : ℕ)^4795*100000000000000^3771 ≤ 9344338836001^3771*625000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96888873 625000000 9344338836001 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5455049799/10000000000 : ℝ)^4795 ≤ (46272979274617/100000000000000 : ℝ)^3771 := by
    have hnat : (5455049799 : ℕ)^4795*100000000000000^3771 ≤ 46272979274617^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5455049799 10000000000 46272979274617 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4795/1024 : ℝ)) 4795 3771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(263950893/500000000 : ℝ), (-96888873/625000000 : ℝ), (5455049799/10000000000 : ℝ)] ![(5547835233963/12500000000000 : ℝ), (9344338836001/100000000000000 : ℝ), (46272979274617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(263950893/500000000 : ℝ)|^4795 ≤ (5547835233963/12500000000000 : ℝ)^3771
        have hw : |(263950893/500000000 : ℝ)|=(263950893/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-96888873/625000000 : ℝ)|^4795 ≤ (9344338836001/100000000000000 : ℝ)^3771
        have hw : |(-96888873/625000000 : ℝ)|=(96888873/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5455049799/10000000000 : ℝ)|^4795 ≤ (46272979274617/100000000000000 : ℝ)^3771
        have hw : |(5455049799/10000000000 : ℝ)|=(5455049799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1619_s3_6 (p : ℝ) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319754269/2500000000 : ℝ)*x 0 + (5455050543/10000000000 : ℝ)*x 1 + (-24222219/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319754269/2500000000 : ℝ)^4795 ≤ (44382673490459/100000000000000 : ℝ)^3771 := by
    have hnat : (1319754269 : ℕ)^4795*100000000000000^3771 ≤ 44382673490459^3771*2500000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319754269 2500000000 44382673490459 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5455050543/10000000000 : ℝ)^4795 ≤ (46272987299409/100000000000000 : ℝ)^3771 := by
    have hnat : (5455050543 : ℕ)^4795*100000000000000^3771 ≤ 46272987299409^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5455050543 10000000000 46272987299409 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (24222219/156250000 : ℝ)^4795 ≤ (9344339203899/100000000000000 : ℝ)^3771 := by
    have hnat : (24222219 : ℕ)^4795*100000000000000^3771 ≤ 9344339203899^3771*156250000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24222219 156250000 9344339203899 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4795/1024 : ℝ)) 4795 3771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319754269/2500000000 : ℝ), (5455050543/10000000000 : ℝ), (-24222219/156250000 : ℝ)] ![(44382673490459/100000000000000 : ℝ), (46272987299409/100000000000000 : ℝ), (9344339203899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319754269/2500000000 : ℝ)|^4795 ≤ (44382673490459/100000000000000 : ℝ)^3771
        have hw : |(1319754269/2500000000 : ℝ)|=(1319754269/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5455050543/10000000000 : ℝ)|^4795 ≤ (46272987299409/100000000000000 : ℝ)^3771
        have hw : |(5455050543/10000000000 : ℝ)|=(5455050543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-24222219/156250000 : ℝ)|^4795 ≤ (9344339203899/100000000000000 : ℝ)^3771
        have hw : |(-24222219/156250000 : ℝ)|=(24222219/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1619_s3_7 (p : ℝ) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2102650627/5000000000 : ℝ)*x 0 + (4553595069/10000000000 : ℝ)*x 1 + (775592703/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2102650627/5000000000 : ℝ)^4795 ≤ (8309611673573/25000000000000 : ℝ)^3771 := by
    have hnat : (2102650627 : ℕ)^4795*25000000000000^3771 ≤ 8309611673573^3771*5000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2102650627 5000000000 8309611673573 25000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4553595069/10000000000 : ℝ)^4795 ≤ (18388737593343/50000000000000 : ℝ)^3771 := by
    have hnat : (4553595069 : ℕ)^4795*50000000000000^3771 ≤ 18388737593343^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4553595069 10000000000 18388737593343 50000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (775592703/2000000000 : ℝ)^4795 ≤ (7496019526479/25000000000000 : ℝ)^3771 := by
    have hnat : (775592703 : ℕ)^4795*25000000000000^3771 ≤ 7496019526479^3771*2000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      775592703 2000000000 7496019526479 25000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4795/1024 : ℝ)) 4795 3771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2102650627/5000000000 : ℝ), (4553595069/10000000000 : ℝ), (775592703/2000000000 : ℝ)] ![(8309611673573/25000000000000 : ℝ), (18388737593343/50000000000000 : ℝ), (7496019526479/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2102650627/5000000000 : ℝ)|^4795 ≤ (8309611673573/25000000000000 : ℝ)^3771
        have hw : |(2102650627/5000000000 : ℝ)|=(2102650627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4553595069/10000000000 : ℝ)|^4795 ≤ (18388737593343/50000000000000 : ℝ)^3771
        have hw : |(4553595069/10000000000 : ℝ)|=(4553595069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(775592703/2000000000 : ℝ)|^4795 ≤ (7496019526479/25000000000000 : ℝ)^3771
        have hw : |(775592703/2000000000 : ℝ)|=(775592703/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1619_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87162187/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16457/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (83/800 : ℝ)*pair X i i ≤ pair X i h) :
    (2621/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1021/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16457/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (83/800 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16457/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (83/800 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16457/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (83/800 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16457/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (83/800 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16457/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (83/800 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16457/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (83/800 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (83/800 : ℝ) ^ (4791/1024 : ℝ) ≤ (2489389113807591/100000000000000000000 : ℝ) := by
    have hpowers : (83/800 : ℝ)^4791 ≤ (2489389113807591/100000000000000000000 : ℝ)^1024 := by
      have hnat : (83 : ℕ)^4791*100000000000000000000^1024 ≤ 2489389113807591^1024*800^4791 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        83 800 2489389113807591 100000000000000000000 4791 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (83/800 : ℝ)) (X := (2489389113807591/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4791 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16457/100000 : ℝ) ^ (4791/1024 : ℝ) ≤ (336783906774423/1562500000000000000 : ℝ) := by
    have hpowers : (16457/100000 : ℝ)^4791 ≤ (336783906774423/1562500000000000000 : ℝ)^1024 := by
      have hnat : (16457 : ℕ)^4791*1562500000000000000^1024 ≤ 336783906774423^1024*100000^4791 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16457 100000 336783906774423 1562500000000000000 4791 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16457/100000 : ℝ)) (X := (336783906774423/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 4791 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002489389113807591/50000000000000000000 : ℝ) ≤ (1000010641137797/1000000000000000 : ℝ) ^ (4791/1024 : ℝ) := by
    have hpowers : (50002489389113807591/50000000000000000000 : ℝ)^1024 ≤ (1000010641137797/1000000000000000 : ℝ)^4791 := by
      have hnat : (50002489389113807591 : ℕ)^1024*1000000000000000^4791 ≤ 1000010641137797^4791*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002489389113807591 50000000000000000000 1000010641137797 1000000000000000 1024 4791 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000010641137797/1000000000000000 : ℝ)) (X := (50002489389113807591/50000000000000000000 : ℝ)) (by norm_num) 4791 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100024043559147370663/100000000000000000000 : ℝ) ≤ (5000256922121507/5000000000000000 : ℝ) ^ (4791/1024 : ℝ) := by
    have hpowers : (100024043559147370663/100000000000000000000 : ℝ)^1024 ≤ (5000256922121507/5000000000000000 : ℝ)^4791 := by
      have hnat : (100024043559147370663 : ℕ)^1024*5000000000000000^4791 ≤ 5000256922121507^4791*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100024043559147370663 100000000000000000000 5000256922121507 5000000000000000 1024 4791 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000256922121507/5000000000000000 : ℝ)) (X := (100024043559147370663/100000000000000000000 : ℝ)) (by norm_num) 4791 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (781586783906774423/781250000000000000 : ℝ) ≤ (5000460638554029/5000000000000000 : ℝ) ^ (4791/1024 : ℝ) := by
    have hpowers : (781586783906774423/781250000000000000 : ℝ)^1024 ≤ (5000460638554029/5000000000000000 : ℝ)^4791 := by
      have hnat : (781586783906774423 : ℕ)^1024*5000000000000000^4791 ≤ 5000460638554029^4791*781250000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781586783906774423 781250000000000000 5000460638554029 5000000000000000 1024 4791 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000460638554029/5000000000000000 : ℝ)) (X := (781586783906774423/781250000000000000 : ℝ)) (by norm_num) 4791 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2489389113807591/100000000000000000000 : ℝ) ≤ ((3040609648102557527/3041000000000000000 : ℝ)+2*(101858216261/152050000000000 : ℝ)*(83/800 : ℝ))^(4791/1024 : ℝ) := by
    rw [show (3040609648102557527/3041000000000000000 : ℝ)+2*(101858216261/152050000000000 : ℝ)*(83/800 : ℝ)=(1000010641137797/1000000000000000 : ℝ) by norm_num, show 1+2*(2489389113807591/100000000000000000000 : ℝ)=(50002489389113807591/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(336783906774423/1562500000000000000 : ℝ)+(2489389113807591/100000000000000000000 : ℝ) ≤ ((3040609648102557527/3041000000000000000 : ℝ)+(101858216261/152050000000000 : ℝ)*((16457/100000 : ℝ)+(83/800 : ℝ)))^(4791/1024 : ℝ) := by
    rw [show (3040609648102557527/3041000000000000000 : ℝ)+(101858216261/152050000000000 : ℝ)*((16457/100000 : ℝ)+(83/800 : ℝ))=(5000256922121507/5000000000000000 : ℝ) by norm_num, show 1+(336783906774423/1562500000000000000 : ℝ)+(2489389113807591/100000000000000000000 : ℝ)=(100024043559147370663/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(336783906774423/1562500000000000000 : ℝ) ≤ ((3040609648102557527/3041000000000000000 : ℝ)+2*(101858216261/152050000000000 : ℝ)*(16457/100000 : ℝ))^(4791/1024 : ℝ) := by
    rw [show (3040609648102557527/3041000000000000000 : ℝ)+2*(101858216261/152050000000000 : ℝ)*(16457/100000 : ℝ)=(5000460638554029/5000000000000000 : ℝ) by norm_num, show 1+2*(336783906774423/1562500000000000000 : ℝ)=(781586783906774423/781250000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3040609648102557527/3041000000000000000 : ℝ)*(X 1 0+X 2 0)+(101858216261/152050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4791/1024 : ℝ)) (lo := (83/800 : ℝ)) (hi := (16457/100000 : ℝ)) (c := (3040609648102557527/3041000000000000000 : ℝ)) (alpha := (101858216261/152050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3040609648102557527/3041000000000000000 : ℝ)*(X 0 1+X 2 1)+(101858216261/152050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4791/1024 : ℝ)) (lo := (83/800 : ℝ)) (hi := (16457/100000 : ℝ)) (c := (3040609648102557527/3041000000000000000 : ℝ)) (alpha := (101858216261/152050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3040609648102557527/3041000000000000000 : ℝ)*(X 0 2+X 1 2)+(101858216261/152050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4791/1024 : ℝ)) (lo := (83/800 : ℝ)) (hi := (16457/100000 : ℝ)) (c := (3040609648102557527/3041000000000000000 : ℝ)) (alpha := (101858216261/152050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-210224871/1250000000 : ℝ)*X 0 0+(5457136667/10000000000 : ℝ)*X 0 1+(2590632267/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1619_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((669049531/1250000000 : ℝ)*X 1 0+(-364801581/2000000000 : ℝ)*X 1 1+(207250589/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1619_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352396293/10000000000 : ℝ)*X 2 0+(2590632451/5000000000 : ℝ)*X 2 1+(-182400761/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1619_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((525641057/1250000000 : ℝ)*X 0 0+(3872776579/10000000000 : ℝ)*X 0 1+(4558728069/10000000000 : ℝ)*X 0 2+(525641057/1250000000 : ℝ)*X 1 0+(3872776579/10000000000 : ℝ)*X 1 1+(4558728069/10000000000 : ℝ)*X 1 2+(525641057/1250000000 : ℝ)*X 2 0+(3872776579/10000000000 : ℝ)*X 2 1+(4558728069/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1619_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-42046713/250000000 : ℝ)*X 0 0+(1036665719/2000000000 : ℝ)*X 0 1+(2727525367/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1619_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((263950893/500000000 : ℝ)*X 1 0+(-96888873/625000000 : ℝ)*X 1 1+(5455049799/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1619_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1319754269/2500000000 : ℝ)*X 2 0+(5455050543/10000000000 : ℝ)*X 2 1+(-24222219/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1619_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2102650627/5000000000 : ℝ)*X 0 0+(4553595069/10000000000 : ℝ)*X 0 1+(775592703/2000000000 : ℝ)*X 0 2+(2102650627/5000000000 : ℝ)*X 1 0+(4553595069/10000000000 : ℝ)*X 1 1+(775592703/2000000000 : ℝ)*X 1 2+(2102650627/5000000000 : ℝ)*X 2 0+(4553595069/10000000000 : ℝ)*X 2 1+(775592703/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1619_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (219488521372603200289514511/38012500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2200303/625000000000 : ℝ)*(base19) + (208641389/100000000000000 : ℝ)*(base23) + (46534559/50000000000000 : ℝ)*(lower2) + (610491/6250000000000 : ℝ)*(upper3) + (14012093/12500000000000 : ℝ)*(upper5) + (635339066647969/25000000000000 : ℝ)*(major0) + (635339066647969/25000000000000 : ℝ)*(major1) + (635339066647969/25000000000000 : ℝ)*(major2) + (453109013870407/12500000000000 : ℝ)*(sp0) + (90622003178267/2500000000000 : ℝ)*(sp1) + (362488027053777/10000000000000 : ℝ)*(sp2) + (291566119356561/20000000000000 : ℝ)*(sp3) + (8368215903/100000000000000 : ℝ)*(sp4) + (12647513/1000000000000 : ℝ)*(sp7) + (728915930767053/50000000000000 : ℝ)*(f.failure) + (90622011979479/2500000000000 : ℝ)*(f.sum) + (10942651541/475156250000000000000000000 : ℝ)*base65 + (887633328680592663/76025000000000000000000000000000 : ℝ)*base67 + (446183468018617663/76025000000000000000000000000000 : ℝ)*base69 + (182820751990392663/76025000000000000000000000000000 : ℝ)*base71 + (63330757595297/15205000000000000000000000000 : ℝ)*base73 + (536719238462732337/76025000000000000000000000000000 : ℝ)*base76 + (16881563678857337/76025000000000000000000000000000 : ℝ)*base78 + (415868211590017663/76025000000000000000000000000000 : ℝ)*base79 + (31868496330547/15205000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (27024911/2500000000000000000000 : ℝ)*base89 + (27024911/2500000000000000000000 : ℝ)*base91 + (27024911/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (83461922228389762456159263/9503125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (407744073/25000000000000 : ℝ)*(base19) + (595625333/50000000000000 : ℝ)*(base23) + (13550161/50000000000000 : ℝ)*(upper3) + (89856823/100000000000000 : ℝ)*(lower4) + (18787091/6250000000000 : ℝ)*(upper5) + (40315049537369/1562500000000 : ℝ)*(major0) + (40315049537369/1562500000000 : ℝ)*(major1) + (40315049537369/1562500000000 : ℝ)*(major2) + (13516752457/100000000000000 : ℝ)*(sp1) + (279903623/3125000000000 : ℝ)*(sp2) + (920058217044967/25000000000000 : ℝ)*(sp4) + (3680217720451119/100000000000000 : ℝ)*(sp5) + (1840111360006633/50000000000000 : ℝ)*(sp6) + (185011647481351/12500000000000 : ℝ)*(sp7) + (185011647481351/12500000000000 : ℝ)*(f.failure) + (920058217044967/25000000000000 : ℝ)*(f.sum) + (2299718931763/950312500000000000000000000 : ℝ)*base66 + (4638352961637713/4751562500000000000000000000000 : ℝ)*base67 + (8861532113481463/4751562500000000000000000000000 : ℝ)*base69 + (24081325267050213/4751562500000000000000000000000 : ℝ)*base71 + (32172469839323/15205000000000000000000000000 : ℝ)*base74 + (1020468207978853/1187890625000000000000000000000 : ℝ)*base76 + (22798456666568963/4751562500000000000000000000000 : ℝ)*base77 + (998457113202943/296972656250000000000000000000 : ℝ)*base79 + (188800033721/1900625000000000000000000000 : ℝ)*base82 + (5125363/625000000000000000000 : ℝ)*base90 + (5125363/625000000000000000000 : ℝ)*base92 + (5125363/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1619_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87162187/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16457/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (83/800 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2621/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1021/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1619_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1619_s4_0 (p : ℝ) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-420473311/2500000000 : ℝ)*x 0 + (5456662687/10000000000 : ℝ)*x 1 + (1295418943/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (420473311/2500000000 : ℝ)^4795 ≤ (10364946827161/100000000000000 : ℝ)^3771 := by
    have hnat : (420473311 : ℕ)^4795*100000000000000^3771 ≤ 10364946827161^3771*2500000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420473311 2500000000 10364946827161 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5456662687/10000000000 : ℝ)^4795 ≤ (46290376599161/100000000000000 : ℝ)^3771 := by
    have hnat : (5456662687 : ℕ)^4795*100000000000000^3771 ≤ 46290376599161^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5456662687 10000000000 46290376599161 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1295418943/2500000000 : ℝ)^4795 ≤ (4334467656437/10000000000000 : ℝ)^3771 := by
    have hnat : (1295418943 : ℕ)^4795*10000000000000^3771 ≤ 4334467656437^3771*2500000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295418943 2500000000 4334467656437 10000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4795/1024 : ℝ)) 4795 3771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-420473311/2500000000 : ℝ), (5456662687/10000000000 : ℝ), (1295418943/2500000000 : ℝ)] ![(10364946827161/100000000000000 : ℝ), (46290376599161/100000000000000 : ℝ), (4334467656437/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-420473311/2500000000 : ℝ)|^4795 ≤ (10364946827161/100000000000000 : ℝ)^3771
        have hw : |(-420473311/2500000000 : ℝ)|=(420473311/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5456662687/10000000000 : ℝ)|^4795 ≤ (46290376599161/100000000000000 : ℝ)^3771
        have hw : |(5456662687/10000000000 : ℝ)|=(5456662687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1295418943/2500000000 : ℝ)|^4795 ≤ (4334467656437/10000000000000 : ℝ)^3771
        have hw : |(1295418943/2500000000 : ℝ)|=(1295418943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1619_s4_1 (p : ℝ) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334516849/625000000 : ℝ)*x 0 + (-911815947/5000000000 : ℝ)*x 1 + (5181675689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334516849/625000000 : ℝ)^4795 ≤ (45167239844557/100000000000000 : ℝ)^3771 := by
    have hnat : (334516849 : ℕ)^4795*100000000000000^3771 ≤ 45167239844557^3771*625000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334516849 625000000 45167239844557 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (911815947/5000000000 : ℝ)^4795 ≤ (179501319619/1562500000000 : ℝ)^3771 := by
    have hnat : (911815947 : ℕ)^4795*1562500000000^3771 ≤ 179501319619^3771*5000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      911815947 5000000000 179501319619 1562500000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5181675689/10000000000 : ℝ)^4795 ≤ (43344675681543/100000000000000 : ℝ)^3771 := by
    have hnat : (5181675689 : ℕ)^4795*100000000000000^3771 ≤ 43344675681543^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181675689 10000000000 43344675681543 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4795/1024 : ℝ)) 4795 3771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334516849/625000000 : ℝ), (-911815947/5000000000 : ℝ), (5181675689/10000000000 : ℝ)] ![(45167239844557/100000000000000 : ℝ), (179501319619/1562500000000 : ℝ), (43344675681543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334516849/625000000 : ℝ)|^4795 ≤ (45167239844557/100000000000000 : ℝ)^3771
        have hw : |(334516849/625000000 : ℝ)|=(334516849/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-911815947/5000000000 : ℝ)|^4795 ≤ (179501319619/1562500000000 : ℝ)^3771
        have hw : |(-911815947/5000000000 : ℝ)|=(911815947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5181675689/10000000000 : ℝ)|^4795 ≤ (43344675681543/100000000000000 : ℝ)^3771
        have hw : |(5181675689/10000000000 : ℝ)|=(5181675689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1619_s4_2 (p : ℝ) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676134763/5000000000 : ℝ)*x 0 + (1295418941/2500000000 : ℝ)*x 1 + (-1823631873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676134763/5000000000 : ℝ)^4795 ≤ (45167239222191/100000000000000 : ℝ)^3771 := by
    have hnat : (2676134763 : ℕ)^4795*100000000000000^3771 ≤ 45167239222191^3771*5000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676134763 5000000000 45167239222191 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1295418941/2500000000 : ℝ)^4795 ≤ (21672338239639/50000000000000 : ℝ)^3771 := by
    have hnat : (1295418941 : ℕ)^4795*50000000000000^3771 ≤ 21672338239639^3771*2500000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295418941 2500000000 21672338239639 50000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1823631873/10000000000 : ℝ)^4795 ≤ (11488084287403/100000000000000 : ℝ)^3771 := by
    have hnat : (1823631873 : ℕ)^4795*100000000000000^3771 ≤ 11488084287403^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1823631873 10000000000 11488084287403 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4795/1024 : ℝ)) 4795 3771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676134763/5000000000 : ℝ), (1295418941/2500000000 : ℝ), (-1823631873/10000000000 : ℝ)] ![(45167239222191/100000000000000 : ℝ), (21672338239639/50000000000000 : ℝ), (11488084287403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676134763/5000000000 : ℝ)|^4795 ≤ (45167239222191/100000000000000 : ℝ)^3771
        have hw : |(2676134763/5000000000 : ℝ)|=(2676134763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1295418941/2500000000 : ℝ)|^4795 ≤ (21672338239639/50000000000000 : ℝ)^3771
        have hw : |(1295418941/2500000000 : ℝ)|=(1295418941/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1823631873/10000000000 : ℝ)|^4795 ≤ (11488084287403/100000000000000 : ℝ)^3771
        have hw : |(-1823631873/10000000000 : ℝ)|=(1823631873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1619_s4_3 (p : ℝ) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4205190199/10000000000 : ℝ)*x 0 + (968467487/2500000000 : ℝ)*x 1 + (4557621579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4205190199/10000000000 : ℝ)^4795 ≤ (33237330570809/100000000000000 : ℝ)^3771 := by
    have hnat : (4205190199 : ℕ)^4795*100000000000000^3771 ≤ 33237330570809^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4205190199 10000000000 33237330570809 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (968467487/2500000000 : ℝ)^4795 ≤ (7485959509627/25000000000000 : ℝ)^3771 := by
    have hnat : (968467487 : ℕ)^4795*25000000000000^3771 ≤ 7485959509627^3771*2500000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      968467487 2500000000 7485959509627 25000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4557621579/10000000000 : ℝ)^4795 ≤ (36818831373643/100000000000000 : ℝ)^3771 := by
    have hnat : (4557621579 : ℕ)^4795*100000000000000^3771 ≤ 36818831373643^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4557621579 10000000000 36818831373643 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4795/1024 : ℝ)) 4795 3771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4205190199/10000000000 : ℝ), (968467487/2500000000 : ℝ), (4557621579/10000000000 : ℝ)] ![(33237330570809/100000000000000 : ℝ), (7485959509627/25000000000000 : ℝ), (36818831373643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4205190199/10000000000 : ℝ)|^4795 ≤ (33237330570809/100000000000000 : ℝ)^3771
        have hw : |(4205190199/10000000000 : ℝ)|=(4205190199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(968467487/2500000000 : ℝ)|^4795 ≤ (7485959509627/25000000000000 : ℝ)^3771
        have hw : |(968467487/2500000000 : ℝ)|=(968467487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4557621579/10000000000 : ℝ)|^4795 ≤ (36818831373643/100000000000000 : ℝ)^3771
        have hw : |(4557621579/10000000000 : ℝ)|=(4557621579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1619_s4_4 (p : ℝ) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-210245247/1250000000 : ℝ)*x 0 + (5183726731/10000000000 : ℝ)*x 1 + (2727295089/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210245247/1250000000 : ℝ)^4795 ≤ (64784283887/625000000000 : ℝ)^3771 := by
    have hnat : (210245247 : ℕ)^4795*625000000000^3771 ≤ 64784283887^3771*1250000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210245247 1250000000 64784283887 625000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5183726731/10000000000 : ℝ)^4795 ≤ (21683246352533/50000000000000 : ℝ)^3771 := by
    have hnat : (5183726731 : ℕ)^4795*50000000000000^3771 ≤ 21683246352533^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183726731 10000000000 21683246352533 50000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2727295089/5000000000 : ℝ)^4795 ≤ (46268021854591/100000000000000 : ℝ)^3771 := by
    have hnat : (2727295089 : ℕ)^4795*100000000000000^3771 ≤ 46268021854591^3771*5000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2727295089 5000000000 46268021854591 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4795/1024 : ℝ)) 4795 3771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-210245247/1250000000 : ℝ), (5183726731/10000000000 : ℝ), (2727295089/5000000000 : ℝ)] ![(64784283887/625000000000 : ℝ), (21683246352533/50000000000000 : ℝ), (46268021854591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-210245247/1250000000 : ℝ)|^4795 ≤ (64784283887/625000000000 : ℝ)^3771
        have hw : |(-210245247/1250000000 : ℝ)|=(210245247/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5183726731/10000000000 : ℝ)|^4795 ≤ (21683246352533/50000000000000 : ℝ)^3771
        have hw : |(5183726731/10000000000 : ℝ)|=(5183726731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2727295089/5000000000 : ℝ)|^4795 ≤ (46268021854591/100000000000000 : ℝ)^3771
        have hw : |(2727295089/5000000000 : ℝ)|=(2727295089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1619_s4_5 (p : ℝ) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279126681/10000000000 : ℝ)*x 0 + (-1550717891/10000000000 : ℝ)*x 1 + (5454589519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279126681/10000000000 : ℝ)^4795 ≤ (44383845211051/100000000000000 : ℝ)^3771 := by
    have hnat : (5279126681 : ℕ)^4795*100000000000000^3771 ≤ 44383845211051^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279126681 10000000000 44383845211051 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1550717891/10000000000 : ℝ)^4795 ≤ (9348140028663/100000000000000 : ℝ)^3771 := by
    have hnat : (1550717891 : ℕ)^4795*100000000000000^3771 ≤ 9348140028663^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1550717891 10000000000 9348140028663 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5454589519/10000000000 : ℝ)^4795 ≤ (46268014746773/100000000000000 : ℝ)^3771 := by
    have hnat : (5454589519 : ℕ)^4795*100000000000000^3771 ≤ 46268014746773^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5454589519 10000000000 46268014746773 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4795/1024 : ℝ)) 4795 3771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279126681/10000000000 : ℝ), (-1550717891/10000000000 : ℝ), (5454589519/10000000000 : ℝ)] ![(44383845211051/100000000000000 : ℝ), (9348140028663/100000000000000 : ℝ), (46268014746773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279126681/10000000000 : ℝ)|^4795 ≤ (44383845211051/100000000000000 : ℝ)^3771
        have hw : |(5279126681/10000000000 : ℝ)|=(5279126681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1550717891/10000000000 : ℝ)|^4795 ≤ (9348140028663/100000000000000 : ℝ)^3771
        have hw : |(-1550717891/10000000000 : ℝ)|=(1550717891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5454589519/10000000000 : ℝ)|^4795 ≤ (46268014746773/100000000000000 : ℝ)^3771
        have hw : |(5454589519/10000000000 : ℝ)|=(5454589519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1619_s4_6 (p : ℝ) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279126383/10000000000 : ℝ)*x 0 + (2727294903/5000000000 : ℝ)*x 1 + (-775358951/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279126383/10000000000 : ℝ)^4795 ≤ (5547980253163/12500000000000 : ℝ)^3771 := by
    have hnat : (5279126383 : ℕ)^4795*12500000000000^3771 ≤ 5547980253163^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279126383 10000000000 5547980253163 12500000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2727294903/5000000000 : ℝ)^4795 ≤ (46268017842287/100000000000000 : ℝ)^3771 := by
    have hnat : (2727294903 : ℕ)^4795*100000000000000^3771 ≤ 46268017842287^3771*5000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2727294903 5000000000 46268017842287 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (775358951/5000000000 : ℝ)^4795 ≤ (467407005649/5000000000000 : ℝ)^3771 := by
    have hnat : (775358951 : ℕ)^4795*5000000000000^3771 ≤ 467407005649^3771*5000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      775358951 5000000000 467407005649 5000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4795/1024 : ℝ)) 4795 3771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279126383/10000000000 : ℝ), (2727294903/5000000000 : ℝ), (-775358951/5000000000 : ℝ)] ![(5547980253163/12500000000000 : ℝ), (46268017842287/100000000000000 : ℝ), (467407005649/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279126383/10000000000 : ℝ)|^4795 ≤ (5547980253163/12500000000000 : ℝ)^3771
        have hw : |(5279126383/10000000000 : ℝ)|=(5279126383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2727294903/5000000000 : ℝ)|^4795 ≤ (46268017842287/100000000000000 : ℝ)^3771
        have hw : |(2727294903/5000000000 : ℝ)|=(2727294903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-775358951/5000000000 : ℝ)|^4795 ≤ (467407005649/5000000000000 : ℝ)^3771
        have hw : |(-775358951/5000000000 : ℝ)|=(775358951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1619_s4_7 (p : ℝ) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4205361543/10000000000 : ℝ)*x 0 + (2276260823/5000000000 : ℝ)*x 1 + (1939511541/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4205361543/10000000000 : ℝ)^4795 ≤ (664781052267/2000000000000 : ℝ)^3771 := by
    have hnat : (4205361543 : ℕ)^4795*2000000000000^3771 ≤ 664781052267^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4205361543 10000000000 664781052267 2000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2276260823/5000000000 : ℝ)^4795 ≤ (287237904383/781250000000 : ℝ)^3771 := by
    have hnat : (2276260823 : ℕ)^4795*781250000000^3771 ≤ 287237904383^3771*5000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2276260823 5000000000 287237904383 781250000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1939511541/5000000000 : ℝ)^4795 ≤ (14997247803979/50000000000000 : ℝ)^3771 := by
    have hnat : (1939511541 : ℕ)^4795*50000000000000^3771 ≤ 14997247803979^3771*5000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1939511541 5000000000 14997247803979 50000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4795/1024 : ℝ)) 4795 3771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4205361543/10000000000 : ℝ), (2276260823/5000000000 : ℝ), (1939511541/5000000000 : ℝ)] ![(664781052267/2000000000000 : ℝ), (287237904383/781250000000 : ℝ), (14997247803979/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4205361543/10000000000 : ℝ)|^4795 ≤ (664781052267/2000000000000 : ℝ)^3771
        have hw : |(4205361543/10000000000 : ℝ)|=(4205361543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2276260823/5000000000 : ℝ)|^4795 ≤ (287237904383/781250000000 : ℝ)^3771
        have hw : |(2276260823/5000000000 : ℝ)|=(2276260823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1939511541/5000000000 : ℝ)|^4795 ≤ (14997247803979/50000000000000 : ℝ)^3771
        have hw : |(1939511541/5000000000 : ℝ)|=(1939511541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1619_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87162187/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1021/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2621/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10493/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8163/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1021/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2621/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1021/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2621/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1021/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2621/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1021/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2621/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1021/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2621/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1021/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2621/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2621/25000 : ℝ) ^ (4791/1024 : ℝ) ≤ (2614141064686429/100000000000000000000 : ℝ) := by
    have hpowers : (2621/25000 : ℝ)^4791 ≤ (2614141064686429/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2621 : ℕ)^4791*100000000000000000000^1024 ≤ 2614141064686429^1024*25000^4791 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2621 25000 2614141064686429 100000000000000000000 4791 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2621/25000 : ℝ)) (X := (2614141064686429/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4791 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1021/6250 : ℝ) ^ (4791/1024 : ℝ) ≤ (10411332116207713/50000000000000000000 : ℝ) := by
    have hpowers : (1021/6250 : ℝ)^4791 ≤ (10411332116207713/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1021 : ℕ)^4791*50000000000000000000^1024 ≤ 10411332116207713^1024*6250^4791 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1021 6250 10411332116207713 50000000000000000000 4791 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1021/6250 : ℝ)) (X := (10411332116207713/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4791 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002614141064686429/50000000000000000000 : ℝ) ≤ (10000111743912799/10000000000000000 : ℝ) ^ (4791/1024 : ℝ) := by
    have hpowers : (50002614141064686429/50000000000000000000 : ℝ)^1024 ≤ (10000111743912799/10000000000000000 : ℝ)^4791 := by
      have hnat : (50002614141064686429 : ℕ)^1024*10000000000000000^4791 ≤ 10000111743912799^4791*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002614141064686429 50000000000000000000 10000111743912799 10000000000000000 1024 4791 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000111743912799/10000000000000000 : ℝ)) (X := (50002614141064686429/50000000000000000000 : ℝ)) (by norm_num) 4791 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20004687361059420371/20000000000000000000 : ℝ) ≤ (1000050087826531/1000000000000000 : ℝ) ^ (4791/1024 : ℝ) := by
    have hpowers : (20004687361059420371/20000000000000000000 : ℝ)^1024 ≤ (1000050087826531/1000000000000000 : ℝ)^4791 := by
      have hnat : (20004687361059420371 : ℕ)^1024*1000000000000000^4791 ≤ 1000050087826531^4791*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20004687361059420371 20000000000000000000 1000050087826531 1000000000000000 1024 4791 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000050087826531/1000000000000000 : ℝ)) (X := (20004687361059420371/20000000000000000000 : ℝ)) (by norm_num) 4791 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25010411332116207713/25000000000000000000 : ℝ) ≤ (10000890012617821/10000000000000000 : ℝ) ^ (4791/1024 : ℝ) := by
    have hpowers : (25010411332116207713/25000000000000000000 : ℝ)^1024 ≤ (10000890012617821/10000000000000000 : ℝ)^4791 := by
      have hnat : (25010411332116207713 : ℕ)^1024*10000000000000000^4791 ≤ 10000890012617821^4791*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010411332116207713 25000000000000000000 10000890012617821 10000000000000000 1024 4791 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000890012617821/10000000000000000 : ℝ)) (X := (25010411332116207713/25000000000000000000 : ℝ)) (by norm_num) 4791 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2614141064686429/100000000000000000000 : ℝ) ≤ ((585124945562742491/585200000000000000 : ℝ)+2*(389134352511/585200000000000 : ℝ)*(2621/25000 : ℝ))^(4791/1024 : ℝ) := by
    rw [show (585124945562742491/585200000000000000 : ℝ)+2*(389134352511/585200000000000 : ℝ)*(2621/25000 : ℝ)=(10000111743912799/10000000000000000 : ℝ) by norm_num, show 1+2*(2614141064686429/100000000000000000000 : ℝ)=(50002614141064686429/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10411332116207713/50000000000000000000 : ℝ)+(2614141064686429/100000000000000000000 : ℝ) ≤ ((585124945562742491/585200000000000000 : ℝ)+(389134352511/585200000000000 : ℝ)*((1021/6250 : ℝ)+(2621/25000 : ℝ)))^(4791/1024 : ℝ) := by
    rw [show (585124945562742491/585200000000000000 : ℝ)+(389134352511/585200000000000 : ℝ)*((1021/6250 : ℝ)+(2621/25000 : ℝ))=(1000050087826531/1000000000000000 : ℝ) by norm_num, show 1+(10411332116207713/50000000000000000000 : ℝ)+(2614141064686429/100000000000000000000 : ℝ)=(20004687361059420371/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10411332116207713/50000000000000000000 : ℝ) ≤ ((585124945562742491/585200000000000000 : ℝ)+2*(389134352511/585200000000000 : ℝ)*(1021/6250 : ℝ))^(4791/1024 : ℝ) := by
    rw [show (585124945562742491/585200000000000000 : ℝ)+2*(389134352511/585200000000000 : ℝ)*(1021/6250 : ℝ)=(10000890012617821/10000000000000000 : ℝ) by norm_num, show 1+2*(10411332116207713/50000000000000000000 : ℝ)=(25010411332116207713/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (585124945562742491/585200000000000000 : ℝ)*(X 1 0+X 2 0)+(389134352511/585200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4791/1024 : ℝ)) (lo := (2621/25000 : ℝ)) (hi := (1021/6250 : ℝ)) (c := (585124945562742491/585200000000000000 : ℝ)) (alpha := (389134352511/585200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (585124945562742491/585200000000000000 : ℝ)*(X 0 1+X 2 1)+(389134352511/585200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4791/1024 : ℝ)) (lo := (2621/25000 : ℝ)) (hi := (1021/6250 : ℝ)) (c := (585124945562742491/585200000000000000 : ℝ)) (alpha := (389134352511/585200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (585124945562742491/585200000000000000 : ℝ)*(X 0 2+X 1 2)+(389134352511/585200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4791/1024 : ℝ)) (lo := (2621/25000 : ℝ)) (hi := (1021/6250 : ℝ)) (c := (585124945562742491/585200000000000000 : ℝ)) (alpha := (389134352511/585200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-420473311/2500000000 : ℝ)*X 0 0+(5456662687/10000000000 : ℝ)*X 0 1+(1295418943/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1619_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334516849/625000000 : ℝ)*X 1 0+(-911815947/5000000000 : ℝ)*X 1 1+(5181675689/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1619_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676134763/5000000000 : ℝ)*X 2 0+(1295418941/2500000000 : ℝ)*X 2 1+(-1823631873/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1619_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4205190199/10000000000 : ℝ)*X 0 0+(968467487/2500000000 : ℝ)*X 0 1+(4557621579/10000000000 : ℝ)*X 0 2+(4205190199/10000000000 : ℝ)*X 1 0+(968467487/2500000000 : ℝ)*X 1 1+(4557621579/10000000000 : ℝ)*X 1 2+(4205190199/10000000000 : ℝ)*X 2 0+(968467487/2500000000 : ℝ)*X 2 1+(4557621579/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1619_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-210245247/1250000000 : ℝ)*X 0 0+(5183726731/10000000000 : ℝ)*X 0 1+(2727295089/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1619_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5279126681/10000000000 : ℝ)*X 1 0+(-1550717891/10000000000 : ℝ)*X 1 1+(5454589519/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1619_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5279126383/10000000000 : ℝ)*X 2 0+(2727294903/5000000000 : ℝ)*X 2 1+(-775358951/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1619_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4205361543/10000000000 : ℝ)*X 0 0+(2276260823/5000000000 : ℝ)*X 0 1+(1939511541/5000000000 : ℝ)*X 0 2+(4205361543/10000000000 : ℝ)*X 1 0+(2276260823/5000000000 : ℝ)*X 1 1+(1939511541/5000000000 : ℝ)*X 1 2+(4205361543/10000000000 : ℝ)*X 2 0+(2276260823/5000000000 : ℝ)*X 2 1+(1939511541/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1619_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1036275569020449953924019/385000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (256657819/50000000000000 : ℝ)*(base19) + (113325029/25000000000000 : ℝ)*(base23) + (11029949/100000000000000 : ℝ)*(lower2) + (15708273/25000000000000 : ℝ)*(upper3) + (58297317/100000000000000 : ℝ)*(upper5) + (1274768069618357/50000000000000 : ℝ)*(major0) + (1274768069618357/50000000000000 : ℝ)*(major1) + (1274768069618357/50000000000000 : ℝ)*(major2) + (363654234414941/10000000000000 : ℝ)*(sp0) + (1818273742597829/50000000000000 : ℝ)*(sp1) + (181827377260559/5000000000000 : ℝ)*(sp2) + (365630437368209/25000000000000 : ℝ)*(sp3) + (2827180943/50000000000000 : ℝ)*(sp4) + (2440768463/100000000000000 : ℝ)*(sp7) + (1462524190241299/100000000000000 : ℝ)*(f.failure) + (56821062476739/1562500000000 : ℝ)*(f.sum) + (3253864162543/770000000000000000000000000 : ℝ)*base65 + (3990919122430827/1540000000000000000000000000000 : ℝ)*base68 + (4143408807470827/1540000000000000000000000000000 : ℝ)*base70 + (2503265369749173/1540000000000000000000000000000 : ℝ)*base71 + (547201452253/770000000000000000000000000 : ℝ)*base73 + (1816019333830827/1540000000000000000000000000000 : ℝ)*base76 + (5729935618570827/1540000000000000000000000000000 : ℝ)*base78 + (7320402485790827/1540000000000000000000000000000 : ℝ)*base80 + (1691895390333/770000000000000000000000000 : ℝ)*base81 + (21439087/5000000000000000000000 : ℝ)*base90 + (21439087/5000000000000000000000 : ℝ)*base92 + (21439087/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14592884972697437344168683/2090000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (663230791/50000000000000 : ℝ)*(base19) + (266406883/20000000000000 : ℝ)*(base23) + (9096441/5000000000000 : ℝ)*(lower1) + (177706983/100000000000000 : ℝ)*(upper3) + (1574357/1562500000000 : ℝ)*(lower4) + (182102831/100000000000000 : ℝ)*(upper5) + (1294167304674397/50000000000000 : ℝ)*(major0) + (1294167304674397/50000000000000 : ℝ)*(major1) + (1294167304674397/50000000000000 : ℝ)*(major2) + (1668145351/100000000000000 : ℝ)*(sp2) + (3691888315326151/100000000000000 : ℝ)*(sp4) + (3691886988864569/100000000000000 : ℝ)*(sp5) + (1845942657573193/50000000000000 : ℝ)*(sp6) + (742390335315013/50000000000000 : ℝ)*(sp7) + (742390335315013/50000000000000 : ℝ)*(f.failure) + (3691888315326151/100000000000000 : ℝ)*(f.sum) + (22122171144593/14630000000000000000000000000 : ℝ)*base66 + (477156791193549927/29260000000000000000000000000000 : ℝ)*base67 + (214936421120030073/29260000000000000000000000000000 : ℝ)*base70 + (4017096415588250073/29260000000000000000000000000000 : ℝ)*base72 + (7179040468157/14630000000000000000000000000 : ℝ)*base73 + (1316335719390389927/29260000000000000000000000000000 : ℝ)*base75 + (120603953456750073/29260000000000000000000000000000 : ℝ)*base78 + (244314984571190073/29260000000000000000000000000000 : ℝ)*base80 + (22620027045443/14630000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (17013431/2500000000000000000000 : ℝ)*base89 + (17013431/2500000000000000000000 : ℝ)*base91 + (17013431/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1619_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87162187/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1021/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2621/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10493/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8163/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1619_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1619_s5_0 (p : ℝ) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352259181/10000000000 : ℝ)*x 0 + (-45590041/250000000 : ℝ)*x 1 + (647713621/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352259181/10000000000 : ℝ)^4795 ≤ (11291782053947/25000000000000 : ℝ)^3771 := by
    have hnat : (5352259181 : ℕ)^4795*25000000000000^3771 ≤ 11291782053947^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352259181 10000000000 11291782053947 25000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (45590041/250000000 : ℝ)^4795 ≤ (287196052901/2500000000000 : ℝ)^3771 := by
    have hnat : (45590041 : ℕ)^4795*2500000000000^3771 ≤ 287196052901^3771*250000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45590041 250000000 287196052901 2500000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (647713621/1250000000 : ℝ)^4795 ≤ (4334502965301/10000000000000 : ℝ)^3771 := by
    have hnat : (647713621 : ℕ)^4795*10000000000000^3771 ≤ 4334502965301^3771*1250000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647713621 1250000000 4334502965301 10000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4795/1024 : ℝ)) 4795 3771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352259181/10000000000 : ℝ), (-45590041/250000000 : ℝ), (647713621/1250000000 : ℝ)] ![(11291782053947/25000000000000 : ℝ), (287196052901/2500000000000 : ℝ), (4334502965301/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352259181/10000000000 : ℝ)|^4795 ≤ (11291782053947/25000000000000 : ℝ)^3771
        have hw : |(5352259181/10000000000 : ℝ)|=(5352259181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-45590041/250000000 : ℝ)|^4795 ≤ (287196052901/2500000000000 : ℝ)^3771
        have hw : |(-45590041/250000000 : ℝ)|=(45590041/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(647713621/1250000000 : ℝ)|^4795 ≤ (4334502965301/10000000000000 : ℝ)^3771
        have hw : |(647713621/1250000000 : ℝ)|=(647713621/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1619_s5_1 (p : ℝ) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-840984777/5000000000 : ℝ)*x 0 + (5183759097/10000000000 : ℝ)*x 1 + (340909547/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (840984777/5000000000 : ℝ)^4795 ≤ (2073108960937/20000000000000 : ℝ)^3771 := by
    have hnat : (840984777 : ℕ)^4795*20000000000000^3771 ≤ 2073108960937^3771*5000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      840984777 5000000000 2073108960937 20000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5183759097/10000000000 : ℝ)^4795 ≤ (8673367400483/20000000000000 : ℝ)^3771 := by
    have hnat : (5183759097 : ℕ)^4795*20000000000000^3771 ≤ 8673367400483^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183759097 10000000000 8673367400483 20000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (340909547/625000000 : ℝ)^4795 ≤ (4626761818699/10000000000000 : ℝ)^3771 := by
    have hnat : (340909547 : ℕ)^4795*10000000000000^3771 ≤ 4626761818699^3771*625000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340909547 625000000 4626761818699 10000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4795/1024 : ℝ)) 4795 3771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-840984777/5000000000 : ℝ), (5183759097/10000000000 : ℝ), (340909547/625000000 : ℝ)] ![(2073108960937/20000000000000 : ℝ), (8673367400483/20000000000000 : ℝ), (4626761818699/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-840984777/5000000000 : ℝ)|^4795 ≤ (2073108960937/20000000000000 : ℝ)^3771
        have hw : |(-840984777/5000000000 : ℝ)|=(840984777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5183759097/10000000000 : ℝ)|^4795 ≤ (8673367400483/20000000000000 : ℝ)^3771
        have hw : |(5183759097/10000000000 : ℝ)|=(5183759097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(340909547/625000000 : ℝ)|^4795 ≤ (4626761818699/10000000000000 : ℝ)^3771
        have hw : |(340909547/625000000 : ℝ)|=(340909547/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1619_s5_2 (p : ℝ) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279135221/10000000000 : ℝ)*x 0 + (-1550757727/10000000000 : ℝ)*x 1 + (5454552743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279135221/10000000000 : ℝ)^4795 ≤ (4438393650729/10000000000000 : ℝ)^3771 := by
    have hnat : (5279135221 : ℕ)^4795*10000000000000^3771 ≤ 4438393650729^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279135221 10000000000 4438393650729 10000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1550757727/10000000000 : ℝ)^4795 ≤ (4674222690669/50000000000000 : ℝ)^3771 := by
    have hnat : (1550757727 : ℕ)^4795*50000000000000^3771 ≤ 4674222690669^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1550757727 10000000000 4674222690669 50000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5454552743/10000000000 : ℝ)^4795 ≤ (23133809044959/50000000000000 : ℝ)^3771 := by
    have hnat : (5454552743 : ℕ)^4795*50000000000000^3771 ≤ 23133809044959^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5454552743 10000000000 23133809044959 50000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4795/1024 : ℝ)) 4795 3771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279135221/10000000000 : ℝ), (-1550757727/10000000000 : ℝ), (5454552743/10000000000 : ℝ)] ![(4438393650729/10000000000000 : ℝ), (4674222690669/50000000000000 : ℝ), (23133809044959/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279135221/10000000000 : ℝ)|^4795 ≤ (4438393650729/10000000000000 : ℝ)^3771
        have hw : |(5279135221/10000000000 : ℝ)|=(5279135221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1550757727/10000000000 : ℝ)|^4795 ≤ (4674222690669/50000000000000 : ℝ)^3771
        have hw : |(-1550757727/10000000000 : ℝ)|=(1550757727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5454552743/10000000000 : ℝ)|^4795 ≤ (23133809044959/50000000000000 : ℝ)^3771
        have hw : |(5454552743/10000000000 : ℝ)|=(5454552743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1619_s5_3 (p : ℝ) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (659891893/1250000000 : ℝ)*x 0 + (2727276389/5000000000 : ℝ)*x 1 + (-775378893/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (659891893/1250000000 : ℝ)^4795 ≤ (44383935684127/100000000000000 : ℝ)^3771 := by
    have hnat : (659891893 : ℕ)^4795*100000000000000^3771 ≤ 44383935684127^3771*1250000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659891893 1250000000 44383935684127 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2727276389/5000000000 : ℝ)^4795 ≤ (46267618467419/100000000000000 : ℝ)^3771 := by
    have hnat : (2727276389 : ℕ)^4795*100000000000000^3771 ≤ 46267618467419^3771*5000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2727276389 5000000000 46267618467419 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (775378893/5000000000 : ℝ)^4795 ≤ (9348445833589/100000000000000 : ℝ)^3771 := by
    have hnat : (775378893 : ℕ)^4795*100000000000000^3771 ≤ 9348445833589^3771*5000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      775378893 5000000000 9348445833589 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4795/1024 : ℝ)) 4795 3771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(659891893/1250000000 : ℝ), (2727276389/5000000000 : ℝ), (-775378893/5000000000 : ℝ)] ![(44383935684127/100000000000000 : ℝ), (46267618467419/100000000000000 : ℝ), (9348445833589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(659891893/1250000000 : ℝ)|^4795 ≤ (44383935684127/100000000000000 : ℝ)^3771
        have hw : |(659891893/1250000000 : ℝ)|=(659891893/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2727276389/5000000000 : ℝ)|^4795 ≤ (46267618467419/100000000000000 : ℝ)^3771
        have hw : |(2727276389/5000000000 : ℝ)|=(2727276389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-775378893/5000000000 : ℝ)|^4795 ≤ (9348445833589/100000000000000 : ℝ)^3771
        have hw : |(-775378893/5000000000 : ℝ)|=(775378893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1619_s5_4 (p : ℝ) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4205365973/10000000000 : ℝ)*x 0 + (4552434537/10000000000 : ℝ)*x 1 + (3879109533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4205365973/10000000000 : ℝ)^4795 ≤ (2077443571001/6250000000000 : ℝ)^3771 := by
    have hnat : (4205365973 : ℕ)^4795*6250000000000^3771 ≤ 2077443571001^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4205365973 10000000000 2077443571001 6250000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4552434537/10000000000 : ℝ)^4795 ≤ (36765557233561/100000000000000 : ℝ)^3771 := by
    have hnat : (4552434537 : ℕ)^4795*100000000000000^3771 ≤ 36765557233561^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4552434537 10000000000 36765557233561 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3879109533/10000000000 : ℝ)^4795 ≤ (29995345615177/100000000000000 : ℝ)^3771 := by
    have hnat : (3879109533 : ℕ)^4795*100000000000000^3771 ≤ 29995345615177^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3879109533 10000000000 29995345615177 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4795/1024 : ℝ)) 4795 3771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4205365973/10000000000 : ℝ), (4552434537/10000000000 : ℝ), (3879109533/10000000000 : ℝ)] ![(2077443571001/6250000000000 : ℝ), (36765557233561/100000000000000 : ℝ), (29995345615177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4205365973/10000000000 : ℝ)|^4795 ≤ (2077443571001/6250000000000 : ℝ)^3771
        have hw : |(4205365973/10000000000 : ℝ)|=(4205365973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4552434537/10000000000 : ℝ)|^4795 ≤ (36765557233561/100000000000000 : ℝ)^3771
        have hw : |(4552434537/10000000000 : ℝ)|=(4552434537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3879109533/10000000000 : ℝ)|^4795 ≤ (29995345615177/100000000000000 : ℝ)^3771
        have hw : |(3879109533/10000000000 : ℝ)|=(3879109533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1619_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87162187/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8163/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10493/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10493/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (653/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8163/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10493/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8163/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10493/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8163/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10493/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8163/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10493/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8163/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10493/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8163/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10493/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10493/100000 : ℝ) ^ (4791/1024 : ℝ) ≤ (164041075452079/6250000000000000000 : ℝ) := by
    have hpowers : (10493/100000 : ℝ)^4791 ≤ (164041075452079/6250000000000000000 : ℝ)^1024 := by
      have hnat : (10493 : ℕ)^4791*6250000000000000000^1024 ≤ 164041075452079^1024*100000^4791 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10493 100000 164041075452079 6250000000000000000 4791 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10493/100000 : ℝ)) (X := (164041075452079/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4791 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8163/50000 : ℝ) ^ (4791/1024 : ℝ) ≤ (10381547103677127/50000000000000000000 : ℝ) := by
    have hpowers : (8163/50000 : ℝ)^4791 ≤ (10381547103677127/50000000000000000000 : ℝ)^1024 := by
      have hnat : (8163 : ℕ)^4791*50000000000000000000^1024 ≤ 10381547103677127^1024*50000^4791 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8163 50000 10381547103677127 50000000000000000000 4791 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8163/50000 : ℝ)) (X := (10381547103677127/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4791 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125164041075452079/3125000000000000000 : ℝ) ≤ (10000112193425903/10000000000000000 : ℝ) ^ (4791/1024 : ℝ) := by
    have hpowers : (3125164041075452079/3125000000000000000 : ℝ)^1024 ≤ (10000112193425903/10000000000000000 : ℝ)^4791 := by
      have hnat : (3125164041075452079 : ℕ)^1024*10000000000000000^4791 ≤ 10000112193425903^4791*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125164041075452079 3125000000000000000 10000112193425903 10000000000000000 1024 4791 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000112193425903/10000000000000000 : ℝ)) (X := (3125164041075452079/3125000000000000000 : ℝ)) (by norm_num) 4791 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50011693875707293759/50000000000000000000 : ℝ) ≤ (5000249915004801/5000000000000000 : ℝ) ^ (4791/1024 : ℝ) := by
    have hpowers : (50011693875707293759/50000000000000000000 : ℝ)^1024 ≤ (5000249915004801/5000000000000000 : ℝ)^4791 := by
      have hnat : (50011693875707293759 : ℕ)^1024*5000000000000000^4791 ≤ 5000249915004801^4791*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50011693875707293759 50000000000000000000 5000249915004801 5000000000000000 1024 4791 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000249915004801/5000000000000000 : ℝ)) (X := (50011693875707293759/50000000000000000000 : ℝ)) (by norm_num) 4791 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25010381547103677127/25000000000000000000 : ℝ) ≤ (10000887466593301/10000000000000000 : ℝ) ^ (4791/1024 : ℝ) := by
    have hpowers : (25010381547103677127/25000000000000000000 : ℝ)^1024 ≤ (10000887466593301/10000000000000000 : ℝ)^4791 := by
      have hnat : (25010381547103677127 : ℕ)^1024*10000000000000000^4791 ≤ 10000887466593301^4791*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010381547103677127 25000000000000000000 10000887466593301 10000000000000000 1024 4791 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000887466593301/10000000000000000 : ℝ)) (X := (25010381547103677127/25000000000000000000 : ℝ)) (by norm_num) 4791 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(164041075452079/6250000000000000000 : ℝ) ≤ ((11664503896581556997/11666000000000000000 : ℝ)+2*(387636583699/583300000000000 : ℝ)*(10493/100000 : ℝ))^(4791/1024 : ℝ) := by
    rw [show (11664503896581556997/11666000000000000000 : ℝ)+2*(387636583699/583300000000000 : ℝ)*(10493/100000 : ℝ)=(10000112193425903/10000000000000000 : ℝ) by norm_num, show 1+2*(164041075452079/6250000000000000000 : ℝ)=(3125164041075452079/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10381547103677127/50000000000000000000 : ℝ)+(164041075452079/6250000000000000000 : ℝ) ≤ ((11664503896581556997/11666000000000000000 : ℝ)+(387636583699/583300000000000 : ℝ)*((8163/50000 : ℝ)+(10493/100000 : ℝ)))^(4791/1024 : ℝ) := by
    rw [show (11664503896581556997/11666000000000000000 : ℝ)+(387636583699/583300000000000 : ℝ)*((8163/50000 : ℝ)+(10493/100000 : ℝ))=(5000249915004801/5000000000000000 : ℝ) by norm_num, show 1+(10381547103677127/50000000000000000000 : ℝ)+(164041075452079/6250000000000000000 : ℝ)=(50011693875707293759/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10381547103677127/50000000000000000000 : ℝ) ≤ ((11664503896581556997/11666000000000000000 : ℝ)+2*(387636583699/583300000000000 : ℝ)*(8163/50000 : ℝ))^(4791/1024 : ℝ) := by
    rw [show (11664503896581556997/11666000000000000000 : ℝ)+2*(387636583699/583300000000000 : ℝ)*(8163/50000 : ℝ)=(10000887466593301/10000000000000000 : ℝ) by norm_num, show 1+2*(10381547103677127/50000000000000000000 : ℝ)=(25010381547103677127/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11664503896581556997/11666000000000000000 : ℝ)*(X 1 0+X 2 0)+(387636583699/583300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4791/1024 : ℝ)) (lo := (10493/100000 : ℝ)) (hi := (8163/50000 : ℝ)) (c := (11664503896581556997/11666000000000000000 : ℝ)) (alpha := (387636583699/583300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11664503896581556997/11666000000000000000 : ℝ)*(X 0 1+X 2 1)+(387636583699/583300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4791/1024 : ℝ)) (lo := (10493/100000 : ℝ)) (hi := (8163/50000 : ℝ)) (c := (11664503896581556997/11666000000000000000 : ℝ)) (alpha := (387636583699/583300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11664503896581556997/11666000000000000000 : ℝ)*(X 0 2+X 1 2)+(387636583699/583300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4791/1024 : ℝ)) (lo := (10493/100000 : ℝ)) (hi := (8163/50000 : ℝ)) (c := (11664503896581556997/11666000000000000000 : ℝ)) (alpha := (387636583699/583300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5352259181/10000000000 : ℝ)*X 1 0+(-45590041/250000000 : ℝ)*X 1 1+(647713621/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1619_s5_0 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-840984777/5000000000 : ℝ)*X 0 0+(5183759097/10000000000 : ℝ)*X 0 1+(340909547/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1619_s5_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5279135221/10000000000 : ℝ)*X 1 0+(-1550757727/10000000000 : ℝ)*X 1 1+(5454552743/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1619_s5_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((659891893/1250000000 : ℝ)*X 2 0+(2727276389/5000000000 : ℝ)*X 2 1+(-775378893/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1619_s5_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((4205365973/10000000000 : ℝ)*X 0 0+(4552434537/10000000000 : ℝ)*X 0 1+(3879109533/10000000000 : ℝ)*X 0 2+(4205365973/10000000000 : ℝ)*X 1 0+(4552434537/10000000000 : ℝ)*X 1 1+(3879109533/10000000000 : ℝ)*X 1 2+(4205365973/10000000000 : ℝ)*X 2 0+(4552434537/10000000000 : ℝ)*X 2 1+(3879109533/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1619_s5_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24212580406400002084255113/4666400000000000000000000000000 : ℝ) := by norm_num
    linear_combination (414871813/50000000000000 : ℝ)*(base19) + (83018441/10000000000000 : ℝ)*(base23) + (13017589/5000000000000 : ℝ)*(lower1) + (106575377/100000000000000 : ℝ)*(upper3) + (305181/1000000000000 : ℝ)*(lower4) + (21796323/20000000000000 : ℝ)*(upper5) + (20712005535257/800000000000 : ℝ)*(major0) + (20712005535257/800000000000 : ℝ)*(major1) + (20712005535257/800000000000 : ℝ)*(major2) + (253070733/100000000000000 : ℝ)*(sp0) + (461604805808193/12500000000000 : ℝ)*(sp1) + (738567472730237/20000000000000 : ℝ)*(sp2) + (1846418808140567/50000000000000 : ℝ)*(sp3) + (742581382195907/50000000000000 : ℝ)*(sp4) + (742581382195907/50000000000000 : ℝ)*(f.failure) + (461604805808193/12500000000000 : ℝ)*(f.sum) + (26932402221957/5833000000000000000000000000 : ℝ)*base65 + (5301355699857571/9332800000000000000000000000000 : ℝ)*base68 + (37224424186043229/9332800000000000000000000000000 : ℝ)*base69 + (42740653741579229/9332800000000000000000000000000 : ℝ)*base71 + (1876947441019/1458250000000000000000000000 : ℝ)*base73 + (49702313287062429/9332800000000000000000000000000 : ℝ)*base75 + (60387129126827171/9332800000000000000000000000000 : ℝ)*base78 + (29401387322267229/9332800000000000000000000000000 : ℝ)*base79 + (67752576803921/5833000000000000000000000000 : ℝ)*base81 + (8431391/2500000000000000000000 : ℝ)*base90 + (8431391/2500000000000000000000 : ℝ)*base92 + (8431391/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1619_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87162187/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8163/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10493/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10493/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (653/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1619_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1619_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87162187/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16457/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (83/800 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10493/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (653/4000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1619_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1619_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1619_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87162187/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16457/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (83/800 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10493/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (653/4000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1619_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
