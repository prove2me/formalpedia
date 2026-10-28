-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1218_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:09:45.201031+00:00
-- url     : https://prove2.me/submissions/0a854d27-68a5-41c8-956a-a9d6744e320c

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
theorem support_rectangle_w1218_s0_0 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-23349851/125000000 : ℝ)*x 0 + (6036930879/10000000000 : ℝ)*x 1 + (2395004163/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (23349851/125000000 : ℝ)^8411 ≤ (2721435372499/25000000000000 : ℝ)^6363 := by
    have hnat : (23349851 : ℕ)^8411*25000000000000^6363 ≤ 2721435372499^6363*125000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23349851 125000000 2721435372499 25000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6036930879/10000000000 : ℝ)^8411 ≤ (25658989253373/50000000000000 : ℝ)^6363 := by
    have hnat : (6036930879 : ℕ)^8411*50000000000000^6363 ≤ 25658989253373^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6036930879 10000000000 25658989253373 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2395004163/5000000000 : ℝ)^8411 ≤ (7559255997127/20000000000000 : ℝ)^6363 := by
    have hnat : (2395004163 : ℕ)^8411*20000000000000^6363 ≤ 7559255997127^6363*5000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2395004163 5000000000 7559255997127 20000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-23349851/125000000 : ℝ), (6036930879/10000000000 : ℝ), (2395004163/5000000000 : ℝ)] ![(2721435372499/25000000000000 : ℝ), (25658989253373/50000000000000 : ℝ), (7559255997127/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-23349851/125000000 : ℝ)|^8411 ≤ (2721435372499/25000000000000 : ℝ)^6363
        have hw : |(-23349851/125000000 : ℝ)|=(23349851/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6036930879/10000000000 : ℝ)|^8411 ≤ (25658989253373/50000000000000 : ℝ)^6363
        have hw : |(6036930879/10000000000 : ℝ)|=(6036930879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2395004163/5000000000 : ℝ)|^8411 ≤ (7559255997127/20000000000000 : ℝ)^6363
        have hw : |(2395004163/5000000000 : ℝ)|=(2395004163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s0_1 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5512511633/10000000000 : ℝ)*x 0 + (-2581476191/10000000000 : ℝ)*x 1 + (4790008291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5512511633/10000000000 : ℝ)^8411 ≤ (1137732300219/2500000000000 : ℝ)^6363 := by
    have hnat : (5512511633 : ℕ)^8411*2500000000000^6363 ≤ 1137732300219^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5512511633 10000000000 1137732300219 2500000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2581476191/10000000000 : ℝ)^8411 ≤ (16694428357363/100000000000000 : ℝ)^6363 := by
    have hnat : (2581476191 : ℕ)^8411*100000000000000^6363 ≤ 16694428357363^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2581476191 10000000000 16694428357363 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4790008291/10000000000 : ℝ)^8411 ≤ (37796279620573/100000000000000 : ℝ)^6363 := by
    have hnat : (4790008291 : ℕ)^8411*100000000000000^6363 ≤ 37796279620573^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4790008291 10000000000 37796279620573 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5512511633/10000000000 : ℝ), (-2581476191/10000000000 : ℝ), (4790008291/10000000000 : ℝ)] ![(1137732300219/2500000000000 : ℝ), (16694428357363/100000000000000 : ℝ), (37796279620573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5512511633/10000000000 : ℝ)|^8411 ≤ (1137732300219/2500000000000 : ℝ)^6363
        have hw : |(5512511633/10000000000 : ℝ)|=(5512511633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2581476191/10000000000 : ℝ)|^8411 ≤ (16694428357363/100000000000000 : ℝ)^6363
        have hw : |(-2581476191/10000000000 : ℝ)|=(2581476191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4790008291/10000000000 : ℝ)|^8411 ≤ (37796279620573/100000000000000 : ℝ)^6363
        have hw : |(4790008291/10000000000 : ℝ)|=(4790008291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s0_2 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5512511609/10000000000 : ℝ)*x 0 + (4790008321/10000000000 : ℝ)*x 1 + (-1290738093/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5512511609/10000000000 : ℝ)^8411 ≤ (45509291746853/100000000000000 : ℝ)^6363 := by
    have hnat : (5512511609 : ℕ)^8411*100000000000000^6363 ≤ 45509291746853^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5512511609 10000000000 45509291746853 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4790008321/10000000000 : ℝ)^8411 ≤ (37796279933483/100000000000000 : ℝ)^6363 := by
    have hnat : (4790008321 : ℕ)^8411*100000000000000^6363 ≤ 37796279933483^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4790008321 10000000000 37796279933483 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1290738093/5000000000 : ℝ)^8411 ≤ (16694428314621/100000000000000 : ℝ)^6363 := by
    have hnat : (1290738093 : ℕ)^8411*100000000000000^6363 ≤ 16694428314621^6363*5000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1290738093 5000000000 16694428314621 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5512511609/10000000000 : ℝ), (4790008321/10000000000 : ℝ), (-1290738093/5000000000 : ℝ)] ![(45509291746853/100000000000000 : ℝ), (37796279933483/100000000000000 : ℝ), (16694428314621/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5512511609/10000000000 : ℝ)|^8411 ≤ (45509291746853/100000000000000 : ℝ)^6363
        have hw : |(5512511609/10000000000 : ℝ)|=(5512511609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4790008321/10000000000 : ℝ)|^8411 ≤ (37796279933483/100000000000000 : ℝ)^6363
        have hw : |(4790008321/10000000000 : ℝ)|=(4790008321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1290738093/5000000000 : ℝ)|^8411 ≤ (16694428314621/100000000000000 : ℝ)^6363
        have hw : |(-1290738093/5000000000 : ℝ)|=(1290738093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s0_3 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2097456509/5000000000 : ℝ)*x 0 + (3117816061/10000000000 : ℝ)*x 1 + (704446207/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2097456509/5000000000 : ℝ)^8411 ≤ (31717013442969/100000000000000 : ℝ)^6363 := by
    have hnat : (2097456509 : ℕ)^8411*100000000000000^6363 ≤ 31717013442969^6363*5000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097456509 5000000000 31717013442969 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3117816061/10000000000 : ℝ)^8411 ≤ (5356496603607/25000000000000 : ℝ)^6363 := by
    have hnat : (3117816061 : ℕ)^8411*25000000000000^6363 ≤ 5356496603607^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3117816061 10000000000 5356496603607 25000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (704446207/1250000000 : ℝ)^8411 ≤ (46857000126807/100000000000000 : ℝ)^6363 := by
    have hnat : (704446207 : ℕ)^8411*100000000000000^6363 ≤ 46857000126807^6363*1250000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      704446207 1250000000 46857000126807 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2097456509/5000000000 : ℝ), (3117816061/10000000000 : ℝ), (704446207/1250000000 : ℝ)] ![(31717013442969/100000000000000 : ℝ), (5356496603607/25000000000000 : ℝ), (46857000126807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2097456509/5000000000 : ℝ)|^8411 ≤ (31717013442969/100000000000000 : ℝ)^6363
        have hw : |(2097456509/5000000000 : ℝ)|=(2097456509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3117816061/10000000000 : ℝ)|^8411 ≤ (5356496603607/25000000000000 : ℝ)^6363
        have hw : |(3117816061/10000000000 : ℝ)|=(3117816061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(704446207/1250000000 : ℝ)|^8411 ≤ (46857000126807/100000000000000 : ℝ)^6363
        have hw : |(704446207/1250000000 : ℝ)|=(704446207/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s0_4 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-936457099/5000000000 : ℝ)*x 0 + (2411067209/5000000000 : ℝ)*x 1 + (6003670081/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (936457099/5000000000 : ℝ)^8411 ≤ (5461852160843/50000000000000 : ℝ)^6363 := by
    have hnat : (936457099 : ℕ)^8411*50000000000000^6363 ≤ 5461852160843^6363*5000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      936457099 5000000000 5461852160843 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2411067209/5000000000 : ℝ)^8411 ≤ (19065863600039/50000000000000 : ℝ)^6363 := by
    have hnat : (2411067209 : ℕ)^8411*50000000000000^6363 ≤ 19065863600039^6363*5000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2411067209 5000000000 19065863600039 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6003670081/10000000000 : ℝ)^8411 ≤ (25472284233513/50000000000000 : ℝ)^6363 := by
    have hnat : (6003670081 : ℕ)^8411*50000000000000^6363 ≤ 25472284233513^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6003670081 10000000000 25472284233513 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-936457099/5000000000 : ℝ), (2411067209/5000000000 : ℝ), (6003670081/10000000000 : ℝ)] ![(5461852160843/50000000000000 : ℝ), (19065863600039/50000000000000 : ℝ), (25472284233513/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-936457099/5000000000 : ℝ)|^8411 ≤ (5461852160843/50000000000000 : ℝ)^6363
        have hw : |(-936457099/5000000000 : ℝ)|=(936457099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2411067209/5000000000 : ℝ)|^8411 ≤ (19065863600039/50000000000000 : ℝ)^6363
        have hw : |(2411067209/5000000000 : ℝ)|=(2411067209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6003670081/10000000000 : ℝ)|^8411 ≤ (25472284233513/50000000000000 : ℝ)^6363
        have hw : |(6003670081/10000000000 : ℝ)|=(6003670081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s0_5 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5173345277/10000000000 : ℝ)*x 0 + (-1367812661/10000000000 : ℝ)*x 1 + (6003671903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5173345277/10000000000 : ℝ)^8411 ≤ (10461302018497/25000000000000 : ℝ)^6363 := by
    have hnat : (5173345277 : ℕ)^8411*25000000000000^6363 ≤ 10461302018497^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5173345277 10000000000 10461302018497 25000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1367812661/10000000000 : ℝ)^8411 ≤ (7210203006921/100000000000000 : ℝ)^6363 := by
    have hnat : (1367812661 : ℕ)^8411*100000000000000^6363 ≤ 7210203006921^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367812661 10000000000 7210203006921 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6003671903/10000000000 : ℝ)^8411 ≤ (50944588903933/100000000000000 : ℝ)^6363 := by
    have hnat : (6003671903 : ℕ)^8411*100000000000000^6363 ≤ 50944588903933^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6003671903 10000000000 50944588903933 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5173345277/10000000000 : ℝ), (-1367812661/10000000000 : ℝ), (6003671903/10000000000 : ℝ)] ![(10461302018497/25000000000000 : ℝ), (7210203006921/100000000000000 : ℝ), (50944588903933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5173345277/10000000000 : ℝ)|^8411 ≤ (10461302018497/25000000000000 : ℝ)^6363
        have hw : |(5173345277/10000000000 : ℝ)|=(5173345277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1367812661/10000000000 : ℝ)|^8411 ≤ (7210203006921/100000000000000 : ℝ)^6363
        have hw : |(-1367812661/10000000000 : ℝ)|=(1367812661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6003671903/10000000000 : ℝ)|^8411 ≤ (50944588903933/100000000000000 : ℝ)^6363
        have hw : |(6003671903/10000000000 : ℝ)|=(6003671903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s0_6 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2586673099/5000000000 : ℝ)*x 0 + (6003670539/10000000000 : ℝ)*x 1 + (-1367813443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2586673099/5000000000 : ℝ)^8411 ≤ (653831530021/1562500000000 : ℝ)^6363 := by
    have hnat : (2586673099 : ℕ)^8411*1562500000000^6363 ≤ 653831530021^6363*5000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586673099 5000000000 653831530021 1562500000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6003670539/10000000000 : ℝ)^8411 ≤ (10188914720859/20000000000000 : ℝ)^6363 := by
    have hnat : (6003670539 : ℕ)^8411*20000000000000^6363 ≤ 10188914720859^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6003670539 10000000000 10188914720859 20000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1367813443/10000000000 : ℝ)^8411 ≤ (3605104227939/50000000000000 : ℝ)^6363 := by
    have hnat : (1367813443 : ℕ)^8411*50000000000000^6363 ≤ 3605104227939^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367813443 10000000000 3605104227939 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2586673099/5000000000 : ℝ), (6003670539/10000000000 : ℝ), (-1367813443/10000000000 : ℝ)] ![(653831530021/1562500000000 : ℝ), (10188914720859/20000000000000 : ℝ), (3605104227939/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2586673099/5000000000 : ℝ)|^8411 ≤ (653831530021/1562500000000 : ℝ)^6363
        have hw : |(2586673099/5000000000 : ℝ)|=(2586673099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6003670539/10000000000 : ℝ)|^8411 ≤ (10188914720859/20000000000000 : ℝ)^6363
        have hw : |(6003670539/10000000000 : ℝ)|=(6003670539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1367813443/10000000000 : ℝ)|^8411 ≤ (3605104227939/50000000000000 : ℝ)^6363
        have hw : |(-1367813443/10000000000 : ℝ)|=(1367813443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s0_7 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (840971769/2000000000 : ℝ)*x 0 + (5570705683/10000000000 : ℝ)*x 1 + (1592485131/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (840971769/2000000000 : ℝ)^8411 ≤ (1988528346017/6250000000000 : ℝ)^6363 := by
    have hnat : (840971769 : ℕ)^8411*6250000000000^6363 ≤ 1988528346017^6363*2000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      840971769 2000000000 1988528346017 6250000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5570705683/10000000000 : ℝ)^8411 ≤ (23072714242267/50000000000000 : ℝ)^6363 := by
    have hnat : (5570705683 : ℕ)^8411*50000000000000^6363 ≤ 23072714242267^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5570705683 10000000000 23072714242267 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1592485131/5000000000 : ℝ)^8411 ≤ (2203811796649/10000000000000 : ℝ)^6363 := by
    have hnat : (1592485131 : ℕ)^8411*10000000000000^6363 ≤ 2203811796649^6363*5000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1592485131 5000000000 2203811796649 10000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(840971769/2000000000 : ℝ), (5570705683/10000000000 : ℝ), (1592485131/5000000000 : ℝ)] ![(1988528346017/6250000000000 : ℝ), (23072714242267/50000000000000 : ℝ), (2203811796649/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(840971769/2000000000 : ℝ)|^8411 ≤ (1988528346017/6250000000000 : ℝ)^6363
        have hw : |(840971769/2000000000 : ℝ)|=(840971769/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5570705683/10000000000 : ℝ)|^8411 ≤ (23072714242267/50000000000000 : ℝ)^6363
        have hw : |(5570705683/10000000000 : ℝ)|=(5570705683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1592485131/5000000000 : ℝ)|^8411 ≤ (2203811796649/10000000000000 : ℝ)^6363
        have hw : |(1592485131/5000000000 : ℝ)|=(1592485131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1218_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150958703/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (361/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13763/50000 : ℝ)*pair X 0 0 := by
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
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (4205/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4205 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4205*1^1024 ≤ 0^1024*1^4205 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4205 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4205/1024 : ℝ) ≤ (2322101060098719827/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4205 ≤ (2322101060098719827/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4205*100000000000000000000^1024 ≤ 2322101060098719827^1024*5^4205 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2322101060098719827 100000000000000000000 4205 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2322101060098719827/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4205/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4205 := by
      have hnat : (1 : ℕ)^1024*1^4205 ≤ 1^4205*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102322101060098719827/100000000000000000000 : ℝ) ≤ (2514014424410763/2500000000000000 : ℝ) ^ (4205/1024 : ℝ) := by
    have hpowers : (102322101060098719827/100000000000000000000 : ℝ)^1024 ≤ (2514014424410763/2500000000000000 : ℝ)^4205 := by
      have hnat : (102322101060098719827 : ℕ)^1024*2500000000000000^4205 ≤ 2514014424410763^4205*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102322101060098719827 100000000000000000000 2514014424410763 2500000000000000 1024 4205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2514014424410763/2500000000000000 : ℝ)) (X := (102322101060098719827/100000000000000000000 : ℝ)) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52322101060098719827/50000000000000000000 : ℝ) ≤ (1264014424410763/1250000000000000 : ℝ) ^ (4205/1024 : ℝ) := by
    have hpowers : (52322101060098719827/50000000000000000000 : ℝ)^1024 ≤ (1264014424410763/1250000000000000 : ℝ)^4205 := by
      have hnat : (52322101060098719827 : ℕ)^1024*1250000000000000^4205 ≤ 1264014424410763^4205*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52322101060098719827 50000000000000000000 1264014424410763 1250000000000000 1024 4205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1264014424410763/1250000000000000 : ℝ)) (X := (52322101060098719827/50000000000000000000 : ℝ)) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(14014424410763/1000000000000000 : ℝ)*(0 : ℝ))^(4205/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(14014424410763/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2322101060098719827/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(14014424410763/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4205/1024 : ℝ) := by
    rw [show (1 : ℝ)+(14014424410763/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2514014424410763/2500000000000000 : ℝ) by norm_num, show 1+(2322101060098719827/100000000000000000000 : ℝ)+(0 : ℝ)=(102322101060098719827/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2322101060098719827/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(14014424410763/1000000000000000 : ℝ)*(2/5 : ℝ))^(4205/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(14014424410763/1000000000000000 : ℝ)*(2/5 : ℝ)=(1264014424410763/1250000000000000 : ℝ) by norm_num, show 1+2*(2322101060098719827/100000000000000000000 : ℝ)=(52322101060098719827/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(14014424410763/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4205/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14014424410763/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(14014424410763/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4205/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14014424410763/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(14014424410763/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4205/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14014424410763/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-23349851/125000000 : ℝ)*X 0 0+(6036930879/10000000000 : ℝ)*X 0 1+(2395004163/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5512511633/10000000000 : ℝ)*X 1 0+(-2581476191/10000000000 : ℝ)*X 1 1+(4790008291/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5512511609/10000000000 : ℝ)*X 2 0+(4790008321/10000000000 : ℝ)*X 2 1+(-1290738093/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2097456509/5000000000 : ℝ)*X 0 0+(3117816061/10000000000 : ℝ)*X 0 1+(704446207/1250000000 : ℝ)*X 0 2+(2097456509/5000000000 : ℝ)*X 1 0+(3117816061/10000000000 : ℝ)*X 1 1+(704446207/1250000000 : ℝ)*X 1 2+(2097456509/5000000000 : ℝ)*X 2 0+(3117816061/10000000000 : ℝ)*X 2 1+(704446207/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-936457099/5000000000 : ℝ)*X 0 0+(2411067209/5000000000 : ℝ)*X 0 1+(6003670081/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5173345277/10000000000 : ℝ)*X 1 0+(-1367812661/10000000000 : ℝ)*X 1 1+(6003671903/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2586673099/5000000000 : ℝ)*X 2 0+(6003670539/10000000000 : ℝ)*X 2 1+(-1367813443/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((840971769/2000000000 : ℝ)*X 0 0+(5570705683/10000000000 : ℝ)*X 0 1+(1592485131/5000000000 : ℝ)*X 0 2+(840971769/2000000000 : ℝ)*X 1 0+(5570705683/10000000000 : ℝ)*X 1 1+(1592485131/5000000000 : ℝ)*X 1 2+(840971769/2000000000 : ℝ)*X 2 0+(5570705683/10000000000 : ℝ)*X 2 1+(1592485131/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (319191363710749717784331/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9024397/12500000000000 : ℝ)*(base1) + (780008121/50000000000000 : ℝ)*(base19) + (289945921/20000000000000 : ℝ)*(base23) + (106795023/100000000000000 : ℝ)*(base24) + (177919659/50000000000000 : ℝ)*(upper3) + (599583569782807/100000000000000 : ℝ)*(major0) + (599583569782807/100000000000000 : ℝ)*(major1) + (599583569782807/100000000000000 : ℝ)*(major2) + (160395940909899/20000000000000 : ℝ)*(sp0) + (40099076457219/5000000000000 : ℝ)*(sp1) + (100247691579499/12500000000000 : ℝ)*(sp2) + (198590522585433/50000000000000 : ℝ)*(sp3) + (1728403151/50000000000000 : ℝ)*(sp4) + (2720244703/100000000000000 : ℝ)*(sp7) + (79436767522149/20000000000000 : ℝ)*(f.failure) + (801983089160621/100000000000000 : ℝ)*(f.sum) + (60583551801741/50000000000000000000000000000 : ℝ)*base65 + (87114431551741/100000000000000000000000000000 : ℝ)*base67 + (146921851751741/100000000000000000000000000000 : ℝ)*base69 + (83257446851741/100000000000000000000000000000 : ℝ)*base71 + (136814393401741/50000000000000000000000000000 : ℝ)*base73 + (460809023048259/100000000000000000000000000000 : ℝ)*base76 + (584791588051741/100000000000000000000000000000 : ℝ)*base77 + (450991322451741/100000000000000000000000000000 : ℝ)*base79 + (260336025348259/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (3187253/2000000000000000000000 : ℝ)*base90 + (3187253/2000000000000000000000 : ℝ)*base92 + (3187253/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (61015925025552828219327/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (73452453/10000000000000 : ℝ)*(base19) + (980047477/100000000000000 : ℝ)*(base23) + (44123941/50000000000000 : ℝ)*(base39) + (3432021/1562500000000 : ℝ)*(upper3) + (158189126292633/25000000000000 : ℝ)*(major0) + (158189126292633/25000000000000 : ℝ)*(major1) + (12655128338453/2000000000000 : ℝ)*(major2) + (939702251/50000000000000 : ℝ)*(sp1) + (1008276547/50000000000000 : ℝ)*(sp2) + (27798043/100000000000000 : ℝ)*(sp3) + (169270832368893/20000000000000 : ℝ)*(sp4) + (105793943489429/12500000000000 : ℝ)*(sp5) + (846351253491777/100000000000000 : ℝ)*(sp6) + (419158651096099/100000000000000 : ℝ)*(sp7) + (209579339447071/50000000000000 : ℝ)*(f.failure) + (846354250092347/100000000000000 : ℝ)*(f.sum) + (106509696908933/50000000000000000000000000000 : ℝ)*base65 + (3367231250361/2000000000000000000000000000 : ℝ)*base68 + (173468162533979/25000000000000000000000000000 : ℝ)*base69 + (8325848251639/2000000000000000000000000000 : ℝ)*base71 + (22732324558933/50000000000000000000000000000 : ℝ)*base73 + (229836124708979/25000000000000000000000000000 : ℝ)*base75 + (75174555216021/25000000000000000000000000000 : ℝ)*base78 + (109482072616021/25000000000000000000000000000 : ℝ)*base80 + (79396564671479/12500000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (24691087/5000000000000000000000 : ℝ)*base90 + (24691087/5000000000000000000000 : ℝ)*base92 + (24691087/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1218_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150958703/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (361/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13763/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1218_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1218_s1_0 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-206714721/1000000000 : ℝ)*x 0 + (5681667953/10000000000 : ℝ)*x 1 + (2508893129/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (206714721/1000000000 : ℝ)^8411 ≤ (12445614010773/100000000000000 : ℝ)^6363 := by
    have hnat : (206714721 : ℕ)^8411*100000000000000^6363 ≤ 12445614010773^6363*1000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206714721 1000000000 12445614010773 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5681667953/10000000000 : ℝ)^8411 ≤ (23682157458371/50000000000000 : ℝ)^6363 := by
    have hnat : (5681667953 : ℕ)^8411*50000000000000^6363 ≤ 23682157458371^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5681667953 10000000000 23682157458371 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2508893129/5000000000 : ℝ)^8411 ≤ (20095035528133/50000000000000 : ℝ)^6363 := by
    have hnat : (2508893129 : ℕ)^8411*50000000000000^6363 ≤ 20095035528133^6363*5000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2508893129 5000000000 20095035528133 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-206714721/1000000000 : ℝ), (5681667953/10000000000 : ℝ), (2508893129/5000000000 : ℝ)] ![(12445614010773/100000000000000 : ℝ), (23682157458371/50000000000000 : ℝ), (20095035528133/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-206714721/1000000000 : ℝ)|^8411 ≤ (12445614010773/100000000000000 : ℝ)^6363
        have hw : |(-206714721/1000000000 : ℝ)|=(206714721/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5681667953/10000000000 : ℝ)|^8411 ≤ (23682157458371/50000000000000 : ℝ)^6363
        have hw : |(5681667953/10000000000 : ℝ)|=(5681667953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2508893129/5000000000 : ℝ)|^8411 ≤ (20095035528133/50000000000000 : ℝ)^6363
        have hw : |(2508893129/5000000000 : ℝ)|=(2508893129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s1_1 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5414962049/10000000000 : ℝ)*x 0 + (-606014449/2500000000 : ℝ)*x 1 + (5017786251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5414962049/10000000000 : ℝ)^8411 ≤ (2222389828537/5000000000000 : ℝ)^6363 := by
    have hnat : (5414962049 : ℕ)^8411*5000000000000^6363 ≤ 2222389828537^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414962049 10000000000 2222389828537 5000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (606014449/2500000000 : ℝ)^8411 ≤ (1536213242773/10000000000000 : ℝ)^6363 := by
    have hnat : (606014449 : ℕ)^8411*10000000000000^6363 ≤ 1536213242773^6363*2500000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      606014449 2500000000 1536213242773 10000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5017786251/10000000000 : ℝ)^8411 ≤ (40190070982153/100000000000000 : ℝ)^6363 := by
    have hnat : (5017786251 : ℕ)^8411*100000000000000^6363 ≤ 40190070982153^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5017786251 10000000000 40190070982153 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5414962049/10000000000 : ℝ), (-606014449/2500000000 : ℝ), (5017786251/10000000000 : ℝ)] ![(2222389828537/5000000000000 : ℝ), (1536213242773/10000000000000 : ℝ), (40190070982153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5414962049/10000000000 : ℝ)|^8411 ≤ (2222389828537/5000000000000 : ℝ)^6363
        have hw : |(5414962049/10000000000 : ℝ)|=(5414962049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-606014449/2500000000 : ℝ)|^8411 ≤ (1536213242773/10000000000000 : ℝ)^6363
        have hw : |(-606014449/2500000000 : ℝ)|=(606014449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5017786251/10000000000 : ℝ)|^8411 ≤ (40190070982153/100000000000000 : ℝ)^6363
        have hw : |(5017786251/10000000000 : ℝ)|=(5017786251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s1_2 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5414962047/10000000000 : ℝ)*x 0 + (627223283/1250000000 : ℝ)*x 1 + (-1212028891/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5414962047/10000000000 : ℝ)^8411 ≤ (555597456863/1250000000000 : ℝ)^6363 := by
    have hnat : (5414962047 : ℕ)^8411*1250000000000^6363 ≤ 555597456863^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414962047 10000000000 555597456863 1250000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (627223283/1250000000 : ℝ)^8411 ≤ (4019007111979/10000000000000 : ℝ)^6363 := by
    have hnat : (627223283 : ℕ)^8411*10000000000000^6363 ≤ 4019007111979^6363*1250000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      627223283 1250000000 4019007111979 10000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1212028891/5000000000 : ℝ)^8411 ≤ (307242646209/2000000000000 : ℝ)^6363 := by
    have hnat : (1212028891 : ℕ)^8411*2000000000000^6363 ≤ 307242646209^6363*5000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1212028891 5000000000 307242646209 2000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5414962047/10000000000 : ℝ), (627223283/1250000000 : ℝ), (-1212028891/5000000000 : ℝ)] ![(555597456863/1250000000000 : ℝ), (4019007111979/10000000000000 : ℝ), (307242646209/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5414962047/10000000000 : ℝ)|^8411 ≤ (555597456863/1250000000000 : ℝ)^6363
        have hw : |(5414962047/10000000000 : ℝ)|=(5414962047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(627223283/1250000000 : ℝ)|^8411 ≤ (4019007111979/10000000000000 : ℝ)^6363
        have hw : |(627223283/1250000000 : ℝ)|=(627223283/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1212028891/5000000000 : ℝ)|^8411 ≤ (307242646209/2000000000000 : ℝ)^6363
        have hw : |(-1212028891/5000000000 : ℝ)|=(1212028891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s1_3 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (862187091/2000000000 : ℝ)*x 0 + (3691107059/10000000000 : ℝ)*x 1 + (2515800033/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (862187091/2000000000 : ℝ)^8411 ≤ (16440856456723/50000000000000 : ℝ)^6363 := by
    have hnat : (862187091 : ℕ)^8411*50000000000000^6363 ≤ 16440856456723^6363*2000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862187091 2000000000 16440856456723 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3691107059/10000000000 : ℝ)^8411 ≤ (26781897945103/100000000000000 : ℝ)^6363 := by
    have hnat : (3691107059 : ℕ)^8411*100000000000000^6363 ≤ 26781897945103^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3691107059 10000000000 26781897945103 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2515800033/5000000000 : ℝ)^8411 ≤ (4033638913417/10000000000000 : ℝ)^6363 := by
    have hnat : (2515800033 : ℕ)^8411*10000000000000^6363 ≤ 4033638913417^6363*5000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2515800033 5000000000 4033638913417 10000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(862187091/2000000000 : ℝ), (3691107059/10000000000 : ℝ), (2515800033/5000000000 : ℝ)] ![(16440856456723/50000000000000 : ℝ), (26781897945103/100000000000000 : ℝ), (4033638913417/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(862187091/2000000000 : ℝ)|^8411 ≤ (16440856456723/50000000000000 : ℝ)^6363
        have hw : |(862187091/2000000000 : ℝ)|=(862187091/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3691107059/10000000000 : ℝ)|^8411 ≤ (26781897945103/100000000000000 : ℝ)^6363
        have hw : |(3691107059/10000000000 : ℝ)|=(3691107059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2515800033/5000000000 : ℝ)|^8411 ≤ (4033638913417/10000000000000 : ℝ)^6363
        have hw : |(2515800033/5000000000 : ℝ)|=(2515800033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s1_4 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-41356987/200000000 : ℝ)*x 0 + (1005317369/2000000000 : ℝ)*x 1 + (5672700593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41356987/200000000 : ℝ)^8411 ≤ (1556400286227/12500000000000 : ℝ)^6363 := by
    have hnat : (41356987 : ℕ)^8411*12500000000000^6363 ≤ 1556400286227^6363*200000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41356987 200000000 1556400286227 12500000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1005317369/2000000000 : ℝ)^8411 ≤ (10070818331103/25000000000000 : ℝ)^6363 := by
    have hnat : (1005317369 : ℕ)^8411*25000000000000^6363 ≤ 10070818331103^6363*2000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005317369 2000000000 10070818331103 25000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5672700593/10000000000 : ℝ)^8411 ≤ (23632762187927/50000000000000 : ℝ)^6363 := by
    have hnat : (5672700593 : ℕ)^8411*50000000000000^6363 ≤ 23632762187927^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5672700593 10000000000 23632762187927 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-41356987/200000000 : ℝ), (1005317369/2000000000 : ℝ), (5672700593/10000000000 : ℝ)] ![(1556400286227/12500000000000 : ℝ), (10070818331103/25000000000000 : ℝ), (23632762187927/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-41356987/200000000 : ℝ)|^8411 ≤ (1556400286227/12500000000000 : ℝ)^6363
        have hw : |(-41356987/200000000 : ℝ)|=(41356987/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1005317369/2000000000 : ℝ)|^8411 ≤ (10070818331103/25000000000000 : ℝ)^6363
        have hw : |(1005317369/2000000000 : ℝ)|=(1005317369/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5672700593/10000000000 : ℝ)|^8411 ≤ (23632762187927/50000000000000 : ℝ)^6363
        have hw : |(5672700593/10000000000 : ℝ)|=(5672700593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s1_5 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1311030417/2500000000 : ℝ)*x 0 + (-55285877/312500000 : ℝ)*x 1 + (5672695249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1311030417/2500000000 : ℝ)^8411 ≤ (5325451502617/12500000000000 : ℝ)^6363 := by
    have hnat : (1311030417 : ℕ)^8411*12500000000000^6363 ≤ 5325451502617^6363*2500000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311030417 2500000000 5325451502617 12500000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (55285877/312500000 : ℝ)^8411 ≤ (5065461227573/50000000000000 : ℝ)^6363 := by
    have hnat : (55285877 : ℕ)^8411*50000000000000^6363 ≤ 5065461227573^6363*312500000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55285877 312500000 5065461227573 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5672695249/10000000000 : ℝ)^8411 ≤ (4726546551769/10000000000000 : ℝ)^6363 := by
    have hnat : (5672695249 : ℕ)^8411*10000000000000^6363 ≤ 4726546551769^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5672695249 10000000000 4726546551769 10000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1311030417/2500000000 : ℝ), (-55285877/312500000 : ℝ), (5672695249/10000000000 : ℝ)] ![(5325451502617/12500000000000 : ℝ), (5065461227573/50000000000000 : ℝ), (4726546551769/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1311030417/2500000000 : ℝ)|^8411 ≤ (5325451502617/12500000000000 : ℝ)^6363
        have hw : |(1311030417/2500000000 : ℝ)|=(1311030417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-55285877/312500000 : ℝ)|^8411 ≤ (5065461227573/50000000000000 : ℝ)^6363
        have hw : |(-55285877/312500000 : ℝ)|=(55285877/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5672695249/10000000000 : ℝ)|^8411 ≤ (4726546551769/10000000000000 : ℝ)^6363
        have hw : |(5672695249/10000000000 : ℝ)|=(5672695249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s1_6 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (327757613/625000000 : ℝ)*x 0 + (56726957/100000000 : ℝ)*x 1 + (-221143401/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (327757613/625000000 : ℝ)^8411 ≤ (2130180676219/5000000000000 : ℝ)^6363 := by
    have hnat : (327757613 : ℕ)^8411*5000000000000^6363 ≤ 2130180676219^6363*625000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327757613 625000000 2130180676219 5000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (56726957/100000000 : ℝ)^8411 ≤ (11816367621237/25000000000000 : ℝ)^6363 := by
    have hnat : (56726957 : ℕ)^8411*25000000000000^6363 ≤ 11816367621237^6363*100000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56726957 100000000 11816367621237 25000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (221143401/1250000000 : ℝ)^8411 ≤ (2026183195121/20000000000000 : ℝ)^6363 := by
    have hnat : (221143401 : ℕ)^8411*20000000000000^6363 ≤ 2026183195121^6363*1250000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221143401 1250000000 2026183195121 20000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(327757613/625000000 : ℝ), (56726957/100000000 : ℝ), (-221143401/1250000000 : ℝ)] ![(2130180676219/5000000000000 : ℝ), (11816367621237/25000000000000 : ℝ), (2026183195121/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(327757613/625000000 : ℝ)|^8411 ≤ (2130180676219/5000000000000 : ℝ)^6363
        have hw : |(327757613/625000000 : ℝ)|=(327757613/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(56726957/100000000 : ℝ)|^8411 ≤ (11816367621237/25000000000000 : ℝ)^6363
        have hw : |(56726957/100000000 : ℝ)|=(56726957/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-221143401/1250000000 : ℝ)|^8411 ≤ (2026183195121/20000000000000 : ℝ)^6363
        have hw : |(-221143401/1250000000 : ℝ)|=(221143401/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s1_7 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4312358551/10000000000 : ℝ)*x 0 + (5013825387/10000000000 : ℝ)*x 1 + (3709223991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4312358551/10000000000 : ℝ)^8411 ≤ (6579212410803/20000000000000 : ℝ)^6363 := by
    have hnat : (4312358551 : ℕ)^8411*20000000000000^6363 ≤ 6579212410803^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4312358551 10000000000 6579212410803 20000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5013825387/10000000000 : ℝ)^8411 ≤ (40148140768673/100000000000000 : ℝ)^6363 := by
    have hnat : (5013825387 : ℕ)^8411*100000000000000^6363 ≤ 40148140768673^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5013825387 10000000000 40148140768673 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3709223991/10000000000 : ℝ)^8411 ≤ (842368661013/3125000000000 : ℝ)^6363 := by
    have hnat : (3709223991 : ℕ)^8411*3125000000000^6363 ≤ 842368661013^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3709223991 10000000000 842368661013 3125000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4312358551/10000000000 : ℝ), (5013825387/10000000000 : ℝ), (3709223991/10000000000 : ℝ)] ![(6579212410803/20000000000000 : ℝ), (40148140768673/100000000000000 : ℝ), (842368661013/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4312358551/10000000000 : ℝ)|^8411 ≤ (6579212410803/20000000000000 : ℝ)^6363
        have hw : |(4312358551/10000000000 : ℝ)|=(4312358551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5013825387/10000000000 : ℝ)|^8411 ≤ (40148140768673/100000000000000 : ℝ)^6363
        have hw : |(5013825387/10000000000 : ℝ)|=(5013825387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3709223991/10000000000 : ℝ)|^8411 ≤ (842368661013/3125000000000 : ℝ)^6363
        have hw : |(3709223991/10000000000 : ℝ)|=(3709223991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1218_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150958703/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13763/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (361/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (379/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20101/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13763/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (361/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13763/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (361/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13763/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (361/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13763/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (361/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13763/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (361/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13763/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (361/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (361/50000 : ℝ) ^ (4205/1024 : ℝ) ≤ (160768186579/100000000000000000000 : ℝ) := by
    have hpowers : (361/50000 : ℝ)^4205 ≤ (160768186579/100000000000000000000 : ℝ)^1024 := by
      have hnat : (361 : ℕ)^4205*100000000000000000000^1024 ≤ 160768186579^1024*50000^4205 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        361 50000 160768186579 100000000000000000000 4205 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (361/50000 : ℝ)) (X := (160768186579/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (13763/50000 : ℝ) ^ (4205/1024 : ℝ) ≤ (500421202247739861/100000000000000000000 : ℝ) := by
    have hpowers : (13763/50000 : ℝ)^4205 ≤ (500421202247739861/100000000000000000000 : ℝ)^1024 := by
      have hnat : (13763 : ℕ)^4205*100000000000000000000^1024 ≤ 500421202247739861^1024*50000^4205 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13763 50000 500421202247739861 100000000000000000000 4205 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13763/50000 : ℝ)) (X := (500421202247739861/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000160768186579/50000000000000000000 : ℝ) ≤ (5000000003915021/5000000000000000 : ℝ) ^ (4205/1024 : ℝ) := by
    have hpowers : (50000000160768186579/50000000000000000000 : ℝ)^1024 ≤ (5000000003915021/5000000000000000 : ℝ)^4205 := by
      have hnat : (50000000160768186579 : ℕ)^1024*5000000000000000^4205 ≤ 5000000003915021^4205*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000160768186579 50000000000000000000 5000000003915021 5000000000000000 1024 4205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000003915021/5000000000000000 : ℝ)) (X := (50000000160768186579/50000000000000000000 : ℝ)) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2512510534075398161/2500000000000000000 : ℝ) ≤ (10012163243286559/10000000000000000 : ℝ) ^ (4205/1024 : ℝ) := by
    have hpowers : (2512510534075398161/2500000000000000000 : ℝ)^1024 ≤ (10012163243286559/10000000000000000 : ℝ)^4205 := by
      have hnat : (2512510534075398161 : ℕ)^1024*10000000000000000^4205 ≤ 10012163243286559^4205*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2512510534075398161 2500000000000000000 10012163243286559 10000000000000000 1024 4205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10012163243286559/10000000000000000 : ℝ)) (X := (2512510534075398161/2500000000000000000 : ℝ)) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50500421202247739861/50000000000000000000 : ℝ) ≤ (2506081619685769/2500000000000000 : ℝ) ^ (4205/1024 : ℝ) := by
    have hpowers : (50500421202247739861/50000000000000000000 : ℝ)^1024 ≤ (2506081619685769/2500000000000000 : ℝ)^4205 := by
      have hnat : (50500421202247739861 : ℕ)^1024*2500000000000000^4205 ≤ 2506081619685769^4205*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50500421202247739861 50000000000000000000 2506081619685769 2500000000000000 1024 4205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2506081619685769/2500000000000000 : ℝ)) (X := (50500421202247739861/50000000000000000000 : ℝ)) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(160768186579/100000000000000000000 : ℝ) ≤ ((13401121824893861761/13402000000000000000 : ℝ)+2*(12163235456517/2680400000000000 : ℝ)*(361/50000 : ℝ))^(4205/1024 : ℝ) := by
    rw [show (13401121824893861761/13402000000000000000 : ℝ)+2*(12163235456517/2680400000000000 : ℝ)*(361/50000 : ℝ)=(5000000003915021/5000000000000000 : ℝ) by norm_num, show 1+2*(160768186579/100000000000000000000 : ℝ)=(50000000160768186579/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(500421202247739861/100000000000000000000 : ℝ)+(160768186579/100000000000000000000 : ℝ) ≤ ((13401121824893861761/13402000000000000000 : ℝ)+(12163235456517/2680400000000000 : ℝ)*((13763/50000 : ℝ)+(361/50000 : ℝ)))^(4205/1024 : ℝ) := by
    rw [show (13401121824893861761/13402000000000000000 : ℝ)+(12163235456517/2680400000000000 : ℝ)*((13763/50000 : ℝ)+(361/50000 : ℝ))=(10012163243286559/10000000000000000 : ℝ) by norm_num, show 1+(500421202247739861/100000000000000000000 : ℝ)+(160768186579/100000000000000000000 : ℝ)=(2512510534075398161/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(500421202247739861/100000000000000000000 : ℝ) ≤ ((13401121824893861761/13402000000000000000 : ℝ)+2*(12163235456517/2680400000000000 : ℝ)*(13763/50000 : ℝ))^(4205/1024 : ℝ) := by
    rw [show (13401121824893861761/13402000000000000000 : ℝ)+2*(12163235456517/2680400000000000 : ℝ)*(13763/50000 : ℝ)=(2506081619685769/2500000000000000 : ℝ) by norm_num, show 1+2*(500421202247739861/100000000000000000000 : ℝ)=(50500421202247739861/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13401121824893861761/13402000000000000000 : ℝ)*(X 1 0+X 2 0)+(12163235456517/2680400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4205/1024 : ℝ)) (lo := (361/50000 : ℝ)) (hi := (13763/50000 : ℝ)) (c := (13401121824893861761/13402000000000000000 : ℝ)) (alpha := (12163235456517/2680400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13401121824893861761/13402000000000000000 : ℝ)*(X 0 1+X 2 1)+(12163235456517/2680400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4205/1024 : ℝ)) (lo := (361/50000 : ℝ)) (hi := (13763/50000 : ℝ)) (c := (13401121824893861761/13402000000000000000 : ℝ)) (alpha := (12163235456517/2680400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13401121824893861761/13402000000000000000 : ℝ)*(X 0 2+X 1 2)+(12163235456517/2680400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4205/1024 : ℝ)) (lo := (361/50000 : ℝ)) (hi := (13763/50000 : ℝ)) (c := (13401121824893861761/13402000000000000000 : ℝ)) (alpha := (12163235456517/2680400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-206714721/1000000000 : ℝ)*X 0 0+(5681667953/10000000000 : ℝ)*X 0 1+(2508893129/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5414962049/10000000000 : ℝ)*X 1 0+(-606014449/2500000000 : ℝ)*X 1 1+(5017786251/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5414962047/10000000000 : ℝ)*X 2 0+(627223283/1250000000 : ℝ)*X 2 1+(-1212028891/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((862187091/2000000000 : ℝ)*X 0 0+(3691107059/10000000000 : ℝ)*X 0 1+(2515800033/5000000000 : ℝ)*X 0 2+(862187091/2000000000 : ℝ)*X 1 0+(3691107059/10000000000 : ℝ)*X 1 1+(2515800033/5000000000 : ℝ)*X 1 2+(862187091/2000000000 : ℝ)*X 2 0+(3691107059/10000000000 : ℝ)*X 2 1+(2515800033/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-41356987/200000000 : ℝ)*X 0 0+(1005317369/2000000000 : ℝ)*X 0 1+(5672700593/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1311030417/2500000000 : ℝ)*X 1 0+(-55285877/312500000 : ℝ)*X 1 1+(5672695249/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((327757613/625000000 : ℝ)*X 2 0+(56726957/100000000 : ℝ)*X 2 1+(-221143401/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4312358551/10000000000 : ℝ)*X 0 0+(5013825387/10000000000 : ℝ)*X 0 1+(3709223991/10000000000 : ℝ)*X 0 2+(4312358551/10000000000 : ℝ)*X 1 0+(5013825387/10000000000 : ℝ)*X 1 1+(3709223991/10000000000 : ℝ)*X 1 2+(4312358551/10000000000 : ℝ)*X 2 0+(5013825387/10000000000 : ℝ)*X 2 1+(3709223991/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2897118510086087325547563363/335050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (98049439/100000000000000 : ℝ)*(base1) + (186095311/10000000000000 : ℝ)*(base19) + (930198379/50000000000000 : ℝ)*(base23) + (40737941/20000000000000 : ℝ)*(upper3) + (208732879/100000000000000 : ℝ)*(upper5) + (563079344289413/50000000000000 : ℝ)*(major0) + (563079344289413/50000000000000 : ℝ)*(major1) + (563079344289413/50000000000000 : ℝ)*(major2) + (150630242658829/10000000000000 : ℝ)*(sp0) + (1506310747149723/100000000000000 : ℝ)*(sp1) + (60252429908243/4000000000000 : ℝ)*(sp2) + (372999615372551/50000000000000 : ℝ)*(sp3) + (5139781991/50000000000000 : ℝ)*(sp4) + (644004099/12500000000000 : ℝ)*(sp7) + (746004480827333/100000000000000 : ℝ)*(f.failure) + (1506312608102833/100000000000000 : ℝ)*(f.sum) + (90054853288501/67010000000000000000000000000 : ℝ)*base65 + (3714653394562241293/670100000000000000000000000000000 : ℝ)*base67 + (3459615299295441293/670100000000000000000000000000000 : ℝ)*base69 + (4278337797517541293/670100000000000000000000000000000 : ℝ)*base71 + (60842406733619/67010000000000000000000000000 : ℝ)*base74 + (6375020490372741293/670100000000000000000000000000000 : ℝ)*base75 + (1952773774547741293/670100000000000000000000000000000 : ℝ)*base77 + (6415647819098241293/670100000000000000000000000000000 : ℝ)*base79 + (139216689396981/67010000000000000000000000000 : ℝ)*base81 + (43370901/10000000000000000000000 : ℝ)*base90 + (43370901/10000000000000000000000 : ℝ)*base92 + (43370901/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3273551592993817950015096663/670100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (339441727/100000000000000 : ℝ)*(base19) + (379661617/50000000000000 : ℝ)*(base23) + (221693/160000000000 : ℝ)*(lower2) + (242995933/100000000000000 : ℝ)*(lower3) + (308934623/100000000000000 : ℝ)*(lower4) + (1157123439342287/100000000000000 : ℝ)*(major0) + (1157123439342287/100000000000000 : ℝ)*(major1) + (1157123439342287/100000000000000 : ℝ)*(major2) + (6676053113/100000000000000 : ℝ)*(sp0) + (329503883/20000000000000 : ℝ)*(sp2) + (154772349165927/10000000000000 : ℝ)*(sp4) + (24183278566729/1562500000000 : ℝ)*(sp5) + (773863880434867/50000000000000 : ℝ)*(sp6) + (30660661925329/4000000000000 : ℝ)*(sp7) + (30660661925329/4000000000000 : ℝ)*(f.failure) + (1547730167712383/100000000000000 : ℝ)*(f.sum) + (4083456014350521/134020000000000000000000000000 : ℝ)*base66 + (2930161959031317593/1340200000000000000000000000000000 : ℝ)*base68 + (4771858533596317593/1340200000000000000000000000000000 : ℝ)*base70 + (2395498910945117593/1340200000000000000000000000000000 : ℝ)*base72 + (30363581821441/134020000000000000000000000000 : ℝ)*base74 + (221671909812317593/1340200000000000000000000000000000 : ℝ)*base76 + (973583390878917593/1340200000000000000000000000000000 : ℝ)*base78 + (29894943770875517593/1340200000000000000000000000000000 : ℝ)*base80 + (903743466963081/134020000000000000000000000000 : ℝ)*base82 + (688287/400000000000000000000 : ℝ)*base89 + (688287/400000000000000000000 : ℝ)*base91 + (688287/400000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1218_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150958703/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13763/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (361/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (379/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20101/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1218_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1218_s2_0 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-33068757/156250000 : ℝ)*x 0 + (1374233037/2500000000 : ℝ)*x 1 + (2585566503/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33068757/156250000 : ℝ)^8411 ≤ (12839090385773/100000000000000 : ℝ)^6363 := by
    have hnat : (33068757 : ℕ)^8411*100000000000000^6363 ≤ 12839090385773^6363*156250000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33068757 156250000 12839090385773 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1374233037/2500000000 : ℝ)^8411 ≤ (45339353552283/100000000000000 : ℝ)^6363 := by
    have hnat : (1374233037 : ℕ)^8411*100000000000000^6363 ≤ 45339353552283^6363*2500000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1374233037 2500000000 45339353552283 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2585566503/5000000000 : ℝ)^8411 ≤ (41821556044513/100000000000000 : ℝ)^6363 := by
    have hnat : (2585566503 : ℕ)^8411*100000000000000^6363 ≤ 41821556044513^6363*5000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2585566503 5000000000 41821556044513 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-33068757/156250000 : ℝ), (1374233037/2500000000 : ℝ), (2585566503/5000000000 : ℝ)] ![(12839090385773/100000000000000 : ℝ), (45339353552283/100000000000000 : ℝ), (41821556044513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-33068757/156250000 : ℝ)|^8411 ≤ (12839090385773/100000000000000 : ℝ)^6363
        have hw : |(-33068757/156250000 : ℝ)|=(33068757/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1374233037/2500000000 : ℝ)|^8411 ≤ (45339353552283/100000000000000 : ℝ)^6363
        have hw : |(1374233037/2500000000 : ℝ)|=(1374233037/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2585566503/5000000000 : ℝ)|^8411 ≤ (41821556044513/100000000000000 : ℝ)^6363
        have hw : |(2585566503/5000000000 : ℝ)|=(2585566503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s2_1 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5370666449/10000000000 : ℝ)*x 0 + (-1142652463/5000000000 : ℝ)*x 1 + (5171132939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370666449/10000000000 : ℝ)^8411 ≤ (2198390562629/5000000000000 : ℝ)^6363 := by
    have hnat : (5370666449 : ℕ)^8411*5000000000000^6363 ≤ 2198390562629^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370666449 10000000000 2198390562629 5000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1142652463/5000000000 : ℝ)^8411 ≤ (2842126681873/20000000000000 : ℝ)^6363 := by
    have hnat : (1142652463 : ℕ)^8411*20000000000000^6363 ≤ 2842126681873^6363*5000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1142652463 5000000000 2842126681873 20000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5171132939/10000000000 : ℝ)^8411 ≤ (20910777664123/50000000000000 : ℝ)^6363 := by
    have hnat : (5171132939 : ℕ)^8411*50000000000000^6363 ≤ 20910777664123^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5171132939 10000000000 20910777664123 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370666449/10000000000 : ℝ), (-1142652463/5000000000 : ℝ), (5171132939/10000000000 : ℝ)] ![(2198390562629/5000000000000 : ℝ), (2842126681873/20000000000000 : ℝ), (20910777664123/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370666449/10000000000 : ℝ)|^8411 ≤ (2198390562629/5000000000000 : ℝ)^6363
        have hw : |(5370666449/10000000000 : ℝ)|=(5370666449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1142652463/5000000000 : ℝ)|^8411 ≤ (2842126681873/20000000000000 : ℝ)^6363
        have hw : |(-1142652463/5000000000 : ℝ)|=(1142652463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5171132939/10000000000 : ℝ)|^8411 ≤ (20910777664123/50000000000000 : ℝ)^6363
        have hw : |(5171132939/10000000000 : ℝ)|=(5171132939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s2_2 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4296533/8000000 : ℝ)*x 0 + (1034226623/2000000000 : ℝ)*x 1 + (-2285304959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4296533/8000000 : ℝ)^8411 ≤ (21983904549539/50000000000000 : ℝ)^6363 := by
    have hnat : (4296533 : ℕ)^8411*50000000000000^6363 ≤ 21983904549539^6363*8000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4296533 8000000 21983904549539 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1034226623/2000000000 : ℝ)^8411 ≤ (41821557209783/100000000000000 : ℝ)^6363 := by
    have hnat : (1034226623 : ℕ)^8411*100000000000000^6363 ≤ 41821557209783^6363*2000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034226623 2000000000 41821557209783 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2285304959/10000000000 : ℝ)^8411 ≤ (7105316840307/50000000000000 : ℝ)^6363 := by
    have hnat : (2285304959 : ℕ)^8411*50000000000000^6363 ≤ 7105316840307^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2285304959 10000000000 7105316840307 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4296533/8000000 : ℝ), (1034226623/2000000000 : ℝ), (-2285304959/10000000000 : ℝ)] ![(21983904549539/50000000000000 : ℝ), (41821557209783/100000000000000 : ℝ), (7105316840307/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4296533/8000000 : ℝ)|^8411 ≤ (21983904549539/50000000000000 : ℝ)^6363
        have hw : |(4296533/8000000 : ℝ)|=(4296533/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1034226623/2000000000 : ℝ)|^8411 ≤ (41821557209783/100000000000000 : ℝ)^6363
        have hw : |(1034226623/2000000000 : ℝ)|=(1034226623/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2285304959/10000000000 : ℝ)|^8411 ≤ (7105316840307/50000000000000 : ℝ)^6363
        have hw : |(-2285304959/10000000000 : ℝ)|=(2285304959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s2_3 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4344903051/10000000000 : ℝ)*x 0 + (4028105039/10000000000 : ℝ)*x 1 + (9371901/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4344903051/10000000000 : ℝ)^8411 ≤ (33224625013089/100000000000000 : ℝ)^6363 := by
    have hnat : (4344903051 : ℕ)^8411*100000000000000^6363 ≤ 33224625013089^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4344903051 10000000000 33224625013089 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4028105039/10000000000 : ℝ)^8411 ≤ (3006064030833/10000000000000 : ℝ)^6363 := by
    have hnat : (4028105039 : ℕ)^8411*10000000000000^6363 ≤ 3006064030833^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4028105039 10000000000 3006064030833 10000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9371901/20000000 : ℝ)^8411 ≤ (9178683665053/25000000000000 : ℝ)^6363 := by
    have hnat : (9371901 : ℕ)^8411*25000000000000^6363 ≤ 9178683665053^6363*20000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9371901 20000000 9178683665053 25000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4344903051/10000000000 : ℝ), (4028105039/10000000000 : ℝ), (9371901/20000000 : ℝ)] ![(33224625013089/100000000000000 : ℝ), (3006064030833/10000000000000 : ℝ), (9178683665053/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4344903051/10000000000 : ℝ)|^8411 ≤ (33224625013089/100000000000000 : ℝ)^6363
        have hw : |(4344903051/10000000000 : ℝ)|=(4344903051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4028105039/10000000000 : ℝ)|^8411 ≤ (3006064030833/10000000000000 : ℝ)^6363
        have hw : |(4028105039/10000000000 : ℝ)|=(4028105039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9371901/20000000 : ℝ)|^8411 ≤ (9178683665053/25000000000000 : ℝ)^6363
        have hw : |(9371901/20000000 : ℝ)|=(9371901/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s2_4 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-105824201/500000000 : ℝ)*x 0 + (20208057/39062500 : ℝ)*x 1 + (5494782291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105824201/500000000 : ℝ)^8411 ≤ (3209940139211/25000000000000 : ℝ)^6363 := by
    have hnat : (105824201 : ℕ)^8411*25000000000000^6363 ≤ 3209940139211^6363*500000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105824201 500000000 3209940139211 25000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20208057/39062500 : ℝ)^8411 ≤ (5230540500769/12500000000000 : ℝ)^6363 := by
    have hnat : (20208057 : ℕ)^8411*12500000000000^6363 ≤ 5230540500769^6363*39062500^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20208057 39062500 5230540500769 12500000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5494782291/10000000000 : ℝ)^8411 ≤ (5664489428231/12500000000000 : ℝ)^6363 := by
    have hnat : (5494782291 : ℕ)^8411*12500000000000^6363 ≤ 5664489428231^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5494782291 10000000000 5664489428231 12500000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-105824201/500000000 : ℝ), (20208057/39062500 : ℝ), (5494782291/10000000000 : ℝ)] ![(3209940139211/25000000000000 : ℝ), (5230540500769/12500000000000 : ℝ), (5664489428231/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-105824201/500000000 : ℝ)|^8411 ≤ (3209940139211/25000000000000 : ℝ)^6363
        have hw : |(-105824201/500000000 : ℝ)|=(105824201/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(20208057/39062500 : ℝ)|^8411 ≤ (5230540500769/12500000000000 : ℝ)^6363
        have hw : |(20208057/39062500 : ℝ)|=(20208057/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5494782291/10000000000 : ℝ)|^8411 ≤ (5664489428231/12500000000000 : ℝ)^6363
        have hw : |(5494782291/10000000000 : ℝ)|=(5494782291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s2_5 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (52875913/100000000 : ℝ)*x 0 + (-98082771/500000000 : ℝ)*x 1 + (1373695581/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52875913/100000000 : ℝ)^8411 ≤ (10767762289011/25000000000000 : ℝ)^6363 := by
    have hnat : (52875913 : ℕ)^8411*25000000000000^6363 ≤ 10767762289011^6363*100000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52875913 100000000 10767762289011 25000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (98082771/500000000 : ℝ)^8411 ≤ (362907344789/3125000000000 : ℝ)^6363 := by
    have hnat : (98082771 : ℕ)^8411*3125000000000^6363 ≤ 362907344789^6363*500000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98082771 500000000 362907344789 3125000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1373695581/2500000000 : ℝ)^8411 ≤ (22657957892799/50000000000000 : ℝ)^6363 := by
    have hnat : (1373695581 : ℕ)^8411*50000000000000^6363 ≤ 22657957892799^6363*2500000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1373695581 2500000000 22657957892799 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(52875913/100000000 : ℝ), (-98082771/500000000 : ℝ), (1373695581/2500000000 : ℝ)] ![(10767762289011/25000000000000 : ℝ), (362907344789/3125000000000 : ℝ), (22657957892799/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(52875913/100000000 : ℝ)|^8411 ≤ (10767762289011/25000000000000 : ℝ)^6363
        have hw : |(52875913/100000000 : ℝ)|=(52875913/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-98082771/500000000 : ℝ)|^8411 ≤ (362907344789/3125000000000 : ℝ)^6363
        have hw : |(-98082771/500000000 : ℝ)|=(98082771/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1373695581/2500000000 : ℝ)|^8411 ≤ (22657957892799/50000000000000 : ℝ)^6363
        have hw : |(1373695581/2500000000 : ℝ)|=(1373695581/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s2_6 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2643795741/5000000000 : ℝ)*x 0 + (5494782367/10000000000 : ℝ)*x 1 + (-1961655111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643795741/5000000000 : ℝ)^8411 ≤ (21535525557861/50000000000000 : ℝ)^6363 := by
    have hnat : (2643795741 : ℕ)^8411*50000000000000^6363 ≤ 21535525557861^6363*5000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643795741 5000000000 21535525557861 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5494782367/10000000000 : ℝ)^8411 ≤ (22657958127181/50000000000000 : ℝ)^6363 := by
    have hnat : (5494782367 : ℕ)^8411*50000000000000^6363 ≤ 22657958127181^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5494782367 10000000000 22657958127181 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1961655111/10000000000 : ℝ)^8411 ≤ (11613032615187/100000000000000 : ℝ)^6363 := by
    have hnat : (1961655111 : ℕ)^8411*100000000000000^6363 ≤ 11613032615187^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1961655111 10000000000 11613032615187 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643795741/5000000000 : ℝ), (5494782367/10000000000 : ℝ), (-1961655111/10000000000 : ℝ)] ![(21535525557861/50000000000000 : ℝ), (22657958127181/50000000000000 : ℝ), (11613032615187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643795741/5000000000 : ℝ)|^8411 ≤ (21535525557861/50000000000000 : ℝ)^6363
        have hw : |(2643795741/5000000000 : ℝ)|=(2643795741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5494782367/10000000000 : ℝ)|^8411 ≤ (22657958127181/50000000000000 : ℝ)^6363
        have hw : |(5494782367/10000000000 : ℝ)|=(5494782367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1961655111/10000000000 : ℝ)|^8411 ≤ (11613032615187/100000000000000 : ℝ)^6363
        have hw : |(-1961655111/10000000000 : ℝ)|=(1961655111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s2_7 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (54313391/125000000 : ℝ)*x 0 + (468165061/1000000000 : ℝ)*x 1 + (4032445667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (54313391/125000000 : ℝ)^8411 ≤ (33226325484273/100000000000000 : ℝ)^6363 := by
    have hnat : (54313391 : ℕ)^8411*100000000000000^6363 ≤ 33226325484273^6363*125000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54313391 125000000 33226325484273 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (468165061/1000000000 : ℝ)^8411 ≤ (36670207848259/100000000000000 : ℝ)^6363 := by
    have hnat : (468165061 : ℕ)^8411*100000000000000^6363 ≤ 36670207848259^6363*1000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      468165061 1000000000 36670207848259 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4032445667/10000000000 : ℝ)^8411 ≤ (30103466652843/100000000000000 : ℝ)^6363 := by
    have hnat : (4032445667 : ℕ)^8411*100000000000000^6363 ≤ 30103466652843^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4032445667 10000000000 30103466652843 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(54313391/125000000 : ℝ), (468165061/1000000000 : ℝ), (4032445667/10000000000 : ℝ)] ![(33226325484273/100000000000000 : ℝ), (36670207848259/100000000000000 : ℝ), (30103466652843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(54313391/125000000 : ℝ)|^8411 ≤ (33226325484273/100000000000000 : ℝ)^6363
        have hw : |(54313391/125000000 : ℝ)|=(54313391/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(468165061/1000000000 : ℝ)|^8411 ≤ (36670207848259/100000000000000 : ℝ)^6363
        have hw : |(468165061/1000000000 : ℝ)|=(468165061/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4032445667/10000000000 : ℝ)|^8411 ≤ (30103466652843/100000000000000 : ℝ)^6363
        have hw : |(4032445667/10000000000 : ℝ)|=(4032445667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1218_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150958703/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20101/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (379/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (47/500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16287/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20101/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (379/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20101/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (379/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20101/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (379/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20101/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (379/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20101/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (379/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20101/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (379/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (379/6250 : ℝ) ^ (4205/1024 : ℝ) ≤ (501692024139657/50000000000000000000 : ℝ) := by
    have hpowers : (379/6250 : ℝ)^4205 ≤ (501692024139657/50000000000000000000 : ℝ)^1024 := by
      have hnat : (379 : ℕ)^4205*50000000000000000000^1024 ≤ 501692024139657^1024*6250^4205 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        379 6250 501692024139657 50000000000000000000 4205 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (379/6250 : ℝ)) (X := (501692024139657/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (20101/100000 : ℝ) ^ (4205/1024 : ℝ) ≤ (137626302047571347/100000000000000000000 : ℝ) := by
    have hpowers : (20101/100000 : ℝ)^4205 ≤ (137626302047571347/100000000000000000000 : ℝ)^1024 := by
      have hnat : (20101 : ℕ)^4205*100000000000000000000^1024 ≤ 137626302047571347^1024*100000^4205 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20101 100000 137626302047571347 100000000000000000000 4205 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20101/100000 : ℝ)) (X := (137626302047571347/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000501692024139657/25000000000000000000 : ℝ) ≤ (10000048868369401/10000000000000000 : ℝ) ^ (4205/1024 : ℝ) := by
    have hpowers : (25000501692024139657/25000000000000000000 : ℝ)^1024 ≤ (10000048868369401/10000000000000000 : ℝ)^4205 := by
      have hnat : (25000501692024139657 : ℕ)^1024*10000000000000000^4205 ≤ 10000048868369401^4205*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000501692024139657 25000000000000000000 10000048868369401 10000000000000000 1024 4205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000048868369401/10000000000000000 : ℝ)) (X := (25000501692024139657/25000000000000000000 : ℝ)) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100138629686095850661/100000000000000000000 : ℝ) ≤ (625210883506869/625000000000000 : ℝ) ^ (4205/1024 : ℝ) := by
    have hpowers : (100138629686095850661/100000000000000000000 : ℝ)^1024 ≤ (625210883506869/625000000000000 : ℝ)^4205 := by
      have hnat : (100138629686095850661 : ℕ)^1024*625000000000000^4205 ≤ 625210883506869^4205*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100138629686095850661 100000000000000000000 625210883506869 625000000000000 1024 4205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625210883506869/625000000000000 : ℝ)) (X := (100138629686095850661/100000000000000000000 : ℝ)) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50137626302047571347/50000000000000000000 : ℝ) ≤ (10006699403850407/10000000000000000 : ℝ) ^ (4205/1024 : ℝ) := by
    have hpowers : (50137626302047571347/50000000000000000000 : ℝ)^1024 ≤ (10006699403850407/10000000000000000 : ℝ)^4205 := by
      have hnat : (50137626302047571347 : ℕ)^1024*10000000000000000^4205 ≤ 10006699403850407^4205*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50137626302047571347 50000000000000000000 10006699403850407 10000000000000000 1024 4205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006699403850407/10000000000000000 : ℝ)) (X := (50137626302047571347/50000000000000000000 : ℝ)) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(501692024139657/50000000000000000000 : ℝ) ≤ ((140330357118144461453/140370000000000000000 : ℝ)+2*(3325267740503/1403700000000000 : ℝ)*(379/6250 : ℝ))^(4205/1024 : ℝ) := by
    rw [show (140330357118144461453/140370000000000000000 : ℝ)+2*(3325267740503/1403700000000000 : ℝ)*(379/6250 : ℝ)=(10000048868369401/10000000000000000 : ℝ) by norm_num, show 1+2*(501692024139657/50000000000000000000 : ℝ)=(25000501692024139657/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(137626302047571347/100000000000000000000 : ℝ)+(501692024139657/50000000000000000000 : ℝ) ≤ ((140330357118144461453/140370000000000000000 : ℝ)+(3325267740503/1403700000000000 : ℝ)*((20101/100000 : ℝ)+(379/6250 : ℝ)))^(4205/1024 : ℝ) := by
    rw [show (140330357118144461453/140370000000000000000 : ℝ)+(3325267740503/1403700000000000 : ℝ)*((20101/100000 : ℝ)+(379/6250 : ℝ))=(625210883506869/625000000000000 : ℝ) by norm_num, show 1+(137626302047571347/100000000000000000000 : ℝ)+(501692024139657/50000000000000000000 : ℝ)=(100138629686095850661/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(137626302047571347/100000000000000000000 : ℝ) ≤ ((140330357118144461453/140370000000000000000 : ℝ)+2*(3325267740503/1403700000000000 : ℝ)*(20101/100000 : ℝ))^(4205/1024 : ℝ) := by
    rw [show (140330357118144461453/140370000000000000000 : ℝ)+2*(3325267740503/1403700000000000 : ℝ)*(20101/100000 : ℝ)=(10006699403850407/10000000000000000 : ℝ) by norm_num, show 1+2*(137626302047571347/100000000000000000000 : ℝ)=(50137626302047571347/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (140330357118144461453/140370000000000000000 : ℝ)*(X 1 0+X 2 0)+(3325267740503/1403700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4205/1024 : ℝ)) (lo := (379/6250 : ℝ)) (hi := (20101/100000 : ℝ)) (c := (140330357118144461453/140370000000000000000 : ℝ)) (alpha := (3325267740503/1403700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (140330357118144461453/140370000000000000000 : ℝ)*(X 0 1+X 2 1)+(3325267740503/1403700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4205/1024 : ℝ)) (lo := (379/6250 : ℝ)) (hi := (20101/100000 : ℝ)) (c := (140330357118144461453/140370000000000000000 : ℝ)) (alpha := (3325267740503/1403700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (140330357118144461453/140370000000000000000 : ℝ)*(X 0 2+X 1 2)+(3325267740503/1403700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4205/1024 : ℝ)) (lo := (379/6250 : ℝ)) (hi := (20101/100000 : ℝ)) (c := (140330357118144461453/140370000000000000000 : ℝ)) (alpha := (3325267740503/1403700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-33068757/156250000 : ℝ)*X 0 0+(1374233037/2500000000 : ℝ)*X 0 1+(2585566503/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5370666449/10000000000 : ℝ)*X 1 0+(-1142652463/5000000000 : ℝ)*X 1 1+(5171132939/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((4296533/8000000 : ℝ)*X 2 0+(1034226623/2000000000 : ℝ)*X 2 1+(-2285304959/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4344903051/10000000000 : ℝ)*X 0 0+(4028105039/10000000000 : ℝ)*X 0 1+(9371901/20000000 : ℝ)*X 0 2+(4344903051/10000000000 : ℝ)*X 1 0+(4028105039/10000000000 : ℝ)*X 1 1+(9371901/20000000 : ℝ)*X 1 2+(4344903051/10000000000 : ℝ)*X 2 0+(4028105039/10000000000 : ℝ)*X 2 1+(9371901/20000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-105824201/500000000 : ℝ)*X 0 0+(20208057/39062500 : ℝ)*X 0 1+(5494782291/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((52875913/100000000 : ℝ)*X 1 0+(-98082771/500000000 : ℝ)*X 1 1+(1373695581/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2643795741/5000000000 : ℝ)*X 2 0+(5494782367/10000000000 : ℝ)*X 2 1+(-1961655111/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((54313391/125000000 : ℝ)*X 0 0+(468165061/1000000000 : ℝ)*X 0 1+(4032445667/10000000000 : ℝ)*X 0 2+(54313391/125000000 : ℝ)*X 1 0+(468165061/1000000000 : ℝ)*X 1 1+(4032445667/10000000000 : ℝ)*X 1 2+(54313391/125000000 : ℝ)*X 2 0+(468165061/1000000000 : ℝ)*X 2 1+(4032445667/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6177759312411250851664709239/584875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (270033489/12500000000000 : ℝ)*(base19) + (1899035849/100000000000000 : ℝ)*(base23) + (39608789/50000000000000 : ℝ)*(lower2) + (327789973/100000000000000 : ℝ)*(upper3) + (156137601/100000000000000 : ℝ)*(upper5) + (573694897445321/25000000000000 : ℝ)*(major0) + (573694897445321/25000000000000 : ℝ)*(major1) + (573694897445321/25000000000000 : ℝ)*(major2) + (1534700017203171/50000000000000 : ℝ)*(sp0) + (191838708882251/6250000000000 : ℝ)*(sp1) + (3069419603348079/100000000000000 : ℝ)*(sp2) + (760062366826703/50000000000000 : ℝ)*(sp3) + (4293595517/20000000000000 : ℝ)*(sp4) + (6295720459/50000000000000 : ℝ)*(sp7) + (380034331273581/25000000000000 : ℝ)*(f.failure) + (383677687797991/12500000000000 : ℝ)*(f.sum) + (181261836531349/35092500000000000000000000000 : ℝ)*base66 + (29506128546981488587/3509250000000000000000000000000000 : ℝ)*base68 + (903006790279238587/3509250000000000000000000000000000 : ℝ)*base70 + (36586981532646488587/3509250000000000000000000000000000 : ℝ)*base72 + (67647557571889/35092500000000000000000000000 : ℝ)*base74 + (7648416032346488587/3509250000000000000000000000000000 : ℝ)*base76 + (19359675214381988587/3509250000000000000000000000000000 : ℝ)*base78 + (37853417110109738587/3509250000000000000000000000000000 : ℝ)*base80 + (123497786410027/70185000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (25925443/2500000000000000000000 : ℝ)*base89 + (25925443/2500000000000000000000 : ℝ)*base91 + (25925443/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8973279593359831497410160519/1169750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (379921893/20000000000000 : ℝ)*(base19) + (2125309981/100000000000000 : ℝ)*(base23) + (10424201/50000000000000 : ℝ)*(upper2) + (31121779/12500000000000 : ℝ)*(upper3) + (154942391/100000000000000 : ℝ)*(upper5) + (1162643724029759/50000000000000 : ℝ)*(major0) + (1162643724029759/50000000000000 : ℝ)*(major1) + (1162643724029759/50000000000000 : ℝ)*(major2) + (3813416387/20000000000000 : ℝ)*(sp1) + (6027304337/25000000000000 : ℝ)*(sp2) + (1555113954297313/50000000000000 : ℝ)*(sp4) + (124408277676129/4000000000000 : ℝ)*(sp5) + (97193802314603/3125000000000 : ℝ)*(sp6) + (770173365910383/50000000000000 : ℝ)*(sp7) + (770173365910383/50000000000000 : ℝ)*(f.failure) + (1555113954297313/50000000000000 : ℝ)*(f.sum) + (113346795562477/35092500000000000000000000000 : ℝ)*base65 + (17092180270616079827/7018500000000000000000000000000000 : ℝ)*base67 + (63122372180750079827/7018500000000000000000000000000000 : ℝ)*base69 + (44355936956670579827/7018500000000000000000000000000000 : ℝ)*base71 + (8431703114201/17546250000000000000000000000 : ℝ)*base73 + (114382803189318579827/7018500000000000000000000000000000 : ℝ)*base75 + (94523919785066079827/7018500000000000000000000000000000 : ℝ)*base77 + (85667009616506079827/7018500000000000000000000000000000 : ℝ)*base79 + (9993031886441/17546250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (68086751/5000000000000000000000 : ℝ)*base90 + (68086751/5000000000000000000000 : ℝ)*base92 + (68086751/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1218_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150958703/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20101/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (379/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (47/500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16287/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1218_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1218_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150958703/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (47/500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16287/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1218_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1218_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1218_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150958703/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (47/500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16287/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1218_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
