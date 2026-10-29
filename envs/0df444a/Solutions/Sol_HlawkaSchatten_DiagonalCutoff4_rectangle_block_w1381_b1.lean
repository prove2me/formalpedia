-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1381_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:23:29.95063+00:00
-- url     : https://prove2.me/submissions/185f7085-657f-4007-8d49-e6d9bb15572d

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
theorem support_rectangle_w1381_s3_0 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2009350427/10000000000 : ℝ)*x 0 + (2711222947/5000000000 : ℝ)*x 1 + (5234899799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2009350427/10000000000 : ℝ)^4341 ≤ (1224334612179/10000000000000 : ℝ)^3317 := by
    have hnat : (2009350427 : ℕ)^4341*10000000000000^3317 ≤ 1224334612179^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2009350427 10000000000 1224334612179 10000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2711222947/5000000000 : ℝ)^4341 ≤ (44888792204199/100000000000000 : ℝ)^3317 := by
    have hnat : (2711222947 : ℕ)^4341*100000000000000^3317 ≤ 44888792204199^3317*5000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711222947 5000000000 44888792204199 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5234899799/10000000000 : ℝ)^4341 ≤ (42867861652633/100000000000000 : ℝ)^3317 := by
    have hnat : (5234899799 : ℕ)^4341*100000000000000^3317 ≤ 42867861652633^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234899799 10000000000 42867861652633 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2009350427/10000000000 : ℝ), (2711222947/5000000000 : ℝ), (5234899799/10000000000 : ℝ)] ![(1224334612179/10000000000000 : ℝ), (44888792204199/100000000000000 : ℝ), (42867861652633/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2009350427/10000000000 : ℝ)|^4341 ≤ (1224334612179/10000000000000 : ℝ)^3317
        have hw : |(-2009350427/10000000000 : ℝ)|=(2009350427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2711222947/5000000000 : ℝ)|^4341 ≤ (44888792204199/100000000000000 : ℝ)^3317
        have hw : |(2711222947/5000000000 : ℝ)|=(2711222947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5234899799/10000000000 : ℝ)|^4341 ≤ (42867861652633/100000000000000 : ℝ)^3317
        have hw : |(5234899799/10000000000 : ℝ)|=(5234899799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s3_1 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351304283/10000000000 : ℝ)*x 0 + (-2105111403/10000000000 : ℝ)*x 1 + (654362503/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351304283/10000000000 : ℝ)^4341 ≤ (22059806415829/50000000000000 : ℝ)^3317 := by
    have hnat : (5351304283 : ℕ)^4341*50000000000000^3317 ≤ 22059806415829^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351304283 10000000000 22059806415829 50000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2105111403/10000000000 : ℝ)^4341 ≤ (325313077121/2500000000000 : ℝ)^3317 := by
    have hnat : (2105111403 : ℕ)^4341*2500000000000^3317 ≤ 325313077121^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105111403 10000000000 325313077121 2500000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (654362503/1250000000 : ℝ)^4341 ≤ (5358483007991/12500000000000 : ℝ)^3317 := by
    have hnat : (654362503 : ℕ)^4341*12500000000000^3317 ≤ 5358483007991^3317*1250000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654362503 1250000000 5358483007991 12500000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351304283/10000000000 : ℝ), (-2105111403/10000000000 : ℝ), (654362503/1250000000 : ℝ)] ![(22059806415829/50000000000000 : ℝ), (325313077121/2500000000000 : ℝ), (5358483007991/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351304283/10000000000 : ℝ)|^4341 ≤ (22059806415829/50000000000000 : ℝ)^3317
        have hw : |(5351304283/10000000000 : ℝ)|=(5351304283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2105111403/10000000000 : ℝ)|^4341 ≤ (325313077121/2500000000000 : ℝ)^3317
        have hw : |(-2105111403/10000000000 : ℝ)|=(2105111403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(654362503/1250000000 : ℝ)|^4341 ≤ (5358483007991/12500000000000 : ℝ)^3317
        have hw : |(654362503/1250000000 : ℝ)|=(654362503/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s3_2 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070260851/2000000000 : ℝ)*x 0 + (5234900119/10000000000 : ℝ)*x 1 + (-526277829/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070260851/2000000000 : ℝ)^4341 ≤ (44119612529541/100000000000000 : ℝ)^3317 := by
    have hnat : (1070260851 : ℕ)^4341*100000000000000^3317 ≤ 44119612529541^3317*2000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070260851 2000000000 44119612529541 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5234900119/10000000000 : ℝ)^4341 ≤ (4286786508203/10000000000000 : ℝ)^3317 := by
    have hnat : (5234900119 : ℕ)^4341*10000000000000^3317 ≤ 4286786508203^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234900119 10000000000 4286786508203 10000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526277829/2500000000 : ℝ)^4341 ≤ (13012522381039/100000000000000 : ℝ)^3317 := by
    have hnat : (526277829 : ℕ)^4341*100000000000000^3317 ≤ 13012522381039^3317*2500000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526277829 2500000000 13012522381039 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070260851/2000000000 : ℝ), (5234900119/10000000000 : ℝ), (-526277829/2500000000 : ℝ)] ![(44119612529541/100000000000000 : ℝ), (4286786508203/10000000000000 : ℝ), (13012522381039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070260851/2000000000 : ℝ)|^4341 ≤ (44119612529541/100000000000000 : ℝ)^3317
        have hw : |(1070260851/2000000000 : ℝ)|=(1070260851/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5234900119/10000000000 : ℝ)|^4341 ≤ (4286786508203/10000000000000 : ℝ)^3317
        have hw : |(5234900119/10000000000 : ℝ)|=(5234900119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-526277829/2500000000 : ℝ)|^4341 ≤ (13012522381039/100000000000000 : ℝ)^3317
        have hw : |(-526277829/2500000000 : ℝ)|=(526277829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s3_3 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4315672759/10000000000 : ℝ)*x 0 + (824119627/2000000000 : ℝ)*x 1 + (4519197381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4315672759/10000000000 : ℝ)^4341 ≤ (33295331883953/100000000000000 : ℝ)^3317 := by
    have hnat : (4315672759 : ℕ)^4341*100000000000000^3317 ≤ 33295331883953^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4315672759 10000000000 33295331883953 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (824119627/2000000000 : ℝ)^4341 ≤ (15669805712011/50000000000000 : ℝ)^3317 := by
    have hnat : (824119627 : ℕ)^4341*50000000000000^3317 ≤ 15669805712011^3317*2000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      824119627 2000000000 15669805712011 50000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4519197381/10000000000 : ℝ)^4341 ≤ (35365056676487/100000000000000 : ℝ)^3317 := by
    have hnat : (4519197381 : ℕ)^4341*100000000000000^3317 ≤ 35365056676487^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4519197381 10000000000 35365056676487 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4315672759/10000000000 : ℝ), (824119627/2000000000 : ℝ), (4519197381/10000000000 : ℝ)] ![(33295331883953/100000000000000 : ℝ), (15669805712011/50000000000000 : ℝ), (35365056676487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4315672759/10000000000 : ℝ)|^4341 ≤ (33295331883953/100000000000000 : ℝ)^3317
        have hw : |(4315672759/10000000000 : ℝ)|=(4315672759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(824119627/2000000000 : ℝ)|^4341 ≤ (15669805712011/50000000000000 : ℝ)^3317
        have hw : |(824119627/2000000000 : ℝ)|=(824119627/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4519197381/10000000000 : ℝ)|^4341 ≤ (35365056676487/100000000000000 : ℝ)^3317
        have hw : |(4519197381/10000000000 : ℝ)|=(4519197381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s3_4 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-200936789/1000000000 : ℝ)*x 0 + (1308916273/2500000000 : ℝ)*x 1 + (1084335197/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (200936789/1000000000 : ℝ)^4341 ≤ (2448697075191/20000000000000 : ℝ)^3317 := by
    have hnat : (200936789 : ℕ)^4341*20000000000000^3317 ≤ 2448697075191^3317*1000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200936789 1000000000 2448697075191 20000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1308916273/2500000000 : ℝ)^4341 ≤ (21438031689747/50000000000000 : ℝ)^3317 := by
    have hnat : (1308916273 : ℕ)^4341*50000000000000^3317 ≤ 21438031689747^3317*2500000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1308916273 2500000000 21438031689747 50000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1084335197/2000000000 : ℝ)^4341 ≤ (22440225613969/50000000000000 : ℝ)^3317 := by
    have hnat : (1084335197 : ℕ)^4341*50000000000000^3317 ≤ 22440225613969^3317*2000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084335197 2000000000 22440225613969 50000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-200936789/1000000000 : ℝ), (1308916273/2500000000 : ℝ), (1084335197/2000000000 : ℝ)] ![(2448697075191/20000000000000 : ℝ), (21438031689747/50000000000000 : ℝ), (22440225613969/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-200936789/1000000000 : ℝ)|^4341 ≤ (2448697075191/20000000000000 : ℝ)^3317
        have hw : |(-200936789/1000000000 : ℝ)|=(200936789/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1308916273/2500000000 : ℝ)|^4341 ≤ (21438031689747/50000000000000 : ℝ)^3317
        have hw : |(1308916273/2500000000 : ℝ)|=(1308916273/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1084335197/2000000000 : ℝ)|^4341 ≤ (22440225613969/50000000000000 : ℝ)^3317
        have hw : |(1084335197/2000000000 : ℝ)|=(1084335197/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s3_5 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (132569669/250000000 : ℝ)*x 0 + (-959167717/5000000000 : ℝ)*x 1 + (5421675957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132569669/250000000 : ℝ)^4341 ≤ (8719369808537/20000000000000 : ℝ)^3317 := by
    have hnat : (132569669 : ℕ)^4341*20000000000000^3317 ≤ 8719369808537^3317*250000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132569669 250000000 8719369808537 20000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (959167717/5000000000 : ℝ)^4341 ≤ (2880675005641/25000000000000 : ℝ)^3317 := by
    have hnat : (959167717 : ℕ)^4341*25000000000000^3317 ≤ 2880675005641^3317*5000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      959167717 5000000000 2880675005641 25000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5421675957/10000000000 : ℝ)^4341 ≤ (224402254623/500000000000 : ℝ)^3317 := by
    have hnat : (5421675957 : ℕ)^4341*500000000000^3317 ≤ 224402254623^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421675957 10000000000 224402254623 500000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132569669/250000000 : ℝ), (-959167717/5000000000 : ℝ), (5421675957/10000000000 : ℝ)] ![(8719369808537/20000000000000 : ℝ), (2880675005641/25000000000000 : ℝ), (224402254623/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132569669/250000000 : ℝ)|^4341 ≤ (8719369808537/20000000000000 : ℝ)^3317
        have hw : |(132569669/250000000 : ℝ)|=(132569669/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-959167717/5000000000 : ℝ)|^4341 ≤ (2880675005641/25000000000000 : ℝ)^3317
        have hw : |(-959167717/5000000000 : ℝ)|=(959167717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5421675957/10000000000 : ℝ)|^4341 ≤ (224402254623/500000000000 : ℝ)^3317
        have hw : |(5421675957/10000000000 : ℝ)|=(5421675957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s3_6 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2651393459/5000000000 : ℝ)*x 0 + (338854739/625000000 : ℝ)*x 1 + (-1918335401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651393459/5000000000 : ℝ)^4341 ≤ (21798425371349/50000000000000 : ℝ)^3317 := by
    have hnat : (2651393459 : ℕ)^4341*50000000000000^3317 ≤ 21798425371349^3317*5000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651393459 5000000000 21798425371349 50000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338854739/625000000 : ℝ)^4341 ≤ (44880449483747/100000000000000 : ℝ)^3317 := by
    have hnat : (338854739 : ℕ)^4341*100000000000000^3317 ≤ 44880449483747^3317*625000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338854739 625000000 44880449483747 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1918335401/10000000000 : ℝ)^4341 ≤ (5761349881577/50000000000000 : ℝ)^3317 := by
    have hnat : (1918335401 : ℕ)^4341*50000000000000^3317 ≤ 5761349881577^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1918335401 10000000000 5761349881577 50000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651393459/5000000000 : ℝ), (338854739/625000000 : ℝ), (-1918335401/10000000000 : ℝ)] ![(21798425371349/50000000000000 : ℝ), (44880449483747/100000000000000 : ℝ), (5761349881577/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651393459/5000000000 : ℝ)|^4341 ≤ (21798425371349/50000000000000 : ℝ)^3317
        have hw : |(2651393459/5000000000 : ℝ)|=(2651393459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338854739/625000000 : ℝ)|^4341 ≤ (44880449483747/100000000000000 : ℝ)^3317
        have hw : |(338854739/625000000 : ℝ)|=(338854739/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1918335401/10000000000 : ℝ)|^4341 ≤ (5761349881577/50000000000000 : ℝ)^3317
        have hw : |(-1918335401/10000000000 : ℝ)|=(1918335401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s3_7 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (431570941/1000000000 : ℝ)*x 0 + (4517571531/10000000000 : ℝ)*x 1 + (32977869/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431570941/1000000000 : ℝ)^4341 ≤ (33295701938337/100000000000000 : ℝ)^3317 := by
    have hnat : (431570941 : ℕ)^4341*100000000000000^3317 ≤ 33295701938337^3317*1000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431570941 1000000000 33295701938337 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4517571531/10000000000 : ℝ)^4341 ≤ (8837101674103/25000000000000 : ℝ)^3317 := by
    have hnat : (4517571531 : ℕ)^4341*25000000000000^3317 ≤ 8837101674103^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4517571531 10000000000 8837101674103 25000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32977869/80000000 : ℝ)^4341 ≤ (7838972834979/25000000000000 : ℝ)^3317 := by
    have hnat : (32977869 : ℕ)^4341*25000000000000^3317 ≤ 7838972834979^3317*80000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32977869 80000000 7838972834979 25000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(431570941/1000000000 : ℝ), (4517571531/10000000000 : ℝ), (32977869/80000000 : ℝ)] ![(33295701938337/100000000000000 : ℝ), (8837101674103/25000000000000 : ℝ), (7838972834979/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(431570941/1000000000 : ℝ)|^4341 ≤ (33295701938337/100000000000000 : ℝ)^3317
        have hw : |(431570941/1000000000 : ℝ)|=(431570941/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4517571531/10000000000 : ℝ)|^4341 ≤ (8837101674103/25000000000000 : ℝ)^3317
        have hw : |(4517571531/10000000000 : ℝ)|=(4517571531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(32977869/80000000 : ℝ)|^4341 ≤ (7838972834979/25000000000000 : ℝ)^3317
        have hw : |(32977869/80000000 : ℝ)|=(32977869/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1381_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1220839/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7979/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (631/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (11007/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14977/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7979/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (631/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7979/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (631/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7979/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (631/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7979/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (631/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7979/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (631/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7979/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (631/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (631/6250 : ℝ) ^ (1085/256 : ℝ) ≤ (6015958448507803/100000000000000000000 : ℝ) := by
    have hpowers : (631/6250 : ℝ)^1085 ≤ (6015958448507803/100000000000000000000 : ℝ)^256 := by
      have hnat : (631 : ℕ)^1085*100000000000000000000^256 ≤ 6015958448507803^256*6250^1085 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        631 6250 6015958448507803 100000000000000000000 1085 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (631/6250 : ℝ)) (X := (6015958448507803/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1085 256 (by norm_num) hpowers
    exact h
  have hpowhi : (7979/50000 : ℝ) ^ (1085/256 : ℝ) ≤ (41879217101633903/100000000000000000000 : ℝ) := by
    have hpowers : (7979/50000 : ℝ)^1085 ≤ (41879217101633903/100000000000000000000 : ℝ)^256 := by
      have hnat : (7979 : ℕ)^1085*100000000000000000000^256 ≤ 41879217101633903^256*50000^1085 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7979 50000 41879217101633903 100000000000000000000 1085 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7979/50000 : ℝ)) (X := (41879217101633903/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1085 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006015958448507803/50000000000000000000 : ℝ) ≤ (1250035484206853/1250000000000000 : ℝ) ^ (1085/256 : ℝ) := by
    have hpowers : (50006015958448507803/50000000000000000000 : ℝ)^256 ≤ (1250035484206853/1250000000000000 : ℝ)^1085 := by
      have hnat : (50006015958448507803 : ℕ)^256*1250000000000000^1085 ≤ 1250035484206853^1085*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006015958448507803 50000000000000000000 1250035484206853 1250000000000000 256 1085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250035484206853/1250000000000000 : ℝ)) (X := (50006015958448507803/50000000000000000000 : ℝ)) (by norm_num) 1085 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023947587775070853/50000000000000000000 : ℝ) ≤ (10001129854572591/10000000000000000 : ℝ) ^ (1085/256 : ℝ) := by
    have hpowers : (50023947587775070853/50000000000000000000 : ℝ)^256 ≤ (10001129854572591/10000000000000000 : ℝ)^1085 := by
      have hnat : (50023947587775070853 : ℕ)^256*10000000000000000^1085 ≤ 10001129854572591^1085*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023947587775070853 50000000000000000000 10001129854572591 10000000000000000 256 1085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001129854572591/10000000000000000 : ℝ)) (X := (50023947587775070853/50000000000000000000 : ℝ)) (by norm_num) 1085 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50041879217101633903/50000000000000000000 : ℝ) ≤ (5000987917745179/5000000000000000 : ℝ) ^ (1085/256 : ℝ) := by
    have hpowers : (50041879217101633903/50000000000000000000 : ℝ)^256 ≤ (5000987917745179/5000000000000000 : ℝ)^1085 := by
      have hnat : (50041879217101633903 : ℕ)^256*5000000000000000^1085 ≤ 5000987917745179^1085*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50041879217101633903 50000000000000000000 5000987917745179 5000000000000000 256 1085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000987917745179/5000000000000000 : ℝ)) (X := (50041879217101633903/50000000000000000000 : ℝ)) (by norm_num) 1085 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6015958448507803/100000000000000000000 : ℝ) ≤ ((3662786376292064189/3663750000000000000 : ℝ)+2*(845980917767/586200000000000 : ℝ)*(631/6250 : ℝ))^(1085/256 : ℝ) := by
    rw [show (3662786376292064189/3663750000000000000 : ℝ)+2*(845980917767/586200000000000 : ℝ)*(631/6250 : ℝ)=(1250035484206853/1250000000000000 : ℝ) by norm_num, show 1+2*(6015958448507803/100000000000000000000 : ℝ)=(50006015958448507803/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(41879217101633903/100000000000000000000 : ℝ)+(6015958448507803/100000000000000000000 : ℝ) ≤ ((3662786376292064189/3663750000000000000 : ℝ)+(845980917767/586200000000000 : ℝ)*((7979/50000 : ℝ)+(631/6250 : ℝ)))^(1085/256 : ℝ) := by
    rw [show (3662786376292064189/3663750000000000000 : ℝ)+(845980917767/586200000000000 : ℝ)*((7979/50000 : ℝ)+(631/6250 : ℝ))=(10001129854572591/10000000000000000 : ℝ) by norm_num, show 1+(41879217101633903/100000000000000000000 : ℝ)+(6015958448507803/100000000000000000000 : ℝ)=(50023947587775070853/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(41879217101633903/100000000000000000000 : ℝ) ≤ ((3662786376292064189/3663750000000000000 : ℝ)+2*(845980917767/586200000000000 : ℝ)*(7979/50000 : ℝ))^(1085/256 : ℝ) := by
    rw [show (3662786376292064189/3663750000000000000 : ℝ)+2*(845980917767/586200000000000 : ℝ)*(7979/50000 : ℝ)=(5000987917745179/5000000000000000 : ℝ) by norm_num, show 1+2*(41879217101633903/100000000000000000000 : ℝ)=(50041879217101633903/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3662786376292064189/3663750000000000000 : ℝ)*(X 1 0+X 2 0)+(845980917767/586200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1085/256 : ℝ)) (lo := (631/6250 : ℝ)) (hi := (7979/50000 : ℝ)) (c := (3662786376292064189/3663750000000000000 : ℝ)) (alpha := (845980917767/586200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3662786376292064189/3663750000000000000 : ℝ)*(X 0 1+X 2 1)+(845980917767/586200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1085/256 : ℝ)) (lo := (631/6250 : ℝ)) (hi := (7979/50000 : ℝ)) (c := (3662786376292064189/3663750000000000000 : ℝ)) (alpha := (845980917767/586200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3662786376292064189/3663750000000000000 : ℝ)*(X 0 2+X 1 2)+(845980917767/586200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1085/256 : ℝ)) (lo := (631/6250 : ℝ)) (hi := (7979/50000 : ℝ)) (c := (3662786376292064189/3663750000000000000 : ℝ)) (alpha := (845980917767/586200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2009350427/10000000000 : ℝ)*X 0 0+(2711222947/5000000000 : ℝ)*X 0 1+(5234899799/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351304283/10000000000 : ℝ)*X 1 0+(-2105111403/10000000000 : ℝ)*X 1 1+(654362503/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070260851/2000000000 : ℝ)*X 2 0+(5234900119/10000000000 : ℝ)*X 2 1+(-526277829/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4315672759/10000000000 : ℝ)*X 0 0+(824119627/2000000000 : ℝ)*X 0 1+(4519197381/10000000000 : ℝ)*X 0 2+(4315672759/10000000000 : ℝ)*X 1 0+(824119627/2000000000 : ℝ)*X 1 1+(4519197381/10000000000 : ℝ)*X 1 2+(4315672759/10000000000 : ℝ)*X 2 0+(824119627/2000000000 : ℝ)*X 2 1+(4519197381/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-200936789/1000000000 : ℝ)*X 0 0+(1308916273/2500000000 : ℝ)*X 0 1+(1084335197/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((132569669/250000000 : ℝ)*X 1 0+(-959167717/5000000000 : ℝ)*X 1 1+(5421675957/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2651393459/5000000000 : ℝ)*X 2 0+(338854739/625000000 : ℝ)*X 2 1+(-1918335401/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((431570941/1000000000 : ℝ)*X 0 0+(4517571531/10000000000 : ℝ)*X 0 1+(32977869/80000000 : ℝ)*X 0 2+(431570941/1000000000 : ℝ)*X 1 0+(4517571531/10000000000 : ℝ)*X 1 1+(32977869/80000000 : ℝ)*X 1 2+(431570941/1000000000 : ℝ)*X 2 0+(4517571531/10000000000 : ℝ)*X 2 1+(32977869/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14796275667150607234923/4885000000000000000000000000 : ℝ) := by norm_num
    linear_combination (171283441/50000000000000 : ℝ)*(base19) + (102732507/100000000000000 : ℝ)*(base23) + (22682589/20000000000000 : ℝ)*(lower2) + (72509467/100000000000000 : ℝ)*(upper3) + (346591/6250000000000 : ℝ)*(upper5) + (1960208090749893/50000000000000 : ℝ)*(major0) + (1960208090749893/50000000000000 : ℝ)*(major1) + (1960208090749893/50000000000000 : ℝ)*(major2) + (266601693758929/5000000000000 : ℝ)*(sp0) + (2666022406695523/50000000000000 : ℝ)*(sp1) + (5332045053225421/100000000000000 : ℝ)*(sp2) + (1254392748499681/50000000000000 : ℝ)*(sp3) + (2820194837/25000000000000 : ℝ)*(sp4) + (402269567/25000000000000 : ℝ)*(sp7) + (250878710607763/10000000000000 : ℝ)*(f.failure) + (666505644494741/12500000000000 : ℝ)*(f.sum) + (2178456997353/4885000000000000000000000000 : ℝ)*base66 + (703420776946391491/61062500000000000000000000000000 : ℝ)*base68 + (552416078766141491/61062500000000000000000000000000 : ℝ)*base70 + (59782133407733509/61062500000000000000000000000000 : ℝ)*base71 + (6091285243423/4885000000000000000000000000 : ℝ)*base74 + (85068977470858509/61062500000000000000000000000000 : ℝ)*base75 + (346760776670328991/61062500000000000000000000000000 : ℝ)*base78 + (199641416300421009/61062500000000000000000000000000 : ℝ)*base79 + (5510887382633/4885000000000000000000000000 : ℝ)*base82 + (8093/7812500000000000000 : ℝ)*base90 + (8093/7812500000000000000 : ℝ)*base92 + (8093/7812500000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (694318968756481205331/61062500000000000000000000 : ℝ) := by norm_num
    linear_combination (1996622879/100000000000000 : ℝ)*(base19) + (458299033/20000000000000 : ℝ)*(base23) + (125694031/50000000000000 : ℝ)*(upper3) + (6588993/12500000000000 : ℝ)*(lower4) + (237606331/100000000000000 : ℝ)*(upper5) + (395275572405001/10000000000000 : ℝ)*(major0) + (395275572405001/10000000000000 : ℝ)*(major1) + (395275572405001/10000000000000 : ℝ)*(major2) + (17338360963/50000000000000 : ℝ)*(sp1) + (19266740227/50000000000000 : ℝ)*(sp2) + (5376028959305339/100000000000000 : ℝ)*(sp4) + (2687996142980267/50000000000000 : ℝ)*(sp5) + (134399703358243/2500000000000 : ℝ)*(sp6) + (1264741054886873/50000000000000 : ℝ)*(sp7) + (1264741054886873/50000000000000 : ℝ)*(f.failure) + (5376028959305339/100000000000000 : ℝ)*(f.sum) + (6312876921883/2931000000000000000000000000 : ℝ)*base66 + (221413930584727939/36637500000000000000000000000000 : ℝ)*base67 + (30719550231284561/36637500000000000000000000000000 : ℝ)*base70 + (193864822480177939/36637500000000000000000000000000 : ℝ)*base71 + (1209439896197/586200000000000000000000000 : ℝ)*base74 + (388258440606997061/36637500000000000000000000000000 : ℝ)*base76 + (91917467685277939/36637500000000000000000000000000 : ℝ)*base77 + (127592590575997061/36637500000000000000000000000000 : ℝ)*base80 + (4407108234679/2931000000000000000000000000 : ℝ)*base82 + (9803/39062500000000000000 : ℝ)*base90 + (9803/39062500000000000000 : ℝ)*base92 + (9803/39062500000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1381_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1220839/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7979/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (631/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11007/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14977/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1381_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1381_s4_0 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-502631567/2500000000 : ℝ)*x 0 + (541263603/1000000000 : ℝ)*x 1 + (1048787333/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (502631567/2500000000 : ℝ)^4341 ≤ (6126361697601/50000000000000 : ℝ)^3317 := by
    have hnat : (502631567 : ℕ)^4341*50000000000000^3317 ≤ 6126361697601^3317*2500000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502631567 2500000000 6126361697601 50000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541263603/1000000000 : ℝ)^4341 ≤ (44782542274873/100000000000000 : ℝ)^3317 := by
    have hnat : (541263603 : ℕ)^4341*100000000000000^3317 ≤ 44782542274873^3317*1000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541263603 1000000000 44782542274873 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048787333/2000000000 : ℝ)^4341 ≤ (8592946864319/20000000000000 : ℝ)^3317 := by
    have hnat : (1048787333 : ℕ)^4341*20000000000000^3317 ≤ 8592946864319^3317*2000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048787333 2000000000 8592946864319 20000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-502631567/2500000000 : ℝ), (541263603/1000000000 : ℝ), (1048787333/2000000000 : ℝ)] ![(6126361697601/50000000000000 : ℝ), (44782542274873/100000000000000 : ℝ), (8592946864319/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-502631567/2500000000 : ℝ)|^4341 ≤ (6126361697601/50000000000000 : ℝ)^3317
        have hw : |(-502631567/2500000000 : ℝ)|=(502631567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541263603/1000000000 : ℝ)|^4341 ≤ (44782542274873/100000000000000 : ℝ)^3317
        have hw : |(541263603/1000000000 : ℝ)|=(541263603/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048787333/2000000000 : ℝ)|^4341 ≤ (8592946864319/20000000000000 : ℝ)^3317
        have hw : |(1048787333/2000000000 : ℝ)|=(1048787333/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s4_1 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674394937/5000000000 : ℝ)*x 0 + (-1048242409/5000000000 : ℝ)*x 1 + (2621968331/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674394937/5000000000 : ℝ)^4341 ≤ (44092484644031/100000000000000 : ℝ)^3317 := by
    have hnat : (2674394937 : ℕ)^4341*100000000000000^3317 ≤ 44092484644031^3317*5000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674394937 5000000000 44092484644031 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048242409/5000000000 : ℝ)^4341 ≤ (12942781053343/100000000000000 : ℝ)^3317 := by
    have hnat : (1048242409 : ℕ)^4341*100000000000000^3317 ≤ 12942781053343^3317*5000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048242409 5000000000 12942781053343 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621968331/5000000000 : ℝ)^4341 ≤ (42964734289427/100000000000000 : ℝ)^3317 := by
    have hnat : (2621968331 : ℕ)^4341*100000000000000^3317 ≤ 42964734289427^3317*5000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621968331 5000000000 42964734289427 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674394937/5000000000 : ℝ), (-1048242409/5000000000 : ℝ), (2621968331/5000000000 : ℝ)] ![(44092484644031/100000000000000 : ℝ), (12942781053343/100000000000000 : ℝ), (42964734289427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674394937/5000000000 : ℝ)|^4341 ≤ (44092484644031/100000000000000 : ℝ)^3317
        have hw : |(2674394937/5000000000 : ℝ)|=(2674394937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1048242409/5000000000 : ℝ)|^4341 ≤ (12942781053343/100000000000000 : ℝ)^3317
        have hw : |(-1048242409/5000000000 : ℝ)|=(1048242409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621968331/5000000000 : ℝ)|^4341 ≤ (42964734289427/100000000000000 : ℝ)^3317
        have hw : |(2621968331/5000000000 : ℝ)|=(2621968331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s4_2 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334299367/625000000 : ℝ)*x 0 + (2621968331/5000000000 : ℝ)*x 1 + (-2096484821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334299367/625000000 : ℝ)^4341 ≤ (22046242311227/50000000000000 : ℝ)^3317 := by
    have hnat : (334299367 : ℕ)^4341*50000000000000^3317 ≤ 22046242311227^3317*625000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334299367 625000000 22046242311227 50000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621968331/5000000000 : ℝ)^4341 ≤ (42964734289427/100000000000000 : ℝ)^3317 := by
    have hnat : (2621968331 : ℕ)^4341*100000000000000^3317 ≤ 42964734289427^3317*5000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621968331 5000000000 42964734289427 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2096484821/10000000000 : ℝ)^4341 ≤ (12942781077581/100000000000000 : ℝ)^3317 := by
    have hnat : (2096484821 : ℕ)^4341*100000000000000^3317 ≤ 12942781077581^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096484821 10000000000 12942781077581 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334299367/625000000 : ℝ), (2621968331/5000000000 : ℝ), (-2096484821/10000000000 : ℝ)] ![(22046242311227/50000000000000 : ℝ), (42964734289427/100000000000000 : ℝ), (12942781077581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334299367/625000000 : ℝ)|^4341 ≤ (22046242311227/50000000000000 : ℝ)^3317
        have hw : |(334299367/625000000 : ℝ)|=(334299367/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621968331/5000000000 : ℝ)|^4341 ≤ (42964734289427/100000000000000 : ℝ)^3317
        have hw : |(2621968331/5000000000 : ℝ)|=(2621968331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2096484821/10000000000 : ℝ)|^4341 ≤ (12942781077581/100000000000000 : ℝ)^3317
        have hw : |(-2096484821/10000000000 : ℝ)|=(2096484821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s4_3 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1079097637/2500000000 : ℝ)*x 0 + (828107507/2000000000 : ℝ)*x 1 + (35992659/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079097637/2500000000 : ℝ)^4341 ≤ (33302579365257/100000000000000 : ℝ)^3317 := by
    have hnat : (1079097637 : ℕ)^4341*100000000000000^3317 ≤ 33302579365257^3317*2500000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079097637 2500000000 33302579365257 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (828107507/2000000000 : ℝ)^4341 ≤ (15769113578863/50000000000000 : ℝ)^3317 := by
    have hnat : (828107507 : ℕ)^4341*50000000000000^3317 ≤ 15769113578863^3317*2000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      828107507 2000000000 15769113578863 50000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35992659/80000000 : ℝ)^4341 ≤ (17579596733053/50000000000000 : ℝ)^3317 := by
    have hnat : (35992659 : ℕ)^4341*50000000000000^3317 ≤ 17579596733053^3317*80000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35992659 80000000 17579596733053 50000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079097637/2500000000 : ℝ), (828107507/2000000000 : ℝ), (35992659/80000000 : ℝ)] ![(33302579365257/100000000000000 : ℝ), (15769113578863/50000000000000 : ℝ), (17579596733053/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079097637/2500000000 : ℝ)|^4341 ≤ (33302579365257/100000000000000 : ℝ)^3317
        have hw : |(1079097637/2500000000 : ℝ)|=(1079097637/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(828107507/2000000000 : ℝ)|^4341 ≤ (15769113578863/50000000000000 : ℝ)^3317
        have hw : |(828107507/2000000000 : ℝ)|=(828107507/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(35992659/80000000 : ℝ)|^4341 ≤ (17579596733053/50000000000000 : ℝ)^3317
        have hw : |(35992659/80000000 : ℝ)|=(35992659/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s4_4 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1005269417/5000000000 : ℝ)*x 0 + (5244556267/10000000000 : ℝ)*x 1 + (5412013177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1005269417/5000000000 : ℝ)^4341 ≤ (3063205904393/25000000000000 : ℝ)^3317 := by
    have hnat : (1005269417 : ℕ)^4341*25000000000000^3317 ≤ 3063205904393^3317*5000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005269417 5000000000 3063205904393 25000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244556267/10000000000 : ℝ)^4341 ≤ (83928472989/195312500000 : ℝ)^3317 := by
    have hnat : (5244556267 : ℕ)^4341*195312500000^3317 ≤ 83928472989^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244556267 10000000000 83928472989 195312500000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412013177/10000000000 : ℝ)^4341 ≤ (22387899102347/50000000000000 : ℝ)^3317 := by
    have hnat : (5412013177 : ℕ)^4341*50000000000000^3317 ≤ 22387899102347^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412013177 10000000000 22387899102347 50000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1005269417/5000000000 : ℝ), (5244556267/10000000000 : ℝ), (5412013177/10000000000 : ℝ)] ![(3063205904393/25000000000000 : ℝ), (83928472989/195312500000 : ℝ), (22387899102347/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1005269417/5000000000 : ℝ)|^4341 ≤ (3063205904393/25000000000000 : ℝ)^3317
        have hw : |(-1005269417/5000000000 : ℝ)|=(1005269417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244556267/10000000000 : ℝ)|^4341 ≤ (83928472989/195312500000 : ℝ)^3317
        have hw : |(5244556267/10000000000 : ℝ)|=(5244556267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412013177/10000000000 : ℝ)|^4341 ≤ (22387899102347/50000000000000 : ℝ)^3317
        have hw : |(5412013177/10000000000 : ℝ)|=(5412013177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s4_5 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (530514771/1000000000 : ℝ)*x 0 + (-1928408201/10000000000 : ℝ)*x 1 + (5412013427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530514771/1000000000 : ℝ)^4341 ≤ (43622253614819/100000000000000 : ℝ)^3317 := by
    have hnat : (530514771 : ℕ)^4341*100000000000000^3317 ≤ 43622253614819^3317*1000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530514771 1000000000 43622253614819 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1928408201/10000000000 : ℝ)^4341 ≤ (2900486363511/25000000000000 : ℝ)^3317 := by
    have hnat : (1928408201 : ℕ)^4341*25000000000000^3317 ≤ 2900486363511^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1928408201 10000000000 2900486363511 25000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412013427/10000000000 : ℝ)^4341 ≤ (11193950227893/25000000000000 : ℝ)^3317 := by
    have hnat : (5412013427 : ℕ)^4341*25000000000000^3317 ≤ 11193950227893^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412013427 10000000000 11193950227893 25000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530514771/1000000000 : ℝ), (-1928408201/10000000000 : ℝ), (5412013427/10000000000 : ℝ)] ![(43622253614819/100000000000000 : ℝ), (2900486363511/25000000000000 : ℝ), (11193950227893/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530514771/1000000000 : ℝ)|^4341 ≤ (43622253614819/100000000000000 : ℝ)^3317
        have hw : |(530514771/1000000000 : ℝ)|=(530514771/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1928408201/10000000000 : ℝ)|^4341 ≤ (2900486363511/25000000000000 : ℝ)^3317
        have hw : |(-1928408201/10000000000 : ℝ)|=(1928408201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412013427/10000000000 : ℝ)|^4341 ≤ (11193950227893/25000000000000 : ℝ)^3317
        have hw : |(5412013427/10000000000 : ℝ)|=(5412013427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s4_6 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (530514783/1000000000 : ℝ)*x 0 + (1082402661/2000000000 : ℝ)*x 1 + (-385681641/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530514783/1000000000 : ℝ)^4341 ≤ (8724450981229/20000000000000 : ℝ)^3317 := by
    have hnat : (530514783 : ℕ)^4341*20000000000000^3317 ≤ 8724450981229^3317*1000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530514783 1000000000 8724450981229 20000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082402661/2000000000 : ℝ)^4341 ≤ (5596974948827/12500000000000 : ℝ)^3317 := by
    have hnat : (1082402661 : ℕ)^4341*12500000000000^3317 ≤ 5596974948827^3317*2000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082402661 2000000000 5596974948827 12500000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (385681641/2000000000 : ℝ)^4341 ≤ (11601945485539/100000000000000 : ℝ)^3317 := by
    have hnat : (385681641 : ℕ)^4341*100000000000000^3317 ≤ 11601945485539^3317*2000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      385681641 2000000000 11601945485539 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530514783/1000000000 : ℝ), (1082402661/2000000000 : ℝ), (-385681641/2000000000 : ℝ)] ![(8724450981229/20000000000000 : ℝ), (5596974948827/12500000000000 : ℝ), (11601945485539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530514783/1000000000 : ℝ)|^4341 ≤ (8724450981229/20000000000000 : ℝ)^3317
        have hw : |(530514783/1000000000 : ℝ)|=(530514783/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082402661/2000000000 : ℝ)|^4341 ≤ (5596974948827/12500000000000 : ℝ)^3317
        have hw : |(1082402661/2000000000 : ℝ)|=(1082402661/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-385681641/2000000000 : ℝ)|^4341 ≤ (11601945485539/100000000000000 : ℝ)^3317
        have hw : |(-385681641/2000000000 : ℝ)|=(385681641/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s4_7 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (33722011/78125000 : ℝ)*x 0 + (899553097/2000000000 : ℝ)*x 1 + (414186129/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33722011/78125000 : ℝ)^4341 ≤ (33302850576619/100000000000000 : ℝ)^3317 := by
    have hnat : (33722011 : ℕ)^4341*100000000000000^3317 ≤ 33302850576619^3317*78125000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33722011 78125000 33302850576619 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (899553097/2000000000 : ℝ)^4341 ≤ (35145725898947/100000000000000 : ℝ)^3317 := by
    have hnat : (899553097 : ℕ)^4341*100000000000000^3317 ≤ 35145725898947^3317*2000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899553097 2000000000 35145725898947 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (414186129/1000000000 : ℝ)^4341 ≤ (6310284702049/20000000000000 : ℝ)^3317 := by
    have hnat : (414186129 : ℕ)^4341*20000000000000^3317 ≤ 6310284702049^3317*1000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414186129 1000000000 6310284702049 20000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33722011/78125000 : ℝ), (899553097/2000000000 : ℝ), (414186129/1000000000 : ℝ)] ![(33302850576619/100000000000000 : ℝ), (35145725898947/100000000000000 : ℝ), (6310284702049/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33722011/78125000 : ℝ)|^4341 ≤ (33302850576619/100000000000000 : ℝ)^3317
        have hw : |(33722011/78125000 : ℝ)|=(33722011/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(899553097/2000000000 : ℝ)|^4341 ≤ (35145725898947/100000000000000 : ℝ)^3317
        have hw : |(899553097/2000000000 : ℝ)|=(899553097/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(414186129/1000000000 : ℝ)|^4341 ≤ (6310284702049/20000000000000 : ℝ)^3317
        have hw : |(414186129/1000000000 : ℝ)|=(414186129/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1381_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1220839/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14977/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11007/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11199/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3693/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14977/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11007/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14977/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11007/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14977/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11007/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14977/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11007/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14977/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11007/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14977/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11007/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11007/100000 : ℝ) ^ (1085/256 : ℝ) ≤ (1084510003589009/12500000000000000000 : ℝ) := by
    have hpowers : (11007/100000 : ℝ)^1085 ≤ (1084510003589009/12500000000000000000 : ℝ)^256 := by
      have hnat : (11007 : ℕ)^1085*12500000000000000000^256 ≤ 1084510003589009^256*100000^1085 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11007 100000 1084510003589009 12500000000000000000 1085 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11007/100000 : ℝ)) (X := (1084510003589009/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 1085 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14977/100000 : ℝ) ^ (1085/256 : ℝ) ≤ (32005050506602067/100000000000000000000 : ℝ) := by
    have hpowers : (14977/100000 : ℝ)^1085 ≤ (32005050506602067/100000000000000000000 : ℝ)^256 := by
      have hnat : (14977 : ℕ)^1085*100000000000000000000^256 ≤ 32005050506602067^256*100000^1085 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14977 100000 32005050506602067 100000000000000000000 1085 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14977/100000 : ℝ)) (X := (32005050506602067/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1085 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251084510003589009/6250000000000000000 : ℝ) ≤ (10000409387883337/10000000000000000 : ℝ) ^ (1085/256 : ℝ) := by
    have hpowers : (6251084510003589009/6250000000000000000 : ℝ)^256 ≤ (10000409387883337/10000000000000000 : ℝ)^1085 := by
      have hnat : (6251084510003589009 : ℕ)^256*10000000000000000^1085 ≤ 10000409387883337^1085*6250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251084510003589009 6250000000000000000 10000409387883337 10000000000000000 256 1085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000409387883337/10000000000000000 : ℝ)) (X := (6251084510003589009/6250000000000000000 : ℝ)) (by norm_num) 1085 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100040681130535314139/100000000000000000000 : ℝ) ≤ (10000959700578247/10000000000000000 : ℝ) ^ (1085/256 : ℝ) := by
    have hpowers : (100040681130535314139/100000000000000000000 : ℝ)^256 ≤ (10000959700578247/10000000000000000 : ℝ)^1085 := by
      have hnat : (100040681130535314139 : ℕ)^256*10000000000000000^1085 ≤ 10000959700578247^1085*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100040681130535314139 100000000000000000000 10000959700578247 10000000000000000 256 1085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000959700578247/10000000000000000 : ℝ)) (X := (100040681130535314139/100000000000000000000 : ℝ)) (by norm_num) 1085 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032005050506602067/50000000000000000000 : ℝ) ≤ (10001510013273157/10000000000000000 : ℝ) ^ (1085/256 : ℝ) := by
    have hpowers : (50032005050506602067/50000000000000000000 : ℝ)^256 ≤ (10001510013273157/10000000000000000 : ℝ)^1085 := by
      have hnat : (50032005050506602067 : ℕ)^256*10000000000000000^1085 ≤ 10001510013273157^1085*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032005050506602067 50000000000000000000 10001510013273157 10000000000000000 256 1085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001510013273157/10000000000000000 : ℝ)) (X := (50032005050506602067/50000000000000000000 : ℝ)) (by norm_num) 1085 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1084510003589009/12500000000000000000 : ℝ) ≤ ((793790213724621983/794000000000000000 : ℝ)+2*(55031269491/39700000000000 : ℝ)*(11007/100000 : ℝ))^(1085/256 : ℝ) := by
    rw [show (793790213724621983/794000000000000000 : ℝ)+2*(55031269491/39700000000000 : ℝ)*(11007/100000 : ℝ)=(10000409387883337/10000000000000000 : ℝ) by norm_num, show 1+2*(1084510003589009/12500000000000000000 : ℝ)=(6251084510003589009/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32005050506602067/100000000000000000000 : ℝ)+(1084510003589009/12500000000000000000 : ℝ) ≤ ((793790213724621983/794000000000000000 : ℝ)+(55031269491/39700000000000 : ℝ)*((14977/100000 : ℝ)+(11007/100000 : ℝ)))^(1085/256 : ℝ) := by
    rw [show (793790213724621983/794000000000000000 : ℝ)+(55031269491/39700000000000 : ℝ)*((14977/100000 : ℝ)+(11007/100000 : ℝ))=(10000959700578247/10000000000000000 : ℝ) by norm_num, show 1+(32005050506602067/100000000000000000000 : ℝ)+(1084510003589009/12500000000000000000 : ℝ)=(100040681130535314139/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32005050506602067/100000000000000000000 : ℝ) ≤ ((793790213724621983/794000000000000000 : ℝ)+2*(55031269491/39700000000000 : ℝ)*(14977/100000 : ℝ))^(1085/256 : ℝ) := by
    rw [show (793790213724621983/794000000000000000 : ℝ)+2*(55031269491/39700000000000 : ℝ)*(14977/100000 : ℝ)=(10001510013273157/10000000000000000 : ℝ) by norm_num, show 1+2*(32005050506602067/100000000000000000000 : ℝ)=(50032005050506602067/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (793790213724621983/794000000000000000 : ℝ)*(X 1 0+X 2 0)+(55031269491/39700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1085/256 : ℝ)) (lo := (11007/100000 : ℝ)) (hi := (14977/100000 : ℝ)) (c := (793790213724621983/794000000000000000 : ℝ)) (alpha := (55031269491/39700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (793790213724621983/794000000000000000 : ℝ)*(X 0 1+X 2 1)+(55031269491/39700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1085/256 : ℝ)) (lo := (11007/100000 : ℝ)) (hi := (14977/100000 : ℝ)) (c := (793790213724621983/794000000000000000 : ℝ)) (alpha := (55031269491/39700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (793790213724621983/794000000000000000 : ℝ)*(X 0 2+X 1 2)+(55031269491/39700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1085/256 : ℝ)) (lo := (11007/100000 : ℝ)) (hi := (14977/100000 : ℝ)) (c := (793790213724621983/794000000000000000 : ℝ)) (alpha := (55031269491/39700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-502631567/2500000000 : ℝ)*X 0 0+(541263603/1000000000 : ℝ)*X 0 1+(1048787333/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674394937/5000000000 : ℝ)*X 1 0+(-1048242409/5000000000 : ℝ)*X 1 1+(2621968331/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334299367/625000000 : ℝ)*X 2 0+(2621968331/5000000000 : ℝ)*X 2 1+(-2096484821/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1079097637/2500000000 : ℝ)*X 0 0+(828107507/2000000000 : ℝ)*X 0 1+(35992659/80000000 : ℝ)*X 0 2+(1079097637/2500000000 : ℝ)*X 1 0+(828107507/2000000000 : ℝ)*X 1 1+(35992659/80000000 : ℝ)*X 1 2+(1079097637/2500000000 : ℝ)*X 2 0+(828107507/2000000000 : ℝ)*X 2 1+(35992659/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1005269417/5000000000 : ℝ)*X 0 0+(5244556267/10000000000 : ℝ)*X 0 1+(5412013177/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((530514771/1000000000 : ℝ)*X 1 0+(-1928408201/10000000000 : ℝ)*X 1 1+(5412013427/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((530514783/1000000000 : ℝ)*X 2 0+(1082402661/2000000000 : ℝ)*X 2 1+(-385681641/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((33722011/78125000 : ℝ)*X 0 0+(899553097/2000000000 : ℝ)*X 0 1+(414186129/1000000000 : ℝ)*X 0 2+(33722011/78125000 : ℝ)*X 1 0+(899553097/2000000000 : ℝ)*X 1 1+(414186129/1000000000 : ℝ)*X 1 2+(33722011/78125000 : ℝ)*X 2 0+(899553097/2000000000 : ℝ)*X 2 1+(414186129/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23118340792155844738846401/1985000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1690121/78125000000 : ℝ)*(base19) + (2014898651/100000000000000 : ℝ)*(base23) + (977757/1250000000000 : ℝ)*(lower2) + (293485221/100000000000000 : ℝ)*(upper3) + (181869603/100000000000000 : ℝ)*(upper5) + (217922203458383/5000000000000 : ℝ)*(major0) + (217922203458383/5000000000000 : ℝ)*(major1) + (217922203458383/5000000000000 : ℝ)*(major2) + (1185550069451671/20000000000000 : ℝ)*(sp0) + (5927791833174619/100000000000000 : ℝ)*(sp1) + (46310874856491/781250000000 : ℝ)*(sp2) + (348633926703721/12500000000000 : ℝ)*(sp3) + (8729854229/20000000000000 : ℝ)*(sp4) + (1396247421/6250000000000 : ℝ)*(sp7) + (2789093753588503/100000000000000 : ℝ)*(f.failure) + (11855587993059/200000000000 : ℝ)*(f.sum) + (197400937671/198500000000000000000000000 : ℝ)*base66 + (24193430555356511/3970000000000000000000000000000 : ℝ)*base68 + (44513942946106511/3970000000000000000000000000000 : ℝ)*base70 + (39809433308766511/3970000000000000000000000000000 : ℝ)*base72 + (776095811747/198500000000000000000000000 : ℝ)*base74 + (1733294556966511/3970000000000000000000000000000 : ℝ)*base76 + (1872762205266511/3970000000000000000000000000000 : ℝ)*base78 + (11861828509026511/3970000000000000000000000000000 : ℝ)*base80 + (639803047473/99250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (39017/78125000000000000000 : ℝ)*base89 + (39017/78125000000000000000 : ℝ)*base91 + (39017/78125000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (122212672333472431545403437/9925000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1815105151/100000000000000 : ℝ)*(base19) + (1115465457/50000000000000 : ℝ)*(base23) + (12723087/5000000000000 : ℝ)*(upper3) + (5025719/4000000000000 : ℝ)*(lower4) + (5146511/2000000000000 : ℝ)*(upper5) + (1097678610392971/25000000000000 : ℝ)*(major0) + (1097678610392971/25000000000000 : ℝ)*(major1) + (1097678610392971/25000000000000 : ℝ)*(major2) + (43289634021/100000000000000 : ℝ)*(sp1) + (24314156091/50000000000000 : ℝ)*(sp2) + (5971683979371633/100000000000000 : ℝ)*(sp4) + (2985819437316231/50000000000000 : ℝ)*(sp5) + (5971633120128537/100000000000000 : ℝ)*(sp6) + (702436123329537/25000000000000 : ℝ)*(sp7) + (702436123329537/25000000000000 : ℝ)*(f.failure) + (5971683979371633/100000000000000 : ℝ)*(f.sum) + (2220839516987/992500000000000000000000000 : ℝ)*base65 + (151525286440848507/19850000000000000000000000000000 : ℝ)*base68 + (20644374365348507/19850000000000000000000000000000 : ℝ)*base70 + (141570312285798507/19850000000000000000000000000000 : ℝ)*base72 + (975493909107/248125000000000000000000000 : ℝ)*base74 + (364891751495098507/19850000000000000000000000000000 : ℝ)*base76 + (49481796079798507/19850000000000000000000000000000 : ℝ)*base78 + (376882877512148507/19850000000000000000000000000000 : ℝ)*base80 + (7631909596239/1985000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (27793/19531250000000000000 : ℝ)*base89 + (27793/19531250000000000000 : ℝ)*base91 + (27793/19531250000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1381_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1220839/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14977/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11007/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11199/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3693/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1381_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1381_s5_0 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-402143719/2000000000 : ℝ)*x 0 + (2705487373/5000000000 : ℝ)*x 1 + (5245471059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (402143719/2000000000 : ℝ)^4341 ≤ (12254257354591/100000000000000 : ℝ)^3317 := by
    have hnat : (402143719 : ℕ)^4341*100000000000000^3317 ≤ 12254257354591^3317*2000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402143719 2000000000 12254257354591 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705487373/5000000000 : ℝ)^4341 ≤ (5595569363773/12500000000000 : ℝ)^3317 := by
    have hnat : (2705487373 : ℕ)^4341*12500000000000^3317 ≤ 5595569363773^3317*5000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705487373 5000000000 5595569363773 12500000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245471059/10000000000 : ℝ)^4341 ≤ (42981187716139/100000000000000 : ℝ)^3317 := by
    have hnat : (5245471059 : ℕ)^4341*100000000000000^3317 ≤ 42981187716139^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245471059 10000000000 42981187716139 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-402143719/2000000000 : ℝ), (2705487373/5000000000 : ℝ), (5245471059/10000000000 : ℝ)] ![(12254257354591/100000000000000 : ℝ), (5595569363773/12500000000000 : ℝ), (42981187716139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-402143719/2000000000 : ℝ)|^4341 ≤ (12254257354591/100000000000000 : ℝ)^3317
        have hw : |(-402143719/2000000000 : ℝ)|=(402143719/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705487373/5000000000 : ℝ)|^4341 ≤ (5595569363773/12500000000000 : ℝ)^3317
        have hw : |(2705487373/5000000000 : ℝ)|=(2705487373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245471059/10000000000 : ℝ)|^4341 ≤ (42981187716139/100000000000000 : ℝ)^3317
        have hw : |(5245471059/10000000000 : ℝ)|=(5245471059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s5_1 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337090597/2500000000 : ℝ)*x 0 + (-2095019053/10000000000 : ℝ)*x 1 + (5245471023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337090597/2500000000 : ℝ)^4341 ≤ (44087872850157/100000000000000 : ℝ)^3317 := by
    have hnat : (1337090597 : ℕ)^4341*100000000000000^3317 ≤ 44087872850157^3317*2500000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337090597 2500000000 44087872850157 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2095019053/10000000000 : ℝ)^4341 ≤ (12930939800197/100000000000000 : ℝ)^3317 := by
    have hnat : (2095019053 : ℕ)^4341*100000000000000^3317 ≤ 12930939800197^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095019053 10000000000 12930939800197 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245471023/10000000000 : ℝ)^4341 ≤ (10745296832523/25000000000000 : ℝ)^3317 := by
    have hnat : (5245471023 : ℕ)^4341*25000000000000^3317 ≤ 10745296832523^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245471023 10000000000 10745296832523 25000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337090597/2500000000 : ℝ), (-2095019053/10000000000 : ℝ), (5245471023/10000000000 : ℝ)] ![(44087872850157/100000000000000 : ℝ), (12930939800197/100000000000000 : ℝ), (10745296832523/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337090597/2500000000 : ℝ)|^4341 ≤ (44087872850157/100000000000000 : ℝ)^3317
        have hw : |(1337090597/2500000000 : ℝ)|=(1337090597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2095019053/10000000000 : ℝ)|^4341 ≤ (12930939800197/100000000000000 : ℝ)^3317
        have hw : |(-2095019053/10000000000 : ℝ)|=(2095019053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245471023/10000000000 : ℝ)|^4341 ≤ (10745296832523/25000000000000 : ℝ)^3317
        have hw : |(5245471023/10000000000 : ℝ)|=(5245471023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s5_2 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069672489/2000000000 : ℝ)*x 0 + (5245471053/10000000000 : ℝ)*x 1 + (-2095018937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069672489/2000000000 : ℝ)^4341 ≤ (1763514938603/4000000000000 : ℝ)^3317 := by
    have hnat : (1069672489 : ℕ)^4341*4000000000000^3317 ≤ 1763514938603^3317*2000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069672489 2000000000 1763514938603 4000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245471053/10000000000 : ℝ)^4341 ≤ (21490593825899/50000000000000 : ℝ)^3317 := by
    have hnat : (5245471053 : ℕ)^4341*50000000000000^3317 ≤ 21490593825899^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245471053 10000000000 21490593825899 50000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2095018937/10000000000 : ℝ)^4341 ≤ (12930938863187/100000000000000 : ℝ)^3317 := by
    have hnat : (2095018937 : ℕ)^4341*100000000000000^3317 ≤ 12930938863187^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095018937 10000000000 12930938863187 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069672489/2000000000 : ℝ), (5245471053/10000000000 : ℝ), (-2095018937/10000000000 : ℝ)] ![(1763514938603/4000000000000 : ℝ), (21490593825899/50000000000000 : ℝ), (12930938863187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069672489/2000000000 : ℝ)|^4341 ≤ (1763514938603/4000000000000 : ℝ)^3317
        have hw : |(1069672489/2000000000 : ℝ)|=(1069672489/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245471053/10000000000 : ℝ)|^4341 ≤ (21490593825899/50000000000000 : ℝ)^3317
        have hw : |(5245471053/10000000000 : ℝ)|=(5245471053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2095018937/10000000000 : ℝ)|^4341 ≤ (12930938863187/100000000000000 : ℝ)^3317
        have hw : |(-2095018937/10000000000 : ℝ)|=(2095018937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s5_3 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1079126107/2500000000 : ℝ)*x 0 + (2071960081/5000000000 : ℝ)*x 1 + (2247836061/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079126107/2500000000 : ℝ)^4341 ≤ (16651864620193/50000000000000 : ℝ)^3317 := by
    have hnat : (1079126107 : ℕ)^4341*50000000000000^3317 ≤ 16651864620193^3317*2500000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079126107 2500000000 16651864620193 50000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2071960081/5000000000 : ℝ)^4341 ≤ (98662346069/312500000000 : ℝ)^3317 := by
    have hnat : (2071960081 : ℕ)^4341*312500000000^3317 ≤ 98662346069^3317*5000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2071960081 5000000000 98662346069 312500000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2247836061/5000000000 : ℝ)^4341 ≤ (17562160002641/50000000000000 : ℝ)^3317 := by
    have hnat : (2247836061 : ℕ)^4341*50000000000000^3317 ≤ 17562160002641^3317*5000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247836061 5000000000 17562160002641 50000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079126107/2500000000 : ℝ), (2071960081/5000000000 : ℝ), (2247836061/5000000000 : ℝ)] ![(16651864620193/50000000000000 : ℝ), (98662346069/312500000000 : ℝ), (17562160002641/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079126107/2500000000 : ℝ)|^4341 ≤ (16651864620193/50000000000000 : ℝ)^3317
        have hw : |(1079126107/2500000000 : ℝ)|=(1079126107/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2071960081/5000000000 : ℝ)|^4341 ≤ (98662346069/312500000000 : ℝ)^3317
        have hw : |(2071960081/5000000000 : ℝ)|=(2071960081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2247836061/5000000000 : ℝ)|^4341 ≤ (17562160002641/50000000000000 : ℝ)^3317
        have hw : |(2247836061/5000000000 : ℝ)|=(2247836061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s5_4 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1005365291/5000000000 : ℝ)*x 0 + (5246067499/10000000000 : ℝ)*x 1 + (5410375147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1005365291/5000000000 : ℝ)^4341 ≤ (6127176480931/50000000000000 : ℝ)^3317 := by
    have hnat : (1005365291 : ℕ)^4341*50000000000000^3317 ≤ 6127176480931^3317*5000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005365291 5000000000 6127176480931 50000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246067499/10000000000 : ℝ)^4341 ≤ (21493791888703/50000000000000 : ℝ)^3317 := by
    have hnat : (5246067499 : ℕ)^4341*50000000000000^3317 ≤ 21493791888703^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246067499 10000000000 21493791888703 50000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410375147/10000000000 : ℝ)^4341 ≤ (44758063238471/100000000000000 : ℝ)^3317 := by
    have hnat : (5410375147 : ℕ)^4341*100000000000000^3317 ≤ 44758063238471^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410375147 10000000000 44758063238471 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1005365291/5000000000 : ℝ), (5246067499/10000000000 : ℝ), (5410375147/10000000000 : ℝ)] ![(6127176480931/50000000000000 : ℝ), (21493791888703/50000000000000 : ℝ), (44758063238471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1005365291/5000000000 : ℝ)|^4341 ≤ (6127176480931/50000000000000 : ℝ)^3317
        have hw : |(-1005365291/5000000000 : ℝ)|=(1005365291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246067499/10000000000 : ℝ)|^4341 ≤ (21493791888703/50000000000000 : ℝ)^3317
        have hw : |(5246067499/10000000000 : ℝ)|=(5246067499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410375147/10000000000 : ℝ)|^4341 ≤ (44758063238471/100000000000000 : ℝ)^3317
        have hw : |(5410375147/10000000000 : ℝ)|=(5410375147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s5_5 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (331596691/625000000 : ℝ)*x 0 + (-965057479/5000000000 : ℝ)*x 1 + (5410375147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331596691/625000000 : ℝ)^4341 ≤ (1363329720307/3125000000000 : ℝ)^3317 := by
    have hnat : (331596691 : ℕ)^4341*3125000000000^3317 ≤ 1363329720307^3317*625000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331596691 625000000 1363329720307 3125000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (965057479/5000000000 : ℝ)^4341 ≤ (1161538569861/10000000000000 : ℝ)^3317 := by
    have hnat : (965057479 : ℕ)^4341*10000000000000^3317 ≤ 1161538569861^3317*5000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      965057479 5000000000 1161538569861 10000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410375147/10000000000 : ℝ)^4341 ≤ (44758063238471/100000000000000 : ℝ)^3317 := by
    have hnat : (5410375147 : ℕ)^4341*100000000000000^3317 ≤ 44758063238471^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410375147 10000000000 44758063238471 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331596691/625000000 : ℝ), (-965057479/5000000000 : ℝ), (5410375147/10000000000 : ℝ)] ![(1363329720307/3125000000000 : ℝ), (1161538569861/10000000000000 : ℝ), (44758063238471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331596691/625000000 : ℝ)|^4341 ≤ (1363329720307/3125000000000 : ℝ)^3317
        have hw : |(331596691/625000000 : ℝ)|=(331596691/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-965057479/5000000000 : ℝ)|^4341 ≤ (1161538569861/10000000000000 : ℝ)^3317
        have hw : |(-965057479/5000000000 : ℝ)|=(965057479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410375147/10000000000 : ℝ)|^4341 ≤ (44758063238471/100000000000000 : ℝ)^3317
        have hw : |(5410375147/10000000000 : ℝ)|=(5410375147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s5_6 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (331596691/625000000 : ℝ)*x 0 + (5410375147/10000000000 : ℝ)*x 1 + (-965057479/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331596691/625000000 : ℝ)^4341 ≤ (1363329720307/3125000000000 : ℝ)^3317 := by
    have hnat : (331596691 : ℕ)^4341*3125000000000^3317 ≤ 1363329720307^3317*625000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331596691 625000000 1363329720307 3125000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410375147/10000000000 : ℝ)^4341 ≤ (44758063238471/100000000000000 : ℝ)^3317 := by
    have hnat : (5410375147 : ℕ)^4341*100000000000000^3317 ≤ 44758063238471^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410375147 10000000000 44758063238471 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (965057479/5000000000 : ℝ)^4341 ≤ (1161538569861/10000000000000 : ℝ)^3317 := by
    have hnat : (965057479 : ℕ)^4341*10000000000000^3317 ≤ 1161538569861^3317*5000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      965057479 5000000000 1161538569861 10000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331596691/625000000 : ℝ), (5410375147/10000000000 : ℝ), (-965057479/5000000000 : ℝ)] ![(1363329720307/3125000000000 : ℝ), (44758063238471/100000000000000 : ℝ), (1161538569861/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331596691/625000000 : ℝ)|^4341 ≤ (1363329720307/3125000000000 : ℝ)^3317
        have hw : |(331596691/625000000 : ℝ)|=(331596691/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410375147/10000000000 : ℝ)|^4341 ≤ (44758063238471/100000000000000 : ℝ)^3317
        have hw : |(5410375147/10000000000 : ℝ)|=(5410375147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-965057479/5000000000 : ℝ)|^4341 ≤ (1161538569861/10000000000000 : ℝ)^3317
        have hw : |(-965057479/5000000000 : ℝ)|=(965057479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s5_7 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1079132511/2500000000 : ℝ)*x 0 + (2247202353/5000000000 : ℝ)*x 1 + (2072596901/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079132511/2500000000 : ℝ)^4341 ≤ (33303987892899/100000000000000 : ℝ)^3317 := by
    have hnat : (1079132511 : ℕ)^4341*100000000000000^3317 ≤ 33303987892899^3317*2500000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079132511 2500000000 33303987892899 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2247202353/5000000000 : ℝ)^4341 ≤ (35111361410943/100000000000000 : ℝ)^3317 := by
    have hnat : (2247202353 : ℕ)^4341*100000000000000^3317 ≤ 35111361410943^3317*5000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247202353 5000000000 35111361410943 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2072596901/5000000000 : ℝ)^4341 ≤ (31584650681317/100000000000000 : ℝ)^3317 := by
    have hnat : (2072596901 : ℕ)^4341*100000000000000^3317 ≤ 31584650681317^3317*5000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072596901 5000000000 31584650681317 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079132511/2500000000 : ℝ), (2247202353/5000000000 : ℝ), (2072596901/5000000000 : ℝ)] ![(33303987892899/100000000000000 : ℝ), (35111361410943/100000000000000 : ℝ), (31584650681317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079132511/2500000000 : ℝ)|^4341 ≤ (33303987892899/100000000000000 : ℝ)^3317
        have hw : |(1079132511/2500000000 : ℝ)|=(1079132511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2247202353/5000000000 : ℝ)|^4341 ≤ (35111361410943/100000000000000 : ℝ)^3317
        have hw : |(2247202353/5000000000 : ℝ)|=(2247202353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2072596901/5000000000 : ℝ)|^4341 ≤ (31584650681317/100000000000000 : ℝ)^3317
        have hw : |(2072596901/5000000000 : ℝ)|=(2072596901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1381_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1220839/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3693/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11199/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (351/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14737/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3693/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11199/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3693/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11199/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3693/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11199/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3693/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11199/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3693/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11199/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3693/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11199/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11199/100000 : ℝ) ^ (1085/256 : ℝ) ≤ (4667928818118351/50000000000000000000 : ℝ) := by
    have hpowers : (11199/100000 : ℝ)^1085 ≤ (4667928818118351/50000000000000000000 : ℝ)^256 := by
      have hnat : (11199 : ℕ)^1085*50000000000000000000^256 ≤ 4667928818118351^256*100000^1085 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11199 100000 4667928818118351 50000000000000000000 1085 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11199/100000 : ℝ)) (X := (4667928818118351/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1085 256 (by norm_num) hpowers
    exact h
  have hpowhi : (3693/25000 : ℝ) ^ (1085/256 : ℝ) ≤ (150945495788659/500000000000000000 : ℝ) := by
    have hpowers : (3693/25000 : ℝ)^1085 ≤ (150945495788659/500000000000000000 : ℝ)^256 := by
      have hnat : (3693 : ℕ)^1085*500000000000000000^256 ≤ 150945495788659^256*25000^1085 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3693 25000 150945495788659 500000000000000000 1085 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3693/25000 : ℝ)) (X := (150945495788659/500000000000000000 : ℝ)) (by norm_num) (by norm_num) 1085 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004667928818118351/25000000000000000000 : ℝ) ≤ (1250055064725661/1250000000000000 : ℝ) ^ (1085/256 : ℝ) := by
    have hpowers : (25004667928818118351/25000000000000000000 : ℝ)^256 ≤ (1250055064725661/1250000000000000 : ℝ)^1085 := by
      have hnat : (25004667928818118351 : ℕ)^256*1250000000000000^1085 ≤ 1250055064725661^1085*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004667928818118351 25000000000000000000 1250055064725661 1250000000000000 256 1085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250055064725661/1250000000000000 : ℝ)) (X := (25004667928818118351/25000000000000000000 : ℝ)) (by norm_num) 1085 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50019762478396984251/50000000000000000000 : ℝ) ≤ (500046621481361/500000000000000 : ℝ) ^ (1085/256 : ℝ) := by
    have hpowers : (50019762478396984251/50000000000000000000 : ℝ)^256 ≤ (500046621481361/500000000000000 : ℝ)^1085 := by
      have hnat : (50019762478396984251 : ℕ)^256*500000000000000^1085 ≤ 500046621481361^1085*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50019762478396984251 50000000000000000000 500046621481361 500000000000000 256 1085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500046621481361/500000000000000 : ℝ)) (X := (50019762478396984251/50000000000000000000 : ℝ)) (by norm_num) 1085 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (250150945495788659/250000000000000000 : ℝ) ≤ (156272255335143/156250000000000 : ℝ) ^ (1085/256 : ℝ) := by
    have hpowers : (250150945495788659/250000000000000000 : ℝ)^256 ≤ (156272255335143/156250000000000 : ℝ)^1085 := by
      have hnat : (250150945495788659 : ℕ)^256*156250000000000^1085 ≤ 156272255335143^1085*250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        250150945495788659 250000000000000000 156272255335143 156250000000000 256 1085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156272255335143/156250000000000 : ℝ)) (X := (250150945495788659/250000000000000000 : ℝ)) (by norm_num) 1085 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4667928818118351/50000000000000000000 : ℝ) ≤ ((372089126345111053/372187500000000000 : ℝ)+2*(122977955483/89325000000000 : ℝ)*(11199/100000 : ℝ))^(1085/256 : ℝ) := by
    rw [show (372089126345111053/372187500000000000 : ℝ)+2*(122977955483/89325000000000 : ℝ)*(11199/100000 : ℝ)=(1250055064725661/1250000000000000 : ℝ) by norm_num, show 1+2*(4667928818118351/50000000000000000000 : ℝ)=(25004667928818118351/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(150945495788659/500000000000000000 : ℝ)+(4667928818118351/50000000000000000000 : ℝ) ≤ ((372089126345111053/372187500000000000 : ℝ)+(122977955483/89325000000000 : ℝ)*((3693/25000 : ℝ)+(11199/100000 : ℝ)))^(1085/256 : ℝ) := by
    rw [show (372089126345111053/372187500000000000 : ℝ)+(122977955483/89325000000000 : ℝ)*((3693/25000 : ℝ)+(11199/100000 : ℝ))=(500046621481361/500000000000000 : ℝ) by norm_num, show 1+(150945495788659/500000000000000000 : ℝ)+(4667928818118351/50000000000000000000 : ℝ)=(50019762478396984251/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(150945495788659/500000000000000000 : ℝ) ≤ ((372089126345111053/372187500000000000 : ℝ)+2*(122977955483/89325000000000 : ℝ)*(3693/25000 : ℝ))^(1085/256 : ℝ) := by
    rw [show (372089126345111053/372187500000000000 : ℝ)+2*(122977955483/89325000000000 : ℝ)*(3693/25000 : ℝ)=(156272255335143/156250000000000 : ℝ) by norm_num, show 1+2*(150945495788659/500000000000000000 : ℝ)=(250150945495788659/250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (372089126345111053/372187500000000000 : ℝ)*(X 1 0+X 2 0)+(122977955483/89325000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1085/256 : ℝ)) (lo := (11199/100000 : ℝ)) (hi := (3693/25000 : ℝ)) (c := (372089126345111053/372187500000000000 : ℝ)) (alpha := (122977955483/89325000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (372089126345111053/372187500000000000 : ℝ)*(X 0 1+X 2 1)+(122977955483/89325000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1085/256 : ℝ)) (lo := (11199/100000 : ℝ)) (hi := (3693/25000 : ℝ)) (c := (372089126345111053/372187500000000000 : ℝ)) (alpha := (122977955483/89325000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (372089126345111053/372187500000000000 : ℝ)*(X 0 2+X 1 2)+(122977955483/89325000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1085/256 : ℝ)) (lo := (11199/100000 : ℝ)) (hi := (3693/25000 : ℝ)) (c := (372089126345111053/372187500000000000 : ℝ)) (alpha := (122977955483/89325000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-402143719/2000000000 : ℝ)*X 0 0+(2705487373/5000000000 : ℝ)*X 0 1+(5245471059/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337090597/2500000000 : ℝ)*X 1 0+(-2095019053/10000000000 : ℝ)*X 1 1+(5245471023/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069672489/2000000000 : ℝ)*X 2 0+(5245471053/10000000000 : ℝ)*X 2 1+(-2095018937/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1079126107/2500000000 : ℝ)*X 0 0+(2071960081/5000000000 : ℝ)*X 0 1+(2247836061/5000000000 : ℝ)*X 0 2+(1079126107/2500000000 : ℝ)*X 1 0+(2071960081/5000000000 : ℝ)*X 1 1+(2247836061/5000000000 : ℝ)*X 1 2+(1079126107/2500000000 : ℝ)*X 2 0+(2071960081/5000000000 : ℝ)*X 2 1+(2247836061/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1005365291/5000000000 : ℝ)*X 0 0+(5246067499/10000000000 : ℝ)*X 0 1+(5410375147/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((331596691/625000000 : ℝ)*X 1 0+(-965057479/5000000000 : ℝ)*X 1 1+(5410375147/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((331596691/625000000 : ℝ)*X 2 0+(5410375147/10000000000 : ℝ)*X 2 1+(-965057479/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1079132511/2500000000 : ℝ)*X 0 0+(2247202353/5000000000 : ℝ)*X 0 1+(2072596901/5000000000 : ℝ)*X 0 2+(1079132511/2500000000 : ℝ)*X 1 0+(2247202353/5000000000 : ℝ)*X 1 1+(2072596901/5000000000 : ℝ)*X 1 2+(1079132511/2500000000 : ℝ)*X 2 0+(2247202353/5000000000 : ℝ)*X 2 1+(2072596901/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (30070893059462697700620951/3101562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (779882807/50000000000000 : ℝ)*(base19) + (1575910611/100000000000000 : ℝ)*(base23) + (6451451/25000000000000 : ℝ)*(lower2) + (29610493/50000000000000 : ℝ)*(upper3) + (179093801/100000000000000 : ℝ)*(upper5) + (555323482824999/12500000000000 : ℝ)*(major0) + (555323482824999/12500000000000 : ℝ)*(major1) + (555323482824999/12500000000000 : ℝ)*(major2) + (6042195553185569/100000000000000 : ℝ)*(sp0) + (302111702720329/5000000000000 : ℝ)*(sp1) + (377639627391349/6250000000000 : ℝ)*(sp2) + (2842926693669751/100000000000000 : ℝ)*(sp3) + (156488229/390625000000 : ℝ)*(sp4) + (13094177987/100000000000000 : ℝ)*(sp7) + (1421469893923869/50000000000000 : ℝ)*(f.failure) + (3021117807086097/50000000000000 : ℝ)*(f.sum) + (63600477557167/5955000000000000000000000000 : ℝ)*base66 + (16536785277437269/9304687500000000000000000000000 : ℝ)*base67 + (18965670081859837/18609375000000000000000000000000 : ℝ)*base70 + (20659004120429803/4652343750000000000000000000000 : ℝ)*base72 + (1785766999417/372187500000000000000000000 : ℝ)*base74 + (44823917906523553/4652343750000000000000000000000 : ℝ)*base76 + (70997827985429803/4652343750000000000000000000000 : ℝ)*base78 + (6854007822250991/581542968750000000000000000000 : ℝ)*base80 + (4801509077/1488750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base87 + (431091/39062500000000000000 : ℝ)*base89 + (431091/39062500000000000000 : ℝ)*base91 + (431091/39062500000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (58449737698497444534282351/6203125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (32370923/2000000000000 : ℝ)*(base19) + (175872137/10000000000000 : ℝ)*(base23) + (191755197/100000000000000 : ℝ)*(upper3) + (31821143/50000000000000 : ℝ)*(lower4) + (193661367/100000000000000 : ℝ)*(upper5) + (2237435385632493/50000000000000 : ℝ)*(major0) + (2237435385632493/50000000000000 : ℝ)*(major1) + (2237435385632493/50000000000000 : ℝ)*(major2) + (33419222823/100000000000000 : ℝ)*(sp1) + (8981224533/25000000000000 : ℝ)*(sp2) + (6086142678551047/100000000000000 : ℝ)*(sp4) + (6086107640782073/100000000000000 : ℝ)*(sp5) + (760763124366443/12500000000000 : ℝ)*(sp6) + (71589963747283/2500000000000 : ℝ)*(sp7) + (71589963747283/2500000000000 : ℝ)*(f.failure) + (6086142678551047/100000000000000 : ℝ)*(f.sum) + (22434309038827/2977500000000000000000000000 : ℝ)*base65 + (71750068129617877/9304687500000000000000000000000 : ℝ)*base67 + (2998158570117877/9304687500000000000000000000000 : ℝ)*base69 + (107869638372845129/18609375000000000000000000000000 : ℝ)*base71 + (22360155370499/5955000000000000000000000000 : ℝ)*base73 + (81001984602095129/18609375000000000000000000000000 : ℝ)*base75 + (67616093977970129/18609375000000000000000000000000 : ℝ)*base77 + (182122246937345129/18609375000000000000000000000000 : ℝ)*base79 + (5593492092041/1488750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (54751/3906250000000000000 : ℝ)*base90 + (54751/3906250000000000000 : ℝ)*base92 + (54751/3906250000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1381_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1220839/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3693/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11199/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (351/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14737/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1381_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1381_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1220839/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7979/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (631/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (351/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14737/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1381_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1381_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1381_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1220839/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7979/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (631/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (351/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14737/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1381_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
