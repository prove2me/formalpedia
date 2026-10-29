-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1408_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:48:05.441514+00:00
-- url     : https://prove2.me/submissions/943d8467-c696-4110-bde2-4ad8364b4f92

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
theorem support_rectangle_w1408_s6_0 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-994148497/5000000000 : ℝ)*x 0 + (2704652071/5000000000 : ℝ)*x 1 + (5246415409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (994148497/5000000000 : ℝ)^273 ≤ (1515556501659/12500000000000 : ℝ)^209 := by
    have hnat : (994148497 : ℕ)^273*12500000000000^209 ≤ 1515556501659^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      994148497 5000000000 1515556501659 12500000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704652071/5000000000 : ℝ)^273 ≤ (22407527554793/50000000000000 : ℝ)^209 := by
    have hnat : (2704652071 : ℕ)^273*50000000000000^209 ≤ 22407527554793^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704652071 5000000000 22407527554793 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246415409/10000000000 : ℝ)^273 ≤ (10765123215487/25000000000000 : ℝ)^209 := by
    have hnat : (5246415409 : ℕ)^273*25000000000000^209 ≤ 10765123215487^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246415409 10000000000 10765123215487 25000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-994148497/5000000000 : ℝ), (2704652071/5000000000 : ℝ), (5246415409/10000000000 : ℝ)] ![(1515556501659/12500000000000 : ℝ), (22407527554793/50000000000000 : ℝ), (10765123215487/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-994148497/5000000000 : ℝ)|^273 ≤ (1515556501659/12500000000000 : ℝ)^209
        have hw : |(-994148497/5000000000 : ℝ)|=(994148497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704652071/5000000000 : ℝ)|^273 ≤ (22407527554793/50000000000000 : ℝ)^209
        have hw : |(2704652071/5000000000 : ℝ)|=(2704652071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246415409/10000000000 : ℝ)|^273 ≤ (10765123215487/25000000000000 : ℝ)^209
        have hw : |(5246415409/10000000000 : ℝ)|=(5246415409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s6_1 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1336940183/2500000000 : ℝ)*x 0 + (-1035620497/5000000000 : ℝ)*x 1 + (81975241/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336940183/2500000000 : ℝ)^273 ≤ (11037552203141/25000000000000 : ℝ)^209 := by
    have hnat : (1336940183 : ℕ)^273*25000000000000^209 ≤ 11037552203141^209*2500000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336940183 2500000000 11037552203141 25000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035620497/5000000000 : ℝ)^273 ≤ (2557859630801/20000000000000 : ℝ)^209 := by
    have hnat : (1035620497 : ℕ)^273*20000000000000^209 ≤ 2557859630801^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035620497 5000000000 2557859630801 20000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81975241/156250000 : ℝ)^273 ≤ (21530246511381/50000000000000 : ℝ)^209 := by
    have hnat : (81975241 : ℕ)^273*50000000000000^209 ≤ 21530246511381^209*156250000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81975241 156250000 21530246511381 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336940183/2500000000 : ℝ), (-1035620497/5000000000 : ℝ), (81975241/156250000 : ℝ)] ![(11037552203141/25000000000000 : ℝ), (2557859630801/20000000000000 : ℝ), (21530246511381/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336940183/2500000000 : ℝ)|^273 ≤ (11037552203141/25000000000000 : ℝ)^209
        have hw : |(1336940183/2500000000 : ℝ)|=(1336940183/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1035620497/5000000000 : ℝ)|^273 ≤ (2557859630801/20000000000000 : ℝ)^209
        have hw : |(-1035620497/5000000000 : ℝ)|=(1035620497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(81975241/156250000 : ℝ)|^273 ≤ (21530246511381/50000000000000 : ℝ)^209
        have hw : |(81975241/156250000 : ℝ)|=(81975241/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s6_2 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1069552149/2000000000 : ℝ)*x 0 + (2623207707/5000000000 : ℝ)*x 1 + (-207124099/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069552149/2000000000 : ℝ)^273 ≤ (11037552238189/25000000000000 : ℝ)^209 := by
    have hnat : (1069552149 : ℕ)^273*25000000000000^209 ≤ 11037552238189^209*2000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069552149 2000000000 11037552238189 25000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623207707/5000000000 : ℝ)^273 ≤ (43060492915553/100000000000000 : ℝ)^209 := by
    have hnat : (2623207707 : ℕ)^273*100000000000000^209 ≤ 43060492915553^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623207707 5000000000 43060492915553 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207124099/1000000000 : ℝ)^273 ≤ (12789298121743/100000000000000 : ℝ)^209 := by
    have hnat : (207124099 : ℕ)^273*100000000000000^209 ≤ 12789298121743^209*1000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207124099 1000000000 12789298121743 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069552149/2000000000 : ℝ), (2623207707/5000000000 : ℝ), (-207124099/1000000000 : ℝ)] ![(11037552238189/25000000000000 : ℝ), (43060492915553/100000000000000 : ℝ), (12789298121743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069552149/2000000000 : ℝ)|^273 ≤ (11037552238189/25000000000000 : ℝ)^209
        have hw : |(1069552149/2000000000 : ℝ)|=(1069552149/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623207707/5000000000 : ℝ)|^273 ≤ (43060492915553/100000000000000 : ℝ)^209
        have hw : |(2623207707/5000000000 : ℝ)|=(2623207707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-207124099/1000000000 : ℝ)|^273 ≤ (12789298121743/100000000000000 : ℝ)^209
        have hw : |(-207124099/1000000000 : ℝ)|=(207124099/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s6_3 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2154826183/5000000000 : ℝ)*x 0 + (51725437/125000000 : ℝ)*x 1 + (4487708307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2154826183/5000000000 : ℝ)^273 ≤ (33304361142167/100000000000000 : ℝ)^209 := by
    have hnat : (2154826183 : ℕ)^273*100000000000000^209 ≤ 33304361142167^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154826183 5000000000 33304361142167 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (51725437/125000000 : ℝ)^273 ≤ (15791334366703/50000000000000 : ℝ)^209 := by
    have hnat : (51725437 : ℕ)^273*50000000000000^209 ≤ 15791334366703^209*125000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51725437 125000000 15791334366703 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4487708307/10000000000 : ℝ)^273 ≤ (8778242529217/25000000000000 : ℝ)^209 := by
    have hnat : (4487708307 : ℕ)^273*25000000000000^209 ≤ 8778242529217^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487708307 10000000000 8778242529217 25000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2154826183/5000000000 : ℝ), (51725437/125000000 : ℝ), (4487708307/10000000000 : ℝ)] ![(33304361142167/100000000000000 : ℝ), (15791334366703/50000000000000 : ℝ), (8778242529217/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2154826183/5000000000 : ℝ)|^273 ≤ (33304361142167/100000000000000 : ℝ)^209
        have hw : |(2154826183/5000000000 : ℝ)|=(2154826183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(51725437/125000000 : ℝ)|^273 ≤ (15791334366703/50000000000000 : ℝ)^209
        have hw : |(51725437/125000000 : ℝ)|=(51725437/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4487708307/10000000000 : ℝ)|^273 ≤ (8778242529217/25000000000000 : ℝ)^209
        have hw : |(4487708307/10000000000 : ℝ)|=(4487708307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s6_4 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-497077127/2500000000 : ℝ)*x 0 + (262350091/500000000 : ℝ)*x 1 + (5408714701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (497077127/2500000000 : ℝ)^273 ≤ (606227186239/5000000000000 : ℝ)^209 := by
    have hnat : (497077127 : ℕ)^273*5000000000000^209 ≤ 606227186239^209*2500000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      497077127 2500000000 606227186239 5000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262350091/500000000 : ℝ)^273 ≤ (43066779844033/100000000000000 : ℝ)^209 := by
    have hnat : (262350091 : ℕ)^273*100000000000000^209 ≤ 43066779844033^209*500000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262350091 500000000 43066779844033 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408714701/10000000000 : ℝ)^273 ≤ (22404338206167/50000000000000 : ℝ)^209 := by
    have hnat : (5408714701 : ℕ)^273*50000000000000^209 ≤ 22404338206167^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408714701 10000000000 22404338206167 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-497077127/2500000000 : ℝ), (262350091/500000000 : ℝ), (5408714701/10000000000 : ℝ)] ![(606227186239/5000000000000 : ℝ), (43066779844033/100000000000000 : ℝ), (22404338206167/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-497077127/2500000000 : ℝ)|^273 ≤ (606227186239/5000000000000 : ℝ)^209
        have hw : |(-497077127/2500000000 : ℝ)|=(497077127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(262350091/500000000 : ℝ)|^273 ≤ (43066779844033/100000000000000 : ℝ)^209
        have hw : |(262350091/500000000 : ℝ)|=(262350091/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408714701/10000000000 : ℝ)|^273 ≤ (22404338206167/50000000000000 : ℝ)^209
        have hw : |(5408714701/10000000000 : ℝ)|=(5408714701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s6_5 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5305502787/10000000000 : ℝ)*x 0 + (-954470849/5000000000 : ℝ)*x 1 + (5408714701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305502787/10000000000 : ℝ)^273 ≤ (546188179387/1250000000000 : ℝ)^209 := by
    have hnat : (5305502787 : ℕ)^273*1250000000000^209 ≤ 546188179387^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305502787 10000000000 546188179387 1250000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (954470849/5000000000 : ℝ)^273 ≤ (5748134609133/50000000000000 : ℝ)^209 := by
    have hnat : (954470849 : ℕ)^273*50000000000000^209 ≤ 5748134609133^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      954470849 5000000000 5748134609133 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408714701/10000000000 : ℝ)^273 ≤ (22404338206167/50000000000000 : ℝ)^209 := by
    have hnat : (5408714701 : ℕ)^273*50000000000000^209 ≤ 22404338206167^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408714701 10000000000 22404338206167 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305502787/10000000000 : ℝ), (-954470849/5000000000 : ℝ), (5408714701/10000000000 : ℝ)] ![(546188179387/1250000000000 : ℝ), (5748134609133/50000000000000 : ℝ), (22404338206167/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305502787/10000000000 : ℝ)|^273 ≤ (546188179387/1250000000000 : ℝ)^209
        have hw : |(5305502787/10000000000 : ℝ)|=(5305502787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-954470849/5000000000 : ℝ)|^273 ≤ (5748134609133/50000000000000 : ℝ)^209
        have hw : |(-954470849/5000000000 : ℝ)|=(954470849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408714701/10000000000 : ℝ)|^273 ≤ (22404338206167/50000000000000 : ℝ)^209
        have hw : |(5408714701/10000000000 : ℝ)|=(5408714701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s6_6 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5305502787/10000000000 : ℝ)*x 0 + (5408714701/10000000000 : ℝ)*x 1 + (-954470849/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305502787/10000000000 : ℝ)^273 ≤ (546188179387/1250000000000 : ℝ)^209 := by
    have hnat : (5305502787 : ℕ)^273*1250000000000^209 ≤ 546188179387^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305502787 10000000000 546188179387 1250000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5408714701/10000000000 : ℝ)^273 ≤ (22404338206167/50000000000000 : ℝ)^209 := by
    have hnat : (5408714701 : ℕ)^273*50000000000000^209 ≤ 22404338206167^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408714701 10000000000 22404338206167 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (954470849/5000000000 : ℝ)^273 ≤ (5748134609133/50000000000000 : ℝ)^209 := by
    have hnat : (954470849 : ℕ)^273*50000000000000^209 ≤ 5748134609133^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      954470849 5000000000 5748134609133 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305502787/10000000000 : ℝ), (5408714701/10000000000 : ℝ), (-954470849/5000000000 : ℝ)] ![(546188179387/1250000000000 : ℝ), (22404338206167/50000000000000 : ℝ), (5748134609133/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305502787/10000000000 : ℝ)|^273 ≤ (546188179387/1250000000000 : ℝ)^209
        have hw : |(5305502787/10000000000 : ℝ)|=(5305502787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5408714701/10000000000 : ℝ)|^273 ≤ (22404338206167/50000000000000 : ℝ)^209
        have hw : |(5408714701/10000000000 : ℝ)|=(5408714701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-954470849/5000000000 : ℝ)|^273 ≤ (5748134609133/50000000000000 : ℝ)^209
        have hw : |(-954470849/5000000000 : ℝ)|=(954470849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s6_7 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (538709637/1250000000 : ℝ)*x 0 + (4486449467/10000000000 : ℝ)*x 1 + (4139300307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538709637/1250000000 : ℝ)^273 ≤ (33304610773863/100000000000000 : ℝ)^209 := by
    have hnat : (538709637 : ℕ)^273*100000000000000^209 ≤ 33304610773863^209*1250000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538709637 1250000000 33304610773863 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4486449467/10000000000 : ℝ)^273 ≤ (8775026268873/25000000000000 : ℝ)^209 := by
    have hnat : (4486449467 : ℕ)^273*25000000000000^209 ≤ 8775026268873^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4486449467 10000000000 8775026268873 25000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4139300307/10000000000 : ℝ)^273 ≤ (3949410516589/12500000000000 : ℝ)^209 := by
    have hnat : (4139300307 : ℕ)^273*12500000000000^209 ≤ 3949410516589^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4139300307 10000000000 3949410516589 12500000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538709637/1250000000 : ℝ), (4486449467/10000000000 : ℝ), (4139300307/10000000000 : ℝ)] ![(33304610773863/100000000000000 : ℝ), (8775026268873/25000000000000 : ℝ), (3949410516589/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538709637/1250000000 : ℝ)|^273 ≤ (33304610773863/100000000000000 : ℝ)^209
        have hw : |(538709637/1250000000 : ℝ)|=(538709637/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4486449467/10000000000 : ℝ)|^273 ≤ (8775026268873/25000000000000 : ℝ)^209
        have hw : |(4486449467/10000000000 : ℝ)|=(4486449467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4139300307/10000000000 : ℝ)|^273 ≤ (3949410516589/12500000000000 : ℝ)^209
        have hw : |(4139300307/10000000000 : ℝ)|=(4139300307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1408_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157335037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (59/400 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2823/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (353/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7373/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (59/400 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2823/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (59/400 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2823/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (59/400 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2823/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (59/400 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2823/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (59/400 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2823/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (59/400 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2823/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2823/25000 : ℝ) ^ (4367/1024 : ℝ) ≤ (2282132086911581/25000000000000000000 : ℝ) := by
    have hpowers : (2823/25000 : ℝ)^4367 ≤ (2282132086911581/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2823 : ℕ)^4367*25000000000000000000^1024 ≤ 2282132086911581^1024*25000^4367 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2823 25000 2282132086911581 25000000000000000000 4367 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2823/25000 : ℝ)) (X := (2282132086911581/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4367 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (59/400 : ℝ) ^ (4367/1024 : ℝ) ≤ (713066767921021/2500000000000000000 : ℝ) := by
    have hpowers : (59/400 : ℝ)^4367 ≤ (713066767921021/2500000000000000000 : ℝ)^1024 := by
      have hnat : (59 : ℕ)^4367*2500000000000000000^1024 ≤ 713066767921021^1024*400^4367 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59 400 713066767921021 2500000000000000000 4367 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (59/400 : ℝ)) (X := (713066767921021/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4367 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502282132086911581/12500000000000000000 : ℝ) ≤ (10000428072355639/10000000000000000 : ℝ) ^ (4367/1024 : ℝ) := by
    have hpowers : (12502282132086911581/12500000000000000000 : ℝ)^1024 ≤ (10000428072355639/10000000000000000 : ℝ)^4367 := by
      have hnat : (12502282132086911581 : ℕ)^1024*10000000000000000^4367 ≤ 10000428072355639^4367*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502282132086911581 12500000000000000000 10000428072355639 10000000000000000 1024 4367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000428072355639/10000000000000000 : ℝ)) (X := (12502282132086911581/12500000000000000000 : ℝ)) (by norm_num) 4367 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25009412799766121791/25000000000000000000 : ℝ) ≤ (10000882740390103/10000000000000000 : ℝ) ^ (4367/1024 : ℝ) := by
    have hpowers : (25009412799766121791/25000000000000000000 : ℝ)^1024 ≤ (10000882740390103/10000000000000000 : ℝ)^4367 := by
      have hnat : (25009412799766121791 : ℕ)^1024*10000000000000000^4367 ≤ 10000882740390103^4367*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009412799766121791 25000000000000000000 10000882740390103 10000000000000000 1024 4367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000882740390103/10000000000000000 : ℝ)) (X := (25009412799766121791/25000000000000000000 : ℝ)) (by norm_num) 4367 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1250713066767921021/1250000000000000000 : ℝ) ≤ (10001337408424567/10000000000000000 : ℝ) ^ (4367/1024 : ℝ) := by
    have hpowers : (1250713066767921021/1250000000000000000 : ℝ)^1024 ≤ (10001337408424567/10000000000000000 : ℝ)^4367 := by
      have hnat : (1250713066767921021 : ℕ)^1024*10000000000000000^4367 ≤ 10001337408424567^4367*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250713066767921021 1250000000000000000 10001337408424567 10000000000000000 1024 4367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001337408424567/10000000000000000 : ℝ)) (X := (1250713066767921021/1250000000000000000 : ℝ)) (by norm_num) 4367 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2282132086911581/25000000000000000000 : ℝ) ≤ ((2469372289379676049/2470000000000000000 : ℝ)+2*(2029768011/1543750000000 : ℝ)*(2823/25000 : ℝ))^(4367/1024 : ℝ) := by
    rw [show (2469372289379676049/2470000000000000000 : ℝ)+2*(2029768011/1543750000000 : ℝ)*(2823/25000 : ℝ)=(10000428072355639/10000000000000000 : ℝ) by norm_num, show 1+2*(2282132086911581/25000000000000000000 : ℝ)=(12502282132086911581/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(713066767921021/2500000000000000000 : ℝ)+(2282132086911581/25000000000000000000 : ℝ) ≤ ((2469372289379676049/2470000000000000000 : ℝ)+(2029768011/1543750000000 : ℝ)*((59/400 : ℝ)+(2823/25000 : ℝ)))^(4367/1024 : ℝ) := by
    rw [show (2469372289379676049/2470000000000000000 : ℝ)+(2029768011/1543750000000 : ℝ)*((59/400 : ℝ)+(2823/25000 : ℝ))=(10000882740390103/10000000000000000 : ℝ) by norm_num, show 1+(713066767921021/2500000000000000000 : ℝ)+(2282132086911581/25000000000000000000 : ℝ)=(25009412799766121791/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(713066767921021/2500000000000000000 : ℝ) ≤ ((2469372289379676049/2470000000000000000 : ℝ)+2*(2029768011/1543750000000 : ℝ)*(59/400 : ℝ))^(4367/1024 : ℝ) := by
    rw [show (2469372289379676049/2470000000000000000 : ℝ)+2*(2029768011/1543750000000 : ℝ)*(59/400 : ℝ)=(10001337408424567/10000000000000000 : ℝ) by norm_num, show 1+2*(713066767921021/2500000000000000000 : ℝ)=(1250713066767921021/1250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2469372289379676049/2470000000000000000 : ℝ)*(X 1 0+X 2 0)+(2029768011/1543750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4367/1024 : ℝ)) (lo := (2823/25000 : ℝ)) (hi := (59/400 : ℝ)) (c := (2469372289379676049/2470000000000000000 : ℝ)) (alpha := (2029768011/1543750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2469372289379676049/2470000000000000000 : ℝ)*(X 0 1+X 2 1)+(2029768011/1543750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4367/1024 : ℝ)) (lo := (2823/25000 : ℝ)) (hi := (59/400 : ℝ)) (c := (2469372289379676049/2470000000000000000 : ℝ)) (alpha := (2029768011/1543750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2469372289379676049/2470000000000000000 : ℝ)*(X 0 2+X 1 2)+(2029768011/1543750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4367/1024 : ℝ)) (lo := (2823/25000 : ℝ)) (hi := (59/400 : ℝ)) (c := (2469372289379676049/2470000000000000000 : ℝ)) (alpha := (2029768011/1543750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-994148497/5000000000 : ℝ)*X 0 0+(2704652071/5000000000 : ℝ)*X 0 1+(5246415409/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336940183/2500000000 : ℝ)*X 1 0+(-1035620497/5000000000 : ℝ)*X 1 1+(81975241/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069552149/2000000000 : ℝ)*X 2 0+(2623207707/5000000000 : ℝ)*X 2 1+(-207124099/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2154826183/5000000000 : ℝ)*X 0 0+(51725437/125000000 : ℝ)*X 0 1+(4487708307/10000000000 : ℝ)*X 0 2+(2154826183/5000000000 : ℝ)*X 1 0+(51725437/125000000 : ℝ)*X 1 1+(4487708307/10000000000 : ℝ)*X 1 2+(2154826183/5000000000 : ℝ)*X 2 0+(51725437/125000000 : ℝ)*X 2 1+(4487708307/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-497077127/2500000000 : ℝ)*X 0 0+(262350091/500000000 : ℝ)*X 0 1+(5408714701/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305502787/10000000000 : ℝ)*X 1 0+(-954470849/5000000000 : ℝ)*X 1 1+(5408714701/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305502787/10000000000 : ℝ)*X 2 0+(5408714701/10000000000 : ℝ)*X 2 1+(-954470849/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((538709637/1250000000 : ℝ)*X 0 0+(4486449467/10000000000 : ℝ)*X 0 1+(4139300307/10000000000 : ℝ)*X 0 2+(538709637/1250000000 : ℝ)*X 1 0+(4486449467/10000000000 : ℝ)*X 1 1+(4139300307/10000000000 : ℝ)*X 1 2+(538709637/1250000000 : ℝ)*X 2 0+(4486449467/10000000000 : ℝ)*X 2 1+(4139300307/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (536899310553589775090714301/61750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1560961027/100000000000000 : ℝ)*(base19) + (1474199789/100000000000000 : ℝ)*(base23) + (54378829/100000000000000 : ℝ)*(lower2) + (211616023/100000000000000 : ℝ)*(upper3) + (72519971/50000000000000 : ℝ)*(upper5) + (4499535537377617/100000000000000 : ℝ)*(major0) + (4499535537377617/100000000000000 : ℝ)*(major1) + (4499535537377617/100000000000000 : ℝ)*(major2) + (95924909725539/1562500000000 : ℝ)*(sp0) + (6139225909236741/100000000000000 : ℝ)*(sp1) + (306961299799899/5000000000000 : ℝ)*(sp2) + (714956704830931/25000000000000 : ℝ)*(sp3) + (4155970409/12500000000000 : ℝ)*(sp4) + (8247704773/50000000000000 : ℝ)*(sp7) + (285984331473327/10000000000000 : ℝ)*(f.failure) + (767403433774721/12500000000000 : ℝ)*(f.sum) + (290298174949/154375000000000000000000000 : ℝ)*base65 + (309411952084795233/247000000000000000000000000000000 : ℝ)*base67 + (2987367196880795233/247000000000000000000000000000000 : ℝ)*base69 + (753849767461204767/247000000000000000000000000000000 : ℝ)*base72 + (1163708927153/308750000000000000000000000 : ℝ)*base73 + (1972670782824795233/247000000000000000000000000000000 : ℝ)*base75 + (497985582602795233/247000000000000000000000000000000 : ℝ)*base77 + (3536411068828795233/247000000000000000000000000000000 : ℝ)*base79 + (984563314721/617500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1941901/1000000000000000000000 : ℝ)*base90 + (1941901/1000000000000000000000 : ℝ)*base92 + (1941901/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27236507753913649797/4062500000000000000000000 : ℝ) := by norm_num
    linear_combination (1140229343/100000000000000 : ℝ)*(base19) + (247796781/20000000000000 : ℝ)*(base23) + (387231351/100000000000000 : ℝ)*(lower1) + (136280471/100000000000000 : ℝ)*(upper3) + (44874031/100000000000000 : ℝ)*(lower4) + (68937909/50000000000000 : ℝ)*(upper5) + (2266092325514631/50000000000000 : ℝ)*(major0) + (2266092325514631/50000000000000 : ℝ)*(major1) + (2266092325514631/50000000000000 : ℝ)*(major2) + (889798983/50000000000000 : ℝ)*(sp2) + (618377443326263/10000000000000 : ℝ)*(sp4) + (6183773293033287/100000000000000 : ℝ)*(sp5) + (6183771414680759/100000000000000 : ℝ)*(sp6) + (720148661329209/25000000000000 : ℝ)*(sp7) + (720148661329209/25000000000000 : ℝ)*(f.failure) + (618377443326263/10000000000000 : ℝ)*(f.sum) + (39988622899/8125000000000000000000000 : ℝ)*base66 + (248499218457190899/6500000000000000000000000000000 : ℝ)*base68 + (53387566287809101/6500000000000000000000000000000 : ℝ)*base69 + (695975768191690899/6500000000000000000000000000000 : ℝ)*base72 + (228760009871/32500000000000000000000000 : ℝ)*base74 + (53359430667309101/6500000000000000000000000000000 : ℝ)*base75 + (69827262437309101/6500000000000000000000000000000 : ℝ)*base77 + (52346114446690899/6500000000000000000000000000000 : ℝ)*base80 + (26994434301/32500000000000000000000000 : ℝ)*base82 + (17195733/2500000000000000000000 : ℝ)*base89 + (17195733/2500000000000000000000 : ℝ)*base91 + (17195733/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1408_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157335037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (59/400 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2823/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (353/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7373/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1408_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1408_s7_0 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-497074913/2500000000 : ℝ)*x 0 + (5409274383/10000000000 : ℝ)*x 1 + (5246443473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (497074913/2500000000 : ℝ)^273 ≤ (2424894636961/20000000000000 : ℝ)^209 := by
    have hnat : (497074913 : ℕ)^273*20000000000000^209 ≤ 2424894636961^209*2500000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      497074913 2500000000 2424894636961 20000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409274383/10000000000 : ℝ)^273 ≤ (22407366532181/50000000000000 : ℝ)^209 := by
    have hnat : (5409274383 : ℕ)^273*50000000000000^209 ≤ 22407366532181^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409274383 10000000000 22407366532181 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246443473/10000000000 : ℝ)^273 ≤ (336412451051/781250000000 : ℝ)^209 := by
    have hnat : (5246443473 : ℕ)^273*781250000000^209 ≤ 336412451051^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246443473 10000000000 336412451051 781250000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-497074913/2500000000 : ℝ), (5409274383/10000000000 : ℝ), (5246443473/10000000000 : ℝ)] ![(2424894636961/20000000000000 : ℝ), (22407366532181/50000000000000 : ℝ), (336412451051/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-497074913/2500000000 : ℝ)|^273 ≤ (2424894636961/20000000000000 : ℝ)^209
        have hw : |(-497074913/2500000000 : ℝ)|=(497074913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409274383/10000000000 : ℝ)|^273 ≤ (22407366532181/50000000000000 : ℝ)^209
        have hw : |(5409274383/10000000000 : ℝ)|=(5409274383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246443473/10000000000 : ℝ)|^273 ≤ (336412451051/781250000000 : ℝ)^209
        have hw : |(5246443473/10000000000 : ℝ)|=(5246443473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s7_1 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1336938243/2500000000 : ℝ)*x 0 + (-82848571/400000000 : ℝ)*x 1 + (5246443331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336938243/2500000000 : ℝ)^273 ≤ (11037531282317/25000000000000 : ℝ)^209 := by
    have hnat : (1336938243 : ℕ)^273*25000000000000^209 ≤ 11037531282317^209*2500000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336938243 2500000000 11037531282317 25000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (82848571/400000000 : ℝ)^273 ≤ (1598635331471/12500000000000 : ℝ)^209 := by
    have hnat : (82848571 : ℕ)^273*12500000000000^209 ≤ 1598635331471^209*400000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82848571 400000000 1598635331471 12500000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246443331/10000000000 : ℝ)^273 ≤ (43060792212153/100000000000000 : ℝ)^209 := by
    have hnat : (5246443331 : ℕ)^273*100000000000000^209 ≤ 43060792212153^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246443331 10000000000 43060792212153 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336938243/2500000000 : ℝ), (-82848571/400000000 : ℝ), (5246443331/10000000000 : ℝ)] ![(11037531282317/25000000000000 : ℝ), (1598635331471/12500000000000 : ℝ), (43060792212153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336938243/2500000000 : ℝ)|^273 ≤ (11037531282317/25000000000000 : ℝ)^209
        have hw : |(1336938243/2500000000 : ℝ)|=(1336938243/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-82848571/400000000 : ℝ)|^273 ≤ (1598635331471/12500000000000 : ℝ)^209
        have hw : |(-82848571/400000000 : ℝ)|=(82848571/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246443331/10000000000 : ℝ)|^273 ≤ (43060792212153/100000000000000 : ℝ)^209
        have hw : |(5246443331/10000000000 : ℝ)|=(5246443331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s7_2 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5347753387/10000000000 : ℝ)*x 0 + (5246443171/10000000000 : ℝ)*x 1 + (-517803483/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347753387/10000000000 : ℝ)^273 ≤ (22075064802299/50000000000000 : ℝ)^209 := by
    have hnat : (5347753387 : ℕ)^273*50000000000000^209 ≤ 22075064802299^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347753387 10000000000 22075064802299 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246443171/10000000000 : ℝ)^273 ≤ (53825988121/125000000000 : ℝ)^209 := by
    have hnat : (5246443171 : ℕ)^273*125000000000^209 ≤ 53825988121^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246443171 10000000000 53825988121 125000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (517803483/2500000000 : ℝ)^273 ≤ (2557815977061/20000000000000 : ℝ)^209 := by
    have hnat : (517803483 : ℕ)^273*20000000000000^209 ≤ 2557815977061^209*2500000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517803483 2500000000 2557815977061 20000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347753387/10000000000 : ℝ), (5246443171/10000000000 : ℝ), (-517803483/2500000000 : ℝ)] ![(22075064802299/50000000000000 : ℝ), (53825988121/125000000000 : ℝ), (2557815977061/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347753387/10000000000 : ℝ)|^273 ≤ (22075064802299/50000000000000 : ℝ)^209
        have hw : |(5347753387/10000000000 : ℝ)|=(5347753387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246443171/10000000000 : ℝ)|^273 ≤ (53825988121/125000000000 : ℝ)^209
        have hw : |(5246443171/10000000000 : ℝ)|=(5246443171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-517803483/2500000000 : ℝ)|^273 ≤ (2557815977061/20000000000000 : ℝ)^209
        have hw : |(-517803483/2500000000 : ℝ)|=(517803483/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s7_3 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (67338347/156250000 : ℝ)*x 0 + (2069048481/5000000000 : ℝ)*x 1 + (2243823003/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67338347/156250000 : ℝ)^273 ≤ (33304379735827/100000000000000 : ℝ)^209 := by
    have hnat : (67338347 : ℕ)^273*100000000000000^209 ≤ 33304379735827^209*156250000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67338347 156250000 33304379735827 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2069048481/5000000000 : ℝ)^273 ≤ (15791643430211/50000000000000 : ℝ)^209 := by
    have hnat : (2069048481 : ℕ)^273*50000000000000^209 ≤ 15791643430211^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069048481 5000000000 15791643430211 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2243823003/5000000000 : ℝ)^273 ≤ (3511233338967/10000000000000 : ℝ)^209 := by
    have hnat : (2243823003 : ℕ)^273*10000000000000^209 ≤ 3511233338967^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243823003 5000000000 3511233338967 10000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(67338347/156250000 : ℝ), (2069048481/5000000000 : ℝ), (2243823003/5000000000 : ℝ)] ![(33304379735827/100000000000000 : ℝ), (15791643430211/50000000000000 : ℝ), (3511233338967/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(67338347/156250000 : ℝ)|^273 ≤ (33304379735827/100000000000000 : ℝ)^209
        have hw : |(67338347/156250000 : ℝ)|=(67338347/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2069048481/5000000000 : ℝ)|^273 ≤ (15791643430211/50000000000000 : ℝ)^209
        have hw : |(2069048481/5000000000 : ℝ)|=(2069048481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2243823003/5000000000 : ℝ)|^273 ≤ (3511233338967/10000000000000 : ℝ)^209
        have hw : |(2243823003/5000000000 : ℝ)|=(2243823003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s7_4 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1988311391/10000000000 : ℝ)*x 0 + (655878671/1250000000 : ℝ)*x 1 + (2704342643/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1988311391/10000000000 : ℝ)^273 ≤ (6062283344263/50000000000000 : ℝ)^209 := by
    have hnat : (1988311391 : ℕ)^273*50000000000000^209 ≤ 6062283344263^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1988311391 10000000000 6062283344263 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655878671/1250000000 : ℝ)^273 ≤ (4306707519471/10000000000000 : ℝ)^209 := by
    have hnat : (655878671 : ℕ)^273*10000000000000^209 ≤ 4306707519471^209*1250000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655878671 1250000000 4306707519471 10000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2704342643/5000000000 : ℝ)^273 ≤ (2240417905021/5000000000000 : ℝ)^209 := by
    have hnat : (2704342643 : ℕ)^273*5000000000000^209 ≤ 2240417905021^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704342643 5000000000 2240417905021 5000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1988311391/10000000000 : ℝ), (655878671/1250000000 : ℝ), (2704342643/5000000000 : ℝ)] ![(6062283344263/50000000000000 : ℝ), (4306707519471/10000000000000 : ℝ), (2240417905021/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1988311391/10000000000 : ℝ)|^273 ≤ (6062283344263/50000000000000 : ℝ)^209
        have hw : |(-1988311391/10000000000 : ℝ)|=(1988311391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655878671/1250000000 : ℝ)|^273 ≤ (4306707519471/10000000000000 : ℝ)^209
        have hw : |(655878671/1250000000 : ℝ)|=(655878671/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2704342643/5000000000 : ℝ)|^273 ≤ (2240417905021/5000000000000 : ℝ)^209
        have hw : |(2704342643/5000000000 : ℝ)|=(2704342643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s7_5 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5305510241/10000000000 : ℝ)*x 0 + (-95448587/500000000 : ℝ)*x 1 + (5408685453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305510241/10000000000 : ℝ)^273 ≤ (21847567269683/50000000000000 : ℝ)^209 := by
    have hnat : (5305510241 : ℕ)^273*50000000000000^209 ≤ 21847567269683^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305510241 10000000000 21847567269683 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (95448587/500000000 : ℝ)^273 ≤ (459860221749/4000000000000 : ℝ)^209 := by
    have hnat : (95448587 : ℕ)^273*4000000000000^209 ≤ 459860221749^209*500000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95448587 500000000 459860221749 4000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408685453/10000000000 : ℝ)^273 ≤ (8961671981519/20000000000000 : ℝ)^209 := by
    have hnat : (5408685453 : ℕ)^273*20000000000000^209 ≤ 8961671981519^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408685453 10000000000 8961671981519 20000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305510241/10000000000 : ℝ), (-95448587/500000000 : ℝ), (5408685453/10000000000 : ℝ)] ![(21847567269683/50000000000000 : ℝ), (459860221749/4000000000000 : ℝ), (8961671981519/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305510241/10000000000 : ℝ)|^273 ≤ (21847567269683/50000000000000 : ℝ)^209
        have hw : |(5305510241/10000000000 : ℝ)|=(5305510241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-95448587/500000000 : ℝ)|^273 ≤ (459860221749/4000000000000 : ℝ)^209
        have hw : |(-95448587/500000000 : ℝ)|=(95448587/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408685453/10000000000 : ℝ)|^273 ≤ (8961671981519/20000000000000 : ℝ)^209
        have hw : |(5408685453/10000000000 : ℝ)|=(5408685453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s7_6 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1061102023/2000000000 : ℝ)*x 0 + (1081737093/2000000000 : ℝ)*x 1 + (-381794379/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061102023/2000000000 : ℝ)^273 ≤ (43695133183887/100000000000000 : ℝ)^209 := by
    have hnat : (1061102023 : ℕ)^273*100000000000000^209 ≤ 43695133183887^209*2000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061102023 2000000000 43695133183887 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081737093/2000000000 : ℝ)^273 ≤ (11202090009363/25000000000000 : ℝ)^209 := by
    have hnat : (1081737093 : ℕ)^273*25000000000000^209 ≤ 11202090009363^209*2000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081737093 2000000000 11202090009363 25000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (381794379/2000000000 : ℝ)^273 ≤ (2874126690759/25000000000000 : ℝ)^209 := by
    have hnat : (381794379 : ℕ)^273*25000000000000^209 ≤ 2874126690759^209*2000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      381794379 2000000000 2874126690759 25000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061102023/2000000000 : ℝ), (1081737093/2000000000 : ℝ), (-381794379/2000000000 : ℝ)] ![(43695133183887/100000000000000 : ℝ), (11202090009363/25000000000000 : ℝ), (2874126690759/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061102023/2000000000 : ℝ)|^273 ≤ (43695133183887/100000000000000 : ℝ)^209
        have hw : |(1061102023/2000000000 : ℝ)|=(1061102023/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081737093/2000000000 : ℝ)|^273 ≤ (11202090009363/25000000000000 : ℝ)^209
        have hw : |(1081737093/2000000000 : ℝ)|=(1081737093/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-381794379/2000000000 : ℝ)|^273 ≤ (2874126690759/25000000000000 : ℝ)^209
        have hw : |(-381794379/2000000000 : ℝ)|=(381794379/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s7_7 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4309679271/10000000000 : ℝ)*x 0 + (2243193977/5000000000 : ℝ)*x 1 + (2069680577/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4309679271/10000000000 : ℝ)^273 ≤ (8326158182239/25000000000000 : ℝ)^209 := by
    have hnat : (4309679271 : ℕ)^273*25000000000000^209 ≤ 8326158182239^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4309679271 10000000000 8326158182239 25000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2243193977/5000000000 : ℝ)^273 ≤ (17549738227891/50000000000000 : ℝ)^209 := by
    have hnat : (2243193977 : ℕ)^273*50000000000000^209 ≤ 17549738227891^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243193977 5000000000 17549738227891 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2069680577/5000000000 : ℝ)^273 ≤ (31595890801761/100000000000000 : ℝ)^209 := by
    have hnat : (2069680577 : ℕ)^273*100000000000000^209 ≤ 31595890801761^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069680577 5000000000 31595890801761 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4309679271/10000000000 : ℝ), (2243193977/5000000000 : ℝ), (2069680577/5000000000 : ℝ)] ![(8326158182239/25000000000000 : ℝ), (17549738227891/50000000000000 : ℝ), (31595890801761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4309679271/10000000000 : ℝ)|^273 ≤ (8326158182239/25000000000000 : ℝ)^209
        have hw : |(4309679271/10000000000 : ℝ)|=(4309679271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2243193977/5000000000 : ℝ)|^273 ≤ (17549738227891/50000000000000 : ℝ)^209
        have hw : |(2243193977/5000000000 : ℝ)|=(2243193977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2069680577/5000000000 : ℝ)|^273 ≤ (31595890801761/100000000000000 : ℝ)^209
        have hw : |(2069680577/5000000000 : ℝ)|=(2069680577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1408_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157335037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7373/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (353/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (11297/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2949/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7373/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (353/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7373/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (353/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7373/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (353/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7373/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (353/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7373/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (353/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7373/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (353/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (353/3125 : ℝ) ^ (4367/1024 : ℝ) ≤ (4571163302477899/50000000000000000000 : ℝ) := by
    have hpowers : (353/3125 : ℝ)^4367 ≤ (4571163302477899/50000000000000000000 : ℝ)^1024 := by
      have hnat : (353 : ℕ)^4367*50000000000000000000^1024 ≤ 4571163302477899^1024*3125^4367 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        353 3125 4571163302477899 50000000000000000000 4367 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (353/3125 : ℝ)) (X := (4571163302477899/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4367 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7373/50000 : ℝ) ^ (4367/1024 : ℝ) ≤ (5697939684855591/20000000000000000000 : ℝ) := by
    have hpowers : (7373/50000 : ℝ)^4367 ≤ (5697939684855591/20000000000000000000 : ℝ)^1024 := by
      have hnat : (7373 : ℕ)^4367*20000000000000000000^1024 ≤ 5697939684855591^1024*50000^4367 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7373 50000 5697939684855591 20000000000000000000 4367 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7373/50000 : ℝ)) (X := (5697939684855591/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4367 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004571163302477899/25000000000000000000 : ℝ) ≤ (10000428719364551/10000000000000000 : ℝ) ^ (4367/1024 : ℝ) := by
    have hpowers : (25004571163302477899/25000000000000000000 : ℝ)^1024 ≤ (10000428719364551/10000000000000000 : ℝ)^4367 := by
      have hnat : (25004571163302477899 : ℕ)^1024*10000000000000000^4367 ≤ 10000428719364551^4367*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004571163302477899 25000000000000000000 10000428719364551 10000000000000000 1024 4367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000428719364551/10000000000000000 : ℝ)) (X := (25004571163302477899/25000000000000000000 : ℝ)) (by norm_num) 4367 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100037632025029233753/100000000000000000000 : ℝ) ≤ (1000088229091549/1000000000000000 : ℝ) ^ (4367/1024 : ℝ) := by
    have hpowers : (100037632025029233753/100000000000000000000 : ℝ)^1024 ≤ (1000088229091549/1000000000000000 : ℝ)^4367 := by
      have hnat : (100037632025029233753 : ℕ)^1024*1000000000000000^4367 ≤ 1000088229091549^4367*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100037632025029233753 100000000000000000000 1000088229091549 1000000000000000 1024 4367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000088229091549/1000000000000000 : ℝ)) (X := (100037632025029233753/100000000000000000000 : ℝ)) (by norm_num) 4367 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10005697939684855591/10000000000000000000 : ℝ) ≤ (10001335862466429/10000000000000000 : ℝ) ^ (4367/1024 : ℝ) := by
    have hpowers : (10005697939684855591/10000000000000000000 : ℝ)^1024 ≤ (10001335862466429/10000000000000000 : ℝ)^4367 := by
      have hnat : (10005697939684855591 : ℕ)^1024*10000000000000000^4367 ≤ 10001335862466429^4367*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005697939684855591 10000000000000000000 10001335862466429 10000000000000000 1024 4367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001335862466429/10000000000000000 : ℝ)) (X := (10005697939684855591/10000000000000000000 : ℝ)) (by norm_num) 4367 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4571163302477899/50000000000000000000 : ℝ) ≤ ((17245615996664443531/17250000000000000000 : ℝ)+2*(453571550939/345000000000000 : ℝ)*(353/3125 : ℝ))^(4367/1024 : ℝ) := by
    rw [show (17245615996664443531/17250000000000000000 : ℝ)+2*(453571550939/345000000000000 : ℝ)*(353/3125 : ℝ)=(10000428719364551/10000000000000000 : ℝ) by norm_num, show 1+2*(4571163302477899/50000000000000000000 : ℝ)=(25004571163302477899/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5697939684855591/20000000000000000000 : ℝ)+(4571163302477899/50000000000000000000 : ℝ) ≤ ((17245615996664443531/17250000000000000000 : ℝ)+(453571550939/345000000000000 : ℝ)*((7373/50000 : ℝ)+(353/3125 : ℝ)))^(4367/1024 : ℝ) := by
    rw [show (17245615996664443531/17250000000000000000 : ℝ)+(453571550939/345000000000000 : ℝ)*((7373/50000 : ℝ)+(353/3125 : ℝ))=(1000088229091549/1000000000000000 : ℝ) by norm_num, show 1+(5697939684855591/20000000000000000000 : ℝ)+(4571163302477899/50000000000000000000 : ℝ)=(100037632025029233753/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5697939684855591/20000000000000000000 : ℝ) ≤ ((17245615996664443531/17250000000000000000 : ℝ)+2*(453571550939/345000000000000 : ℝ)*(7373/50000 : ℝ))^(4367/1024 : ℝ) := by
    rw [show (17245615996664443531/17250000000000000000 : ℝ)+2*(453571550939/345000000000000 : ℝ)*(7373/50000 : ℝ)=(10001335862466429/10000000000000000 : ℝ) by norm_num, show 1+2*(5697939684855591/20000000000000000000 : ℝ)=(10005697939684855591/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17245615996664443531/17250000000000000000 : ℝ)*(X 1 0+X 2 0)+(453571550939/345000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4367/1024 : ℝ)) (lo := (353/3125 : ℝ)) (hi := (7373/50000 : ℝ)) (c := (17245615996664443531/17250000000000000000 : ℝ)) (alpha := (453571550939/345000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17245615996664443531/17250000000000000000 : ℝ)*(X 0 1+X 2 1)+(453571550939/345000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4367/1024 : ℝ)) (lo := (353/3125 : ℝ)) (hi := (7373/50000 : ℝ)) (c := (17245615996664443531/17250000000000000000 : ℝ)) (alpha := (453571550939/345000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17245615996664443531/17250000000000000000 : ℝ)*(X 0 2+X 1 2)+(453571550939/345000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4367/1024 : ℝ)) (lo := (353/3125 : ℝ)) (hi := (7373/50000 : ℝ)) (c := (17245615996664443531/17250000000000000000 : ℝ)) (alpha := (453571550939/345000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-497074913/2500000000 : ℝ)*X 0 0+(5409274383/10000000000 : ℝ)*X 0 1+(5246443473/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336938243/2500000000 : ℝ)*X 1 0+(-82848571/400000000 : ℝ)*X 1 1+(5246443331/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347753387/10000000000 : ℝ)*X 2 0+(5246443171/10000000000 : ℝ)*X 2 1+(-517803483/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((67338347/156250000 : ℝ)*X 0 0+(2069048481/5000000000 : ℝ)*X 0 1+(2243823003/5000000000 : ℝ)*X 0 2+(67338347/156250000 : ℝ)*X 1 0+(2069048481/5000000000 : ℝ)*X 1 1+(2243823003/5000000000 : ℝ)*X 1 2+(67338347/156250000 : ℝ)*X 2 0+(2069048481/5000000000 : ℝ)*X 2 1+(2243823003/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1988311391/10000000000 : ℝ)*X 0 0+(655878671/1250000000 : ℝ)*X 0 1+(2704342643/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305510241/10000000000 : ℝ)*X 1 0+(-95448587/500000000 : ℝ)*X 1 1+(5408685453/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061102023/2000000000 : ℝ)*X 2 0+(1081737093/2000000000 : ℝ)*X 2 1+(-381794379/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4309679271/10000000000 : ℝ)*X 0 0+(2243193977/5000000000 : ℝ)*X 0 1+(2069680577/5000000000 : ℝ)*X 0 2+(4309679271/10000000000 : ℝ)*X 1 0+(2243193977/5000000000 : ℝ)*X 1 1+(2069680577/5000000000 : ℝ)*X 1 2+(4309679271/10000000000 : ℝ)*X 2 0+(2243193977/5000000000 : ℝ)*X 2 1+(2069680577/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (427822369943583961752031803/71875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (143719229/50000000000000 : ℝ)*(base19) + (331693009/50000000000000 : ℝ)*(base23) + (23767303/25000000000000 : ℝ)*(lower2) + (36854069/50000000000000 : ℝ)*(upper5) + (1125273936726087/25000000000000 : ℝ)*(major0) + (1125273936726087/25000000000000 : ℝ)*(major1) + (1125273936726087/25000000000000 : ℝ)*(major2) + (6141343521115459/100000000000000 : ℝ)*(sp0) + (6141346280273869/100000000000000 : ℝ)*(sp1) + (6141355669419477/100000000000000 : ℝ)*(sp2) + (715207775220601/25000000000000 : ℝ)*(sp3) + (3202922509/25000000000000 : ℝ)*(sp4) + (610318323/6250000000000 : ℝ)*(sp5) + (772342083/20000000000000 : ℝ)*(sp7) + (2860834962592819/100000000000000 : ℝ)*(f.failure) + (767669541600687/12500000000000 : ℝ)*(f.sum) + (2050178865587/2875000000000000000000000000 : ℝ)*base65 + (596907181605664399/143750000000000000000000000000000 : ℝ)*base67 + (401767256093164399/143750000000000000000000000000000 : ℝ)*base69 + (529959349418164399/143750000000000000000000000000000 : ℝ)*base71 + (3475864700663/2875000000000000000000000000 : ℝ)*base74 + (2151799599031835601/143750000000000000000000000000000 : ℝ)*base76 + (244665764263085601/143750000000000000000000000000000 : ℝ)*base78 + (10108537818164399/143750000000000000000000000000000 : ℝ)*base79 + (120673404817/44921875000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (6700697/10000000000000000000000 : ℝ)*base90 + (6700697/10000000000000000000000 : ℝ)*base92 + (6700697/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1476701490422558311441/575000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20900763/3125000000000 : ℝ)*(base19) + (536865817/100000000000000 : ℝ)*(base23) + (114568179/50000000000000 : ℝ)*(lower1) + (41453577/50000000000000 : ℝ)*(upper3) + (3353709/10000000000000 : ℝ)*(lower4) + (104790653/100000000000000 : ℝ)*(upper5) + (226689417491603/5000000000000 : ℝ)*(major0) + (226689417491603/5000000000000 : ℝ)*(major1) + (226689417491603/5000000000000 : ℝ)*(major2) + (6061335361/100000000000000 : ℝ)*(sp1) + (6185962679692129/100000000000000 : ℝ)*(sp4) + (96655561711443/1562500000000 : ℝ)*(sp5) + (773245267853289/12500000000000 : ℝ)*(sp6) + (28816139343661/1000000000000 : ℝ)*(sp7) + (28816139343661/1000000000000 : ℝ)*(f.failure) + (6185962679692129/100000000000000 : ℝ)*(f.sum) + (7321322415209/1725000000000000000000000000 : ℝ)*base65 + (190998078838979807/86250000000000000000000000000000 : ℝ)*base68 + (447425333513520193/86250000000000000000000000000000 : ℝ)*base69 + (410494849051020193/86250000000000000000000000000000 : ℝ)*base71 + (1278452882191/1725000000000000000000000000 : ℝ)*base74 + (152520097307729807/86250000000000000000000000000000 : ℝ)*base76 + (385669081903979807/86250000000000000000000000000000 : ℝ)*base78 + (699747881221020193/86250000000000000000000000000000 : ℝ)*base79 + (858738102217/862500000000000000000000000 : ℝ)*base81 + (849543/100000000000000000000 : ℝ)*base90 + (849543/100000000000000000000 : ℝ)*base92 + (849543/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1408_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157335037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7373/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (353/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11297/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2949/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1408_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1408_box_0 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1826108147/10000000000 : ℝ)*x 0 + (5387152457/10000000000 : ℝ)*x 1 + (5387152133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1826108147/10000000000 : ℝ)^273 ≤ (10849033903351/100000000000000 : ℝ)^209 := by
    have hnat : (1826108147 : ℕ)^273*100000000000000^209 ≤ 10849033903351^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1826108147 10000000000 10849033903351 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5387152457/10000000000 : ℝ)^273 ≤ (44575484788651/100000000000000 : ℝ)^209 := by
    have hnat : (5387152457 : ℕ)^273*100000000000000^209 ≤ 44575484788651^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387152457 10000000000 44575484788651 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5387152133/10000000000 : ℝ)^273 ≤ (11143870321699/25000000000000 : ℝ)^209 := by
    have hnat : (5387152133 : ℕ)^273*25000000000000^209 ≤ 11143870321699^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387152133 10000000000 11143870321699 25000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1826108147/10000000000 : ℝ), (5387152457/10000000000 : ℝ), (5387152133/10000000000 : ℝ)] ![(10849033903351/100000000000000 : ℝ), (44575484788651/100000000000000 : ℝ), (11143870321699/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1826108147/10000000000 : ℝ)|^273 ≤ (10849033903351/100000000000000 : ℝ)^209
        have hw : |(-1826108147/10000000000 : ℝ)|=(1826108147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5387152457/10000000000 : ℝ)|^273 ≤ (44575484788651/100000000000000 : ℝ)^209
        have hw : |(5387152457/10000000000 : ℝ)|=(5387152457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5387152133/10000000000 : ℝ)|^273 ≤ (11143870321699/25000000000000 : ℝ)^209
        have hw : |(5387152133/10000000000 : ℝ)|=(5387152133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_box_1 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5285900053/10000000000 : ℝ)*x 0 + (-491281881/2500000000 : ℝ)*x 1 + (2693575793/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285900053/10000000000 : ℝ)^273 ≤ (8696858424681/20000000000000 : ℝ)^209 := by
    have hnat : (5285900053 : ℕ)^273*20000000000000^209 ≤ 8696858424681^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285900053 10000000000 8696858424681 20000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (491281881/2500000000 : ℝ)^273 ≤ (1194023248333/10000000000000 : ℝ)^209 := by
    have hnat : (491281881 : ℕ)^273*10000000000000^209 ≤ 1194023248333^209*2500000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      491281881 2500000000 1194023248333 10000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693575793/5000000000 : ℝ)^273 ≤ (44575475374713/100000000000000 : ℝ)^209 := by
    have hnat : (2693575793 : ℕ)^273*100000000000000^209 ≤ 44575475374713^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693575793 5000000000 44575475374713 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285900053/10000000000 : ℝ), (-491281881/2500000000 : ℝ), (2693575793/5000000000 : ℝ)] ![(8696858424681/20000000000000 : ℝ), (1194023248333/10000000000000 : ℝ), (44575475374713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285900053/10000000000 : ℝ)|^273 ≤ (8696858424681/20000000000000 : ℝ)^209
        have hw : |(5285900053/10000000000 : ℝ)|=(5285900053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-491281881/2500000000 : ℝ)|^273 ≤ (1194023248333/10000000000000 : ℝ)^209
        have hw : |(-491281881/2500000000 : ℝ)|=(491281881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693575793/5000000000 : ℝ)|^273 ≤ (44575475374713/100000000000000 : ℝ)^209
        have hw : |(2693575793/5000000000 : ℝ)|=(2693575793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_box_2 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1321475201/2500000000 : ℝ)*x 0 + (1346787959/2500000000 : ℝ)*x 1 + (-1965126167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321475201/2500000000 : ℝ)^273 ≤ (8696860038667/20000000000000 : ℝ)^209 := by
    have hnat : (1321475201 : ℕ)^273*20000000000000^209 ≤ 8696860038667^209*2500000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321475201 2500000000 8696860038667 20000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1346787959/2500000000 : ℝ)^273 ≤ (22287739038381/50000000000000 : ℝ)^209 := by
    have hnat : (1346787959 : ℕ)^273*50000000000000^209 ≤ 22287739038381^209*2500000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346787959 2500000000 22287739038381 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1965126167/10000000000 : ℝ)^273 ≤ (2985055428317/25000000000000 : ℝ)^209 := by
    have hnat : (1965126167 : ℕ)^273*25000000000000^209 ≤ 2985055428317^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1965126167 10000000000 2985055428317 25000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321475201/2500000000 : ℝ), (1346787959/2500000000 : ℝ), (-1965126167/10000000000 : ℝ)] ![(8696860038667/20000000000000 : ℝ), (22287739038381/50000000000000 : ℝ), (2985055428317/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321475201/2500000000 : ℝ)|^273 ≤ (8696860038667/20000000000000 : ℝ)^209
        have hw : |(1321475201/2500000000 : ℝ)|=(1321475201/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1346787959/2500000000 : ℝ)|^273 ≤ (22287739038381/50000000000000 : ℝ)^209
        have hw : |(1346787959/2500000000 : ℝ)|=(1346787959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1965126167/10000000000 : ℝ)|^273 ≤ (2985055428317/25000000000000 : ℝ)^209
        have hw : |(-1965126167/10000000000 : ℝ)|=(1965126167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_box_3 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4456376819/10000000000 : ℝ)*x 0 + (424004277/1000000000 : ℝ)*x 1 + (2120021753/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4456376819/10000000000 : ℝ)^273 ≤ (6958619791401/20000000000000 : ℝ)^209 := by
    have hnat : (4456376819 : ℕ)^273*20000000000000^209 ≤ 6958619791401^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4456376819 10000000000 6958619791401 20000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (424004277/1000000000 : ℝ)^273 ≤ (8150861704381/25000000000000 : ℝ)^209 := by
    have hnat : (424004277 : ℕ)^273*25000000000000^209 ≤ 8150861704381^209*1000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424004277 1000000000 8150861704381 25000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2120021753/5000000000 : ℝ)^273 ≤ (32603454209959/100000000000000 : ℝ)^209 := by
    have hnat : (2120021753 : ℕ)^273*100000000000000^209 ≤ 32603454209959^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120021753 5000000000 32603454209959 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4456376819/10000000000 : ℝ), (424004277/1000000000 : ℝ), (2120021753/5000000000 : ℝ)] ![(6958619791401/20000000000000 : ℝ), (8150861704381/25000000000000 : ℝ), (32603454209959/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4456376819/10000000000 : ℝ)|^273 ≤ (6958619791401/20000000000000 : ℝ)^209
        have hw : |(4456376819/10000000000 : ℝ)|=(4456376819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(424004277/1000000000 : ℝ)|^273 ≤ (8150861704381/25000000000000 : ℝ)^209
        have hw : |(424004277/1000000000 : ℝ)|=(424004277/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2120021753/5000000000 : ℝ)|^273 ≤ (32603454209959/100000000000000 : ℝ)^209
        have hw : |(2120021753/5000000000 : ℝ)|=(2120021753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_box_4 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-2153230179/10000000000 : ℝ)*x 0 + (1316549943/2500000000 : ℝ)*x 1 + (5266199799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2153230179/10000000000 : ℝ)^273 ≤ (2690911099371/20000000000000 : ℝ)^209 := by
    have hnat : (2153230179 : ℕ)^273*20000000000000^209 ≤ 2690911099371^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153230179 10000000000 2690911099371 20000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316549943/2500000000 : ℝ)^273 ≤ (1730908884049/4000000000000 : ℝ)^209 := by
    have hnat : (1316549943 : ℕ)^273*4000000000000^209 ≤ 1730908884049^209*2500000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316549943 2500000000 1730908884049 4000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266199799/10000000000 : ℝ)^273 ≤ (2704545149439/6250000000000 : ℝ)^209 := by
    have hnat : (5266199799 : ℕ)^273*6250000000000^209 ≤ 2704545149439^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266199799 10000000000 2704545149439 6250000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2153230179/10000000000 : ℝ), (1316549943/2500000000 : ℝ), (5266199799/10000000000 : ℝ)] ![(2690911099371/20000000000000 : ℝ), (1730908884049/4000000000000 : ℝ), (2704545149439/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2153230179/10000000000 : ℝ)|^273 ≤ (2690911099371/20000000000000 : ℝ)^209
        have hw : |(-2153230179/10000000000 : ℝ)|=(2153230179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316549943/2500000000 : ℝ)|^273 ≤ (1730908884049/4000000000000 : ℝ)^209
        have hw : |(1316549943/2500000000 : ℝ)|=(1316549943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266199799/10000000000 : ℝ)|^273 ≤ (2704545149439/6250000000000 : ℝ)^209
        have hw : |(5266199799/10000000000 : ℝ)|=(5266199799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_box_5 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (53706211/100000000 : ℝ)*x 0 + (-40281987/200000000 : ℝ)*x 1 + (2633100021/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53706211/100000000 : ℝ)^273 ≤ (44396894667803/100000000000000 : ℝ)^209 := by
    have hnat : (53706211 : ℕ)^273*100000000000000^209 ≤ 44396894667803^209*100000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53706211 100000000 44396894667803 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40281987/200000000 : ℝ)^273 ≤ (12330380330971/100000000000000 : ℝ)^209 := by
    have hnat : (40281987 : ℕ)^273*100000000000000^209 ≤ 12330380330971^209*200000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40281987 200000000 12330380330971 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633100021/5000000000 : ℝ)^273 ≤ (2704545312451/6250000000000 : ℝ)^209 := by
    have hnat : (2633100021 : ℕ)^273*6250000000000^209 ≤ 2704545312451^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633100021 5000000000 2704545312451 6250000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53706211/100000000 : ℝ), (-40281987/200000000 : ℝ), (2633100021/5000000000 : ℝ)] ![(44396894667803/100000000000000 : ℝ), (12330380330971/100000000000000 : ℝ), (2704545312451/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53706211/100000000 : ℝ)|^273 ≤ (44396894667803/100000000000000 : ℝ)^209
        have hw : |(53706211/100000000 : ℝ)|=(53706211/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-40281987/200000000 : ℝ)|^273 ≤ (12330380330971/100000000000000 : ℝ)^209
        have hw : |(-40281987/200000000 : ℝ)|=(40281987/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633100021/5000000000 : ℝ)|^273 ≤ (2704545312451/6250000000000 : ℝ)^209
        have hw : |(2633100021/5000000000 : ℝ)|=(2633100021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_box_6 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (537062113/1000000000 : ℝ)*x 0 + (2633099833/5000000000 : ℝ)*x 1 + (-503524953/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537062113/1000000000 : ℝ)^273 ≤ (346850742123/781250000000 : ℝ)^209 := by
    have hnat : (537062113 : ℕ)^273*781250000000^209 ≤ 346850742123^209*1000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537062113 1000000000 346850742123 781250000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633099833/5000000000 : ℝ)^273 ≤ (8654544192699/20000000000000 : ℝ)^209 := by
    have hnat : (2633099833 : ℕ)^273*20000000000000^209 ≤ 8654544192699^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633099833 5000000000 8654544192699 20000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (503524953/2500000000 : ℝ)^273 ≤ (770649001591/6250000000000 : ℝ)^209 := by
    have hnat : (503524953 : ℕ)^273*6250000000000^209 ≤ 770649001591^209*2500000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503524953 2500000000 770649001591 6250000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537062113/1000000000 : ℝ), (2633099833/5000000000 : ℝ), (-503524953/2500000000 : ℝ)] ![(346850742123/781250000000 : ℝ), (8654544192699/20000000000000 : ℝ), (770649001591/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537062113/1000000000 : ℝ)|^273 ≤ (346850742123/781250000000 : ℝ)^209
        have hw : |(537062113/1000000000 : ℝ)|=(537062113/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633099833/5000000000 : ℝ)|^273 ≤ (8654544192699/20000000000000 : ℝ)^209
        have hw : |(2633099833/5000000000 : ℝ)|=(2633099833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-503524953/2500000000 : ℝ)|^273 ≤ (770649001591/6250000000000 : ℝ)^209
        have hw : |(-503524953/2500000000 : ℝ)|=(503524953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_box_7 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1040477989/2500000000 : ℝ)*x 0 + (4387224047/10000000000 : ℝ)*x 1 + (4387224079/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1040477989/2500000000 : ℝ)^273 ≤ (3182091917891/10000000000000 : ℝ)^209 := by
    have hnat : (1040477989 : ℕ)^273*10000000000000^209 ≤ 3182091917891^209*2500000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040477989 2500000000 3182091917891 10000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4387224047/10000000000 : ℝ)^273 ≤ (34089540239941/100000000000000 : ℝ)^209 := by
    have hnat : (4387224047 : ℕ)^273*100000000000000^209 ≤ 34089540239941^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4387224047 10000000000 34089540239941 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4387224079/10000000000 : ℝ)^273 ≤ (4261192570591/12500000000000 : ℝ)^209 := by
    have hnat : (4387224079 : ℕ)^273*12500000000000^209 ≤ 4261192570591^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4387224079 10000000000 4261192570591 12500000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1040477989/2500000000 : ℝ), (4387224047/10000000000 : ℝ), (4387224079/10000000000 : ℝ)] ![(3182091917891/10000000000000 : ℝ), (34089540239941/100000000000000 : ℝ), (4261192570591/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1040477989/2500000000 : ℝ)|^273 ≤ (3182091917891/10000000000000 : ℝ)^209
        have hw : |(1040477989/2500000000 : ℝ)|=(1040477989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4387224047/10000000000 : ℝ)|^273 ≤ (34089540239941/100000000000000 : ℝ)^209
        have hw : |(4387224047/10000000000 : ℝ)|=(4387224047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4387224079/10000000000 : ℝ)|^273 ≤ (4261192570591/12500000000000 : ℝ)^209
        have hw : |(4387224079/10000000000 : ℝ)|=(4387224079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_box_8 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-2084376281/10000000000 : ℝ)*x 0 + (1295657883/2500000000 : ℝ)*x 1 + (1080227717/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2084376281/10000000000 : ℝ)^273 ≤ (161191797613/1250000000000 : ℝ)^209 := by
    have hnat : (2084376281 : ℕ)^273*1250000000000^209 ≤ 161191797613^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084376281 10000000000 161191797613 1250000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1295657883/2500000000 : ℝ)^273 ≤ (42377946532937/100000000000000 : ℝ)^209 := by
    have hnat : (1295657883 : ℕ)^273*100000000000000^209 ≤ 42377946532937^209*2500000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295657883 2500000000 42377946532937 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1080227717/2000000000 : ℝ)^273 ≤ (4472670963937/10000000000000 : ℝ)^209 := by
    have hnat : (1080227717 : ℕ)^273*10000000000000^209 ≤ 4472670963937^209*2000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080227717 2000000000 4472670963937 10000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2084376281/10000000000 : ℝ), (1295657883/2500000000 : ℝ), (1080227717/2000000000 : ℝ)] ![(161191797613/1250000000000 : ℝ), (42377946532937/100000000000000 : ℝ), (4472670963937/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2084376281/10000000000 : ℝ)|^273 ≤ (161191797613/1250000000000 : ℝ)^209
        have hw : |(-2084376281/10000000000 : ℝ)|=(2084376281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1295657883/2500000000 : ℝ)|^273 ≤ (42377946532937/100000000000000 : ℝ)^209
        have hw : |(1295657883/2500000000 : ℝ)|=(1295657883/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1080227717/2000000000 : ℝ)|^273 ≤ (4472670963937/10000000000000 : ℝ)^209
        have hw : |(1080227717/2000000000 : ℝ)|=(1080227717/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_box_9 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1055219861/2000000000 : ℝ)*x 0 + (-1959336349/10000000000 : ℝ)*x 1 + (2700568943/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055219861/2000000000 : ℝ)^273 ≤ (43379007322431/100000000000000 : ℝ)^209 := by
    have hnat : (1055219861 : ℕ)^273*100000000000000^209 ≤ 43379007322431^209*2000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055219861 2000000000 43379007322431 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1959336349/10000000000 : ℝ)^273 ≤ (11894290582751/100000000000000 : ℝ)^209 := by
    have hnat : (1959336349 : ℕ)^273*100000000000000^209 ≤ 11894290582751^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1959336349 10000000000 11894290582751 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2700568943/5000000000 : ℝ)^273 ≤ (44726702078441/100000000000000 : ℝ)^209 := by
    have hnat : (2700568943 : ℕ)^273*100000000000000^209 ≤ 44726702078441^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700568943 5000000000 44726702078441 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055219861/2000000000 : ℝ), (-1959336349/10000000000 : ℝ), (2700568943/5000000000 : ℝ)] ![(43379007322431/100000000000000 : ℝ), (11894290582751/100000000000000 : ℝ), (44726702078441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055219861/2000000000 : ℝ)|^273 ≤ (43379007322431/100000000000000 : ℝ)^209
        have hw : |(1055219861/2000000000 : ℝ)|=(1055219861/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1959336349/10000000000 : ℝ)|^273 ≤ (11894290582751/100000000000000 : ℝ)^209
        have hw : |(-1959336349/10000000000 : ℝ)|=(1959336349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2700568943/5000000000 : ℝ)|^273 ≤ (44726702078441/100000000000000 : ℝ)^209
        have hw : |(2700568943/5000000000 : ℝ)|=(2700568943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_box_10 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5276098833/10000000000 : ℝ)*x 0 + (2700568959/5000000000 : ℝ)*x 1 + (-391867389/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276098833/10000000000 : ℝ)^273 ≤ (43379002253399/100000000000000 : ℝ)^209 := by
    have hnat : (5276098833 : ℕ)^273*100000000000000^209 ≤ 43379002253399^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276098833 10000000000 43379002253399 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2700568959/5000000000 : ℝ)^273 ≤ (22363351212289/50000000000000 : ℝ)^209 := by
    have hnat : (2700568959 : ℕ)^273*50000000000000^209 ≤ 22363351212289^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700568959 5000000000 22363351212289 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (391867389/2000000000 : ℝ)^273 ≤ (5947147654367/50000000000000 : ℝ)^209 := by
    have hnat : (391867389 : ℕ)^273*50000000000000^209 ≤ 5947147654367^209*2000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      391867389 2000000000 5947147654367 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276098833/10000000000 : ℝ), (2700568959/5000000000 : ℝ), (-391867389/2000000000 : ℝ)] ![(43379002253399/100000000000000 : ℝ), (22363351212289/50000000000000 : ℝ), (5947147654367/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276098833/10000000000 : ℝ)|^273 ≤ (43379002253399/100000000000000 : ℝ)^209
        have hw : |(5276098833/10000000000 : ℝ)|=(5276098833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2700568959/5000000000 : ℝ)|^273 ≤ (22363351212289/50000000000000 : ℝ)^209
        have hw : |(2700568959/5000000000 : ℝ)|=(2700568959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-391867389/2000000000 : ℝ)|^273 ≤ (5947147654367/50000000000000 : ℝ)^209
        have hw : |(-391867389/2000000000 : ℝ)|=(391867389/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_box_11 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4489869053/10000000000 : ℝ)*x 0 + (2111504813/5000000000 : ℝ)*x 1 + (2111505053/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4489869053/10000000000 : ℝ)^273 ≤ (35135054996469/100000000000000 : ℝ)^209 := by
    have hnat : (4489869053 : ℕ)^273*100000000000000^209 ≤ 35135054996469^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489869053 10000000000 35135054996469 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2111504813/5000000000 : ℝ)^273 ≤ (32432470089143/100000000000000 : ℝ)^209 := by
    have hnat : (2111504813 : ℕ)^273*100000000000000^209 ≤ 32432470089143^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111504813 5000000000 32432470089143 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2111505053/5000000000 : ℝ)^273 ≤ (32432474904357/100000000000000 : ℝ)^209 := by
    have hnat : (2111505053 : ℕ)^273*100000000000000^209 ≤ 32432474904357^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111505053 5000000000 32432474904357 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4489869053/10000000000 : ℝ), (2111504813/5000000000 : ℝ), (2111505053/5000000000 : ℝ)] ![(35135054996469/100000000000000 : ℝ), (32432470089143/100000000000000 : ℝ), (32432474904357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4489869053/10000000000 : ℝ)|^273 ≤ (35135054996469/100000000000000 : ℝ)^209
        have hw : |(4489869053/10000000000 : ℝ)|=(4489869053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2111504813/5000000000 : ℝ)|^273 ≤ (32432470089143/100000000000000 : ℝ)^209
        have hw : |(2111504813/5000000000 : ℝ)|=(2111504813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2111505053/5000000000 : ℝ)|^273 ≤ (32432474904357/100000000000000 : ℝ)^209
        have hw : |(2111505053/5000000000 : ℝ)|=(2111505053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_box_12 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-379035907/2000000000 : ℝ)*x 0 + (5468654427/10000000000 : ℝ)*x 1 + (656885637/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (379035907/2000000000 : ℝ)^273 ≤ (113881290927/1000000000000 : ℝ)^209 := by
    have hnat : (379035907 : ℕ)^273*1000000000000^209 ≤ 113881290927^209*2000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      379035907 2000000000 113881290927 1000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5468654427/10000000000 : ℝ)^273 ≤ (22729203681383/50000000000000 : ℝ)^209 := by
    have hnat : (5468654427 : ℕ)^273*50000000000000^209 ≤ 22729203681383^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5468654427 10000000000 22729203681383 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (656885637/1250000000 : ℝ)^273 ≤ (2157673176243/5000000000000 : ℝ)^209 := by
    have hnat : (656885637 : ℕ)^273*5000000000000^209 ≤ 2157673176243^209*1250000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656885637 1250000000 2157673176243 5000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-379035907/2000000000 : ℝ), (5468654427/10000000000 : ℝ), (656885637/1250000000 : ℝ)] ![(113881290927/1000000000000 : ℝ), (22729203681383/50000000000000 : ℝ), (2157673176243/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-379035907/2000000000 : ℝ)|^273 ≤ (113881290927/1000000000000 : ℝ)^209
        have hw : |(-379035907/2000000000 : ℝ)|=(379035907/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5468654427/10000000000 : ℝ)|^273 ≤ (22729203681383/50000000000000 : ℝ)^209
        have hw : |(5468654427/10000000000 : ℝ)|=(5468654427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(656885637/1250000000 : ℝ)|^273 ≤ (2157673176243/5000000000000 : ℝ)^209
        have hw : |(656885637/1250000000 : ℝ)|=(656885637/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_box_13 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5378404469/10000000000 : ℝ)*x 0 + (-1009249437/5000000000 : ℝ)*x 1 + (5255085493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378404469/10000000000 : ℝ)^273 ≤ (22240479172813/50000000000000 : ℝ)^209 := by
    have hnat : (5378404469 : ℕ)^273*50000000000000^209 ≤ 22240479172813^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378404469 10000000000 22240479172813 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1009249437/5000000000 : ℝ)^273 ≤ (6182786928739/50000000000000 : ℝ)^209 := by
    have hnat : (1009249437 : ℕ)^273*50000000000000^209 ≤ 6182786928739^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1009249437 5000000000 6182786928739 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255085493/10000000000 : ℝ)^273 ≤ (5394183472903/12500000000000 : ℝ)^209 := by
    have hnat : (5255085493 : ℕ)^273*12500000000000^209 ≤ 5394183472903^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255085493 10000000000 5394183472903 12500000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378404469/10000000000 : ℝ), (-1009249437/5000000000 : ℝ), (5255085493/10000000000 : ℝ)] ![(22240479172813/50000000000000 : ℝ), (6182786928739/50000000000000 : ℝ), (5394183472903/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378404469/10000000000 : ℝ)|^273 ≤ (22240479172813/50000000000000 : ℝ)^209
        have hw : |(5378404469/10000000000 : ℝ)|=(5378404469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1009249437/5000000000 : ℝ)|^273 ≤ (6182786928739/50000000000000 : ℝ)^209
        have hw : |(-1009249437/5000000000 : ℝ)|=(1009249437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255085493/10000000000 : ℝ)|^273 ≤ (5394183472903/12500000000000 : ℝ)^209
        have hw : |(5255085493/10000000000 : ℝ)|=(5255085493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_box_14 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1075681073/2000000000 : ℝ)*x 0 + (656885601/1250000000 : ℝ)*x 1 + (-2018498583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075681073/2000000000 : ℝ)^273 ≤ (889619360499/2000000000000 : ℝ)^209 := by
    have hnat : (1075681073 : ℕ)^273*2000000000000^209 ≤ 889619360499^209*2000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075681073 2000000000 889619360499 2000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (656885601/1250000000 : ℝ)^273 ≤ (43153460435669/100000000000000 : ℝ)^209 := by
    have hnat : (656885601 : ℕ)^273*100000000000000^209 ≤ 43153460435669^209*1250000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656885601 1250000000 43153460435669 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2018498583/10000000000 : ℝ)^273 ≤ (12365571528877/100000000000000 : ℝ)^209 := by
    have hnat : (2018498583 : ℕ)^273*100000000000000^209 ≤ 12365571528877^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2018498583 10000000000 12365571528877 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075681073/2000000000 : ℝ), (656885601/1250000000 : ℝ), (-2018498583/10000000000 : ℝ)] ![(889619360499/2000000000000 : ℝ), (43153460435669/100000000000000 : ℝ), (12365571528877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075681073/2000000000 : ℝ)|^273 ≤ (889619360499/2000000000000 : ℝ)^209
        have hw : |(1075681073/2000000000 : ℝ)|=(1075681073/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(656885601/1250000000 : ℝ)|^273 ≤ (43153460435669/100000000000000 : ℝ)^209
        have hw : |(656885601/1250000000 : ℝ)|=(656885601/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2018498583/10000000000 : ℝ)|^273 ≤ (12365571528877/100000000000000 : ℝ)^209
        have hw : |(-2018498583/10000000000 : ℝ)|=(2018498583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_box_15 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (826880611/2000000000 : ℝ)*x 0 + (2200368941/5000000000 : ℝ)*x 1 + (2200369209/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (826880611/2000000000 : ℝ)^273 ≤ (31546465518931/100000000000000 : ℝ)^209 := by
    have hnat : (826880611 : ℕ)^273*100000000000000^209 ≤ 31546465518931^209*2000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      826880611 2000000000 31546465518931 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2200368941/5000000000 : ℝ)^273 ≤ (8556691127679/25000000000000 : ℝ)^209 := by
    have hnat : (2200368941 : ℕ)^273*25000000000000^209 ≤ 8556691127679^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2200368941 5000000000 8556691127679 25000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2200369209/5000000000 : ℝ)^273 ≤ (8556692489003/25000000000000 : ℝ)^209 := by
    have hnat : (2200369209 : ℕ)^273*25000000000000^209 ≤ 8556692489003^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2200369209 5000000000 8556692489003 25000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(826880611/2000000000 : ℝ), (2200368941/5000000000 : ℝ), (2200369209/5000000000 : ℝ)] ![(31546465518931/100000000000000 : ℝ), (8556691127679/25000000000000 : ℝ), (8556692489003/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(826880611/2000000000 : ℝ)|^273 ≤ (31546465518931/100000000000000 : ℝ)^209
        have hw : |(826880611/2000000000 : ℝ)|=(826880611/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2200368941/5000000000 : ℝ)|^273 ≤ (8556691127679/25000000000000 : ℝ)^209
        have hw : |(2200368941/5000000000 : ℝ)|=(2200368941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2200369209/5000000000 : ℝ)|^273 ≤ (8556692489003/25000000000000 : ℝ)^209
        have hw : |(2200369209/5000000000 : ℝ)|=(2200369209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1408_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157335037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2949/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11297/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62887/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59071/100000 : ℝ) ∧ (20083/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (42303/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2949/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11297/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2949/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11297/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2949/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11297/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2949/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11297/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2949/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11297/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2949/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11297/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11297/100000 : ℝ) ^ (4367/1024 : ℝ) ≤ (9145778662614313/100000000000000000000 : ℝ) := by
    have hpowers : (11297/100000 : ℝ)^4367 ≤ (9145778662614313/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11297 : ℕ)^4367*100000000000000000000^1024 ≤ 9145778662614313^1024*100000^4367 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11297 100000 9145778662614313 100000000000000000000 4367 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11297/100000 : ℝ)) (X := (9145778662614313/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4367 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2949/20000 : ℝ) ^ (4367/1024 : ℝ) ≤ (14240729956098461/50000000000000000000 : ℝ) := by
    have hpowers : (2949/20000 : ℝ)^4367 ≤ (14240729956098461/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2949 : ℕ)^4367*50000000000000000000^1024 ≤ 14240729956098461^1024*20000^4367 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2949 20000 14240729956098461 50000000000000000000 4367 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2949/20000 : ℝ)) (X := (14240729956098461/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4367 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009145778662614313/50000000000000000000 : ℝ) ≤ (10000428881233671/10000000000000000 : ℝ) ^ (4367/1024 : ℝ) := by
    have hpowers : (50009145778662614313/50000000000000000000 : ℝ)^1024 ≤ (10000428881233671/10000000000000000 : ℝ)^4367 := by
      have hnat : (50009145778662614313 : ℕ)^1024*10000000000000000^4367 ≤ 10000428881233671^4367*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009145778662614313 50000000000000000000 10000428881233671 10000000000000000 1024 4367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000428881233671/10000000000000000 : ℝ)) (X := (50009145778662614313/50000000000000000000 : ℝ)) (by norm_num) 4367 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20007525447714962247/20000000000000000000 : ℝ) ≤ (5000441089356097/5000000000000000 : ℝ) ^ (4367/1024 : ℝ) := by
    have hpowers : (20007525447714962247/20000000000000000000 : ℝ)^1024 ≤ (5000441089356097/5000000000000000 : ℝ)^4367 := by
      have hnat : (20007525447714962247 : ℕ)^1024*5000000000000000^4367 ≤ 5000441089356097^4367*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20007525447714962247 20000000000000000000 5000441089356097 5000000000000000 1024 4367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000441089356097/5000000000000000 : ℝ)) (X := (20007525447714962247/20000000000000000000 : ℝ)) (by norm_num) 4367 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014240729956098461/25000000000000000000 : ℝ) ≤ (10001335476190717/10000000000000000 : ℝ) ^ (4367/1024 : ℝ) := by
    have hpowers : (25014240729956098461/25000000000000000000 : ℝ)^1024 ≤ (10001335476190717/10000000000000000 : ℝ)^4367 := by
      have hnat : (25014240729956098461 : ℕ)^1024*10000000000000000^4367 ≤ 10001335476190717^4367*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014240729956098461 25000000000000000000 10001335476190717 10000000000000000 1024 4367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001335476190717/10000000000000000 : ℝ)) (X := (25014240729956098461/25000000000000000000 : ℝ)) (by norm_num) 4367 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9145778662614313/100000000000000000000 : ℝ) ≤ ((17235618489631974473/17240000000000000000 : ℝ)+2*(453297478523/344800000000000 : ℝ)*(11297/100000 : ℝ))^(4367/1024 : ℝ) := by
    rw [show (17235618489631974473/17240000000000000000 : ℝ)+2*(453297478523/344800000000000 : ℝ)*(11297/100000 : ℝ)=(10000428881233671/10000000000000000 : ℝ) by norm_num, show 1+2*(9145778662614313/100000000000000000000 : ℝ)=(50009145778662614313/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14240729956098461/50000000000000000000 : ℝ)+(9145778662614313/100000000000000000000 : ℝ) ≤ ((17235618489631974473/17240000000000000000 : ℝ)+(453297478523/344800000000000 : ℝ)*((2949/20000 : ℝ)+(11297/100000 : ℝ)))^(4367/1024 : ℝ) := by
    rw [show (17235618489631974473/17240000000000000000 : ℝ)+(453297478523/344800000000000 : ℝ)*((2949/20000 : ℝ)+(11297/100000 : ℝ))=(5000441089356097/5000000000000000 : ℝ) by norm_num, show 1+(14240729956098461/50000000000000000000 : ℝ)+(9145778662614313/100000000000000000000 : ℝ)=(20007525447714962247/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14240729956098461/50000000000000000000 : ℝ) ≤ ((17235618489631974473/17240000000000000000 : ℝ)+2*(453297478523/344800000000000 : ℝ)*(2949/20000 : ℝ))^(4367/1024 : ℝ) := by
    rw [show (17235618489631974473/17240000000000000000 : ℝ)+2*(453297478523/344800000000000 : ℝ)*(2949/20000 : ℝ)=(10001335476190717/10000000000000000 : ℝ) by norm_num, show 1+2*(14240729956098461/50000000000000000000 : ℝ)=(25014240729956098461/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17235618489631974473/17240000000000000000 : ℝ)*(X 1 0+X 2 0)+(453297478523/344800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4367/1024 : ℝ)) (lo := (11297/100000 : ℝ)) (hi := (2949/20000 : ℝ)) (c := (17235618489631974473/17240000000000000000 : ℝ)) (alpha := (453297478523/344800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17235618489631974473/17240000000000000000 : ℝ)*(X 0 1+X 2 1)+(453297478523/344800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4367/1024 : ℝ)) (lo := (11297/100000 : ℝ)) (hi := (2949/20000 : ℝ)) (c := (17235618489631974473/17240000000000000000 : ℝ)) (alpha := (453297478523/344800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17235618489631974473/17240000000000000000 : ℝ)*(X 0 2+X 1 2)+(453297478523/344800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4367/1024 : ℝ)) (lo := (11297/100000 : ℝ)) (hi := (2949/20000 : ℝ)) (c := (17235618489631974473/17240000000000000000 : ℝ)) (alpha := (453297478523/344800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1826108147/10000000000 : ℝ)*X 0 0+(5387152457/10000000000 : ℝ)*X 0 1+(5387152133/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5285900053/10000000000 : ℝ)*X 1 0+(-491281881/2500000000 : ℝ)*X 1 1+(2693575793/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1321475201/2500000000 : ℝ)*X 2 0+(1346787959/2500000000 : ℝ)*X 2 1+(-1965126167/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4456376819/10000000000 : ℝ)*X 0 0+(424004277/1000000000 : ℝ)*X 0 1+(2120021753/5000000000 : ℝ)*X 0 2+(4456376819/10000000000 : ℝ)*X 1 0+(424004277/1000000000 : ℝ)*X 1 1+(2120021753/5000000000 : ℝ)*X 1 2+(4456376819/10000000000 : ℝ)*X 2 0+(424004277/1000000000 : ℝ)*X 2 1+(2120021753/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2153230179/10000000000 : ℝ)*X 0 0+(1316549943/2500000000 : ℝ)*X 0 1+(5266199799/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((53706211/100000000 : ℝ)*X 1 0+(-40281987/200000000 : ℝ)*X 1 1+(2633100021/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((537062113/1000000000 : ℝ)*X 2 0+(2633099833/5000000000 : ℝ)*X 2 1+(-503524953/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1040477989/2500000000 : ℝ)*X 0 0+(4387224047/10000000000 : ℝ)*X 0 1+(4387224079/10000000000 : ℝ)*X 0 2+(1040477989/2500000000 : ℝ)*X 1 0+(4387224047/10000000000 : ℝ)*X 1 1+(4387224079/10000000000 : ℝ)*X 1 2+(1040477989/2500000000 : ℝ)*X 2 0+(4387224047/10000000000 : ℝ)*X 2 1+(4387224079/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2084376281/10000000000 : ℝ)*X 0 0+(1295657883/2500000000 : ℝ)*X 0 1+(1080227717/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1055219861/2000000000 : ℝ)*X 1 0+(-1959336349/10000000000 : ℝ)*X 1 1+(2700568943/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5276098833/10000000000 : ℝ)*X 2 0+(2700568959/5000000000 : ℝ)*X 2 1+(-391867389/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4489869053/10000000000 : ℝ)*X 0 0+(2111504813/5000000000 : ℝ)*X 0 1+(2111505053/5000000000 : ℝ)*X 0 2+(4489869053/10000000000 : ℝ)*X 1 0+(2111504813/5000000000 : ℝ)*X 1 1+(2111505053/5000000000 : ℝ)*X 1 2+(4489869053/10000000000 : ℝ)*X 2 0+(2111504813/5000000000 : ℝ)*X 2 1+(2111505053/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-379035907/2000000000 : ℝ)*X 0 0+(5468654427/10000000000 : ℝ)*X 0 1+(656885637/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5378404469/10000000000 : ℝ)*X 1 0+(-1009249437/5000000000 : ℝ)*X 1 1+(5255085493/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1075681073/2000000000 : ℝ)*X 2 0+(656885601/1250000000 : ℝ)*X 2 1+(-2018498583/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((826880611/2000000000 : ℝ)*X 0 0+(2200368941/5000000000 : ℝ)*X 0 1+(2200369209/5000000000 : ℝ)*X 0 2+(826880611/2000000000 : ℝ)*X 1 0+(2200368941/5000000000 : ℝ)*X 1 1+(2200369209/5000000000 : ℝ)*X 1 2+(826880611/2000000000 : ℝ)*X 2 0+(2200368941/5000000000 : ℝ)*X 2 1+(2200369209/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62887/100000 : ℝ) ≤ (-169395087490898617380794217/269375000000000000000000000 : ℝ) := by norm_num
    linear_combination (53317621/50000000000000 : ℝ)*(upper1) + (6641751/5000000000000 : ℝ)*(upper2) + (56193439/100000000000000 : ℝ)*(lower4) + (37570209/100000000000000 : ℝ)*(upper5) + (187119660013237/6250000000000 : ℝ)*(major0) + (187119660013237/6250000000000 : ℝ)*(major1) + (187119660013237/6250000000000 : ℝ)*(major2) + (419033113/6250000000000 : ℝ)*(sp2) + (106503917/12500000000000 : ℝ)*(sp3) + (4105899424671621/100000000000000 : ℝ)*(sp4) + (128303553574813/3125000000000 : ℝ)*(sp5) + (4105892720141813/100000000000000 : ℝ)*(sp6) + (95144516973291/5000000000000 : ℝ)*(sp7) + (92855138803/50000000000000 : ℝ)*(sp13) + (475722797874289/25000000000000 : ℝ)*(f.failure) + (4105899424671621/100000000000000 : ℝ)*(f.sum) + (5595082033573/2155000000000000000000000000 : ℝ)*base66 + (653127784665649101/107750000000000000000000000000000 : ℝ)*base67 + (191752703767399101/107750000000000000000000000000000 : ℝ)*base69 + (146896381340850899/107750000000000000000000000000000 : ℝ)*base72 + (2342548744211/1077500000000000000000000000 : ℝ)*base73 + (369184556777850899/107750000000000000000000000000000 : ℝ)*base76 + (2416077327850899/107750000000000000000000000000000 : ℝ)*base78 + (643204921877149101/107750000000000000000000000000000 : ℝ)*base79 + (341685455391/1077500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (18836307/2500000000000000000000 : ℝ)*base90 + (18836307/2500000000000000000000 : ℝ)*base92 + (18836307/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59071/100000 : ℝ) ≤ (63651858744864074976476361858141/107750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (60348913/12500000000000 : ℝ)*(lower1) + (11497033/25000000000000 : ℝ)*(lower2) + (647900157/100000000000000 : ℝ)*(upper4) + (766198782955761/25000000000000 : ℝ)*(major0) + (766198782955761/25000000000000 : ℝ)*(major1) + (766198782955761/25000000000000 : ℝ)*(major2) + (260122057025291/6250000000000 : ℝ)*(sp0) + (260090309421229/6250000000000 : ℝ)*(sp1) + (416183404386017/10000000000000 : ℝ)*(sp2) + (24349250939043/1250000000000 : ℝ)*(sp3) + (183931679/10000000000000 : ℝ)*(sp7) + (527483179/12500000000000 : ℝ)*(sp8) + (64022691303/12500000000000 : ℝ)*(sp9) + (123088409917/100000000000000 : ℝ)*(sp10) + (194794191444023/10000000000000 : ℝ)*(f.failure) + (520244641533761/12500000000000 : ℝ)*(f.sum) + (26463264093557/4310000000000000000000000000 : ℝ)*base66 + (408753155835561047/431000000000000000000000000000000 : ℝ)*base68 + (1351505808732438953/431000000000000000000000000000000 : ℝ)*base69 + (197656704218438953/431000000000000000000000000000000 : ℝ)*base71 + (5317353496577/4310000000000000000000000000 : ℝ)*base74 + (357479388932438953/431000000000000000000000000000000 : ℝ)*base75 + (1686181565719438953/431000000000000000000000000000000 : ℝ)*base77 + (3319369557554438953/431000000000000000000000000000000 : ℝ)*base79 + (8713336438447/4310000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (2133851/1000000000000000000000 : ℝ)*base89 + (2133851/1000000000000000000000 : ℝ)*base91 + (2133851/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (20083/25000 : ℝ) ≤ (173120753802640531211243467881453/215500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15022581/12500000000000 : ℝ)*(upper0) + (198411579/100000000000000 : ℝ)*(upper1) + (371034297/100000000000000 : ℝ)*(upper2) + (843461924492029/25000000000000 : ℝ)*(major0) + (843461924492029/25000000000000 : ℝ)*(major1) + (843461924492029/25000000000000 : ℝ)*(major2) + (39543241373/25000000000000 : ℝ)*(sp1) + (24633532557/100000000000000 : ℝ)*(sp3) + (2876733109/50000000000000 : ℝ)*(sp4) + (91530436754687/2000000000000 : ℝ)*(sp8) + (1144096891900711/25000000000000 : ℝ)*(sp9) + (286034108785521/6250000000000 : ℝ)*(sp10) + (428869373932337/20000000000000 : ℝ)*(sp11) + (2268670971/12500000000000 : ℝ)*(sp12) + (1072185751597121/50000000000000 : ℝ)*(f.failure) + (286034108785521/6250000000000 : ℝ)*(f.sum) + (22666785493993/4310000000000000000000000000 : ℝ)*base66 + (557083868413674283/431000000000000000000000000000000 : ℝ)*base68 + (4673745793674283/431000000000000000000000000000000 : ℝ)*base70 + (4240559361625674283/431000000000000000000000000000000 : ℝ)*base72 + (6523520905007/4310000000000000000000000000 : ℝ)*base73 + (1078487590709674283/431000000000000000000000000000000 : ℝ)*base76 + (6504152997577674283/431000000000000000000000000000000 : ℝ)*base78 + (2076198974309674283/431000000000000000000000000000000 : ℝ)*base80 + (7506306086247/4310000000000000000000000000 : ℝ)*base81 + (41628477/5000000000000000000000 : ℝ)*base89 + (41628477/5000000000000000000000 : ℝ)*base91 + (41628477/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-42303/50000 : ℝ) ≤ (-364639408534055177386204674012807/431000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (267683197/100000000000000 : ℝ)*(lower1) + (33076013/10000000000000 : ℝ)*(lower2) + (109103/312500000000 : ℝ)*(upper5) + (3411086075441453/100000000000000 : ℝ)*(major0) + (3411086075441453/100000000000000 : ℝ)*(major1) + (3411086075441453/100000000000000 : ℝ)*(major2) + (11430829687/100000000000000 : ℝ)*(sp0) + (104708764143/50000000000000 : ℝ)*(sp5) + (323441338513/100000000000000 : ℝ)*(sp6) + (14623697443/10000000000000 : ℝ)*(sp7) + (2341161024949313/50000000000000 : ℝ)*(sp12) + (4682124063200027/100000000000000 : ℝ)*(sp13) + (23410050196949/500000000000 : ℝ)*(sp14) + (2167893470189749/100000000000000 : ℝ)*(sp15) + (2168039707164179/100000000000000 : ℝ)*(f.failure) + (4682333480728313/100000000000000 : ℝ)*(f.sum) + (231927069428321/17240000000000000000000000000 : ℝ)*base66 + (11619998332761979269/1724000000000000000000000000000000 : ℝ)*base67 + (12546769995441979269/1724000000000000000000000000000000 : ℝ)*base69 + (14300084858685979269/1724000000000000000000000000000000 : ℝ)*base71 + (80877374267281/17240000000000000000000000000 : ℝ)*base74 + (22495894939697979269/1724000000000000000000000000000000 : ℝ)*base75 + (786124401462020731/1724000000000000000000000000000000 : ℝ)*base78 + (15969673094733979269/1724000000000000000000000000000000 : ℝ)*base79 + (77143466398879/17240000000000000000000000000 : ℝ)*base81 + (31960377/10000000000000000000000 : ℝ)*base90 + (31960377/10000000000000000000000 : ℝ)*base92 + (31960377/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1408_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157335037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2949/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11297/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62887/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59071/100000 : ℝ) else (20083/25000 : ℝ) ≤ X j i ∧ X j i ≤ (42303/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1408_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1408_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157335037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (59/400 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2823/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62887/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59071/100000 : ℝ) else (20083/25000 : ℝ) ≤ X j i ∧ X j i ≤ (42303/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1408_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1408_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1408_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157335037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (59/400 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2823/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62887/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59071/100000 : ℝ) else (20083/25000 : ℝ) ≤ X j i ∧ X j i ≤ (42303/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1408_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
