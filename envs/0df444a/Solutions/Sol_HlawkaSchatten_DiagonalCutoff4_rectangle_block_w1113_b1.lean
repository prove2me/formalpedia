-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1113_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:05:51.215879+00:00
-- url     : https://prove2.me/submissions/ef9726c0-815a-48c1-b439-c607fa5e8991

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
theorem support_rectangle_w1113_s3_0 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1088347209/5000000000 : ℝ)*x 0 + (679031117/1250000000 : ℝ)*x 1 + (5229271673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088347209/5000000000 : ℝ)^4153 ≤ (13215522219093/100000000000000 : ℝ)^3129 := by
    have hnat : (1088347209 : ℕ)^4153*100000000000000^3129 ≤ 13215522219093^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088347209 5000000000 13215522219093 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (679031117/1250000000 : ℝ)^4153 ≤ (5561075971817/12500000000000 : ℝ)^3129 := by
    have hnat : (679031117 : ℕ)^4153*12500000000000^3129 ≤ 5561075971817^3129*1250000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679031117 1250000000 5561075971817 12500000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5229271673/10000000000 : ℝ)^4153 ≤ (2643491874383/6250000000000 : ℝ)^3129 := by
    have hnat : (5229271673 : ℕ)^4153*6250000000000^3129 ≤ 2643491874383^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229271673 10000000000 2643491874383 6250000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1088347209/5000000000 : ℝ), (679031117/1250000000 : ℝ), (5229271673/10000000000 : ℝ)] ![(13215522219093/100000000000000 : ℝ), (5561075971817/12500000000000 : ℝ), (2643491874383/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1088347209/5000000000 : ℝ)|^4153 ≤ (13215522219093/100000000000000 : ℝ)^3129
        have hw : |(-1088347209/5000000000 : ℝ)|=(1088347209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(679031117/1250000000 : ℝ)|^4153 ≤ (5561075971817/12500000000000 : ℝ)^3129
        have hw : |(679031117/1250000000 : ℝ)|=(679031117/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5229271673/10000000000 : ℝ)|^4153 ≤ (2643491874383/6250000000000 : ℝ)^3129
        have hw : |(5229271673/10000000000 : ℝ)|=(5229271673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s3_1 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354503763/10000000000 : ℝ)*x 0 + (-114025863/500000000 : ℝ)*x 1 + (2614635849/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354503763/10000000000 : ℝ)^4153 ≤ (21822755508321/50000000000000 : ℝ)^3129 := by
    have hnat : (5354503763 : ℕ)^4153*50000000000000^3129 ≤ 21822755508321^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354503763 10000000000 21822755508321 50000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (114025863/500000000 : ℝ)^4153 ≤ (1757327337951/12500000000000 : ℝ)^3129 := by
    have hnat : (114025863 : ℕ)^4153*12500000000000^3129 ≤ 1757327337951^3129*500000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114025863 500000000 1757327337951 12500000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2614635849/5000000000 : ℝ)^4153 ≤ (4229587025851/10000000000000 : ℝ)^3129 := by
    have hnat : (2614635849 : ℕ)^4153*10000000000000^3129 ≤ 4229587025851^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614635849 5000000000 4229587025851 10000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354503763/10000000000 : ℝ), (-114025863/500000000 : ℝ), (2614635849/5000000000 : ℝ)] ![(21822755508321/50000000000000 : ℝ), (1757327337951/12500000000000 : ℝ), (4229587025851/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354503763/10000000000 : ℝ)|^4153 ≤ (21822755508321/50000000000000 : ℝ)^3129
        have hw : |(5354503763/10000000000 : ℝ)|=(5354503763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-114025863/500000000 : ℝ)|^4153 ≤ (1757327337951/12500000000000 : ℝ)^3129
        have hw : |(-114025863/500000000 : ℝ)|=(114025863/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2614635849/5000000000 : ℝ)|^4153 ≤ (4229587025851/10000000000000 : ℝ)^3129
        have hw : |(2614635849/5000000000 : ℝ)|=(2614635849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s3_2 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338625971/2500000000 : ℝ)*x 0 + (5229271799/10000000000 : ℝ)*x 1 + (-285064621/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338625971/2500000000 : ℝ)^4153 ≤ (43645512325709/100000000000000 : ℝ)^3129 := by
    have hnat : (1338625971 : ℕ)^4153*100000000000000^3129 ≤ 43645512325709^3129*2500000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338625971 2500000000 43645512325709 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5229271799/10000000000 : ℝ)^4153 ≤ (42295871342773/100000000000000 : ℝ)^3129 := by
    have hnat : (5229271799 : ℕ)^4153*100000000000000^3129 ≤ 42295871342773^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229271799 10000000000 42295871342773 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (285064621/1250000000 : ℝ)^4153 ≤ (1405861631443/10000000000000 : ℝ)^3129 := by
    have hnat : (285064621 : ℕ)^4153*10000000000000^3129 ≤ 1405861631443^3129*1250000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285064621 1250000000 1405861631443 10000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338625971/2500000000 : ℝ), (5229271799/10000000000 : ℝ), (-285064621/1250000000 : ℝ)] ![(43645512325709/100000000000000 : ℝ), (42295871342773/100000000000000 : ℝ), (1405861631443/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338625971/2500000000 : ℝ)|^4153 ≤ (43645512325709/100000000000000 : ℝ)^3129
        have hw : |(1338625971/2500000000 : ℝ)|=(1338625971/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5229271799/10000000000 : ℝ)|^4153 ≤ (42295871342773/100000000000000 : ℝ)^3129
        have hw : |(5229271799/10000000000 : ℝ)|=(5229271799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-285064621/1250000000 : ℝ)|^4153 ≤ (1405861631443/10000000000000 : ℝ)^3129
        have hw : |(-285064621/1250000000 : ℝ)|=(285064621/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s3_3 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (174652919/400000000 : ℝ)*x 0 + (130318109/312500000 : ℝ)*x 1 + (914340203/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174652919/400000000 : ℝ)^4153 ≤ (1664599573111/5000000000000 : ℝ)^3129 := by
    have hnat : (174652919 : ℕ)^4153*5000000000000^3129 ≤ 1664599573111^3129*400000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174652919 400000000 1664599573111 5000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130318109/312500000 : ℝ)^4153 ≤ (3915220117221/12500000000000 : ℝ)^3129 := by
    have hnat : (130318109 : ℕ)^4153*12500000000000^3129 ≤ 3915220117221^3129*312500000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130318109 312500000 3915220117221 12500000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (914340203/2000000000 : ℝ)^4153 ≤ (17693123791033/50000000000000 : ℝ)^3129 := by
    have hnat : (914340203 : ℕ)^4153*50000000000000^3129 ≤ 17693123791033^3129*2000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      914340203 2000000000 17693123791033 50000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(174652919/400000000 : ℝ), (130318109/312500000 : ℝ), (914340203/2000000000 : ℝ)] ![(1664599573111/5000000000000 : ℝ), (3915220117221/12500000000000 : ℝ), (17693123791033/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(174652919/400000000 : ℝ)|^4153 ≤ (1664599573111/5000000000000 : ℝ)^3129
        have hw : |(174652919/400000000 : ℝ)|=(174652919/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(130318109/312500000 : ℝ)|^4153 ≤ (3915220117221/12500000000000 : ℝ)^3129
        have hw : |(130318109/312500000 : ℝ)|=(130318109/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(914340203/2000000000 : ℝ)|^4153 ≤ (17693123791033/50000000000000 : ℝ)^3129
        have hw : |(914340203/2000000000 : ℝ)|=(914340203/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s3_4 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2176713921/10000000000 : ℝ)*x 0 + (2615037889/5000000000 : ℝ)*x 1 + (1357860073/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2176713921/10000000000 : ℝ)^4153 ≤ (13215679380277/100000000000000 : ℝ)^3129 := by
    have hnat : (2176713921 : ℕ)^4153*100000000000000^3129 ≤ 13215679380277^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176713921 10000000000 13215679380277 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2615037889/5000000000 : ℝ)^4153 ≤ (42304502494659/100000000000000 : ℝ)^3129 := by
    have hnat : (2615037889 : ℕ)^4153*100000000000000^3129 ≤ 42304502494659^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615037889 5000000000 42304502494659 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357860073/2500000000 : ℝ)^4153 ≤ (44479818109821/100000000000000 : ℝ)^3129 := by
    have hnat : (1357860073 : ℕ)^4153*100000000000000^3129 ≤ 44479818109821^3129*2500000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357860073 2500000000 44479818109821 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2176713921/10000000000 : ℝ), (2615037889/5000000000 : ℝ), (1357860073/2500000000 : ℝ)] ![(13215679380277/100000000000000 : ℝ), (42304502494659/100000000000000 : ℝ), (44479818109821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2176713921/10000000000 : ℝ)|^4153 ≤ (13215679380277/100000000000000 : ℝ)^3129
        have hw : |(-2176713921/10000000000 : ℝ)|=(2176713921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2615037889/5000000000 : ℝ)|^4153 ≤ (42304502494659/100000000000000 : ℝ)^3129
        have hw : |(2615037889/5000000000 : ℝ)|=(2615037889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1357860073/2500000000 : ℝ)|^4153 ≤ (44479818109821/100000000000000 : ℝ)^3129
        have hw : |(1357860073/2500000000 : ℝ)|=(1357860073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s3_5 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5303190517/10000000000 : ℝ)*x 0 + (-2078348529/10000000000 : ℝ)*x 1 + (1086288091/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303190517/10000000000 : ℝ)^4153 ≤ (43091238702561/100000000000000 : ℝ)^3129 := by
    have hnat : (5303190517 : ℕ)^4153*100000000000000^3129 ≤ 43091238702561^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303190517 10000000000 43091238702561 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2078348529/10000000000 : ℝ)^4153 ≤ (3107235350473/25000000000000 : ℝ)^3129 := by
    have hnat : (2078348529 : ℕ)^4153*25000000000000^3129 ≤ 3107235350473^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078348529 10000000000 3107235350473 25000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1086288091/2000000000 : ℝ)^4153 ≤ (44479819881529/100000000000000 : ℝ)^3129 := by
    have hnat : (1086288091 : ℕ)^4153*100000000000000^3129 ≤ 44479819881529^3129*2000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086288091 2000000000 44479819881529 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303190517/10000000000 : ℝ), (-2078348529/10000000000 : ℝ), (1086288091/2000000000 : ℝ)] ![(43091238702561/100000000000000 : ℝ), (3107235350473/25000000000000 : ℝ), (44479819881529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303190517/10000000000 : ℝ)|^4153 ≤ (43091238702561/100000000000000 : ℝ)^3129
        have hw : |(5303190517/10000000000 : ℝ)|=(5303190517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2078348529/10000000000 : ℝ)|^4153 ≤ (3107235350473/25000000000000 : ℝ)^3129
        have hw : |(-2078348529/10000000000 : ℝ)|=(2078348529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1086288091/2000000000 : ℝ)|^4153 ≤ (44479819881529/100000000000000 : ℝ)^3129
        have hw : |(1086288091/2000000000 : ℝ)|=(1086288091/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s3_6 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5303190547/10000000000 : ℝ)*x 0 + (5431440307/10000000000 : ℝ)*x 1 + (-519587173/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303190547/10000000000 : ℝ)^4153 ≤ (43091239026103/100000000000000 : ℝ)^3129 := by
    have hnat : (5303190547 : ℕ)^4153*100000000000000^3129 ≤ 43091239026103^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303190547 10000000000 43091239026103 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5431440307/10000000000 : ℝ)^4153 ≤ (22239909136431/50000000000000 : ℝ)^3129 := by
    have hnat : (5431440307 : ℕ)^4153*50000000000000^3129 ≤ 22239909136431^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431440307 10000000000 22239909136431 50000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (519587173/2500000000 : ℝ)^4153 ≤ (1242894269567/10000000000000 : ℝ)^3129 := by
    have hnat : (519587173 : ℕ)^4153*10000000000000^3129 ≤ 1242894269567^3129*2500000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519587173 2500000000 1242894269567 10000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303190547/10000000000 : ℝ), (5431440307/10000000000 : ℝ), (-519587173/2500000000 : ℝ)] ![(43091239026103/100000000000000 : ℝ), (22239909136431/50000000000000 : ℝ), (1242894269567/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303190547/10000000000 : ℝ)|^4153 ≤ (43091239026103/100000000000000 : ℝ)^3129
        have hw : |(5303190547/10000000000 : ℝ)|=(5303190547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5431440307/10000000000 : ℝ)|^4153 ≤ (22239909136431/50000000000000 : ℝ)^3129
        have hw : |(5431440307/10000000000 : ℝ)|=(5431440307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-519587173/2500000000 : ℝ)|^4153 ≤ (1242894269567/10000000000000 : ℝ)^3129
        have hw : |(-519587173/2500000000 : ℝ)|=(519587173/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s3_7 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (545795193/1250000000 : ℝ)*x 0 + (4570111059/10000000000 : ℝ)*x 1 + (4171778657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545795193/1250000000 : ℝ)^4153 ≤ (1664619089043/5000000000000 : ℝ)^3129 := by
    have hnat : (545795193 : ℕ)^4153*5000000000000^3129 ≤ 1664619089043^3129*1250000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545795193 1250000000 1664619089043 5000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4570111059/10000000000 : ℝ)^4153 ≤ (2210619643783/6250000000000 : ℝ)^3129 := by
    have hnat : (4570111059 : ℕ)^4153*6250000000000^3129 ≤ 2210619643783^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4570111059 10000000000 2210619643783 6250000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4171778657/10000000000 : ℝ)^4153 ≤ (6267540782819/20000000000000 : ℝ)^3129 := by
    have hnat : (4171778657 : ℕ)^4153*20000000000000^3129 ≤ 6267540782819^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171778657 10000000000 6267540782819 20000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(545795193/1250000000 : ℝ), (4570111059/10000000000 : ℝ), (4171778657/10000000000 : ℝ)] ![(1664619089043/5000000000000 : ℝ), (2210619643783/6250000000000 : ℝ), (6267540782819/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(545795193/1250000000 : ℝ)|^4153 ≤ (1664619089043/5000000000000 : ℝ)^3129
        have hw : |(545795193/1250000000 : ℝ)|=(545795193/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4570111059/10000000000 : ℝ)|^4153 ≤ (2210619643783/6250000000000 : ℝ)^3129
        have hw : |(4570111059/10000000000 : ℝ)|=(4570111059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4171778657/10000000000 : ℝ)|^4153 ≤ (6267540782819/20000000000000 : ℝ)^3129
        have hw : |(4171778657/10000000000 : ℝ)|=(4171778657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1113_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74454099/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16591/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8937/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10547/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7421/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16591/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8937/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16591/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8937/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16591/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8937/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16591/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8937/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16591/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8937/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16591/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8937/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8937/100000 : ℝ) ^ (8305/2048 : ℝ) ≤ (558339325527191/10000000000000000000 : ℝ) := by
    have hpowers : (8937/100000 : ℝ)^8305 ≤ (558339325527191/10000000000000000000 : ℝ)^2048 := by
      have hnat : (8937 : ℕ)^8305*10000000000000000000^2048 ≤ 558339325527191^2048*100000^8305 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8937 100000 558339325527191 10000000000000000000 8305 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8937/100000 : ℝ)) (X := (558339325527191/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8305 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (16591/100000 : ℝ) ^ (8305/2048 : ℝ) ≤ (6861927299562717/10000000000000000000 : ℝ) := by
    have hpowers : (16591/100000 : ℝ)^8305 ≤ (6861927299562717/10000000000000000000 : ℝ)^2048 := by
      have hnat : (16591 : ℕ)^8305*10000000000000000000^2048 ≤ 6861927299562717^2048*100000^8305 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16591 100000 6861927299562717 10000000000000000000 8305 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16591/100000 : ℝ)) (X := (6861927299562717/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8305 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000558339325527191/5000000000000000000 : ℝ) ≤ (1250034419953069/1250000000000000 : ℝ) ^ (8305/2048 : ℝ) := by
    have hpowers : (5000558339325527191/5000000000000000000 : ℝ)^2048 ≤ (1250034419953069/1250000000000000 : ℝ)^8305 := by
      have hnat : (5000558339325527191 : ℕ)^2048*1250000000000000^8305 ≤ 1250034419953069^8305*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000558339325527191 5000000000000000000 1250034419953069 1250000000000000 2048 8305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250034419953069/1250000000000000 : ℝ)) (X := (5000558339325527191/5000000000000000000 : ℝ)) (by norm_num) 8305 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (2501855066656272477/2500000000000000000 : ℝ) ≤ (2500457328719911/2500000000000000 : ℝ) ^ (8305/2048 : ℝ) := by
    have hpowers : (2501855066656272477/2500000000000000000 : ℝ)^2048 ≤ (2500457328719911/2500000000000000 : ℝ)^8305 := by
      have hnat : (2501855066656272477 : ℕ)^2048*2500000000000000^8305 ≤ 2500457328719911^8305*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501855066656272477 2500000000000000000 2500457328719911 2500000000000000 2048 8305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500457328719911/2500000000000000 : ℝ)) (X := (2501855066656272477/2500000000000000000 : ℝ)) (by norm_num) 8305 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (5006861927299562717/5000000000000000000 : ℝ) ≤ (625211454383421/625000000000000 : ℝ) ^ (8305/2048 : ℝ) := by
    have hpowers : (5006861927299562717/5000000000000000000 : ℝ)^2048 ≤ (625211454383421/625000000000000 : ℝ)^8305 := by
      have hnat : (5006861927299562717 : ℕ)^2048*625000000000000^8305 ≤ 625211454383421^8305*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5006861927299562717 5000000000000000000 625211454383421 625000000000000 2048 8305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625211454383421/625000000000000 : ℝ)) (X := (5006861927299562717/5000000000000000000 : ℝ)) (by norm_num) 8305 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(558339325527191/10000000000000000000 : ℝ) ≤ ((382571661031684033/382700000000000000 : ℝ)+2*(388488813773/191350000000000 : ℝ)*(8937/100000 : ℝ))^(8305/2048 : ℝ) := by
    rw [show (382571661031684033/382700000000000000 : ℝ)+2*(388488813773/191350000000000 : ℝ)*(8937/100000 : ℝ)=(1250034419953069/1250000000000000 : ℝ) by norm_num, show 1+2*(558339325527191/10000000000000000000 : ℝ)=(5000558339325527191/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6861927299562717/10000000000000000000 : ℝ)+(558339325527191/10000000000000000000 : ℝ) ≤ ((382571661031684033/382700000000000000 : ℝ)+(388488813773/191350000000000 : ℝ)*((16591/100000 : ℝ)+(8937/100000 : ℝ)))^(8305/2048 : ℝ) := by
    rw [show (382571661031684033/382700000000000000 : ℝ)+(388488813773/191350000000000 : ℝ)*((16591/100000 : ℝ)+(8937/100000 : ℝ))=(2500457328719911/2500000000000000 : ℝ) by norm_num, show 1+(6861927299562717/10000000000000000000 : ℝ)+(558339325527191/10000000000000000000 : ℝ)=(2501855066656272477/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6861927299562717/10000000000000000000 : ℝ) ≤ ((382571661031684033/382700000000000000 : ℝ)+2*(388488813773/191350000000000 : ℝ)*(16591/100000 : ℝ))^(8305/2048 : ℝ) := by
    rw [show (382571661031684033/382700000000000000 : ℝ)+2*(388488813773/191350000000000 : ℝ)*(16591/100000 : ℝ)=(625211454383421/625000000000000 : ℝ) by norm_num, show 1+2*(6861927299562717/10000000000000000000 : ℝ)=(5006861927299562717/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (382571661031684033/382700000000000000 : ℝ)*(X 1 0+X 2 0)+(388488813773/191350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8305/2048 : ℝ)) (lo := (8937/100000 : ℝ)) (hi := (16591/100000 : ℝ)) (c := (382571661031684033/382700000000000000 : ℝ)) (alpha := (388488813773/191350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (382571661031684033/382700000000000000 : ℝ)*(X 0 1+X 2 1)+(388488813773/191350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8305/2048 : ℝ)) (lo := (8937/100000 : ℝ)) (hi := (16591/100000 : ℝ)) (c := (382571661031684033/382700000000000000 : ℝ)) (alpha := (388488813773/191350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (382571661031684033/382700000000000000 : ℝ)*(X 0 2+X 1 2)+(388488813773/191350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8305/2048 : ℝ)) (lo := (8937/100000 : ℝ)) (hi := (16591/100000 : ℝ)) (c := (382571661031684033/382700000000000000 : ℝ)) (alpha := (388488813773/191350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1088347209/5000000000 : ℝ)*X 0 0+(679031117/1250000000 : ℝ)*X 0 1+(5229271673/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5354503763/10000000000 : ℝ)*X 1 0+(-114025863/500000000 : ℝ)*X 1 1+(2614635849/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338625971/2500000000 : ℝ)*X 2 0+(5229271799/10000000000 : ℝ)*X 2 1+(-285064621/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((174652919/400000000 : ℝ)*X 0 0+(130318109/312500000 : ℝ)*X 0 1+(914340203/2000000000 : ℝ)*X 0 2+(174652919/400000000 : ℝ)*X 1 0+(130318109/312500000 : ℝ)*X 1 1+(914340203/2000000000 : ℝ)*X 1 2+(174652919/400000000 : ℝ)*X 2 0+(130318109/312500000 : ℝ)*X 2 1+(914340203/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2176713921/10000000000 : ℝ)*X 0 0+(2615037889/5000000000 : ℝ)*X 0 1+(1357860073/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5303190517/10000000000 : ℝ)*X 1 0+(-2078348529/10000000000 : ℝ)*X 1 1+(1086288091/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5303190547/10000000000 : ℝ)*X 2 0+(5431440307/10000000000 : ℝ)*X 2 1+(-519587173/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((545795193/1250000000 : ℝ)*X 0 0+(4570111059/10000000000 : ℝ)*X 0 1+(4171778657/10000000000 : ℝ)*X 0 2+(545795193/1250000000 : ℝ)*X 1 0+(4570111059/10000000000 : ℝ)*X 1 1+(4171778657/10000000000 : ℝ)*X 1 2+(545795193/1250000000 : ℝ)*X 2 0+(4570111059/10000000000 : ℝ)*X 2 1+(4171778657/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18263909558138820724258977/4783750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1244460699/100000000000000 : ℝ)*(base19) + (1175043393/100000000000000 : ℝ)*(base23) + (48391351/50000000000000 : ℝ)*(lower2) + (14676581/100000000000000 : ℝ)*(upper3) + (198495219/100000000000000 : ℝ)*(upper5) + (1854314339077573/50000000000000 : ℝ)*(major0) + (1854314339077573/50000000000000 : ℝ)*(major1) + (1854314339077573/50000000000000 : ℝ)*(major2) + (2463340482884661/50000000000000 : ℝ)*(sp0) + (2463354485539837/50000000000000 : ℝ)*(sp1) + (4926709040496979/100000000000000 : ℝ)*(sp2) + (1245268704605329/50000000000000 : ℝ)*(sp3) + (584995421/2000000000000 : ℝ)*(sp4) + (2401073927/25000000000000 : ℝ)*(sp7) + (1245273506753183/50000000000000 : ℝ)*(f.failure) + (4926710215540373/100000000000000 : ℝ)*(f.sum) + (17490084791289/4783750000000000000000000000 : ℝ)*base65 + (66526457186330091/19135000000000000000000000000000 : ℝ)*base68 + (137733497554470091/19135000000000000000000000000000 : ℝ)*base70 + (5582396762790091/19135000000000000000000000000000 : ℝ)*base72 + (79882441933/597968750000000000000000000 : ℝ)*base73 + (306487055388180091/19135000000000000000000000000000 : ℝ)*base76 + (95068599252719909/19135000000000000000000000000000 : ℝ)*base77 + (233437750472745091/19135000000000000000000000000000 : ℝ)*base80 + (56211435796037/9567500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (5647117/2500000000000000000000 : ℝ)*base89 + (5647117/2500000000000000000000 : ℝ)*base91 + (5647117/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (87773266908942627678108567/9567500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1696642227/100000000000000 : ℝ)*(base19) + (1000005553/50000000000000 : ℝ)*(base23) + (221916431/100000000000000 : ℝ)*(upper3) + (66712049/50000000000000 : ℝ)*(lower4) + (145560239/100000000000000 : ℝ)*(upper5) + (1869145098672089/50000000000000 : ℝ)*(major0) + (1869145098672089/50000000000000 : ℝ)*(major1) + (1869145098672089/50000000000000 : ℝ)*(major2) + (15683737089/50000000000000 : ℝ)*(sp1) + (33815098709/100000000000000 : ℝ)*(sp2) + (993222748560957/20000000000000 : ℝ)*(sp4) + (248304033934419/5000000000000 : ℝ)*(sp5) + (496607792769497/10000000000000 : ℝ)*(sp6) + (627616586520001/25000000000000 : ℝ)*(sp7) + (627616586520001/25000000000000 : ℝ)*(f.failure) + (993222748560957/20000000000000 : ℝ)*(f.sum) + (84734488582403/19135000000000000000000000000 : ℝ)*base65 + (9214055768238937/19135000000000000000000000000000 : ℝ)*base67 + (204760172176168937/19135000000000000000000000000000 : ℝ)*base69 + (150519745226898937/19135000000000000000000000000000 : ℝ)*base71 + (19722642196707/4783750000000000000000000000 : ℝ)*base73 + (92012352580428937/19135000000000000000000000000000 : ℝ)*base75 + (19121420999178937/19135000000000000000000000000000 : ℝ)*base77 + (138888782949853937/19135000000000000000000000000000 : ℝ)*base79 + (13366991492241/2391875000000000000000000000 : ℝ)*base81 + (5065901/1250000000000000000000 : ℝ)*base90 + (5065901/1250000000000000000000 : ℝ)*base92 + (5065901/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1113_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74454099/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16591/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8937/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10547/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7421/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1113_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1113_s4_0 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2179939857/10000000000 : ℝ)*x 0 + (5403325347/10000000000 : ℝ)*x 1 + (5256073239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179939857/10000000000 : ℝ)^4153 ≤ (1324168130667/10000000000000 : ℝ)^3129 := by
    have hnat : (2179939857 : ℕ)^4153*10000000000000^3129 ≤ 1324168130667^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179939857 10000000000 1324168130667 10000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5403325347/10000000000 : ℝ)^4153 ≤ (11043621379393/25000000000000 : ℝ)^3129 := by
    have hnat : (5403325347 : ℕ)^4153*25000000000000^3129 ≤ 11043621379393^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403325347 10000000000 11043621379393 25000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5256073239/10000000000 : ℝ)^4153 ≤ (42583833162243/100000000000000 : ℝ)^3129 := by
    have hnat : (5256073239 : ℕ)^4153*100000000000000^3129 ≤ 42583833162243^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256073239 10000000000 42583833162243 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2179939857/10000000000 : ℝ), (5403325347/10000000000 : ℝ), (5256073239/10000000000 : ℝ)] ![(1324168130667/10000000000000 : ℝ), (11043621379393/25000000000000 : ℝ), (42583833162243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2179939857/10000000000 : ℝ)|^4153 ≤ (1324168130667/10000000000000 : ℝ)^3129
        have hw : |(-2179939857/10000000000 : ℝ)|=(2179939857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5403325347/10000000000 : ℝ)|^4153 ≤ (11043621379393/25000000000000 : ℝ)^3129
        have hw : |(5403325347/10000000000 : ℝ)|=(5403325347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5256073239/10000000000 : ℝ)|^4153 ≤ (42583833162243/100000000000000 : ℝ)^3129
        have hw : |(5256073239/10000000000 : ℝ)|=(5256073239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s4_1 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673651463/5000000000 : ℝ)*x 0 + (-2254794197/10000000000 : ℝ)*x 1 + (2628036787/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673651463/5000000000 : ℝ)^4153 ≤ (10891906043653/25000000000000 : ℝ)^3129 := by
    have hnat : (2673651463 : ℕ)^4153*25000000000000^3129 ≤ 10891906043653^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673651463 5000000000 10891906043653 25000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2254794197/10000000000 : ℝ)^4153 ≤ (13848539049893/100000000000000 : ℝ)^3129 := by
    have hnat : (2254794197 : ℕ)^4153*100000000000000^3129 ≤ 13848539049893^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254794197 10000000000 13848539049893 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2628036787/5000000000 : ℝ)^4153 ≤ (42583836764581/100000000000000 : ℝ)^3129 := by
    have hnat : (2628036787 : ℕ)^4153*100000000000000^3129 ≤ 42583836764581^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628036787 5000000000 42583836764581 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673651463/5000000000 : ℝ), (-2254794197/10000000000 : ℝ), (2628036787/5000000000 : ℝ)] ![(10891906043653/25000000000000 : ℝ), (13848539049893/100000000000000 : ℝ), (42583836764581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673651463/5000000000 : ℝ)|^4153 ≤ (10891906043653/25000000000000 : ℝ)^3129
        have hw : |(2673651463/5000000000 : ℝ)|=(2673651463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2254794197/10000000000 : ℝ)|^4153 ≤ (13848539049893/100000000000000 : ℝ)^3129
        have hw : |(-2254794197/10000000000 : ℝ)|=(2254794197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2628036787/5000000000 : ℝ)|^4153 ≤ (42583836764581/100000000000000 : ℝ)^3129
        have hw : |(2628036787/5000000000 : ℝ)|=(2628036787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s4_2 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347302621/10000000000 : ℝ)*x 0 + (5256073379/10000000000 : ℝ)*x 1 + (-2254794857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347302621/10000000000 : ℝ)^4153 ≤ (43567620876349/100000000000000 : ℝ)^3129 := by
    have hnat : (5347302621 : ℕ)^4153*100000000000000^3129 ≤ 43567620876349^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347302621 10000000000 43567620876349 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5256073379/10000000000 : ℝ)^4153 ≤ (42583834667697/100000000000000 : ℝ)^3129 := by
    have hnat : (5256073379 : ℕ)^4153*100000000000000^3129 ≤ 42583834667697^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256073379 10000000000 42583834667697 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2254794857/10000000000 : ℝ)^4153 ≤ (1352396917/9765625000 : ℝ)^3129 := by
    have hnat : (2254794857 : ℕ)^4153*9765625000^3129 ≤ 1352396917^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254794857 10000000000 1352396917 9765625000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347302621/10000000000 : ℝ), (5256073379/10000000000 : ℝ), (-2254794857/10000000000 : ℝ)] ![(43567620876349/100000000000000 : ℝ), (42583834667697/100000000000000 : ℝ), (1352396917/9765625000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347302621/10000000000 : ℝ)|^4153 ≤ (43567620876349/100000000000000 : ℝ)^3129
        have hw : |(5347302621/10000000000 : ℝ)|=(5347302621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5256073379/10000000000 : ℝ)|^4153 ≤ (42583834667697/100000000000000 : ℝ)^3129
        have hw : |(5256073379/10000000000 : ℝ)|=(5256073379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2254794857/10000000000 : ℝ)|^4153 ≤ (1352396917/9765625000 : ℝ)^3129
        have hw : |(-2254794857/10000000000 : ℝ)|=(2254794857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s4_3 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2184128559/5000000000 : ℝ)*x 0 + (211252183/500000000 : ℝ)*x 1 + (4516333089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184128559/5000000000 : ℝ)^4153 ≤ (6662313279551/20000000000000 : ℝ)^3129 := by
    have hnat : (2184128559 : ℕ)^4153*20000000000000^3129 ≤ 6662313279551^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184128559 5000000000 6662313279551 20000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (211252183/500000000 : ℝ)^4153 ≤ (6373974210281/20000000000000 : ℝ)^3129 := by
    have hnat : (211252183 : ℕ)^4153*20000000000000^3129 ≤ 6373974210281^3129*500000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211252183 500000000 6373974210281 20000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4516333089/10000000000 : ℝ)^4153 ≤ (34818562538499/100000000000000 : ℝ)^3129 := by
    have hnat : (4516333089 : ℕ)^4153*100000000000000^3129 ≤ 34818562538499^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4516333089 10000000000 34818562538499 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2184128559/5000000000 : ℝ), (211252183/500000000 : ℝ), (4516333089/10000000000 : ℝ)] ![(6662313279551/20000000000000 : ℝ), (6373974210281/20000000000000 : ℝ), (34818562538499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2184128559/5000000000 : ℝ)|^4153 ≤ (6662313279551/20000000000000 : ℝ)^3129
        have hw : |(2184128559/5000000000 : ℝ)|=(2184128559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(211252183/500000000 : ℝ)|^4153 ≤ (6373974210281/20000000000000 : ℝ)^3129
        have hw : |(211252183/500000000 : ℝ)|=(211252183/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4516333089/10000000000 : ℝ)|^4153 ≤ (34818562538499/100000000000000 : ℝ)^3129
        have hw : |(4516333089/10000000000 : ℝ)|=(4516333089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s4_4 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-217994687/1000000000 : ℝ)*x 0 + (5256497263/10000000000 : ℝ)*x 1 + (2701449959/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (217994687/1000000000 : ℝ)^4153 ≤ (13241737847093/100000000000000 : ℝ)^3129 := by
    have hnat : (217994687 : ℕ)^4153*100000000000000^3129 ≤ 13241737847093^3129*1000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217994687 1000000000 13241737847093 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5256497263/10000000000 : ℝ)^4153 ≤ (42588392858181/100000000000000 : ℝ)^3129 := by
    have hnat : (5256497263 : ℕ)^4153*100000000000000^3129 ≤ 42588392858181^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256497263 10000000000 42588392858181 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2701449959/5000000000 : ℝ)^4153 ≤ (44169869279/100000000000 : ℝ)^3129 := by
    have hnat : (2701449959 : ℕ)^4153*100000000000^3129 ≤ 44169869279^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701449959 5000000000 44169869279 100000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-217994687/1000000000 : ℝ), (5256497263/10000000000 : ℝ), (2701449959/5000000000 : ℝ)] ![(13241737847093/100000000000000 : ℝ), (42588392858181/100000000000000 : ℝ), (44169869279/100000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-217994687/1000000000 : ℝ)|^4153 ≤ (13241737847093/100000000000000 : ℝ)^3129
        have hw : |(-217994687/1000000000 : ℝ)|=(217994687/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5256497263/10000000000 : ℝ)|^4153 ≤ (42588392858181/100000000000000 : ℝ)^3129
        have hw : |(5256497263/10000000000 : ℝ)|=(5256497263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2701449959/5000000000 : ℝ)|^4153 ≤ (44169869279/100000000000 : ℝ)^3129
        have hw : |(2701449959/5000000000 : ℝ)|=(2701449959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s4_5 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2655039353/5000000000 : ℝ)*x 0 + (-65874009/312500000 : ℝ)*x 1 + (2701449991/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655039353/5000000000 : ℝ)^4153 ≤ (43165541546801/100000000000000 : ℝ)^3129 := by
    have hnat : (2655039353 : ℕ)^4153*100000000000000^3129 ≤ 43165541546801^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655039353 5000000000 43165541546801 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65874009/312500000 : ℝ)^4153 ≤ (12664588466299/100000000000000 : ℝ)^3129 := by
    have hnat : (65874009 : ℕ)^4153*100000000000000^3129 ≤ 12664588466299^3129*312500000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65874009 312500000 12664588466299 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2701449991/5000000000 : ℝ)^4153 ≤ (44169869973441/100000000000000 : ℝ)^3129 := by
    have hnat : (2701449991 : ℕ)^4153*100000000000000^3129 ≤ 44169869973441^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701449991 5000000000 44169869973441 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655039353/5000000000 : ℝ), (-65874009/312500000 : ℝ), (2701449991/5000000000 : ℝ)] ![(43165541546801/100000000000000 : ℝ), (12664588466299/100000000000000 : ℝ), (44169869973441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655039353/5000000000 : ℝ)|^4153 ≤ (43165541546801/100000000000000 : ℝ)^3129
        have hw : |(2655039353/5000000000 : ℝ)|=(2655039353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-65874009/312500000 : ℝ)|^4153 ≤ (12664588466299/100000000000000 : ℝ)^3129
        have hw : |(-65874009/312500000 : ℝ)|=(65874009/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2701449991/5000000000 : ℝ)|^4153 ≤ (44169869973441/100000000000000 : ℝ)^3129
        have hw : |(2701449991/5000000000 : ℝ)|=(2701449991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s4_6 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2655039399/5000000000 : ℝ)*x 0 + (5402899963/10000000000 : ℝ)*x 1 + (-2107968189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655039399/5000000000 : ℝ)^4153 ≤ (8633108507883/20000000000000 : ℝ)^3129 := by
    have hnat : (2655039399 : ℕ)^4153*20000000000000^3129 ≤ 8633108507883^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655039399 5000000000 8633108507883 20000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5402899963/10000000000 : ℝ)^4153 ≤ (44169869767279/100000000000000 : ℝ)^3129 := by
    have hnat : (5402899963 : ℕ)^4153*100000000000000^3129 ≤ 44169869767279^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402899963 10000000000 44169869767279 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2107968189/10000000000 : ℝ)^4153 ≤ (633229383843/5000000000000 : ℝ)^3129 := by
    have hnat : (2107968189 : ℕ)^4153*5000000000000^3129 ≤ 633229383843^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107968189 10000000000 633229383843 5000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655039399/5000000000 : ℝ), (5402899963/10000000000 : ℝ), (-2107968189/10000000000 : ℝ)] ![(8633108507883/20000000000000 : ℝ), (44169869767279/100000000000000 : ℝ), (633229383843/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655039399/5000000000 : ℝ)|^4153 ≤ (8633108507883/20000000000000 : ℝ)^3129
        have hw : |(2655039399/5000000000 : ℝ)|=(2655039399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5402899963/10000000000 : ℝ)|^4153 ≤ (44169869767279/100000000000000 : ℝ)^3129
        have hw : |(5402899963/10000000000 : ℝ)|=(5402899963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2107968189/10000000000 : ℝ)|^4153 ≤ (633229383843/5000000000000 : ℝ)^3129
        have hw : |(-2107968189/10000000000 : ℝ)|=(2107968189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s4_7 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1092067959/2500000000 : ℝ)*x 0 + (1128873597/2500000000 : ℝ)*x 1 + (4225885929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092067959/2500000000 : ℝ)^4153 ≤ (8327928841377/25000000000000 : ℝ)^3129 := by
    have hnat : (1092067959 : ℕ)^4153*25000000000000^3129 ≤ 8327928841377^3129*2500000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092067959 2500000000 8327928841377 25000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1128873597/2500000000 : ℝ)^4153 ≤ (4351247600179/12500000000000 : ℝ)^3129 := by
    have hnat : (1128873597 : ℕ)^4153*12500000000000^3129 ≤ 4351247600179^3129*2500000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128873597 2500000000 4351247600179 12500000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4225885929/10000000000 : ℝ)^4153 ≤ (15939151912647/50000000000000 : ℝ)^3129 := by
    have hnat : (4225885929 : ℕ)^4153*50000000000000^3129 ≤ 15939151912647^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4225885929 10000000000 15939151912647 50000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1092067959/2500000000 : ℝ), (1128873597/2500000000 : ℝ), (4225885929/10000000000 : ℝ)] ![(8327928841377/25000000000000 : ℝ), (4351247600179/12500000000000 : ℝ), (15939151912647/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1092067959/2500000000 : ℝ)|^4153 ≤ (8327928841377/25000000000000 : ℝ)^3129
        have hw : |(1092067959/2500000000 : ℝ)|=(1092067959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1128873597/2500000000 : ℝ)|^4153 ≤ (4351247600179/12500000000000 : ℝ)^3129
        have hw : |(1128873597/2500000000 : ℝ)|=(1128873597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4225885929/10000000000 : ℝ)|^4153 ≤ (15939151912647/50000000000000 : ℝ)^3129
        have hw : |(4225885929/10000000000 : ℝ)|=(4225885929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1113_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74454099/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7421/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10547/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11119/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14237/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7421/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10547/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7421/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10547/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7421/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10547/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7421/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10547/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7421/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10547/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7421/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10547/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10547/100000 : ℝ) ^ (8305/2048 : ℝ) ≤ (1092989929389157/10000000000000000000 : ℝ) := by
    have hpowers : (10547/100000 : ℝ)^8305 ≤ (1092989929389157/10000000000000000000 : ℝ)^2048 := by
      have hnat : (10547 : ℕ)^8305*10000000000000000000^2048 ≤ 1092989929389157^2048*100000^8305 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10547 100000 1092989929389157 10000000000000000000 8305 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10547/100000 : ℝ)) (X := (1092989929389157/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8305 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7421/50000 : ℝ) ^ (8305/2048 : ℝ) ≤ (2729833592498329/6250000000000000000 : ℝ) := by
    have hpowers : (7421/50000 : ℝ)^8305 ≤ (2729833592498329/6250000000000000000 : ℝ)^2048 := by
      have hnat : (7421 : ℕ)^8305*6250000000000000000^2048 ≤ 2729833592498329^2048*50000^8305 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7421 50000 2729833592498329 6250000000000000000 8305 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7421/50000 : ℝ)) (X := (2729833592498329/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8305 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001092989929389157/5000000000000000000 : ℝ) ≤ (625033688426731/625000000000000 : ℝ) ^ (8305/2048 : ℝ) := by
    have hpowers : (5001092989929389157/5000000000000000000 : ℝ)^2048 ≤ (625033688426731/625000000000000 : ℝ)^8305 := by
      have hnat : (5001092989929389157 : ℕ)^2048*625000000000000^8305 ≤ 625033688426731^8305*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001092989929389157 5000000000000000000 625033688426731 625000000000000 2048 8305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625033688426731/625000000000000 : ℝ)) (X := (5001092989929389157/5000000000000000000 : ℝ)) (by norm_num) 8305 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50027303618386932417/50000000000000000000 : ℝ) ≤ (10001346328994663/10000000000000000 : ℝ) ^ (8305/2048 : ℝ) := by
    have hpowers : (50027303618386932417/50000000000000000000 : ℝ)^2048 ≤ (10001346328994663/10000000000000000 : ℝ)^8305 := by
      have hnat : (50027303618386932417 : ℕ)^2048*10000000000000000^8305 ≤ 10001346328994663^8305*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027303618386932417 50000000000000000000 10001346328994663 10000000000000000 2048 8305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001346328994663/10000000000000000 : ℝ)) (X := (50027303618386932417/50000000000000000000 : ℝ)) (by norm_num) 8305 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (3127729833592498329/3125000000000000000 : ℝ) ≤ (1000215364316163/1000000000000000 : ℝ) ^ (8305/2048 : ℝ) := by
    have hpowers : (3127729833592498329/3125000000000000000 : ℝ)^2048 ≤ (1000215364316163/1000000000000000 : ℝ)^8305 := by
      have hnat : (3127729833592498329 : ℕ)^2048*1000000000000000^8305 ≤ 1000215364316163^8305*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3127729833592498329 3125000000000000000 1000215364316163 1000000000000000 2048 8305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000215364316163/1000000000000000 : ℝ)) (X := (3127729833592498329/3125000000000000000 : ℝ)) (by norm_num) 8305 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1092989929389157/10000000000000000000 : ℝ) ≤ ((21467642791823476211/21475000000000000000 : ℝ)+2*(807314166967/429500000000000 : ℝ)*(10547/100000 : ℝ))^(8305/2048 : ℝ) := by
    rw [show (21467642791823476211/21475000000000000000 : ℝ)+2*(807314166967/429500000000000 : ℝ)*(10547/100000 : ℝ)=(625033688426731/625000000000000 : ℝ) by norm_num, show 1+2*(1092989929389157/10000000000000000000 : ℝ)=(5001092989929389157/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2729833592498329/6250000000000000000 : ℝ)+(1092989929389157/10000000000000000000 : ℝ) ≤ ((21467642791823476211/21475000000000000000 : ℝ)+(807314166967/429500000000000 : ℝ)*((7421/50000 : ℝ)+(10547/100000 : ℝ)))^(8305/2048 : ℝ) := by
    rw [show (21467642791823476211/21475000000000000000 : ℝ)+(807314166967/429500000000000 : ℝ)*((7421/50000 : ℝ)+(10547/100000 : ℝ))=(10001346328994663/10000000000000000 : ℝ) by norm_num, show 1+(2729833592498329/6250000000000000000 : ℝ)+(1092989929389157/10000000000000000000 : ℝ)=(50027303618386932417/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2729833592498329/6250000000000000000 : ℝ) ≤ ((21467642791823476211/21475000000000000000 : ℝ)+2*(807314166967/429500000000000 : ℝ)*(7421/50000 : ℝ))^(8305/2048 : ℝ) := by
    rw [show (21467642791823476211/21475000000000000000 : ℝ)+2*(807314166967/429500000000000 : ℝ)*(7421/50000 : ℝ)=(1000215364316163/1000000000000000 : ℝ) by norm_num, show 1+2*(2729833592498329/6250000000000000000 : ℝ)=(3127729833592498329/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (21467642791823476211/21475000000000000000 : ℝ)*(X 1 0+X 2 0)+(807314166967/429500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8305/2048 : ℝ)) (lo := (10547/100000 : ℝ)) (hi := (7421/50000 : ℝ)) (c := (21467642791823476211/21475000000000000000 : ℝ)) (alpha := (807314166967/429500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (21467642791823476211/21475000000000000000 : ℝ)*(X 0 1+X 2 1)+(807314166967/429500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8305/2048 : ℝ)) (lo := (10547/100000 : ℝ)) (hi := (7421/50000 : ℝ)) (c := (21467642791823476211/21475000000000000000 : ℝ)) (alpha := (807314166967/429500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (21467642791823476211/21475000000000000000 : ℝ)*(X 0 2+X 1 2)+(807314166967/429500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8305/2048 : ℝ)) (lo := (10547/100000 : ℝ)) (hi := (7421/50000 : ℝ)) (c := (21467642791823476211/21475000000000000000 : ℝ)) (alpha := (807314166967/429500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2179939857/10000000000 : ℝ)*X 0 0+(5403325347/10000000000 : ℝ)*X 0 1+(5256073239/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673651463/5000000000 : ℝ)*X 1 0+(-2254794197/10000000000 : ℝ)*X 1 1+(2628036787/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347302621/10000000000 : ℝ)*X 2 0+(5256073379/10000000000 : ℝ)*X 2 1+(-2254794857/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2184128559/5000000000 : ℝ)*X 0 0+(211252183/500000000 : ℝ)*X 0 1+(4516333089/10000000000 : ℝ)*X 0 2+(2184128559/5000000000 : ℝ)*X 1 0+(211252183/500000000 : ℝ)*X 1 1+(4516333089/10000000000 : ℝ)*X 1 2+(2184128559/5000000000 : ℝ)*X 2 0+(211252183/500000000 : ℝ)*X 2 1+(4516333089/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-217994687/1000000000 : ℝ)*X 0 0+(5256497263/10000000000 : ℝ)*X 0 1+(2701449959/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655039353/5000000000 : ℝ)*X 1 0+(-65874009/312500000 : ℝ)*X 1 1+(2701449991/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2655039399/5000000000 : ℝ)*X 2 0+(5402899963/10000000000 : ℝ)*X 2 1+(-2107968189/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1092067959/2500000000 : ℝ)*X 0 0+(1128873597/2500000000 : ℝ)*X 0 1+(4225885929/10000000000 : ℝ)*X 0 2+(1092067959/2500000000 : ℝ)*X 1 0+(1128873597/2500000000 : ℝ)*X 1 1+(4225885929/10000000000 : ℝ)*X 1 2+(1092067959/2500000000 : ℝ)*X 2 0+(1128873597/2500000000 : ℝ)*X 2 1+(4225885929/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2783405962797656899597009557/1073750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (39469219/2000000000000 : ℝ)*(base19) + (991294167/50000000000000 : ℝ)*(base23) + (11286121/5000000000000 : ℝ)*(upper2) + (11733469/2000000000000 : ℝ)*(upper3) + (5112131845877571/100000000000000 : ℝ)*(major0) + (5112131845877571/100000000000000 : ℝ)*(major1) + (5112131845877571/100000000000000 : ℝ)*(major2) + (1697787036364677/25000000000000 : ℝ)*(sp0) + (106112272997661/1562500000000 : ℝ)*(sp1) + (3395590889721719/50000000000000 : ℝ)*(sp2) + (1716520228079751/50000000000000 : ℝ)*(sp3) + (7859970509/20000000000000 : ℝ)*(sp4) + (92081987/2500000000000 : ℝ)*(sp6) + (7140775349/20000000000000 : ℝ)*(sp7) + (3433076160036247/100000000000000 : ℝ)*(f.failure) + (6791187445311253/100000000000000 : ℝ)*(f.sum) + (29970826824093/21475000000000000000000000000 : ℝ)*base66 + (1810122789322313481/2147500000000000000000000000000000 : ℝ)*base67 + (12556923796507313481/2147500000000000000000000000000000 : ℝ)*base69 + (1371308628605186519/2147500000000000000000000000000000 : ℝ)*base72 + (39807926281457/21475000000000000000000000000 : ℝ)*base73 + (22763781747657686519/2147500000000000000000000000000000 : ℝ)*base76 + (14559004139629813481/2147500000000000000000000000000000 : ℝ)*base77 + (20827652143249813481/2147500000000000000000000000000000 : ℝ)*base79 + (5131909739541/10737500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (27726453/5000000000000000000000 : ℝ)*base89 + (27726453/5000000000000000000000 : ℝ)*base91 + (27726453/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1528786328143490406668640231/268437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (456858267/50000000000000 : ℝ)*(base19) + (1261927467/100000000000000 : ℝ)*(base23) + (172070137/100000000000000 : ℝ)*(upper3) + (87205093/100000000000000 : ℝ)*(lower4) + (35337507/20000000000000 : ℝ)*(upper5) + (1285426856058107/25000000000000 : ℝ)*(major0) + (1285426856058107/25000000000000 : ℝ)*(major1) + (1285426856058107/25000000000000 : ℝ)*(major2) + (794651447/4000000000000 : ℝ)*(sp1) + (29230737193/100000000000000 : ℝ)*(sp2) + (106726201249817/1562500000000 : ℝ)*(sp4) + (6830456099985579/100000000000000 : ℝ)*(sp5) + (6830446387323629/100000000000000 : ℝ)*(sp6) + (3452937778638909/100000000000000 : ℝ)*(sp7) + (3452937778638909/100000000000000 : ℝ)*(f.failure) + (106726201249817/1562500000000 : ℝ)*(f.sum) + (4622820824311/1342187500000000000000000000 : ℝ)*base65 + (3077645178405857423/536875000000000000000000000000000 : ℝ)*base68 + (329002035137267577/536875000000000000000000000000000 : ℝ)*base69 + (676347327214142577/536875000000000000000000000000000 : ℝ)*base71 + (16468005254999/21475000000000000000000000000 : ℝ)*base74 + (2807549836860232423/536875000000000000000000000000000 : ℝ)*base76 + (5724583499716482423/536875000000000000000000000000000 : ℝ)*base78 + (20322905088824607423/536875000000000000000000000000000 : ℝ)*base80 + (161932127386851/21475000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (15937991/5000000000000000000000 : ℝ)*base89 + (15937991/5000000000000000000000 : ℝ)*base91 + (15937991/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1113_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74454099/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7421/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10547/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11119/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1113_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1113_s5_0 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-436129177/2000000000 : ℝ)*x 0 + (2697843407/5000000000 : ℝ)*x 1 + (5263248399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436129177/2000000000 : ℝ)^4153 ≤ (662368688293/5000000000000 : ℝ)^3129 := by
    have hnat : (436129177 : ℕ)^4153*5000000000000^3129 ≤ 662368688293^3129*2000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436129177 2000000000 662368688293 5000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697843407/5000000000 : ℝ)^4153 ≤ (4409161955021/10000000000000 : ℝ)^3129 := by
    have hnat : (2697843407 : ℕ)^4153*10000000000000^3129 ≤ 4409161955021^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697843407 5000000000 4409161955021 10000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263248399/10000000000 : ℝ)^4153 ≤ (1706440267019/4000000000000 : ℝ)^3129 := by
    have hnat : (5263248399 : ℕ)^4153*4000000000000^3129 ≤ 1706440267019^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263248399 10000000000 1706440267019 4000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-436129177/2000000000 : ℝ), (2697843407/5000000000 : ℝ), (5263248399/10000000000 : ℝ)] ![(662368688293/5000000000000 : ℝ), (4409161955021/10000000000000 : ℝ), (1706440267019/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-436129177/2000000000 : ℝ)|^4153 ≤ (662368688293/5000000000000 : ℝ)^3129
        have hw : |(-436129177/2000000000 : ℝ)|=(436129177/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697843407/5000000000 : ℝ)|^4153 ≤ (4409161955021/10000000000000 : ℝ)^3129
        have hw : |(2697843407/5000000000 : ℝ)|=(2697843407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263248399/10000000000 : ℝ)|^4153 ≤ (1706440267019/4000000000000 : ℝ)^3129
        have hw : |(5263248399/10000000000 : ℝ)|=(5263248399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s5_1 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672695673/5000000000 : ℝ)*x 0 + (-2247859507/10000000000 : ℝ)*x 1 + (5263248621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672695673/5000000000 : ℝ)^4153 ≤ (2177347680049/5000000000000 : ℝ)^3129 := by
    have hnat : (2672695673 : ℕ)^4153*5000000000000^3129 ≤ 2177347680049^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672695673 5000000000 2177347680049 5000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2247859507/10000000000 : ℝ)^4153 ≤ (13792037325021/100000000000000 : ℝ)^3129 := by
    have hnat : (2247859507 : ℕ)^4153*100000000000000^3129 ≤ 13792037325021^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247859507 10000000000 13792037325021 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263248621/10000000000 : ℝ)^4153 ≤ (21330504531881/50000000000000 : ℝ)^3129 := by
    have hnat : (5263248621 : ℕ)^4153*50000000000000^3129 ≤ 21330504531881^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263248621 10000000000 21330504531881 50000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672695673/5000000000 : ℝ), (-2247859507/10000000000 : ℝ), (5263248621/10000000000 : ℝ)] ![(2177347680049/5000000000000 : ℝ), (13792037325021/100000000000000 : ℝ), (21330504531881/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672695673/5000000000 : ℝ)|^4153 ≤ (2177347680049/5000000000000 : ℝ)^3129
        have hw : |(2672695673/5000000000 : ℝ)|=(2672695673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2247859507/10000000000 : ℝ)|^4153 ≤ (13792037325021/100000000000000 : ℝ)^3129
        have hw : |(-2247859507/10000000000 : ℝ)|=(2247859507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263248621/10000000000 : ℝ)|^4153 ≤ (21330504531881/50000000000000 : ℝ)^3129
        have hw : |(5263248621/10000000000 : ℝ)|=(5263248621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s5_2 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336347877/2500000000 : ℝ)*x 0 + (2631624227/5000000000 : ℝ)*x 1 + (-280982439/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336347877/2500000000 : ℝ)^4153 ≤ (43546955352639/100000000000000 : ℝ)^3129 := by
    have hnat : (1336347877 : ℕ)^4153*100000000000000^3129 ≤ 43546955352639^3129*2500000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336347877 2500000000 43546955352639 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631624227/5000000000 : ℝ)^4153 ≤ (1333156477099/3125000000000 : ℝ)^3129 := by
    have hnat : (2631624227 : ℕ)^4153*3125000000000^3129 ≤ 1333156477099^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631624227 5000000000 1333156477099 3125000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (280982439/1250000000 : ℝ)^4153 ≤ (13792037365739/100000000000000 : ℝ)^3129 := by
    have hnat : (280982439 : ℕ)^4153*100000000000000^3129 ≤ 13792037365739^3129*1250000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280982439 1250000000 13792037365739 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336347877/2500000000 : ℝ), (2631624227/5000000000 : ℝ), (-280982439/1250000000 : ℝ)] ![(43546955352639/100000000000000 : ℝ), (1333156477099/3125000000000 : ℝ), (13792037365739/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336347877/2500000000 : ℝ)|^4153 ≤ (43546955352639/100000000000000 : ℝ)^3129
        have hw : |(1336347877/2500000000 : ℝ)|=(1336347877/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631624227/5000000000 : ℝ)|^4153 ≤ (1333156477099/3125000000000 : ℝ)^3129
        have hw : |(2631624227/5000000000 : ℝ)|=(2631624227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-280982439/1250000000 : ℝ)|^4153 ≤ (13792037365739/100000000000000 : ℝ)^3129
        have hw : |(-280982439/1250000000 : ℝ)|=(280982439/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s5_3 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4368667633/10000000000 : ℝ)*x 0 + (4239642607/10000000000 : ℝ)*x 1 + (900325449/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4368667633/10000000000 : ℝ)^4153 ≤ (6663144294687/20000000000000 : ℝ)^3129 := by
    have hnat : (4368667633 : ℕ)^4153*20000000000000^3129 ≤ 6663144294687^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4368667633 10000000000 6663144294687 20000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4239642607/10000000000 : ℝ)^4153 ≤ (32016113111143/100000000000000 : ℝ)^3129 := by
    have hnat : (4239642607 : ℕ)^4153*100000000000000^3129 ≤ 32016113111143^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4239642607 10000000000 32016113111143 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (900325449/2000000000 : ℝ)^4153 ≤ (34668165401019/100000000000000 : ℝ)^3129 := by
    have hnat : (900325449 : ℕ)^4153*100000000000000^3129 ≤ 34668165401019^3129*2000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900325449 2000000000 34668165401019 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4368667633/10000000000 : ℝ), (4239642607/10000000000 : ℝ), (900325449/2000000000 : ℝ)] ![(6663144294687/20000000000000 : ℝ), (32016113111143/100000000000000 : ℝ), (34668165401019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4368667633/10000000000 : ℝ)|^4153 ≤ (6663144294687/20000000000000 : ℝ)^3129
        have hw : |(4368667633/10000000000 : ℝ)|=(4368667633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4239642607/10000000000 : ℝ)|^4153 ≤ (32016113111143/100000000000000 : ℝ)^3129
        have hw : |(4239642607/10000000000 : ℝ)|=(4239642607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(900325449/2000000000 : ℝ)|^4153 ≤ (34668165401019/100000000000000 : ℝ)^3129
        have hw : |(900325449/2000000000 : ℝ)|=(900325449/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s5_4 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-218065091/1000000000 : ℝ)*x 0 + (1315897951/2500000000 : ℝ)*x 1 + (5395342447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218065091/1000000000 : ℝ)^4153 ≤ (1655926785357/12500000000000 : ℝ)^3129 := by
    have hnat : (218065091 : ℕ)^4153*12500000000000^3129 ≤ 1655926785357^3129*1000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218065091 1000000000 1655926785357 12500000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315897951/2500000000 : ℝ)^4153 ≤ (5333087635429/12500000000000 : ℝ)^3129 := by
    have hnat : (1315897951 : ℕ)^4153*12500000000000^3129 ≤ 5333087635429^3129*2500000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315897951 2500000000 5333087635429 12500000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5395342447/10000000000 : ℝ)^4153 ≤ (22043942309199/50000000000000 : ℝ)^3129 := by
    have hnat : (5395342447 : ℕ)^4153*50000000000000^3129 ≤ 22043942309199^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395342447 10000000000 22043942309199 50000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-218065091/1000000000 : ℝ), (1315897951/2500000000 : ℝ), (5395342447/10000000000 : ℝ)] ![(1655926785357/12500000000000 : ℝ), (5333087635429/12500000000000 : ℝ), (22043942309199/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-218065091/1000000000 : ℝ)|^4153 ≤ (1655926785357/12500000000000 : ℝ)^3129
        have hw : |(-218065091/1000000000 : ℝ)|=(218065091/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1315897951/2500000000 : ℝ)|^4153 ≤ (5333087635429/12500000000000 : ℝ)^3129
        have hw : |(1315897951/2500000000 : ℝ)|=(1315897951/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5395342447/10000000000 : ℝ)|^4153 ≤ (22043942309199/50000000000000 : ℝ)^3129
        have hw : |(5395342447/10000000000 : ℝ)|=(5395342447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s5_5 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2655955549/5000000000 : ℝ)*x 0 + (-2115766037/10000000000 : ℝ)*x 1 + (5395342093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655955549/5000000000 : ℝ)^4153 ≤ (539816410747/1250000000000 : ℝ)^3129 := by
    have hnat : (2655955549 : ℕ)^4153*1250000000000^3129 ≤ 539816410747^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655955549 5000000000 539816410747 1250000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2115766037/10000000000 : ℝ)^4153 ≤ (6363403173167/50000000000000 : ℝ)^3129 := by
    have hnat : (2115766037 : ℕ)^4153*50000000000000^3129 ≤ 6363403173167^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115766037 10000000000 6363403173167 50000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5395342093/10000000000 : ℝ)^4153 ≤ (44087880779029/100000000000000 : ℝ)^3129 := by
    have hnat : (5395342093 : ℕ)^4153*100000000000000^3129 ≤ 44087880779029^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395342093 10000000000 44087880779029 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655955549/5000000000 : ℝ), (-2115766037/10000000000 : ℝ), (5395342093/10000000000 : ℝ)] ![(539816410747/1250000000000 : ℝ), (6363403173167/50000000000000 : ℝ), (44087880779029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655955549/5000000000 : ℝ)|^4153 ≤ (539816410747/1250000000000 : ℝ)^3129
        have hw : |(2655955549/5000000000 : ℝ)|=(2655955549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2115766037/10000000000 : ℝ)|^4153 ≤ (6363403173167/50000000000000 : ℝ)^3129
        have hw : |(-2115766037/10000000000 : ℝ)|=(2115766037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5395342093/10000000000 : ℝ)|^4153 ≤ (44087880779029/100000000000000 : ℝ)^3129
        have hw : |(5395342093/10000000000 : ℝ)|=(5395342093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s5_6 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062382271/2000000000 : ℝ)*x 0 + (2697671169/5000000000 : ℝ)*x 1 + (-528941339/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062382271/2000000000 : ℝ)^4153 ≤ (43185315632919/100000000000000 : ℝ)^3129 := by
    have hnat : (1062382271 : ℕ)^4153*100000000000000^3129 ≤ 43185315632919^3129*2000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062382271 2000000000 43185315632919 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697671169/5000000000 : ℝ)^4153 ≤ (2204394171811/5000000000000 : ℝ)^3129 := by
    have hnat : (2697671169 : ℕ)^4153*5000000000000^3129 ≤ 2204394171811^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697671169 5000000000 2204394171811 5000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (528941339/2500000000 : ℝ)^4153 ≤ (2545360181877/20000000000000 : ℝ)^3129 := by
    have hnat : (528941339 : ℕ)^4153*20000000000000^3129 ≤ 2545360181877^3129*2500000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528941339 2500000000 2545360181877 20000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062382271/2000000000 : ℝ), (2697671169/5000000000 : ℝ), (-528941339/2500000000 : ℝ)] ![(43185315632919/100000000000000 : ℝ), (2204394171811/5000000000000 : ℝ), (2545360181877/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062382271/2000000000 : ℝ)|^4153 ≤ (43185315632919/100000000000000 : ℝ)^3129
        have hw : |(1062382271/2000000000 : ℝ)|=(1062382271/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697671169/5000000000 : ℝ)|^4153 ≤ (2204394171811/5000000000000 : ℝ)^3129
        have hw : |(2697671169/5000000000 : ℝ)|=(2697671169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-528941339/2500000000 : ℝ)|^4153 ≤ (2545360181877/20000000000000 : ℝ)^3129
        have hw : |(-528941339/2500000000 : ℝ)|=(528941339/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s5_7 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4368678903/10000000000 : ℝ)*x 0 + (2250474229/5000000000 : ℝ)*x 1 + (1060080857/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4368678903/10000000000 : ℝ)^4153 ≤ (33315835545863/100000000000000 : ℝ)^3129 := by
    have hnat : (4368678903 : ℕ)^4153*100000000000000^3129 ≤ 33315835545863^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4368678903 10000000000 33315835545863 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2250474229/5000000000 : ℝ)^4153 ≤ (1733061365097/5000000000000 : ℝ)^3129 := by
    have hnat : (2250474229 : ℕ)^4153*5000000000000^3129 ≤ 1733061365097^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250474229 5000000000 1733061365097 5000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1060080857/2500000000 : ℝ)^4153 ≤ (32022937127827/100000000000000 : ℝ)^3129 := by
    have hnat : (1060080857 : ℕ)^4153*100000000000000^3129 ≤ 32022937127827^3129*2500000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060080857 2500000000 32022937127827 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4368678903/10000000000 : ℝ), (2250474229/5000000000 : ℝ), (1060080857/2500000000 : ℝ)] ![(33315835545863/100000000000000 : ℝ), (1733061365097/5000000000000 : ℝ), (32022937127827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4368678903/10000000000 : ℝ)|^4153 ≤ (33315835545863/100000000000000 : ℝ)^3129
        have hw : |(4368678903/10000000000 : ℝ)|=(4368678903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2250474229/5000000000 : ℝ)|^4153 ≤ (1733061365097/5000000000000 : ℝ)^3129
        have hw : |(2250474229/5000000000 : ℝ)|=(2250474229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1060080857/2500000000 : ℝ)|^4153 ≤ (32022937127827/100000000000000 : ℝ)^3129
        have hw : |(1060080857/2500000000 : ℝ)|=(1060080857/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1113_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74454099/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11119/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1409/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14077/100000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (11119/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11119/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11119/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11119/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11119/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11119/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11119/100000 : ℝ) ^ (8305/2048 : ℝ) ≤ (541612705373453/4000000000000000000 : ℝ) := by
    have hpowers : (11119/100000 : ℝ)^8305 ≤ (541612705373453/4000000000000000000 : ℝ)^2048 := by
      have hnat : (11119 : ℕ)^8305*4000000000000000000^2048 ≤ 541612705373453^2048*100000^8305 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11119 100000 541612705373453 4000000000000000000 8305 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11119/100000 : ℝ)) (X := (541612705373453/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8305 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14237/100000 : ℝ) ^ (8305/2048 : ℝ) ≤ (36894628667624477/100000000000000000000 : ℝ) := by
    have hpowers : (14237/100000 : ℝ)^8305 ≤ (36894628667624477/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14237 : ℕ)^8305*100000000000000000000^2048 ≤ 36894628667624477^2048*100000^8305 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14237 100000 36894628667624477 100000000000000000000 8305 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14237/100000 : ℝ)) (X := (36894628667624477/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8305 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000541612705373453/2000000000000000000 : ℝ) ≤ (5000333868056413/5000000000000000 : ℝ) ^ (8305/2048 : ℝ) := by
    have hpowers : (2000541612705373453/2000000000000000000 : ℝ)^2048 ≤ (5000333868056413/5000000000000000 : ℝ)^8305 := by
      have hnat : (2000541612705373453 : ℕ)^2048*5000000000000000^8305 ≤ 5000333868056413^8305*2000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000541612705373453 2000000000000000000 5000333868056413 5000000000000000 2048 8305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000333868056413/5000000000000000 : ℝ)) (X := (2000541612705373453/2000000000000000000 : ℝ)) (by norm_num) 8305 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025217473150980401/50000000000000000000 : ℝ) ≤ (2500310870414557/2500000000000000 : ℝ) ^ (8305/2048 : ℝ) := by
    have hpowers : (50025217473150980401/50000000000000000000 : ℝ)^2048 ≤ (2500310870414557/2500000000000000 : ℝ)^8305 := by
      have hnat : (50025217473150980401 : ℕ)^2048*2500000000000000^8305 ≤ 2500310870414557^8305*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025217473150980401 50000000000000000000 2500310870414557 2500000000000000 2048 8305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500310870414557/2500000000000000 : ℝ)) (X := (50025217473150980401/50000000000000000000 : ℝ)) (by norm_num) 8305 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036894628667624477/50000000000000000000 : ℝ) ≤ (1000181922720363/1000000000000000 : ℝ) ^ (8305/2048 : ℝ) := by
    have hpowers : (50036894628667624477/50000000000000000000 : ℝ)^2048 ≤ (1000181922720363/1000000000000000 : ℝ)^8305 := by
      have hnat : (50036894628667624477 : ℕ)^2048*1000000000000000^8305 ≤ 1000181922720363^8305*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036894628667624477 50000000000000000000 1000181922720363 1000000000000000 2048 8305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000181922720363/1000000000000000 : ℝ)) (X := (50036894628667624477/50000000000000000000 : ℝ)) (by norm_num) 8305 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(541612705373453/4000000000000000000 : ℝ) ≤ ((974039955367535681/974375000000000000 : ℝ)+2*(287872772701/155900000000000 : ℝ)*(11119/100000 : ℝ))^(8305/2048 : ℝ) := by
    rw [show (974039955367535681/974375000000000000 : ℝ)+2*(287872772701/155900000000000 : ℝ)*(11119/100000 : ℝ)=(5000333868056413/5000000000000000 : ℝ) by norm_num, show 1+2*(541612705373453/4000000000000000000 : ℝ)=(2000541612705373453/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36894628667624477/100000000000000000000 : ℝ)+(541612705373453/4000000000000000000 : ℝ) ≤ ((974039955367535681/974375000000000000 : ℝ)+(287872772701/155900000000000 : ℝ)*((14237/100000 : ℝ)+(11119/100000 : ℝ)))^(8305/2048 : ℝ) := by
    rw [show (974039955367535681/974375000000000000 : ℝ)+(287872772701/155900000000000 : ℝ)*((14237/100000 : ℝ)+(11119/100000 : ℝ))=(2500310870414557/2500000000000000 : ℝ) by norm_num, show 1+(36894628667624477/100000000000000000000 : ℝ)+(541612705373453/4000000000000000000 : ℝ)=(50025217473150980401/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36894628667624477/100000000000000000000 : ℝ) ≤ ((974039955367535681/974375000000000000 : ℝ)+2*(287872772701/155900000000000 : ℝ)*(14237/100000 : ℝ))^(8305/2048 : ℝ) := by
    rw [show (974039955367535681/974375000000000000 : ℝ)+2*(287872772701/155900000000000 : ℝ)*(14237/100000 : ℝ)=(1000181922720363/1000000000000000 : ℝ) by norm_num, show 1+2*(36894628667624477/100000000000000000000 : ℝ)=(50036894628667624477/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (974039955367535681/974375000000000000 : ℝ)*(X 1 0+X 2 0)+(287872772701/155900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8305/2048 : ℝ)) (lo := (11119/100000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (974039955367535681/974375000000000000 : ℝ)) (alpha := (287872772701/155900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (974039955367535681/974375000000000000 : ℝ)*(X 0 1+X 2 1)+(287872772701/155900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8305/2048 : ℝ)) (lo := (11119/100000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (974039955367535681/974375000000000000 : ℝ)) (alpha := (287872772701/155900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (974039955367535681/974375000000000000 : ℝ)*(X 0 2+X 1 2)+(287872772701/155900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8305/2048 : ℝ)) (lo := (11119/100000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (974039955367535681/974375000000000000 : ℝ)) (alpha := (287872772701/155900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-436129177/2000000000 : ℝ)*X 0 0+(2697843407/5000000000 : ℝ)*X 0 1+(5263248399/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672695673/5000000000 : ℝ)*X 1 0+(-2247859507/10000000000 : ℝ)*X 1 1+(5263248621/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336347877/2500000000 : ℝ)*X 2 0+(2631624227/5000000000 : ℝ)*X 2 1+(-280982439/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4368667633/10000000000 : ℝ)*X 0 0+(4239642607/10000000000 : ℝ)*X 0 1+(900325449/2000000000 : ℝ)*X 0 2+(4368667633/10000000000 : ℝ)*X 1 0+(4239642607/10000000000 : ℝ)*X 1 1+(900325449/2000000000 : ℝ)*X 1 2+(4368667633/10000000000 : ℝ)*X 2 0+(4239642607/10000000000 : ℝ)*X 2 1+(900325449/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-218065091/1000000000 : ℝ)*X 0 0+(1315897951/2500000000 : ℝ)*X 0 1+(5395342447/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655955549/5000000000 : ℝ)*X 1 0+(-2115766037/10000000000 : ℝ)*X 1 1+(5395342093/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062382271/2000000000 : ℝ)*X 2 0+(2697671169/5000000000 : ℝ)*X 2 1+(-528941339/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4368678903/10000000000 : ℝ)*X 0 0+(2250474229/5000000000 : ℝ)*X 0 1+(1060080857/2500000000 : ℝ)*X 0 2+(4368678903/10000000000 : ℝ)*X 1 0+(2250474229/5000000000 : ℝ)*X 1 1+(1060080857/2500000000 : ℝ)*X 1 2+(4368678903/10000000000 : ℝ)*X 2 0+(2250474229/5000000000 : ℝ)*X 2 1+(1060080857/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2521328961361438202992713/487187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (110480111/10000000000000 : ℝ)*(base19) + (1204412311/100000000000000 : ℝ)*(base23) + (3453809/5000000000000 : ℝ)*(lower2) + (159061971/100000000000000 : ℝ)*(upper3) + (97709297/100000000000000 : ℝ)*(upper5) + (113678123882581/2000000000000 : ℝ)*(major0) + (113678123882581/2000000000000 : ℝ)*(major1) + (113678123882581/2000000000000 : ℝ)*(major2) + (23595993876033/312500000000 : ℝ)*(sp0) + (7550757200907873/100000000000000 : ℝ)*(sp1) + (235961159415521/3125000000000 : ℝ)*(sp2) + (763406845405257/20000000000000 : ℝ)*(sp3) + (5033172303/12500000000000 : ℝ)*(sp4) + (9841506839/50000000000000 : ℝ)*(sp7) + (3817053910039963/100000000000000 : ℝ)*(f.failure) + (7550758305708983/100000000000000 : ℝ)*(f.sum) + (5486938039569/1559000000000000000000000000 : ℝ)*base65 + (21254520090447661/1948750000000000000000000000000 : ℝ)*base67 + (280681724700161/1948750000000000000000000000000 : ℝ)*base69 + (27087266340350161/1948750000000000000000000000000 : ℝ)*base71 + (423388254381/779500000000000000000000000 : ℝ)*base74 + (39958486398156411/1948750000000000000000000000000 : ℝ)*base75 + (29776552413147661/1948750000000000000000000000000 : ℝ)*base77 + (40778515594487661/1948750000000000000000000000000 : ℝ)*base79 + (305956140489/311800000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (841663/5000000000000000000000 : ℝ)*base90 + (841663/5000000000000000000000 : ℝ)*base92 + (841663/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (35922751099647364207400127/6089843750000000000000000000000 : ℝ) := by norm_num
    linear_combination (37374471/4000000000000 : ℝ)*(base19) + (838514943/50000000000000 : ℝ)*(base23) + (277363717/100000000000000 : ℝ)*(lower2) + (161552299/100000000000000 : ℝ)*(upper3) + (153669997/50000000000000 : ℝ)*(lower4) + (1428379171017997/25000000000000 : ℝ)*(major0) + (1428379171017997/25000000000000 : ℝ)*(major1) + (1428379171017997/25000000000000 : ℝ)*(major2) + (12653544601/25000000000000 : ℝ)*(sp2) + (318245963/25000000000000 : ℝ)*(sp3) + (7590094197833777/100000000000000 : ℝ)*(sp4) + (3795046631736001/50000000000000 : ℝ)*(sp5) + (7590041906625487/100000000000000 : ℝ)*(sp6) + (1918468850349889/50000000000000 : ℝ)*(sp7) + (383693897368363/10000000000000 : ℝ)*(f.failure) + (7590094197833777/100000000000000 : ℝ)*(f.sum) + (3471595938093/487187500000000000000000000 : ℝ)*base65 + (92035351221930293/24359375000000000000000000000000 : ℝ)*base68 + (41757789775964541/12179687500000000000000000000000 : ℝ)*base69 + (268587270806975957/24359375000000000000000000000000 : ℝ)*base71 + (9388217643771/3897500000000000000000000000 : ℝ)*base74 + (102536649479225957/24359375000000000000000000000000 : ℝ)*base75 + (87642753709433291/12179687500000000000000000000000 : ℝ)*base77 + (210972248370774043/24359375000000000000000000000000 : ℝ)*base80 + (19162077316477/1948750000000000000000000000 : ℝ)*base81 + (1730063/500000000000000000000 : ℝ)*base90 + (1730063/500000000000000000000 : ℝ)*base92 + (1730063/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1113_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74454099/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11119/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1409/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14077/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1113_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1113_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74454099/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16591/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8937/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1409/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14077/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1113_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1113_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1113_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74454099/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16591/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8937/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1409/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14077/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1113_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
