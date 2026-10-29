-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1603_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:39:46.873321+00:00
-- url     : https://prove2.me/submissions/fcfb304f-e050-4736-b709-dad08cf44480

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
theorem support_rectangle_w1603_s6_0 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-430517431/2500000000 : ℝ)*x 0 + (273077853/500000000 : ℝ)*x 1 + (1295035911/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (430517431/2500000000 : ℝ)^4731 ≤ (10593070272427/100000000000000 : ℝ)^3707 := by
    have hnat : (430517431 : ℕ)^4731*100000000000000^3707 ≤ 10593070272427^3707*2500000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430517431 2500000000 10593070272427 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (273077853/500000000 : ℝ)^4731 ≤ (23105976063139/50000000000000 : ℝ)^3707 := by
    have hnat : (273077853 : ℕ)^4731*50000000000000^3707 ≤ 23105976063139^3707*500000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273077853 500000000 23105976063139 50000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1295035911/2500000000 : ℝ)^4731 ≤ (43194977590037/100000000000000 : ℝ)^3707 := by
    have hnat : (1295035911 : ℕ)^4731*100000000000000^3707 ≤ 43194977590037^3707*2500000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295035911 2500000000 43194977590037 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-430517431/2500000000 : ℝ), (273077853/500000000 : ℝ), (1295035911/2500000000 : ℝ)] ![(10593070272427/100000000000000 : ℝ), (23105976063139/50000000000000 : ℝ), (43194977590037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-430517431/2500000000 : ℝ)|^4731 ≤ (10593070272427/100000000000000 : ℝ)^3707
        have hw : |(-430517431/2500000000 : ℝ)|=(430517431/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(273077853/500000000 : ℝ)|^4731 ≤ (23105976063139/50000000000000 : ℝ)^3707
        have hw : |(273077853/500000000 : ℝ)|=(273077853/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1295035911/2500000000 : ℝ)|^4731 ≤ (43194977590037/100000000000000 : ℝ)^3707
        have hw : |(1295035911/2500000000 : ℝ)|=(1295035911/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1603_s6_1 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354534609/10000000000 : ℝ)*x 0 + (-1867223933/10000000000 : ℝ)*x 1 + (25900719/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354534609/10000000000 : ℝ)^4731 ≤ (22529700141861/50000000000000 : ℝ)^3707 := by
    have hnat : (5354534609 : ℕ)^4731*50000000000000^3707 ≤ 22529700141861^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354534609 10000000000 22529700141861 50000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1867223933/10000000000 : ℝ)^4731 ≤ (5872810221351/50000000000000 : ℝ)^3707 := by
    have hnat : (1867223933 : ℕ)^4731*50000000000000^3707 ≤ 5872810221351^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1867223933 10000000000 5872810221351 50000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (25900719/50000000 : ℝ)^4731 ≤ (5399372406273/12500000000000 : ℝ)^3707 := by
    have hnat : (25900719 : ℕ)^4731*12500000000000^3707 ≤ 5399372406273^3707*50000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25900719 50000000 5399372406273 12500000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354534609/10000000000 : ℝ), (-1867223933/10000000000 : ℝ), (25900719/50000000 : ℝ)] ![(22529700141861/50000000000000 : ℝ), (5872810221351/50000000000000 : ℝ), (5399372406273/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354534609/10000000000 : ℝ)|^4731 ≤ (22529700141861/50000000000000 : ℝ)^3707
        have hw : |(5354534609/10000000000 : ℝ)|=(5354534609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1867223933/10000000000 : ℝ)|^4731 ≤ (5872810221351/50000000000000 : ℝ)^3707
        have hw : |(-1867223933/10000000000 : ℝ)|=(1867223933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(25900719/50000000 : ℝ)|^4731 ≤ (5399372406273/12500000000000 : ℝ)^3707
        have hw : |(25900719/50000000 : ℝ)|=(25900719/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1603_s6_2 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354534533/10000000000 : ℝ)*x 0 + (647517967/1250000000 : ℝ)*x 1 + (-933612061/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354534533/10000000000 : ℝ)^4731 ≤ (45059399467501/100000000000000 : ℝ)^3707 := by
    have hnat : (5354534533 : ℕ)^4731*100000000000000^3707 ≤ 45059399467501^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354534533 10000000000 45059399467501 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (647517967/1250000000 : ℝ)^4731 ≤ (21597489284549/50000000000000 : ℝ)^3707 := by
    have hnat : (647517967 : ℕ)^4731*50000000000000^3707 ≤ 21597489284549^3707*1250000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647517967 1250000000 21597489284549 50000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (933612061/5000000000 : ℝ)^4731 ≤ (11745621960003/100000000000000 : ℝ)^3707 := by
    have hnat : (933612061 : ℕ)^4731*100000000000000^3707 ≤ 11745621960003^3707*5000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      933612061 5000000000 11745621960003 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354534533/10000000000 : ℝ), (647517967/1250000000 : ℝ), (-933612061/5000000000 : ℝ)] ![(45059399467501/100000000000000 : ℝ), (21597489284549/50000000000000 : ℝ), (11745621960003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354534533/10000000000 : ℝ)|^4731 ≤ (45059399467501/100000000000000 : ℝ)^3707
        have hw : |(5354534533/10000000000 : ℝ)|=(5354534533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(647517967/1250000000 : ℝ)|^4731 ≤ (21597489284549/50000000000000 : ℝ)^3707
        have hw : |(647517967/1250000000 : ℝ)|=(647517967/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-933612061/5000000000 : ℝ)|^4731 ≤ (11745621960003/100000000000000 : ℝ)^3707
        have hw : |(-933612061/5000000000 : ℝ)|=(933612061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1603_s6_3 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4218360209/10000000000 : ℝ)*x 0 + (3886609743/10000000000 : ℝ)*x 1 + (2285884347/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4218360209/10000000000 : ℝ)^4731 ≤ (33234988983023/100000000000000 : ℝ)^3707 := by
    have hnat : (4218360209 : ℕ)^4731*100000000000000^3707 ≤ 33234988983023^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4218360209 10000000000 33234988983023 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3886609743/10000000000 : ℝ)^4731 ≤ (29936181998207/100000000000000 : ℝ)^3707 := by
    have hnat : (3886609743 : ℕ)^4731*100000000000000^3707 ≤ 29936181998207^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3886609743 10000000000 29936181998207 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2285884347/5000000000 : ℝ)^4731 ≤ (36828829004891/100000000000000 : ℝ)^3707 := by
    have hnat : (2285884347 : ℕ)^4731*100000000000000^3707 ≤ 36828829004891^3707*5000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2285884347 5000000000 36828829004891 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4218360209/10000000000 : ℝ), (3886609743/10000000000 : ℝ), (2285884347/5000000000 : ℝ)] ![(33234988983023/100000000000000 : ℝ), (29936181998207/100000000000000 : ℝ), (36828829004891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4218360209/10000000000 : ℝ)|^4731 ≤ (33234988983023/100000000000000 : ℝ)^3707
        have hw : |(4218360209/10000000000 : ℝ)|=(4218360209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3886609743/10000000000 : ℝ)|^4731 ≤ (29936181998207/100000000000000 : ℝ)^3707
        have hw : |(3886609743/10000000000 : ℝ)|=(3886609743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2285884347/5000000000 : ℝ)|^4731 ≤ (36828829004891/100000000000000 : ℝ)^3707
        have hw : |(2285884347/5000000000 : ℝ)|=(2285884347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1603_s6_4 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1722140517/10000000000 : ℝ)*x 0 + (5182228021/10000000000 : ℝ)*x 1 + (1364862807/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1722140517/10000000000 : ℝ)^4731 ≤ (10593626041361/100000000000000 : ℝ)^3707 := by
    have hnat : (1722140517 : ℕ)^4731*100000000000000^3707 ≤ 10593626041361^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1722140517 10000000000 10593626041361 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5182228021/10000000000 : ℝ)^4731 ≤ (5402145086131/12500000000000 : ℝ)^3707 := by
    have hnat : (5182228021 : ℕ)^4731*12500000000000^3707 ≤ 5402145086131^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182228021 10000000000 5402145086131 12500000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1364862807/2500000000 : ℝ)^4731 ≤ (23094606630423/50000000000000 : ℝ)^3707 := by
    have hnat : (1364862807 : ℕ)^4731*50000000000000^3707 ≤ 23094606630423^3707*2500000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364862807 2500000000 23094606630423 50000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1722140517/10000000000 : ℝ), (5182228021/10000000000 : ℝ), (1364862807/2500000000 : ℝ)] ![(10593626041361/100000000000000 : ℝ), (5402145086131/12500000000000 : ℝ), (23094606630423/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1722140517/10000000000 : ℝ)|^4731 ≤ (10593626041361/100000000000000 : ℝ)^3707
        have hw : |(-1722140517/10000000000 : ℝ)|=(1722140517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5182228021/10000000000 : ℝ)|^4731 ≤ (5402145086131/12500000000000 : ℝ)^3707
        have hw : |(5182228021/10000000000 : ℝ)|=(5182228021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1364862807/2500000000 : ℝ)|^4731 ≤ (23094606630423/50000000000000 : ℝ)^3707
        have hw : |(1364862807/2500000000 : ℝ)|=(1364862807/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1603_s6_5 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639947623/5000000000 : ℝ)*x 0 + (5459451349/10000000000 : ℝ)*x 1 + (-793958373/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639947623/5000000000 : ℝ)^4731 ≤ (22129670484931/50000000000000 : ℝ)^3707 := by
    have hnat : (2639947623 : ℕ)^4731*50000000000000^3707 ≤ 22129670484931^3707*5000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639947623 5000000000 22129670484931 50000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5459451349/10000000000 : ℝ)^4731 ≤ (2309460728367/5000000000000 : ℝ)^3707 := by
    have hnat : (5459451349 : ℕ)^4731*5000000000000^3707 ≤ 2309460728367^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5459451349 10000000000 2309460728367 5000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (793958373/5000000000 : ℝ)^4731 ≤ (9551444454399/100000000000000 : ℝ)^3707 := by
    have hnat : (793958373 : ℕ)^4731*100000000000000^3707 ≤ 9551444454399^3707*5000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      793958373 5000000000 9551444454399 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639947623/5000000000 : ℝ), (5459451349/10000000000 : ℝ), (-793958373/5000000000 : ℝ)] ![(22129670484931/50000000000000 : ℝ), (2309460728367/5000000000000 : ℝ), (9551444454399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639947623/5000000000 : ℝ)|^4731 ≤ (22129670484931/50000000000000 : ℝ)^3707
        have hw : |(2639947623/5000000000 : ℝ)|=(2639947623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5459451349/10000000000 : ℝ)|^4731 ≤ (2309460728367/5000000000000 : ℝ)^3707
        have hw : |(5459451349/10000000000 : ℝ)|=(5459451349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-793958373/5000000000 : ℝ)|^4731 ≤ (9551444454399/100000000000000 : ℝ)^3707
        have hw : |(-793958373/5000000000 : ℝ)|=(793958373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1603_s6_6 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (263658409/625000000 : ℝ)*x 0 + (4566693793/10000000000 : ℝ)*x 1 + (3891737363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (263658409/625000000 : ℝ)^4731 ≤ (33236741932117/100000000000000 : ℝ)^3707 := by
    have hnat : (263658409 : ℕ)^4731*100000000000000^3707 ≤ 33236741932117^3707*625000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263658409 625000000 33236741932117 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4566693793/10000000000 : ℝ)^4731 ≤ (9194165527419/25000000000000 : ℝ)^3707 := by
    have hnat : (4566693793 : ℕ)^4731*25000000000000^3707 ≤ 9194165527419^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4566693793 10000000000 9194165527419 25000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3891737363/10000000000 : ℝ)^4731 ≤ (14993297976891/50000000000000 : ℝ)^3707 := by
    have hnat : (3891737363 : ℕ)^4731*50000000000000^3707 ≤ 14993297976891^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3891737363 10000000000 14993297976891 50000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(263658409/625000000 : ℝ), (4566693793/10000000000 : ℝ), (3891737363/10000000000 : ℝ)] ![(33236741932117/100000000000000 : ℝ), (9194165527419/25000000000000 : ℝ), (14993297976891/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(263658409/625000000 : ℝ)|^4731 ≤ (33236741932117/100000000000000 : ℝ)^3707
        have hw : |(263658409/625000000 : ℝ)|=(263658409/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4566693793/10000000000 : ℝ)|^4731 ≤ (9194165527419/25000000000000 : ℝ)^3707
        have hw : |(4566693793/10000000000 : ℝ)|=(4566693793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3891737363/10000000000 : ℝ)|^4731 ≤ (14993297976891/50000000000000 : ℝ)^3707
        have hw : |(3891737363/10000000000 : ℝ)|=(3891737363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1603_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5366729/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16353/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2597/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10389/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16353/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16353/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2597/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16353/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2597/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16353/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2597/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16353/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2597/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16353/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2597/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16353/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2597/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2597/25000 : ℝ) ^ (4727/1024 : ℝ) ≤ (721180537390809/25000000000000000000 : ℝ) := by
    have hpowers : (2597/25000 : ℝ)^4727 ≤ (721180537390809/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2597 : ℕ)^4727*25000000000000000000^1024 ≤ 721180537390809^1024*25000^4727 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2597 25000 721180537390809 25000000000000000000 4727 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2597/25000 : ℝ)) (X := (721180537390809/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4727 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16353/100000 : ℝ) ^ (4727/1024 : ℝ) ≤ (5857872231995967/25000000000000000000 : ℝ) := by
    have hpowers : (16353/100000 : ℝ)^4727 ≤ (5857872231995967/25000000000000000000 : ℝ)^1024 := by
      have hnat : (16353 : ℕ)^4727*25000000000000000000^1024 ≤ 5857872231995967^1024*100000^4727 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16353 100000 5857872231995967 25000000000000000000 4727 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16353/100000 : ℝ)) (X := (5857872231995967/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4727 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500721180537390809/12500000000000000000 : ℝ) ≤ (10000124979425837/10000000000000000 : ℝ) ^ (4727/1024 : ℝ) := by
    have hpowers : (12500721180537390809/12500000000000000000 : ℝ)^1024 ≤ (10000124979425837/10000000000000000 : ℝ)^4727 := by
      have hnat : (12500721180537390809 : ℕ)^1024*10000000000000000^4727 ≤ 10000124979425837^4727*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500721180537390809 12500000000000000000 10000124979425837 10000000000000000 1024 4727 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000124979425837/10000000000000000 : ℝ)) (X := (12500721180537390809/12500000000000000000 : ℝ)) (by norm_num) 4727 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3125822381596173347/3125000000000000000 : ℝ) ≤ (1000057002375463/1000000000000000 : ℝ) ^ (4727/1024 : ℝ) := by
    have hpowers : (3125822381596173347/3125000000000000000 : ℝ)^1024 ≤ (1000057002375463/1000000000000000 : ℝ)^4727 := by
      have hnat : (3125822381596173347 : ℕ)^1024*1000000000000000^4727 ≤ 1000057002375463^4727*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125822381596173347 3125000000000000000 1000057002375463 1000000000000000 1024 4727 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000057002375463/1000000000000000 : ℝ)) (X := (3125822381596173347/3125000000000000000 : ℝ)) (by norm_num) 4727 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12505857872231995967/12500000000000000000 : ℝ) ≤ (10001015068083423/10000000000000000 : ℝ) ^ (4727/1024 : ℝ) := by
    have hpowers : (12505857872231995967/12500000000000000000 : ℝ)^1024 ≤ (10001015068083423/10000000000000000 : ℝ)^4727 := by
      have hnat : (12505857872231995967 : ℕ)^1024*10000000000000000^4727 ≤ 10001015068083423^4727*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505857872231995967 12500000000000000000 10001015068083423 10000000000000000 1024 4727 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001015068083423/10000000000000000 : ℝ)) (X := (12505857872231995967/12500000000000000000 : ℝ)) (by norm_num) 4727 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(721180537390809/25000000000000000000 : ℝ) ≤ ((59641499261300114337/59650000000000000000 : ℝ)+2*(445044328793/596500000000000 : ℝ)*(2597/25000 : ℝ))^(4727/1024 : ℝ) := by
    rw [show (59641499261300114337/59650000000000000000 : ℝ)+2*(445044328793/596500000000000 : ℝ)*(2597/25000 : ℝ)=(10000124979425837/10000000000000000 : ℝ) by norm_num, show 1+2*(721180537390809/25000000000000000000 : ℝ)=(12500721180537390809/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5857872231995967/25000000000000000000 : ℝ)+(721180537390809/25000000000000000000 : ℝ) ≤ ((59641499261300114337/59650000000000000000 : ℝ)+(445044328793/596500000000000 : ℝ)*((16353/100000 : ℝ)+(2597/25000 : ℝ)))^(4727/1024 : ℝ) := by
    rw [show (59641499261300114337/59650000000000000000 : ℝ)+(445044328793/596500000000000 : ℝ)*((16353/100000 : ℝ)+(2597/25000 : ℝ))=(1000057002375463/1000000000000000 : ℝ) by norm_num, show 1+(5857872231995967/25000000000000000000 : ℝ)+(721180537390809/25000000000000000000 : ℝ)=(3125822381596173347/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5857872231995967/25000000000000000000 : ℝ) ≤ ((59641499261300114337/59650000000000000000 : ℝ)+2*(445044328793/596500000000000 : ℝ)*(16353/100000 : ℝ))^(4727/1024 : ℝ) := by
    rw [show (59641499261300114337/59650000000000000000 : ℝ)+2*(445044328793/596500000000000 : ℝ)*(16353/100000 : ℝ)=(10001015068083423/10000000000000000 : ℝ) by norm_num, show 1+2*(5857872231995967/25000000000000000000 : ℝ)=(12505857872231995967/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (59641499261300114337/59650000000000000000 : ℝ)*(X 1 0+X 2 0)+(445044328793/596500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4727/1024 : ℝ)) (lo := (2597/25000 : ℝ)) (hi := (16353/100000 : ℝ)) (c := (59641499261300114337/59650000000000000000 : ℝ)) (alpha := (445044328793/596500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (59641499261300114337/59650000000000000000 : ℝ)*(X 0 1+X 2 1)+(445044328793/596500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4727/1024 : ℝ)) (lo := (2597/25000 : ℝ)) (hi := (16353/100000 : ℝ)) (c := (59641499261300114337/59650000000000000000 : ℝ)) (alpha := (445044328793/596500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (59641499261300114337/59650000000000000000 : ℝ)*(X 0 2+X 1 2)+(445044328793/596500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4727/1024 : ℝ)) (lo := (2597/25000 : ℝ)) (hi := (16353/100000 : ℝ)) (c := (59641499261300114337/59650000000000000000 : ℝ)) (alpha := (445044328793/596500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-430517431/2500000000 : ℝ)*X 0 0+(273077853/500000000 : ℝ)*X 0 1+(1295035911/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5354534609/10000000000 : ℝ)*X 1 0+(-1867223933/10000000000 : ℝ)*X 1 1+(25900719/50000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5354534533/10000000000 : ℝ)*X 2 0+(647517967/1250000000 : ℝ)*X 2 1+(-933612061/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4218360209/10000000000 : ℝ)*X 0 0+(3886609743/10000000000 : ℝ)*X 0 1+(2285884347/5000000000 : ℝ)*X 0 2+(4218360209/10000000000 : ℝ)*X 1 0+(3886609743/10000000000 : ℝ)*X 1 1+(2285884347/5000000000 : ℝ)*X 1 2+(4218360209/10000000000 : ℝ)*X 2 0+(3886609743/10000000000 : ℝ)*X 2 1+(2285884347/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1722140517/10000000000 : ℝ)*X 0 0+(5182228021/10000000000 : ℝ)*X 0 1+(1364862807/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2639947623/5000000000 : ℝ)*X 2 0+(5459451349/10000000000 : ℝ)*X 2 1+(-793958373/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_s6_5 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((263658409/625000000 : ℝ)*X 0 0+(4566693793/10000000000 : ℝ)*X 0 1+(3891737363/10000000000 : ℝ)*X 0 2+(263658409/625000000 : ℝ)*X 1 0+(4566693793/10000000000 : ℝ)*X 1 1+(3891737363/10000000000 : ℝ)*X 1 2+(263658409/625000000 : ℝ)*X 2 0+(4566693793/10000000000 : ℝ)*X 2 1+(3891737363/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_s6_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7448473969369667806705242099/2982500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (27441133/10000000000000 : ℝ)*(base19) + (145141803/50000000000000 : ℝ)*(base23) + (35511329/100000000000000 : ℝ)*(upper2) + (3177523/3125000000000 : ℝ)*(upper3) + (2506509491305009/100000000000000 : ℝ)*(major0) + (2506509491305009/100000000000000 : ℝ)*(major1) + (2506509491305009/100000000000000 : ℝ)*(major2) + (1776748482822347/50000000000000 : ℝ)*(sp0) + (44418747135693/1250000000000 : ℝ)*(sp1) + (3553499754197131/100000000000000 : ℝ)*(sp2) + (291903361723153/20000000000000 : ℝ)*(sp3) + (769905519/25000000000000 : ℝ)*(sp4) + (786033/100000000000000 : ℝ)*(sp5) + (2045481051/100000000000000 : ℝ)*(sp6) + (91219928381051/6250000000000 : ℝ)*(f.failure) + (355350004526677/10000000000000 : ℝ)*(f.sum) + (12429131737289/3728125000000000000000000000 : ℝ)*base65 + (4306189389955485967/5965000000000000000000000000000000 : ℝ)*base68 + (14233486051500485967/5965000000000000000000000000000000 : ℝ)*base70 + (9672288566930485967/5965000000000000000000000000000000 : ℝ)*base72 + (97618308914787/29825000000000000000000000000 : ℝ)*base73 + (11823198353259514033/5965000000000000000000000000000000 : ℝ)*base75 + (58847660581404514033/5965000000000000000000000000000000 : ℝ)*base77 + (31007907617560485967/5965000000000000000000000000000000 : ℝ)*base80 + (15478262914081/14912500000000000000000000000 : ℝ)*base81 + (236267/39062500000000000000 : ℝ)*base90 + (236267/39062500000000000000 : ℝ)*base92 + (236267/39062500000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1603_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5366729/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16353/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2597/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10389/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16353/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1603_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1603_s7_0 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354534447/10000000000 : ℝ)*x 0 + (1036029179/2000000000 : ℝ)*x 1 + (-933610687/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354534447/10000000000 : ℝ)^4731 ≤ (45059398543883/100000000000000 : ℝ)^3707 := by
    have hnat : (5354534447 : ℕ)^4731*100000000000000^3707 ≤ 45059398543883^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354534447 10000000000 45059398543883 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036029179/2000000000 : ℝ)^4731 ≤ (43195001545101/100000000000000 : ℝ)^3707 := by
    have hnat : (1036029179 : ℕ)^4731*100000000000000^3707 ≤ 43195001545101^3707*2000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036029179 2000000000 43195001545101 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (933610687/5000000000 : ℝ)^4731 ≤ (11745599898933/100000000000000 : ℝ)^3707 := by
    have hnat : (933610687 : ℕ)^4731*100000000000000^3707 ≤ 11745599898933^3707*5000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      933610687 5000000000 11745599898933 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354534447/10000000000 : ℝ), (1036029179/2000000000 : ℝ), (-933610687/5000000000 : ℝ)] ![(45059398543883/100000000000000 : ℝ), (43195001545101/100000000000000 : ℝ), (11745599898933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354534447/10000000000 : ℝ)|^4731 ≤ (45059398543883/100000000000000 : ℝ)^3707
        have hw : |(5354534447/10000000000 : ℝ)|=(5354534447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036029179/2000000000 : ℝ)|^4731 ≤ (43195001545101/100000000000000 : ℝ)^3707
        have hw : |(1036029179/2000000000 : ℝ)|=(1036029179/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-933610687/5000000000 : ℝ)|^4731 ≤ (11745599898933/100000000000000 : ℝ)^3707
        have hw : |(-933610687/5000000000 : ℝ)|=(933610687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1603_s7_1 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2109180763/5000000000 : ℝ)*x 0 + (3886613031/10000000000 : ℝ)*x 1 + (2285882131/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2109180763/5000000000 : ℝ)^4731 ≤ (33235002225463/100000000000000 : ℝ)^3707 := by
    have hnat : (2109180763 : ℕ)^4731*100000000000000^3707 ≤ 33235002225463^3707*5000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109180763 5000000000 33235002225463 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3886613031/10000000000 : ℝ)^4731 ≤ (29936214319423/100000000000000 : ℝ)^3707 := by
    have hnat : (3886613031 : ℕ)^4731*100000000000000^3707 ≤ 29936214319423^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3886613031 10000000000 29936214319423 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2285882131/5000000000 : ℝ)^4731 ≤ (7365756687929/20000000000000 : ℝ)^3707 := by
    have hnat : (2285882131 : ℕ)^4731*20000000000000^3707 ≤ 7365756687929^3707*5000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2285882131 5000000000 7365756687929 20000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2109180763/5000000000 : ℝ), (3886613031/10000000000 : ℝ), (2285882131/5000000000 : ℝ)] ![(33235002225463/100000000000000 : ℝ), (29936214319423/100000000000000 : ℝ), (7365756687929/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2109180763/5000000000 : ℝ)|^4731 ≤ (33235002225463/100000000000000 : ℝ)^3707
        have hw : |(2109180763/5000000000 : ℝ)|=(2109180763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3886613031/10000000000 : ℝ)|^4731 ≤ (29936214319423/100000000000000 : ℝ)^3707
        have hw : |(3886613031/10000000000 : ℝ)|=(3886613031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2285882131/5000000000 : ℝ)|^4731 ≤ (7365756687929/20000000000000 : ℝ)^3707
        have hw : |(2285882131/5000000000 : ℝ)|=(2285882131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1603_s7_2 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1722140461/10000000000 : ℝ)*x 0 + (51822301/100000000 : ℝ)*x 1 + (5459449219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1722140461/10000000000 : ℝ)^4731 ≤ (10593625601723/100000000000000 : ℝ)^3707 := by
    have hnat : (1722140461 : ℕ)^4731*100000000000000^3707 ≤ 10593625601723^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1722140461 10000000000 10593625601723 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (51822301/100000000 : ℝ)^4731 ≤ (5402147852019/12500000000000 : ℝ)^3707 := by
    have hnat : (51822301 : ℕ)^4731*12500000000000^3707 ≤ 5402147852019^3707*100000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51822301 100000000 5402147852019 12500000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5459449219/10000000000 : ℝ)^4731 ≤ (23094595784367/50000000000000 : ℝ)^3707 := by
    have hnat : (5459449219 : ℕ)^4731*50000000000000^3707 ≤ 23094595784367^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5459449219 10000000000 23094595784367 50000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1722140461/10000000000 : ℝ), (51822301/100000000 : ℝ), (5459449219/10000000000 : ℝ)] ![(10593625601723/100000000000000 : ℝ), (5402147852019/12500000000000 : ℝ), (23094595784367/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1722140461/10000000000 : ℝ)|^4731 ≤ (10593625601723/100000000000000 : ℝ)^3707
        have hw : |(-1722140461/10000000000 : ℝ)|=(1722140461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(51822301/100000000 : ℝ)|^4731 ≤ (5402147852019/12500000000000 : ℝ)^3707
        have hw : |(51822301/100000000 : ℝ)|=(51822301/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5459449219/10000000000 : ℝ)|^4731 ≤ (23094595784367/50000000000000 : ℝ)^3707
        have hw : |(5459449219/10000000000 : ℝ)|=(5459449219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1603_s7_3 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639948279/5000000000 : ℝ)*x 0 + (-793958669/5000000000 : ℝ)*x 1 + (1364862407/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639948279/5000000000 : ℝ)^4731 ≤ (22129677502939/50000000000000 : ℝ)^3707 := by
    have hnat : (2639948279 : ℕ)^4731*50000000000000^3707 ≤ 22129677502939^3707*5000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639948279 5000000000 22129677502939 50000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (793958669/5000000000 : ℝ)^4731 ≤ (149241390609/1562500000000 : ℝ)^3707 := by
    have hnat : (793958669 : ℕ)^4731*1562500000000^3707 ≤ 149241390609^3707*5000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      793958669 5000000000 149241390609 1562500000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1364862407/2500000000 : ℝ)^4731 ≤ (23094597992449/50000000000000 : ℝ)^3707 := by
    have hnat : (1364862407 : ℕ)^4731*50000000000000^3707 ≤ 23094597992449^3707*2500000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364862407 2500000000 23094597992449 50000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639948279/5000000000 : ℝ), (-793958669/5000000000 : ℝ), (1364862407/2500000000 : ℝ)] ![(22129677502939/50000000000000 : ℝ), (149241390609/1562500000000 : ℝ), (23094597992449/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639948279/5000000000 : ℝ)|^4731 ≤ (22129677502939/50000000000000 : ℝ)^3707
        have hw : |(2639948279/5000000000 : ℝ)|=(2639948279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-793958669/5000000000 : ℝ)|^4731 ≤ (149241390609/1562500000000 : ℝ)^3707
        have hw : |(-793958669/5000000000 : ℝ)|=(793958669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1364862407/2500000000 : ℝ)|^4731 ≤ (23094597992449/50000000000000 : ℝ)^3707
        have hw : |(1364862407/2500000000 : ℝ)|=(1364862407/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1603_s7_4 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279896747/10000000000 : ℝ)*x 0 + (5459449607/10000000000 : ℝ)*x 1 + (-1587917103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279896747/10000000000 : ℝ)^4731 ≤ (22129678513917/50000000000000 : ℝ)^3707 := by
    have hnat : (5279896747 : ℕ)^4731*50000000000000^3707 ≤ 22129678513917^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279896747 10000000000 22129678513917 50000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5459449607/10000000000 : ℝ)^4731 ≤ (46189195758151/100000000000000 : ℝ)^3707 := by
    have hnat : (5459449607 : ℕ)^4731*100000000000000^3707 ≤ 46189195758151^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5459449607 10000000000 46189195758151 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1587917103/10000000000 : ℝ)^4731 ≤ (9551447194963/100000000000000 : ℝ)^3707 := by
    have hnat : (1587917103 : ℕ)^4731*100000000000000^3707 ≤ 9551447194963^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1587917103 10000000000 9551447194963 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279896747/10000000000 : ℝ), (5459449607/10000000000 : ℝ), (-1587917103/10000000000 : ℝ)] ![(22129678513917/50000000000000 : ℝ), (46189195758151/100000000000000 : ℝ), (9551447194963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279896747/10000000000 : ℝ)|^4731 ≤ (22129678513917/50000000000000 : ℝ)^3707
        have hw : |(5279896747/10000000000 : ℝ)|=(5279896747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5459449607/10000000000 : ℝ)|^4731 ≤ (46189195758151/100000000000000 : ℝ)^3707
        have hw : |(5459449607/10000000000 : ℝ)|=(5459449607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1587917103/10000000000 : ℝ)|^4731 ≤ (9551447194963/100000000000000 : ℝ)^3707
        have hw : |(-1587917103/10000000000 : ℝ)|=(1587917103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1603_s7_5 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (168741363/400000000 : ℝ)*x 0 + (570836301/1250000000 : ℝ)*x 1 + (3891741379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168741363/400000000 : ℝ)^4731 ≤ (33236737216267/100000000000000 : ℝ)^3707 := by
    have hnat : (168741363 : ℕ)^4731*100000000000000^3707 ≤ 33236737216267^3707*400000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168741363 400000000 33236737216267 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (570836301/1250000000 : ℝ)^4731 ≤ (36776627319277/100000000000000 : ℝ)^3707 := by
    have hnat : (570836301 : ℕ)^4731*100000000000000^3707 ≤ 36776627319277^3707*1250000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      570836301 1250000000 36776627319277 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3891741379/10000000000 : ℝ)^4731 ≤ (14993317722829/50000000000000 : ℝ)^3707 := by
    have hnat : (3891741379 : ℕ)^4731*50000000000000^3707 ≤ 14993317722829^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3891741379 10000000000 14993317722829 50000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(168741363/400000000 : ℝ), (570836301/1250000000 : ℝ), (3891741379/10000000000 : ℝ)] ![(33236737216267/100000000000000 : ℝ), (36776627319277/100000000000000 : ℝ), (14993317722829/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(168741363/400000000 : ℝ)|^4731 ≤ (33236737216267/100000000000000 : ℝ)^3707
        have hw : |(168741363/400000000 : ℝ)|=(168741363/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(570836301/1250000000 : ℝ)|^4731 ≤ (36776627319277/100000000000000 : ℝ)^3707
        have hw : |(570836301/1250000000 : ℝ)|=(570836301/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3891741379/10000000000 : ℝ)|^4731 ≤ (14993317722829/50000000000000 : ℝ)^3707
        have hw : |(3891741379/10000000000 : ℝ)|=(3891741379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1603_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5366729/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16353/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10389/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10389/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (511/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16353/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10389/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16353/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10389/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16353/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10389/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16353/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10389/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16353/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10389/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16353/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10389/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10389/100000 : ℝ) ^ (4727/1024 : ℝ) ≤ (115440171327013/4000000000000000000 : ℝ) := by
    have hpowers : (10389/100000 : ℝ)^4727 ≤ (115440171327013/4000000000000000000 : ℝ)^1024 := by
      have hnat : (10389 : ℕ)^4727*4000000000000000000^1024 ≤ 115440171327013^1024*100000^4727 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10389 100000 115440171327013 4000000000000000000 4727 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10389/100000 : ℝ)) (X := (115440171327013/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4727 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16353/100000 : ℝ) ^ (4727/1024 : ℝ) ≤ (5857872231995967/25000000000000000000 : ℝ) := by
    have hpowers : (16353/100000 : ℝ)^4727 ≤ (5857872231995967/25000000000000000000 : ℝ)^1024 := by
      have hnat : (16353 : ℕ)^4727*25000000000000000000^1024 ≤ 5857872231995967^1024*100000^4727 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16353 100000 5857872231995967 25000000000000000000 4727 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16353/100000 : ℝ)) (X := (5857872231995967/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4727 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000115440171327013/2000000000000000000 : ℝ) ≤ (10000125034972503/10000000000000000 : ℝ) ^ (4727/1024 : ℝ) := by
    have hpowers : (2000115440171327013/2000000000000000000 : ℝ)^1024 ≤ (10000125034972503/10000000000000000 : ℝ)^4727 := by
      have hnat : (2000115440171327013 : ℕ)^1024*10000000000000000^4727 ≤ 10000125034972503^4727*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000115440171327013 2000000000000000000 10000125034972503 10000000000000000 1024 4727 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000125034972503/10000000000000000 : ℝ)) (X := (2000115440171327013/2000000000000000000 : ℝ)) (by norm_num) 4727 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100026317493211159193/100000000000000000000 : ℝ) ≤ (2000114010304699/2000000000000000 : ℝ) ^ (4727/1024 : ℝ) := by
    have hpowers : (100026317493211159193/100000000000000000000 : ℝ)^1024 ≤ (2000114010304699/2000000000000000 : ℝ)^4727 := by
      have hnat : (100026317493211159193 : ℕ)^1024*2000000000000000^4727 ≤ 2000114010304699^4727*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100026317493211159193 100000000000000000000 2000114010304699 2000000000000000 1024 4727 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000114010304699/2000000000000000 : ℝ)) (X := (100026317493211159193/100000000000000000000 : ℝ)) (by norm_num) 4727 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12505857872231995967/12500000000000000000 : ℝ) ≤ (10001015068074487/10000000000000000 : ℝ) ^ (4727/1024 : ℝ) := by
    have hpowers : (12505857872231995967/12500000000000000000 : ℝ)^1024 ≤ (10001015068074487/10000000000000000 : ℝ)^4727 := by
      have hnat : (12505857872231995967 : ℕ)^1024*10000000000000000^4727 ≤ 10001015068074487^4727*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505857872231995967 12500000000000000000 10001015068074487 10000000000000000 1024 4727 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001015068074487/10000000000000000 : ℝ)) (X := (12505857872231995967/12500000000000000000 : ℝ)) (by norm_num) 4727 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(115440171327013/4000000000000000000 : ℝ) ≤ ((4969291596223291343/4970000000000000000 : ℝ)+2*(27813534437/37275000000000 : ℝ)*(10389/100000 : ℝ))^(4727/1024 : ℝ) := by
    rw [show (4969291596223291343/4970000000000000000 : ℝ)+2*(27813534437/37275000000000 : ℝ)*(10389/100000 : ℝ)=(10000125034972503/10000000000000000 : ℝ) by norm_num, show 1+2*(115440171327013/4000000000000000000 : ℝ)=(2000115440171327013/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5857872231995967/25000000000000000000 : ℝ)+(115440171327013/4000000000000000000 : ℝ) ≤ ((4969291596223291343/4970000000000000000 : ℝ)+(27813534437/37275000000000 : ℝ)*((16353/100000 : ℝ)+(10389/100000 : ℝ)))^(4727/1024 : ℝ) := by
    rw [show (4969291596223291343/4970000000000000000 : ℝ)+(27813534437/37275000000000 : ℝ)*((16353/100000 : ℝ)+(10389/100000 : ℝ))=(2000114010304699/2000000000000000 : ℝ) by norm_num, show 1+(5857872231995967/25000000000000000000 : ℝ)+(115440171327013/4000000000000000000 : ℝ)=(100026317493211159193/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5857872231995967/25000000000000000000 : ℝ) ≤ ((4969291596223291343/4970000000000000000 : ℝ)+2*(27813534437/37275000000000 : ℝ)*(16353/100000 : ℝ))^(4727/1024 : ℝ) := by
    rw [show (4969291596223291343/4970000000000000000 : ℝ)+2*(27813534437/37275000000000 : ℝ)*(16353/100000 : ℝ)=(10001015068074487/10000000000000000 : ℝ) by norm_num, show 1+2*(5857872231995967/25000000000000000000 : ℝ)=(12505857872231995967/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4969291596223291343/4970000000000000000 : ℝ)*(X 1 0+X 2 0)+(27813534437/37275000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4727/1024 : ℝ)) (lo := (10389/100000 : ℝ)) (hi := (16353/100000 : ℝ)) (c := (4969291596223291343/4970000000000000000 : ℝ)) (alpha := (27813534437/37275000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4969291596223291343/4970000000000000000 : ℝ)*(X 0 1+X 2 1)+(27813534437/37275000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4727/1024 : ℝ)) (lo := (10389/100000 : ℝ)) (hi := (16353/100000 : ℝ)) (c := (4969291596223291343/4970000000000000000 : ℝ)) (alpha := (27813534437/37275000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4969291596223291343/4970000000000000000 : ℝ)*(X 0 2+X 1 2)+(27813534437/37275000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4727/1024 : ℝ)) (lo := (10389/100000 : ℝ)) (hi := (16353/100000 : ℝ)) (c := (4969291596223291343/4970000000000000000 : ℝ)) (alpha := (27813534437/37275000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5354534447/10000000000 : ℝ)*X 2 0+(1036029179/2000000000 : ℝ)*X 2 1+(-933610687/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_s7_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2109180763/5000000000 : ℝ)*X 0 0+(3886613031/10000000000 : ℝ)*X 0 1+(2285882131/5000000000 : ℝ)*X 0 2+(2109180763/5000000000 : ℝ)*X 1 0+(3886613031/10000000000 : ℝ)*X 1 1+(2285882131/5000000000 : ℝ)*X 1 2+(2109180763/5000000000 : ℝ)*X 2 0+(3886613031/10000000000 : ℝ)*X 2 1+(2285882131/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_s7_1 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-1722140461/10000000000 : ℝ)*X 0 0+(51822301/100000000 : ℝ)*X 0 1+(5459449219/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_s7_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2639948279/5000000000 : ℝ)*X 1 0+(-793958669/5000000000 : ℝ)*X 1 1+(1364862407/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_s7_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((5279896747/10000000000 : ℝ)*X 2 0+(5459449607/10000000000 : ℝ)*X 2 1+(-1587917103/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_s7_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((168741363/400000000 : ℝ)*X 0 0+(570836301/1250000000 : ℝ)*X 0 1+(3891741379/10000000000 : ℝ)*X 0 2+(168741363/400000000 : ℝ)*X 1 0+(570836301/1250000000 : ℝ)*X 1 1+(3891741379/10000000000 : ℝ)*X 1 2+(168741363/400000000 : ℝ)*X 2 0+(570836301/1250000000 : ℝ)*X 2 1+(3891741379/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_s7_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (156166112472887427320185807/124250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3934783/1250000000000 : ℝ)*(base19) + (243114711/25000000000000 : ℝ)*(base23) + (115380021/100000000000000 : ℝ)*(lower1) + (99848267/50000000000000 : ℝ)*(upper2) + (175084927/100000000000000 : ℝ)*(upper3) + (1272209437256683/50000000000000 : ℝ)*(major0) + (1272209437256683/50000000000000 : ℝ)*(major1) + (1272209437256683/50000000000000 : ℝ)*(major2) + (10634410431/100000000000000 : ℝ)*(sp0) + (127372359/50000000000000 : ℝ)*(sp1) + (1803622273110809/50000000000000 : ℝ)*(sp2) + (1803622115719489/50000000000000 : ℝ)*(sp3) + (450904117419043/12500000000000 : ℝ)*(sp4) + (740796453082353/50000000000000 : ℝ)*(sp5) + (1481593160909423/100000000000000 : ℝ)*(f.failure) + (1803622273110809/50000000000000 : ℝ)*(f.sum) + (7985312209729/931875000000000000000000000 : ℝ)*base66 + (7505518332086214193/745500000000000000000000000000000 : ℝ)*base68 + (11675615662919214193/745500000000000000000000000000000 : ℝ)*base70 + (1481768174024214193/745500000000000000000000000000000 : ℝ)*base72 + (15185275368421/3727500000000000000000000000 : ℝ)*base74 + (8784047482869785807/745500000000000000000000000000000 : ℝ)*base75 + (5698288517780285807/745500000000000000000000000000000 : ℝ)*base77 + (66478189786947714193/745500000000000000000000000000000 : ℝ)*base80 + (2612757404081/931875000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1962633/312500000000000000000 : ℝ)*base90 + (1962633/312500000000000000000 : ℝ)*base92 + (1962633/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1603_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5366729/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16353/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10389/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10389/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (511/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1603_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1603_box_0 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-722950697/5000000000 : ℝ)*x 0 + (677486439/1250000000 : ℝ)*x 1 + (5419891051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (722950697/5000000000 : ℝ)^4731 ≤ (4237505750619/50000000000000 : ℝ)^3707 := by
    have hnat : (722950697 : ℕ)^4731*50000000000000^3707 ≤ 4237505750619^3707*5000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      722950697 5000000000 4237505750619 50000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (677486439/1250000000 : ℝ)^4731 ≤ (45762496722959/100000000000000 : ℝ)^3707 := by
    have hnat : (677486439 : ℕ)^4731*100000000000000^3707 ≤ 45762496722959^3707*1250000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677486439 1250000000 45762496722959 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5419891051/10000000000 : ℝ)^4731 ≤ (11440622938829/25000000000000 : ℝ)^3707 := by
    have hnat : (5419891051 : ℕ)^4731*25000000000000^3707 ≤ 11440622938829^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419891051 10000000000 11440622938829 25000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-722950697/5000000000 : ℝ), (677486439/1250000000 : ℝ), (5419891051/10000000000 : ℝ)] ![(4237505750619/50000000000000 : ℝ), (45762496722959/100000000000000 : ℝ), (11440622938829/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-722950697/5000000000 : ℝ)|^4731 ≤ (4237505750619/50000000000000 : ℝ)^3707
        have hw : |(-722950697/5000000000 : ℝ)|=(722950697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(677486439/1250000000 : ℝ)|^4731 ≤ (45762496722959/100000000000000 : ℝ)^3707
        have hw : |(677486439/1250000000 : ℝ)|=(677486439/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5419891051/10000000000 : ℝ)|^4731 ≤ (11440622938829/25000000000000 : ℝ)^3707
        have hw : |(5419891051/10000000000 : ℝ)|=(5419891051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1603_box_1 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (656382653/1250000000 : ℝ)*x 0 + (-168288343/1000000000 : ℝ)*x 1 + (5419890899/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (656382653/1250000000 : ℝ)^4731 ≤ (43951102321163/100000000000000 : ℝ)^3707 := by
    have hnat : (656382653 : ℕ)^4731*100000000000000^3707 ≤ 43951102321163^3707*1250000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656382653 1250000000 43951102321163 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168288343/1000000000 : ℝ)^4731 ≤ (2057281509507/20000000000000 : ℝ)^3707 := by
    have hnat : (168288343 : ℕ)^4731*20000000000000^3707 ≤ 2057281509507^3707*1000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168288343 1000000000 2057281509507 20000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5419890899/10000000000 : ℝ)^4731 ≤ (9152498023479/20000000000000 : ℝ)^3707 := by
    have hnat : (5419890899 : ℕ)^4731*20000000000000^3707 ≤ 9152498023479^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419890899 10000000000 9152498023479 20000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(656382653/1250000000 : ℝ), (-168288343/1000000000 : ℝ), (5419890899/10000000000 : ℝ)] ![(43951102321163/100000000000000 : ℝ), (2057281509507/20000000000000 : ℝ), (9152498023479/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(656382653/1250000000 : ℝ)|^4731 ≤ (43951102321163/100000000000000 : ℝ)^3707
        have hw : |(656382653/1250000000 : ℝ)|=(656382653/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-168288343/1000000000 : ℝ)|^4731 ≤ (2057281509507/20000000000000 : ℝ)^3707
        have hw : |(-168288343/1000000000 : ℝ)|=(168288343/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5419890899/10000000000 : ℝ)|^4731 ≤ (9152498023479/20000000000000 : ℝ)^3707
        have hw : |(5419890899/10000000000 : ℝ)|=(5419890899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1603_box_2 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050212069/2000000000 : ℝ)*x 0 + (677486431/1250000000 : ℝ)*x 1 + (-13463071/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050212069/2000000000 : ℝ)^4731 ≤ (1758043717267/4000000000000 : ℝ)^3707 := by
    have hnat : (1050212069 : ℕ)^4731*4000000000000^3707 ≤ 1758043717267^3707*2000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050212069 2000000000 1758043717267 4000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (677486431/1250000000 : ℝ)^4731 ≤ (11440624008327/25000000000000 : ℝ)^3707 := by
    have hnat : (677486431 : ℕ)^4731*25000000000000^3707 ≤ 11440624008327^3707*1250000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677486431 1250000000 11440624008327 25000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13463071/80000000 : ℝ)^4731 ≤ (10286411018899/100000000000000 : ℝ)^3707 := by
    have hnat : (13463071 : ℕ)^4731*100000000000000^3707 ≤ 10286411018899^3707*80000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13463071 80000000 10286411018899 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050212069/2000000000 : ℝ), (677486431/1250000000 : ℝ), (-13463071/80000000 : ℝ)] ![(1758043717267/4000000000000 : ℝ), (11440624008327/25000000000000 : ℝ), (10286411018899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050212069/2000000000 : ℝ)|^4731 ≤ (1758043717267/4000000000000 : ℝ)^3707
        have hw : |(1050212069/2000000000 : ℝ)|=(1050212069/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(677486431/1250000000 : ℝ)|^4731 ≤ (11440624008327/25000000000000 : ℝ)^3707
        have hw : |(677486431/1250000000 : ℝ)|=(677486431/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-13463071/80000000 : ℝ)|^4731 ≤ (10286411018899/100000000000000 : ℝ)^3707
        have hw : |(-13463071/80000000 : ℝ)|=(13463071/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1603_box_3 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1124709193/2500000000 : ℝ)*x 0 + (4090990547/10000000000 : ℝ)*x 1 + (4090989489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1124709193/2500000000 : ℝ)^4731 ≤ (4510084588667/12500000000000 : ℝ)^3707 := by
    have hnat : (1124709193 : ℕ)^4731*12500000000000^3707 ≤ 4510084588667^3707*2500000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124709193 2500000000 4510084588667 12500000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4090990547/10000000000 : ℝ)^4731 ≤ (3195966691029/10000000000000 : ℝ)^3707 := by
    have hnat : (4090990547 : ℕ)^4731*10000000000000^3707 ≤ 3195966691029^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4090990547 10000000000 3195966691029 10000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4090989489/10000000000 : ℝ)^4731 ≤ (31959656361813/100000000000000 : ℝ)^3707 := by
    have hnat : (4090989489 : ℕ)^4731*100000000000000^3707 ≤ 31959656361813^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4090989489 10000000000 31959656361813 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1124709193/2500000000 : ℝ), (4090990547/10000000000 : ℝ), (4090989489/10000000000 : ℝ)] ![(4510084588667/12500000000000 : ℝ), (3195966691029/10000000000000 : ℝ), (31959656361813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1124709193/2500000000 : ℝ)|^4731 ≤ (4510084588667/12500000000000 : ℝ)^3707
        have hw : |(1124709193/2500000000 : ℝ)|=(1124709193/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4090990547/10000000000 : ℝ)|^4731 ≤ (3195966691029/10000000000000 : ℝ)^3707
        have hw : |(4090990547/10000000000 : ℝ)|=(4090990547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4090989489/10000000000 : ℝ)|^4731 ≤ (31959656361813/100000000000000 : ℝ)^3707
        have hw : |(4090989489/10000000000 : ℝ)|=(4090989489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1603_box_4 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2009008091/10000000000 : ℝ)*x 0 + (5213681221/10000000000 : ℝ)*x 1 + (5213681217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2009008091/10000000000 : ℝ)^4731 ≤ (3223899031703/25000000000000 : ℝ)^3707 := by
    have hnat : (2009008091 : ℕ)^4731*25000000000000^3707 ≤ 3223899031703^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2009008091 10000000000 3223899031703 25000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5213681221/10000000000 : ℝ)^4731 ≤ (43552201949039/100000000000000 : ℝ)^3707 := by
    have hnat : (5213681221 : ℕ)^4731*100000000000000^3707 ≤ 43552201949039^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5213681221 10000000000 43552201949039 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5213681217/10000000000 : ℝ)^4731 ≤ (8710440381279/20000000000000 : ℝ)^3707 := by
    have hnat : (5213681217 : ℕ)^4731*20000000000000^3707 ≤ 8710440381279^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5213681217 10000000000 8710440381279 20000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2009008091/10000000000 : ℝ), (5213681221/10000000000 : ℝ), (5213681217/10000000000 : ℝ)] ![(3223899031703/25000000000000 : ℝ), (43552201949039/100000000000000 : ℝ), (8710440381279/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2009008091/10000000000 : ℝ)|^4731 ≤ (3223899031703/25000000000000 : ℝ)^3707
        have hw : |(-2009008091/10000000000 : ℝ)|=(2009008091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5213681221/10000000000 : ℝ)|^4731 ≤ (43552201949039/100000000000000 : ℝ)^3707
        have hw : |(5213681221/10000000000 : ℝ)|=(5213681221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5213681217/10000000000 : ℝ)|^4731 ≤ (8710440381279/20000000000000 : ℝ)^3707
        have hw : |(5213681217/10000000000 : ℝ)|=(5213681217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1603_box_5 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1348380891/2500000000 : ℝ)*x 0 + (-884902523/5000000000 : ℝ)*x 1 + (208547251/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1348380891/2500000000 : ℝ)^4731 ≤ (45478552164853/100000000000000 : ℝ)^3707 := by
    have hnat : (1348380891 : ℕ)^4731*100000000000000^3707 ≤ 45478552164853^3707*2500000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348380891 2500000000 45478552164853 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (884902523/5000000000 : ℝ)^4731 ≤ (10969245285839/100000000000000 : ℝ)^3707 := by
    have hnat : (884902523 : ℕ)^4731*100000000000000^3707 ≤ 10969245285839^3707*5000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      884902523 5000000000 10969245285839 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208547251/400000000 : ℝ)^4731 ≤ (43552202524731/100000000000000 : ℝ)^3707 := by
    have hnat : (208547251 : ℕ)^4731*100000000000000^3707 ≤ 43552202524731^3707*400000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208547251 400000000 43552202524731 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1348380891/2500000000 : ℝ), (-884902523/5000000000 : ℝ), (208547251/400000000 : ℝ)] ![(45478552164853/100000000000000 : ℝ), (10969245285839/100000000000000 : ℝ), (43552202524731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1348380891/2500000000 : ℝ)|^4731 ≤ (45478552164853/100000000000000 : ℝ)^3707
        have hw : |(1348380891/2500000000 : ℝ)|=(1348380891/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-884902523/5000000000 : ℝ)|^4731 ≤ (10969245285839/100000000000000 : ℝ)^3707
        have hw : |(-884902523/5000000000 : ℝ)|=(884902523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(208547251/400000000 : ℝ)|^4731 ≤ (43552202524731/100000000000000 : ℝ)^3707
        have hw : |(208547251/400000000 : ℝ)|=(208547251/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1603_box_6 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1348380929/2500000000 : ℝ)*x 0 + (2606840561/5000000000 : ℝ)*x 1 + (-1769805047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1348380929/2500000000 : ℝ)^4731 ≤ (45478553800569/100000000000000 : ℝ)^3707 := by
    have hnat : (1348380929 : ℕ)^4731*100000000000000^3707 ≤ 45478553800569^3707*2500000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348380929 2500000000 45478553800569 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2606840561/5000000000 : ℝ)^4731 ≤ (8710440178721/20000000000000 : ℝ)^3707 := by
    have hnat : (2606840561 : ℕ)^4731*20000000000000^3707 ≤ 8710440178721^3707*5000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2606840561 5000000000 8710440178721 20000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1769805047/10000000000 : ℝ)^4731 ≤ (10969245293749/100000000000000 : ℝ)^3707 := by
    have hnat : (1769805047 : ℕ)^4731*100000000000000^3707 ≤ 10969245293749^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1769805047 10000000000 10969245293749 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1348380929/2500000000 : ℝ), (2606840561/5000000000 : ℝ), (-1769805047/10000000000 : ℝ)] ![(45478553800569/100000000000000 : ℝ), (8710440178721/20000000000000 : ℝ), (10969245293749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1348380929/2500000000 : ℝ)|^4731 ≤ (45478553800569/100000000000000 : ℝ)^3707
        have hw : |(1348380929/2500000000 : ℝ)|=(1348380929/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2606840561/5000000000 : ℝ)|^4731 ≤ (8710440178721/20000000000000 : ℝ)^3707
        have hw : |(2606840561/5000000000 : ℝ)|=(2606840561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1769805047/10000000000 : ℝ)|^4731 ≤ (10969245293749/100000000000000 : ℝ)^3707
        have hw : |(-1769805047/10000000000 : ℝ)|=(1769805047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1603_box_7 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3932128229/10000000000 : ℝ)*x 0 + (437399709/1000000000 : ℝ)*x 1 + (4373997167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3932128229/10000000000 : ℝ)^4731 ≤ (15192176426441/50000000000000 : ℝ)^3707 := by
    have hnat : (3932128229 : ℕ)^4731*50000000000000^3707 ≤ 15192176426441^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3932128229 10000000000 15192176426441 50000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (437399709/1000000000 : ℝ)^4731 ≤ (8701955793887/25000000000000 : ℝ)^3707 := by
    have hnat : (437399709 : ℕ)^4731*25000000000000^3707 ≤ 8701955793887^3707*1000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437399709 1000000000 8701955793887 25000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4373997167/10000000000 : ℝ)^4731 ≤ (34807823957571/100000000000000 : ℝ)^3707 := by
    have hnat : (4373997167 : ℕ)^4731*100000000000000^3707 ≤ 34807823957571^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4373997167 10000000000 34807823957571 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3932128229/10000000000 : ℝ), (437399709/1000000000 : ℝ), (4373997167/10000000000 : ℝ)] ![(15192176426441/50000000000000 : ℝ), (8701955793887/25000000000000 : ℝ), (34807823957571/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3932128229/10000000000 : ℝ)|^4731 ≤ (15192176426441/50000000000000 : ℝ)^3707
        have hw : |(3932128229/10000000000 : ℝ)|=(3932128229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(437399709/1000000000 : ℝ)|^4731 ≤ (8701955793887/25000000000000 : ℝ)^3707
        have hw : |(437399709/1000000000 : ℝ)|=(437399709/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4373997167/10000000000 : ℝ)|^4731 ≤ (34807823957571/100000000000000 : ℝ)^3707
        have hw : |(4373997167/10000000000 : ℝ)|=(4373997167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1603_box_8 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-94468371/500000000 : ℝ)*x 0 + (1013313753/2000000000 : ℝ)*x 1 + (2724959903/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (94468371/500000000 : ℝ)^4731 ≤ (11923679747763/100000000000000 : ℝ)^3707 := by
    have hnat : (94468371 : ℕ)^4731*100000000000000^3707 ≤ 11923679747763^3707*500000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94468371 500000000 11923679747763 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1013313753/2000000000 : ℝ)^4731 ≤ (20994998689329/50000000000000 : ℝ)^3707 := by
    have hnat : (1013313753 : ℕ)^4731*50000000000000^3707 ≤ 20994998689329^3707*2000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1013313753 2000000000 20994998689329 50000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2724959903/5000000000 : ℝ)^4731 ≤ (4608632286093/10000000000000 : ℝ)^3707 := by
    have hnat : (2724959903 : ℕ)^4731*10000000000000^3707 ≤ 4608632286093^3707*5000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2724959903 5000000000 4608632286093 10000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-94468371/500000000 : ℝ), (1013313753/2000000000 : ℝ), (2724959903/5000000000 : ℝ)] ![(11923679747763/100000000000000 : ℝ), (20994998689329/50000000000000 : ℝ), (4608632286093/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-94468371/500000000 : ℝ)|^4731 ≤ (11923679747763/100000000000000 : ℝ)^3707
        have hw : |(-94468371/500000000 : ℝ)|=(94468371/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1013313753/2000000000 : ℝ)|^4731 ≤ (20994998689329/50000000000000 : ℝ)^3707
        have hw : |(1013313753/2000000000 : ℝ)|=(1013313753/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2724959903/5000000000 : ℝ)|^4731 ≤ (4608632286093/10000000000000 : ℝ)^3707
        have hw : |(2724959903/5000000000 : ℝ)|=(2724959903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1603_box_9 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5230309399/10000000000 : ℝ)*x 0 + (-834878813/5000000000 : ℝ)*x 1 + (54499197/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5230309399/10000000000 : ℝ)^4731 ≤ (43729552192473/100000000000000 : ℝ)^3707 := by
    have hnat : (5230309399 : ℕ)^4731*100000000000000^3707 ≤ 43729552192473^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230309399 10000000000 43729552192473 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (834878813/5000000000 : ℝ)^4731 ≤ (5092063035773/50000000000000 : ℝ)^3707 := by
    have hnat : (834878813 : ℕ)^4731*50000000000000^3707 ≤ 5092063035773^3707*5000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834878813 5000000000 5092063035773 50000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54499197/100000000 : ℝ)^4731 ≤ (46086321716951/100000000000000 : ℝ)^3707 := by
    have hnat : (54499197 : ℕ)^4731*100000000000000^3707 ≤ 46086321716951^3707*100000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54499197 100000000 46086321716951 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5230309399/10000000000 : ℝ), (-834878813/5000000000 : ℝ), (54499197/100000000 : ℝ)] ![(43729552192473/100000000000000 : ℝ), (5092063035773/50000000000000 : ℝ), (46086321716951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5230309399/10000000000 : ℝ)|^4731 ≤ (43729552192473/100000000000000 : ℝ)^3707
        have hw : |(5230309399/10000000000 : ℝ)|=(5230309399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-834878813/5000000000 : ℝ)|^4731 ≤ (5092063035773/50000000000000 : ℝ)^3707
        have hw : |(-834878813/5000000000 : ℝ)|=(834878813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(54499197/100000000 : ℝ)|^4731 ≤ (46086321716951/100000000000000 : ℝ)^3707
        have hw : |(54499197/100000000 : ℝ)|=(54499197/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1603_box_10 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5230309727/10000000000 : ℝ)*x 0 + (2724960027/5000000000 : ℝ)*x 1 + (-834878343/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5230309727/10000000000 : ℝ)^4731 ≤ (21864777846171/50000000000000 : ℝ)^3707 := by
    have hnat : (5230309727 : ℕ)^4731*50000000000000^3707 ≤ 21864777846171^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230309727 10000000000 21864777846171 50000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2724960027/5000000000 : ℝ)^4731 ≤ (4608632553741/10000000000000 : ℝ)^3707 := by
    have hnat : (2724960027 : ℕ)^4731*10000000000000^3707 ≤ 4608632553741^3707*5000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2724960027 5000000000 4608632553741 10000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (834878343/5000000000 : ℝ)^4731 ≤ (5092059377311/50000000000000 : ℝ)^3707 := by
    have hnat : (834878343 : ℕ)^4731*50000000000000^3707 ≤ 5092059377311^3707*5000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834878343 5000000000 5092059377311 50000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5230309727/10000000000 : ℝ), (2724960027/5000000000 : ℝ), (-834878343/5000000000 : ℝ)] ![(21864777846171/50000000000000 : ℝ), (4608632553741/10000000000000 : ℝ), (5092059377311/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5230309727/10000000000 : ℝ)|^4731 ≤ (21864777846171/50000000000000 : ℝ)^3707
        have hw : |(5230309727/10000000000 : ℝ)|=(5230309727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2724960027/5000000000 : ℝ)|^4731 ≤ (4608632553741/10000000000000 : ℝ)^3707
        have hw : |(2724960027/5000000000 : ℝ)|=(2724960027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-834878343/5000000000 : ℝ)|^4731 ≤ (5092059377311/50000000000000 : ℝ)^3707
        have hw : |(-834878343/5000000000 : ℝ)|=(834878343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1603_box_11 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4578960763/10000000000 : ℝ)*x 0 + (202485211/500000000 : ℝ)*x 1 + (4049703787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4578960763/10000000000 : ℝ)^4731 ≤ (9225696624649/25000000000000 : ℝ)^3707 := by
    have hnat : (4578960763 : ℕ)^4731*25000000000000^3707 ≤ 9225696624649^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4578960763 10000000000 9225696624649 25000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (202485211/500000000 : ℝ)^4731 ≤ (3154860889629/10000000000000 : ℝ)^3707 := by
    have hnat : (202485211 : ℕ)^4731*10000000000000^3707 ≤ 3154860889629^3707*500000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202485211 500000000 3154860889629 10000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4049703787/10000000000 : ℝ)^4731 ≤ (31548604591271/100000000000000 : ℝ)^3707 := by
    have hnat : (4049703787 : ℕ)^4731*100000000000000^3707 ≤ 31548604591271^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4049703787 10000000000 31548604591271 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4578960763/10000000000 : ℝ), (202485211/500000000 : ℝ), (4049703787/10000000000 : ℝ)] ![(9225696624649/25000000000000 : ℝ), (3154860889629/10000000000000 : ℝ), (31548604591271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4578960763/10000000000 : ℝ)|^4731 ≤ (9225696624649/25000000000000 : ℝ)^3707
        have hw : |(4578960763/10000000000 : ℝ)|=(4578960763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(202485211/500000000 : ℝ)|^4731 ≤ (3154860889629/10000000000000 : ℝ)^3707
        have hw : |(202485211/500000000 : ℝ)|=(202485211/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4049703787/10000000000 : ℝ)|^4731 ≤ (31548604591271/100000000000000 : ℝ)^3707
        have hw : |(4049703787/10000000000 : ℝ)|=(4049703787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1603_box_12 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-782214277/5000000000 : ℝ)*x 0 + (5560957223/10000000000 : ℝ)*x 1 + (5193810563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (782214277/5000000000 : ℝ)^4731 ≤ (937150354549/10000000000000 : ℝ)^3707 := by
    have hnat : (782214277 : ℕ)^4731*10000000000000^3707 ≤ 937150354549^3707*5000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      782214277 5000000000 937150354549 10000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5560957223/10000000000 : ℝ)^4731 ≤ (23644011506113/50000000000000 : ℝ)^3707 := by
    have hnat : (5560957223 : ℕ)^4731*50000000000000^3707 ≤ 23644011506113^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5560957223 10000000000 23644011506113 50000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5193810563/10000000000 : ℝ)^4731 ≤ (43340473424427/100000000000000 : ℝ)^3707 := by
    have hnat : (5193810563 : ℕ)^4731*100000000000000^3707 ≤ 43340473424427^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5193810563 10000000000 43340473424427 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-782214277/5000000000 : ℝ), (5560957223/10000000000 : ℝ), (5193810563/10000000000 : ℝ)] ![(937150354549/10000000000000 : ℝ), (23644011506113/50000000000000 : ℝ), (43340473424427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-782214277/5000000000 : ℝ)|^4731 ≤ (937150354549/10000000000000 : ℝ)^3707
        have hw : |(-782214277/5000000000 : ℝ)|=(782214277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5560957223/10000000000 : ℝ)|^4731 ≤ (23644011506113/50000000000000 : ℝ)^3707
        have hw : |(5560957223/10000000000 : ℝ)|=(5560957223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5193810563/10000000000 : ℝ)|^4731 ≤ (43340473424427/100000000000000 : ℝ)^3707
        have hw : |(5193810563/10000000000 : ℝ)|=(5193810563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1603_box_13 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5407257593/10000000000 : ℝ)*x 0 + (-1777875769/10000000000 : ℝ)*x 1 + (5193810649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5407257593/10000000000 : ℝ)^4731 ≤ (45626400007841/100000000000000 : ℝ)^3707 := by
    have hnat : (5407257593 : ℕ)^4731*100000000000000^3707 ≤ 45626400007841^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407257593 10000000000 45626400007841 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1777875769/10000000000 : ℝ)^4731 ≤ (172392588033/1562500000000 : ℝ)^3707 := by
    have hnat : (1777875769 : ℕ)^4731*1562500000000^3707 ≤ 172392588033^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1777875769 10000000000 172392588033 1562500000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5193810649/10000000000 : ℝ)^4731 ≤ (21670237170151/50000000000000 : ℝ)^3707 := by
    have hnat : (5193810649 : ℕ)^4731*50000000000000^3707 ≤ 21670237170151^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5193810649 10000000000 21670237170151 50000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5407257593/10000000000 : ℝ), (-1777875769/10000000000 : ℝ), (5193810649/10000000000 : ℝ)] ![(45626400007841/100000000000000 : ℝ), (172392588033/1562500000000 : ℝ), (21670237170151/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5407257593/10000000000 : ℝ)|^4731 ≤ (45626400007841/100000000000000 : ℝ)^3707
        have hw : |(5407257593/10000000000 : ℝ)|=(5407257593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1777875769/10000000000 : ℝ)|^4731 ≤ (172392588033/1562500000000 : ℝ)^3707
        have hw : |(-1777875769/10000000000 : ℝ)|=(1777875769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5193810649/10000000000 : ℝ)|^4731 ≤ (21670237170151/50000000000000 : ℝ)^3707
        have hw : |(5193810649/10000000000 : ℝ)|=(5193810649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1603_box_14 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5407257773/10000000000 : ℝ)*x 0 + (5193810601/10000000000 : ℝ)*x 1 + (-1777875589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5407257773/10000000000 : ℝ)^4731 ≤ (22813200973117/50000000000000 : ℝ)^3707 := by
    have hnat : (5407257773 : ℕ)^4731*50000000000000^3707 ≤ 22813200973117^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407257773 10000000000 22813200973117 50000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5193810601/10000000000 : ℝ)^4731 ≤ (10835118457279/25000000000000 : ℝ)^3707 := by
    have hnat : (5193810601 : ℕ)^4731*25000000000000^3707 ≤ 10835118457279^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5193810601 10000000000 10835118457279 25000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1777875589/10000000000 : ℝ)^4731 ≤ (2206624841701/20000000000000 : ℝ)^3707 := by
    have hnat : (1777875589 : ℕ)^4731*20000000000000^3707 ≤ 2206624841701^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1777875589 10000000000 2206624841701 20000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5407257773/10000000000 : ℝ), (5193810601/10000000000 : ℝ), (-1777875589/10000000000 : ℝ)] ![(22813200973117/50000000000000 : ℝ), (10835118457279/25000000000000 : ℝ), (2206624841701/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5407257773/10000000000 : ℝ)|^4731 ≤ (22813200973117/50000000000000 : ℝ)^3707
        have hw : |(5407257773/10000000000 : ℝ)|=(5407257773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5193810601/10000000000 : ℝ)|^4731 ≤ (10835118457279/25000000000000 : ℝ)^3707
        have hw : |(5193810601/10000000000 : ℝ)|=(5193810601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1777875589/10000000000 : ℝ)|^4731 ≤ (2206624841701/20000000000000 : ℝ)^3707
        have hw : |(-1777875589/10000000000 : ℝ)|=(1777875589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1603_box_15 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (775179547/2000000000 : ℝ)*x 0 + (2200609983/5000000000 : ℝ)*x 1 + (880243949/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (775179547/2000000000 : ℝ)^4731 ≤ (29830922508109/100000000000000 : ℝ)^3707 := by
    have hnat : (775179547 : ℕ)^4731*100000000000000^3707 ≤ 29830922508109^3707*2000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      775179547 2000000000 29830922508109 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2200609983/5000000000 : ℝ)^4731 ≤ (35084539861279/100000000000000 : ℝ)^3707 := by
    have hnat : (2200609983 : ℕ)^4731*100000000000000^3707 ≤ 35084539861279^3707*5000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2200609983 5000000000 35084539861279 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (880243949/2000000000 : ℝ)^4731 ≤ (17542268806461/50000000000000 : ℝ)^3707 := by
    have hnat : (880243949 : ℕ)^4731*50000000000000^3707 ≤ 17542268806461^3707*2000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      880243949 2000000000 17542268806461 50000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(775179547/2000000000 : ℝ), (2200609983/5000000000 : ℝ), (880243949/2000000000 : ℝ)] ![(29830922508109/100000000000000 : ℝ), (35084539861279/100000000000000 : ℝ), (17542268806461/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(775179547/2000000000 : ℝ)|^4731 ≤ (29830922508109/100000000000000 : ℝ)^3707
        have hw : |(775179547/2000000000 : ℝ)|=(775179547/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2200609983/5000000000 : ℝ)|^4731 ≤ (35084539861279/100000000000000 : ℝ)^3707
        have hw : |(2200609983/5000000000 : ℝ)|=(2200609983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(880243949/2000000000 : ℝ)|^4731 ≤ (17542268806461/50000000000000 : ℝ)^3707
        have hw : |(880243949/2000000000 : ℝ)|=(880243949/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1603_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5366729/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (511/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10389/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(64897/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29059/50000 : ℝ) ∧ (80293/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (10969/12500 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (511/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10389/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (511/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10389/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (511/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10389/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (511/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10389/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (511/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10389/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (511/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10389/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10389/100000 : ℝ) ^ (4727/1024 : ℝ) ≤ (115440171327013/4000000000000000000 : ℝ) := by
    have hpowers : (10389/100000 : ℝ)^4727 ≤ (115440171327013/4000000000000000000 : ℝ)^1024 := by
      have hnat : (10389 : ℕ)^4727*4000000000000000000^1024 ≤ 115440171327013^1024*100000^4727 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10389 100000 115440171327013 4000000000000000000 4727 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10389/100000 : ℝ)) (X := (115440171327013/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4727 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (511/3125 : ℝ) ^ (4727/1024 : ℝ) ≤ (23424875295216719/100000000000000000000 : ℝ) := by
    have hpowers : (511/3125 : ℝ)^4727 ≤ (23424875295216719/100000000000000000000 : ℝ)^1024 := by
      have hnat : (511 : ℕ)^4727*100000000000000000000^1024 ≤ 23424875295216719^1024*3125^4727 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        511 3125 23424875295216719 100000000000000000000 4727 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (511/3125 : ℝ)) (X := (23424875295216719/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4727 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000115440171327013/2000000000000000000 : ℝ) ≤ (10000125034972503/10000000000000000 : ℝ) ^ (4727/1024 : ℝ) := by
    have hpowers : (2000115440171327013/2000000000000000000 : ℝ)^1024 ≤ (10000125034972503/10000000000000000 : ℝ)^4727 := by
      have hnat : (2000115440171327013 : ℕ)^1024*10000000000000000^4727 ≤ 10000125034972503^4727*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000115440171327013 2000000000000000000 10000125034972503 10000000000000000 1024 4727 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000125034972503/10000000000000000 : ℝ)) (X := (2000115440171327013/2000000000000000000 : ℝ)) (by norm_num) 4727 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25006577719894598011/25000000000000000000 : ℝ) ≤ (2000113981656659/2000000000000000 : ℝ) ^ (4727/1024 : ℝ) := by
    have hpowers : (25006577719894598011/25000000000000000000 : ℝ)^1024 ≤ (2000113981656659/2000000000000000 : ℝ)^4727 := by
      have hnat : (25006577719894598011 : ℕ)^1024*2000000000000000^4727 ≤ 2000113981656659^4727*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006577719894598011 25000000000000000000 2000113981656659 2000000000000000 1024 4727 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000113981656659/2000000000000000 : ℝ)) (X := (25006577719894598011/25000000000000000000 : ℝ)) (by norm_num) 4727 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50023424875295216719/50000000000000000000 : ℝ) ≤ (10001014781594087/10000000000000000 : ℝ) ^ (4727/1024 : ℝ) := by
    have hpowers : (50023424875295216719/50000000000000000000 : ℝ)^1024 ≤ (10001014781594087/10000000000000000 : ℝ)^4727 := by
      have hnat : (50023424875295216719 : ℕ)^1024*10000000000000000^4727 ≤ 10001014781594087^4727*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023424875295216719 50000000000000000000 10001014781594087 10000000000000000 1024 4727 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001014781594087/10000000000000000 : ℝ)) (X := (50023424875295216719/50000000000000000000 : ℝ)) (by norm_num) 4727 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(115440171327013/4000000000000000000 : ℝ) ≤ ((59621502005889399213/59630000000000000000 : ℝ)+2*(55609163849/74537500000000 : ℝ)*(10389/100000 : ℝ))^(4727/1024 : ℝ) := by
    rw [show (59621502005889399213/59630000000000000000 : ℝ)+2*(55609163849/74537500000000 : ℝ)*(10389/100000 : ℝ)=(10000125034972503/10000000000000000 : ℝ) by norm_num, show 1+2*(115440171327013/4000000000000000000 : ℝ)=(2000115440171327013/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(23424875295216719/100000000000000000000 : ℝ)+(115440171327013/4000000000000000000 : ℝ) ≤ ((59621502005889399213/59630000000000000000 : ℝ)+(55609163849/74537500000000 : ℝ)*((511/3125 : ℝ)+(10389/100000 : ℝ)))^(4727/1024 : ℝ) := by
    rw [show (59621502005889399213/59630000000000000000 : ℝ)+(55609163849/74537500000000 : ℝ)*((511/3125 : ℝ)+(10389/100000 : ℝ))=(2000113981656659/2000000000000000 : ℝ) by norm_num, show 1+(23424875295216719/100000000000000000000 : ℝ)+(115440171327013/4000000000000000000 : ℝ)=(25006577719894598011/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(23424875295216719/100000000000000000000 : ℝ) ≤ ((59621502005889399213/59630000000000000000 : ℝ)+2*(55609163849/74537500000000 : ℝ)*(511/3125 : ℝ))^(4727/1024 : ℝ) := by
    rw [show (59621502005889399213/59630000000000000000 : ℝ)+2*(55609163849/74537500000000 : ℝ)*(511/3125 : ℝ)=(10001014781594087/10000000000000000 : ℝ) by norm_num, show 1+2*(23424875295216719/100000000000000000000 : ℝ)=(50023424875295216719/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (59621502005889399213/59630000000000000000 : ℝ)*(X 1 0+X 2 0)+(55609163849/74537500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4727/1024 : ℝ)) (lo := (10389/100000 : ℝ)) (hi := (511/3125 : ℝ)) (c := (59621502005889399213/59630000000000000000 : ℝ)) (alpha := (55609163849/74537500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (59621502005889399213/59630000000000000000 : ℝ)*(X 0 1+X 2 1)+(55609163849/74537500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4727/1024 : ℝ)) (lo := (10389/100000 : ℝ)) (hi := (511/3125 : ℝ)) (c := (59621502005889399213/59630000000000000000 : ℝ)) (alpha := (55609163849/74537500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (59621502005889399213/59630000000000000000 : ℝ)*(X 0 2+X 1 2)+(55609163849/74537500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4727/1024 : ℝ)) (lo := (10389/100000 : ℝ)) (hi := (511/3125 : ℝ)) (c := (59621502005889399213/59630000000000000000 : ℝ)) (alpha := (55609163849/74537500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-722950697/5000000000 : ℝ)*X 0 0+(677486439/1250000000 : ℝ)*X 0 1+(5419891051/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((656382653/1250000000 : ℝ)*X 1 0+(-168288343/1000000000 : ℝ)*X 1 1+(5419890899/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1050212069/2000000000 : ℝ)*X 2 0+(677486431/1250000000 : ℝ)*X 2 1+(-13463071/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1124709193/2500000000 : ℝ)*X 0 0+(4090990547/10000000000 : ℝ)*X 0 1+(4090989489/10000000000 : ℝ)*X 0 2+(1124709193/2500000000 : ℝ)*X 1 0+(4090990547/10000000000 : ℝ)*X 1 1+(4090989489/10000000000 : ℝ)*X 1 2+(1124709193/2500000000 : ℝ)*X 2 0+(4090990547/10000000000 : ℝ)*X 2 1+(4090989489/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2009008091/10000000000 : ℝ)*X 0 0+(5213681221/10000000000 : ℝ)*X 0 1+(5213681217/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1348380891/2500000000 : ℝ)*X 1 0+(-884902523/5000000000 : ℝ)*X 1 1+(208547251/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1348380929/2500000000 : ℝ)*X 2 0+(2606840561/5000000000 : ℝ)*X 2 1+(-1769805047/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3932128229/10000000000 : ℝ)*X 0 0+(437399709/1000000000 : ℝ)*X 0 1+(4373997167/10000000000 : ℝ)*X 0 2+(3932128229/10000000000 : ℝ)*X 1 0+(437399709/1000000000 : ℝ)*X 1 1+(4373997167/10000000000 : ℝ)*X 1 2+(3932128229/10000000000 : ℝ)*X 2 0+(437399709/1000000000 : ℝ)*X 2 1+(4373997167/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-94468371/500000000 : ℝ)*X 0 0+(1013313753/2000000000 : ℝ)*X 0 1+(2724959903/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5230309399/10000000000 : ℝ)*X 1 0+(-834878813/5000000000 : ℝ)*X 1 1+(54499197/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5230309727/10000000000 : ℝ)*X 2 0+(2724960027/5000000000 : ℝ)*X 2 1+(-834878343/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4578960763/10000000000 : ℝ)*X 0 0+(202485211/500000000 : ℝ)*X 0 1+(4049703787/10000000000 : ℝ)*X 0 2+(4578960763/10000000000 : ℝ)*X 1 0+(202485211/500000000 : ℝ)*X 1 1+(4049703787/10000000000 : ℝ)*X 1 2+(4578960763/10000000000 : ℝ)*X 2 0+(202485211/500000000 : ℝ)*X 2 1+(4049703787/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-782214277/5000000000 : ℝ)*X 0 0+(5560957223/10000000000 : ℝ)*X 0 1+(5193810563/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5407257593/10000000000 : ℝ)*X 1 0+(-1777875769/10000000000 : ℝ)*X 1 1+(5193810649/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5407257773/10000000000 : ℝ)*X 2 0+(5193810601/10000000000 : ℝ)*X 2 1+(-1777875589/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((775179547/2000000000 : ℝ)*X 0 0+(2200609983/5000000000 : ℝ)*X 0 1+(880243949/2000000000 : ℝ)*X 0 2+(775179547/2000000000 : ℝ)*X 1 0+(2200609983/5000000000 : ℝ)*X 1 1+(880243949/2000000000 : ℝ)*X 1 2+(775179547/2000000000 : ℝ)*X 2 0+(2200609983/5000000000 : ℝ)*X 2 1+(880243949/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-64897/100000 : ℝ) ≤ (-38696730677403885291169739339781/59630000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12366547/100000000000000 : ℝ)*(upper0) + (959271/50000000000000 : ℝ)*(lower1) + (17294321/100000000000000 : ℝ)*(lower2) + (2141277/50000000000000 : ℝ)*(lower3) + (66720170781779/4000000000000 : ℝ)*(major0) + (66720170781779/4000000000000 : ℝ)*(major1) + (66720170781779/4000000000000 : ℝ)*(major2) + (545975163/100000000000000 : ℝ)*(sp2) + (97372973/100000000000000 : ℝ)*(sp3) + (238637562060573/10000000000000 : ℝ)*(sp4) + (1193183732678499/50000000000000 : ℝ)*(sp5) + (1193187537315283/50000000000000 : ℝ)*(sp6) + (971264399553643/100000000000000 : ℝ)*(sp7) + (2038812183/25000000000000 : ℝ)*(sp13) + (971264496926617/100000000000000 : ℝ)*(f.failure) + (238637562060573/10000000000000 : ℝ)*(f.sum) + (34706826585841/5963000000000000000000000000 : ℝ)*base65 + (34427865812019927/238520000000000000000000000000000 : ℝ)*base67 + (553184499324379927/238520000000000000000000000000000 : ℝ)*base69 + (354976582533619927/238520000000000000000000000000000 : ℝ)*base71 + (7496987744277/1192600000000000000000000000 : ℝ)*base73 + (1475329379155780073/238520000000000000000000000000000 : ℝ)*base76 + (1750845343697259927/238520000000000000000000000000000 : ℝ)*base77 + (1299422324196099927/238520000000000000000000000000000 : ℝ)*base79 + (1019038773973/5963000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (1950793/312500000000000000000 : ℝ)*base89 + (1950793/312500000000000000000 : ℝ)*base91 + (1950793/312500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (29059/50000 : ℝ) ≤ (216609229762778706146420279873889/372687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (90289771/100000000000000 : ℝ)*(lower0) + (144556257/100000000000000 : ℝ)*(upper2) + (118571177/100000000000000 : ℝ)*(upper3) + (54284573/100000000000000 : ℝ)*(lower5) + (218976715442083/12500000000000 : ℝ)*(major0) + (218976715442083/12500000000000 : ℝ)*(major1) + (218976715442083/12500000000000 : ℝ)*(major2) + (246418780363813/10000000000000 : ℝ)*(sp0) + (308016980572103/12500000000000 : ℝ)*(sp1) + (123208528070621/5000000000000 : ℝ)*(sp2) + (1020065398560891/100000000000000 : ℝ)*(sp3) + (620433561/100000000000000 : ℝ)*(sp7) + (25979530653/50000000000000 : ℝ)*(sp9) + (1724222571/10000000000000 : ℝ)*(sp10) + (255016504748613/25000000000000 : ℝ)*(f.failure) + (246418780363813/10000000000000 : ℝ)*(f.sum) + (53033065693427/29815000000000000000000000000 : ℝ)*base66 + (3197863661140755679/745375000000000000000000000000000 : ℝ)*base67 + (2016232905989880679/745375000000000000000000000000000 : ℝ)*base69 + (1894666734374255679/745375000000000000000000000000000 : ℝ)*base71 + (159477531888777/29815000000000000000000000000 : ℝ)*base74 + (5033750658840130679/745375000000000000000000000000000 : ℝ)*base75 + (2781306396974255679/745375000000000000000000000000000 : ℝ)*base77 + (979761873363255679/745375000000000000000000000000000 : ℝ)*base79 + (3351422692849/14907500000000000000000000000 : ℝ)*base81 + (346877/78125000000000000000 : ℝ)*base89 + (346877/78125000000000000000 : ℝ)*base91 + (346877/78125000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (80293/100000 : ℝ) ≤ (23939998469378510321979808983/29815000000000000000000000000 : ℝ) := by norm_num
    linear_combination (69689523/100000000000000 : ℝ)*(upper0) + (4469673/25000000000000 : ℝ)*(lower3) + (65164107/25000000000000 : ℝ)*(upper4) + (1858875517656227/100000000000000 : ℝ)*(major0) + (1858875517656227/100000000000000 : ℝ)*(major1) + (1858875517656227/100000000000000 : ℝ)*(major2) + (19322447/25000000000000 : ℝ)*(sp0) + (84380640437/100000000000000 : ℝ)*(sp2) + (3040597159/10000000000000 : ℝ)*(sp3) + (1304289178976227/50000000000000 : ℝ)*(sp8) + (652144701936363/25000000000000 : ℝ)*(sp9) + (521698885421003/20000000000000 : ℝ)*(sp10) + (541188386078951/50000000000000 : ℝ)*(sp11) + (37250321/10000000000000 : ℝ)*(sp12) + (270601794532373/25000000000000 : ℝ)*(f.failure) + (652144701936363/25000000000000 : ℝ)*(f.sum) + (150259018598187/14907500000000000000000000000 : ℝ)*base65 + (2412611483418749351/5963000000000000000000000000000000 : ℝ)*base67 + (14291659438061250649/5963000000000000000000000000000000 : ℝ)*base70 + (27511240509074749351/5963000000000000000000000000000000 : ℝ)*base71 + (27372709533557/14907500000000000000000000000 : ℝ)*base73 + (69940561915250649/5963000000000000000000000000000000 : ℝ)*base76 + (3759019635011250649/5963000000000000000000000000000000 : ℝ)*base78 + (10196777336048749351/5963000000000000000000000000000000 : ℝ)*base79 + (18625405105201/29815000000000000000000000000 : ℝ)*base82 + (274167/78125000000000000000 : ℝ)*base89 + (274167/78125000000000000000 : ℝ)*base91 + (274167/78125000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-10969/12500 : ℝ) ≤ (-327031953099911646443444902593393/372687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (131/1562500000000 : ℝ)*(lower1) + (7909231/12500000000000 : ℝ)*(lower2) + (1618843/10000000000000 : ℝ)*(upper5) + (237571580951787/12500000000000 : ℝ)*(major0) + (237571580951787/12500000000000 : ℝ)*(major1) + (237571580951787/12500000000000 : ℝ)*(major2) + (306572567/20000000000000 : ℝ)*(sp0) + (10373575443/100000000000000 : ℝ)*(sp5) + (2599853079/100000000000000 : ℝ)*(sp7) + (365992713/100000000000000 : ℝ)*(sp8) + (8511581938699/312500000000 : ℝ)*(sp12) + (340462218207973/12500000000000 : ℝ)*(sp13) + (680927029809807/25000000000000 : ℝ)*(sp14) + (1106684457345947/100000000000000 : ℝ)*(sp15) + (1106687057199027/100000000000000 : ℝ)*(f.failure) + (680927029809807/25000000000000 : ℝ)*(f.sum) + (481274610028071/14907500000000000000000000000 : ℝ)*base65 + (1446197456820268631/745375000000000000000000000000000 : ℝ)*base67 + (446101927694981369/745375000000000000000000000000000 : ℝ)*base70 + (4761369507716643631/745375000000000000000000000000000 : ℝ)*base71 + (46141281965231/14907500000000000000000000000 : ℝ)*base73 + (2142145275043268631/745375000000000000000000000000000 : ℝ)*base75 + (25007119676936643631/745375000000000000000000000000000 : ℝ)*base77 + (740710001848356369/745375000000000000000000000000000 : ℝ)*base80 + (8254318463049/3726875000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1972683/312500000000000000000 : ℝ)*base89 + (1972683/312500000000000000000 : ℝ)*base91 + (1972683/312500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1603_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5366729/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (511/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10389/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(64897/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29059/50000 : ℝ) else (80293/100000 : ℝ) ≤ X j i ∧ X j i ≤ (10969/12500 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1603_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1603_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5366729/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16353/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2597/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(64897/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29059/50000 : ℝ) else (80293/100000 : ℝ) ≤ X j i ∧ X j i ≤ (10969/12500 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1603_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1603_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1603_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5366729/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16353/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2597/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(64897/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29059/50000 : ℝ) else (80293/100000 : ℝ) ≤ X j i ∧ X j i ≤ (10969/12500 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1603_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
