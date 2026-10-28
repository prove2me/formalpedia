-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1193_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:00:17.213344+00:00
-- url     : https://prove2.me/submissions/ff32235b-c9f9-4992-b6bb-c624090f0d8a

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
theorem support_rectangle_w1193_s9_0 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668067191/1250000000 : ℝ)*x 0 + (210662957/400000000 : ℝ)*x 1 + (-2206368111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668067191/1250000000 : ℝ)^4193 ≤ (43650542248433/100000000000000 : ℝ)^3169 := by
    have hnat : (668067191 : ℕ)^4193*100000000000000^3169 ≤ 43650542248433^3169*1250000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668067191 1250000000 43650542248433 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210662957/400000000 : ℝ)^4193 ≤ (4281002647139/10000000000000 : ℝ)^3169 := by
    have hnat : (210662957 : ℕ)^4193*10000000000000^3169 ≤ 4281002647139^3169*400000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210662957 400000000 4281002647139 10000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2206368111/10000000000 : ℝ)^4193 ≤ (13539431260931/100000000000000 : ℝ)^3169 := by
    have hnat : (2206368111 : ℕ)^4193*100000000000000^3169 ≤ 13539431260931^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2206368111 10000000000 13539431260931 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668067191/1250000000 : ℝ), (210662957/400000000 : ℝ), (-2206368111/10000000000 : ℝ)] ![(43650542248433/100000000000000 : ℝ), (4281002647139/10000000000000 : ℝ), (13539431260931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668067191/1250000000 : ℝ)|^4193 ≤ (43650542248433/100000000000000 : ℝ)^3169
        have hw : |(668067191/1250000000 : ℝ)|=(668067191/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210662957/400000000 : ℝ)|^4193 ≤ (4281002647139/10000000000000 : ℝ)^3169
        have hw : |(210662957/400000000 : ℝ)|=(210662957/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2206368111/10000000000 : ℝ)|^4193 ≤ (13539431260931/100000000000000 : ℝ)^3169
        have hw : |(-2206368111/10000000000 : ℝ)|=(2206368111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_s9_1 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2142739069/10000000000 : ℝ)*x 0 + (210675579/400000000 : ℝ)*x 1 + (2695869891/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2142739069/10000000000 : ℝ)^4193 ≤ (13025223284931/100000000000000 : ℝ)^3169 := by
    have hnat : (2142739069 : ℕ)^4193*100000000000000^3169 ≤ 13025223284931^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142739069 10000000000 13025223284931 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210675579/400000000 : ℝ)^4193 ≤ (5351677539861/12500000000000 : ℝ)^3169 := by
    have hnat : (210675579 : ℕ)^4193*12500000000000^3169 ≤ 5351677539861^3169*400000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210675579 400000000 5351677539861 12500000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695869891/5000000000 : ℝ)^4193 ≤ (8832271276871/20000000000000 : ℝ)^3169 := by
    have hnat : (2695869891 : ℕ)^4193*20000000000000^3169 ≤ 8832271276871^3169*5000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695869891 5000000000 8832271276871 20000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2142739069/10000000000 : ℝ), (210675579/400000000 : ℝ), (2695869891/5000000000 : ℝ)] ![(13025223284931/100000000000000 : ℝ), (5351677539861/12500000000000 : ℝ), (8832271276871/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2142739069/10000000000 : ℝ)|^4193 ≤ (13025223284931/100000000000000 : ℝ)^3169
        have hw : |(-2142739069/10000000000 : ℝ)|=(2142739069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210675579/400000000 : ℝ)|^4193 ≤ (5351677539861/12500000000000 : ℝ)^3169
        have hw : |(210675579/400000000 : ℝ)|=(210675579/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695869891/5000000000 : ℝ)|^4193 ≤ (8832271276871/20000000000000 : ℝ)^3169
        have hw : |(2695869891/5000000000 : ℝ)|=(2695869891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_s9_2 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312628333/10000000000 : ℝ)*x 0 + (-1040601071/5000000000 : ℝ)*x 1 + (2695869883/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312628333/10000000000 : ℝ)^4193 ≤ (10826512731143/25000000000000 : ℝ)^3169 := by
    have hnat : (5312628333 : ℕ)^4193*25000000000000^3169 ≤ 10826512731143^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312628333 10000000000 10826512731143 25000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1040601071/5000000000 : ℝ)^4193 ≤ (6266296424821/50000000000000 : ℝ)^3169 := by
    have hnat : (1040601071 : ℕ)^4193*50000000000000^3169 ≤ 6266296424821^3169*5000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040601071 5000000000 6266296424821 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695869883/5000000000 : ℝ)^4193 ≤ (44161356210961/100000000000000 : ℝ)^3169 := by
    have hnat : (2695869883 : ℕ)^4193*100000000000000^3169 ≤ 44161356210961^3169*5000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695869883 5000000000 44161356210961 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312628333/10000000000 : ℝ), (-1040601071/5000000000 : ℝ), (2695869883/5000000000 : ℝ)] ![(10826512731143/25000000000000 : ℝ), (6266296424821/50000000000000 : ℝ), (44161356210961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312628333/10000000000 : ℝ)|^4193 ≤ (10826512731143/25000000000000 : ℝ)^3169
        have hw : |(5312628333/10000000000 : ℝ)|=(5312628333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1040601071/5000000000 : ℝ)|^4193 ≤ (6266296424821/50000000000000 : ℝ)^3169
        have hw : |(-1040601071/5000000000 : ℝ)|=(1040601071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695869883/5000000000 : ℝ)|^4193 ≤ (44161356210961/100000000000000 : ℝ)^3169
        have hw : |(2695869883/5000000000 : ℝ)|=(2695869883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_s9_3 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312628337/10000000000 : ℝ)*x 0 + (539173977/1000000000 : ℝ)*x 1 + (-2081202131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312628337/10000000000 : ℝ)^4193 ≤ (8661210193543/20000000000000 : ℝ)^3169 := by
    have hnat : (5312628337 : ℕ)^4193*20000000000000^3169 ≤ 8661210193543^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312628337 10000000000 8661210193543 20000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539173977/1000000000 : ℝ)^4193 ≤ (44161356254309/100000000000000 : ℝ)^3169 := by
    have hnat : (539173977 : ℕ)^4193*100000000000000^3169 ≤ 44161356254309^3169*1000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539173977 1000000000 44161356254309 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2081202131/10000000000 : ℝ)^4193 ≤ (6266296380999/50000000000000 : ℝ)^3169 := by
    have hnat : (2081202131 : ℕ)^4193*50000000000000^3169 ≤ 6266296380999^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2081202131 10000000000 6266296380999 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312628337/10000000000 : ℝ), (539173977/1000000000 : ℝ), (-2081202131/10000000000 : ℝ)] ![(8661210193543/20000000000000 : ℝ), (44161356254309/100000000000000 : ℝ), (6266296380999/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312628337/10000000000 : ℝ)|^4193 ≤ (8661210193543/20000000000000 : ℝ)^3169
        have hw : |(5312628337/10000000000 : ℝ)|=(5312628337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539173977/1000000000 : ℝ)|^4193 ≤ (44161356254309/100000000000000 : ℝ)^3169
        have hw : |(539173977/1000000000 : ℝ)|=(539173977/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2081202131/10000000000 : ℝ)|^4193 ≤ (6266296380999/50000000000000 : ℝ)^3169
        have hw : |(-2081202131/10000000000 : ℝ)|=(2081202131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_s9_4 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4357549527/10000000000 : ℝ)*x 0 + (896954249/2000000000 : ℝ)*x 1 + (66154651/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4357549527/10000000000 : ℝ)^4193 ≤ (33317360604647/100000000000000 : ℝ)^3169 := by
    have hnat : (4357549527 : ℕ)^4193*100000000000000^3169 ≤ 33317360604647^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4357549527 10000000000 33317360604647 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (896954249/2000000000 : ℝ)^4193 ≤ (34610432348251/100000000000000 : ℝ)^3169 := by
    have hnat : (896954249 : ℕ)^4193*100000000000000^3169 ≤ 34610432348251^3169*2000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896954249 2000000000 34610432348251 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (66154651/156250000 : ℝ)^4193 ≤ (32072207036113/100000000000000 : ℝ)^3169 := by
    have hnat : (66154651 : ℕ)^4193*100000000000000^3169 ≤ 32072207036113^3169*156250000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66154651 156250000 32072207036113 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4357549527/10000000000 : ℝ), (896954249/2000000000 : ℝ), (66154651/156250000 : ℝ)] ![(33317360604647/100000000000000 : ℝ), (34610432348251/100000000000000 : ℝ), (32072207036113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4357549527/10000000000 : ℝ)|^4193 ≤ (33317360604647/100000000000000 : ℝ)^3169
        have hw : |(4357549527/10000000000 : ℝ)|=(4357549527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(896954249/2000000000 : ℝ)|^4193 ≤ (34610432348251/100000000000000 : ℝ)^3169
        have hw : |(896954249/2000000000 : ℝ)|=(896954249/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(66154651/156250000 : ℝ)|^4193 ≤ (32072207036113/100000000000000 : ℝ)^3169
        have hw : |(66154651/156250000 : ℝ)|=(66154651/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1193_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150469749/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7039/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11419/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11419/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14077/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7039/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11419/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7039/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11419/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7039/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11419/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7039/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11419/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7039/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11419/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7039/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11419/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11419/100000 : ℝ) ^ (8385/2048 : ℝ) ≤ (13858134789110449/100000000000000000000 : ℝ) := by
    have hpowers : (11419/100000 : ℝ)^8385 ≤ (13858134789110449/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11419 : ℕ)^8385*100000000000000000000^2048 ≤ 13858134789110449^2048*100000^8385 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11419 100000 13858134789110449 100000000000000000000 8385 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11419/100000 : ℝ)) (X := (13858134789110449/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8385 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7039/50000 : ℝ) ^ (8385/2048 : ℝ) ≤ (63775496171069/195312500000000000 : ℝ) := by
    have hpowers : (7039/50000 : ℝ)^8385 ≤ (63775496171069/195312500000000000 : ℝ)^2048 := by
      have hnat : (7039 : ℕ)^8385*195312500000000000^2048 ≤ 63775496171069^2048*50000^8385 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7039 50000 63775496171069 195312500000000000 8385 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7039/50000 : ℝ)) (X := (63775496171069/195312500000000000 : ℝ)) (by norm_num) (by norm_num) 8385 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013858134789110449/50000000000000000000 : ℝ) ≤ (10000676887013521/10000000000000000 : ℝ) ^ (8385/2048 : ℝ) := by
    have hpowers : (50013858134789110449/50000000000000000000 : ℝ)^2048 ≤ (10000676887013521/10000000000000000 : ℝ)^8385 := by
      have hnat : (50013858134789110449 : ℕ)^2048*10000000000000000^8385 ≤ 10000676887013521^8385*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013858134789110449 50000000000000000000 10000676887013521 10000000000000000 2048 8385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000676887013521/10000000000000000 : ℝ)) (X := (50013858134789110449/50000000000000000000 : ℝ)) (by norm_num) 8385 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046511188828697777/100000000000000000000 : ℝ) ≤ (2500283954018289/2500000000000000 : ℝ) ^ (8385/2048 : ℝ) := by
    have hpowers : (100046511188828697777/100000000000000000000 : ℝ)^2048 ≤ (2500283954018289/2500000000000000 : ℝ)^8385 := by
      have hnat : (100046511188828697777 : ℕ)^2048*2500000000000000^8385 ≤ 2500283954018289^8385*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046511188828697777 100000000000000000000 2500283954018289 2500000000000000 2048 8385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500283954018289/2500000000000000 : ℝ)) (X := (100046511188828697777/100000000000000000000 : ℝ)) (by norm_num) 8385 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (97720025496171069/97656250000000000 : ℝ) ≤ (10001594745132791/10000000000000000 : ℝ) ^ (8385/2048 : ℝ) := by
    have hpowers : (97720025496171069/97656250000000000 : ℝ)^2048 ≤ (10001594745132791/10000000000000000 : ℝ)^8385 := by
      have hnat : (97720025496171069 : ℕ)^2048*10000000000000000^8385 ≤ 10001594745132791^8385*97656250000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        97720025496171069 97656250000000000 10001594745132791 10000000000000000 2048 8385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001594745132791/10000000000000000 : ℝ)) (X := (97720025496171069/97656250000000000 : ℝ)) (by norm_num) 8385 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13858134789110449/100000000000000000000 : ℝ) ≤ ((26581318820705008209/26590000000000000000 : ℝ)+2*(91785811927/53180000000000 : ℝ)*(11419/100000 : ℝ))^(8385/2048 : ℝ) := by
    rw [show (26581318820705008209/26590000000000000000 : ℝ)+2*(91785811927/53180000000000 : ℝ)*(11419/100000 : ℝ)=(10000676887013521/10000000000000000 : ℝ) by norm_num, show 1+2*(13858134789110449/100000000000000000000 : ℝ)=(50013858134789110449/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(63775496171069/195312500000000000 : ℝ)+(13858134789110449/100000000000000000000 : ℝ) ≤ ((26581318820705008209/26590000000000000000 : ℝ)+(91785811927/53180000000000 : ℝ)*((7039/50000 : ℝ)+(11419/100000 : ℝ)))^(8385/2048 : ℝ) := by
    rw [show (26581318820705008209/26590000000000000000 : ℝ)+(91785811927/53180000000000 : ℝ)*((7039/50000 : ℝ)+(11419/100000 : ℝ))=(2500283954018289/2500000000000000 : ℝ) by norm_num, show 1+(63775496171069/195312500000000000 : ℝ)+(13858134789110449/100000000000000000000 : ℝ)=(100046511188828697777/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(63775496171069/195312500000000000 : ℝ) ≤ ((26581318820705008209/26590000000000000000 : ℝ)+2*(91785811927/53180000000000 : ℝ)*(7039/50000 : ℝ))^(8385/2048 : ℝ) := by
    rw [show (26581318820705008209/26590000000000000000 : ℝ)+2*(91785811927/53180000000000 : ℝ)*(7039/50000 : ℝ)=(10001594745132791/10000000000000000 : ℝ) by norm_num, show 1+2*(63775496171069/195312500000000000 : ℝ)=(97720025496171069/97656250000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26581318820705008209/26590000000000000000 : ℝ)*(X 1 0+X 2 0)+(91785811927/53180000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8385/2048 : ℝ)) (lo := (11419/100000 : ℝ)) (hi := (7039/50000 : ℝ)) (c := (26581318820705008209/26590000000000000000 : ℝ)) (alpha := (91785811927/53180000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26581318820705008209/26590000000000000000 : ℝ)*(X 0 1+X 2 1)+(91785811927/53180000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8385/2048 : ℝ)) (lo := (11419/100000 : ℝ)) (hi := (7039/50000 : ℝ)) (c := (26581318820705008209/26590000000000000000 : ℝ)) (alpha := (91785811927/53180000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26581318820705008209/26590000000000000000 : ℝ)*(X 0 2+X 1 2)+(91785811927/53180000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8385/2048 : ℝ)) (lo := (11419/100000 : ℝ)) (hi := (7039/50000 : ℝ)) (c := (26581318820705008209/26590000000000000000 : ℝ)) (alpha := (91785811927/53180000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((668067191/1250000000 : ℝ)*X 2 0+(210662957/400000000 : ℝ)*X 2 1+(-2206368111/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s9_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-2142739069/10000000000 : ℝ)*X 0 0+(210675579/400000000 : ℝ)*X 0 1+(2695869891/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s9_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5312628333/10000000000 : ℝ)*X 1 0+(-1040601071/5000000000 : ℝ)*X 1 1+(2695869883/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s9_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5312628337/10000000000 : ℝ)*X 2 0+(539173977/1000000000 : ℝ)*X 2 1+(-2081202131/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s9_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((4357549527/10000000000 : ℝ)*X 0 0+(896954249/2000000000 : ℝ)*X 0 1+(66154651/156250000 : ℝ)*X 0 2+(4357549527/10000000000 : ℝ)*X 1 0+(896954249/2000000000 : ℝ)*X 1 1+(66154651/156250000 : ℝ)*X 1 2+(4357549527/10000000000 : ℝ)*X 2 0+(896954249/2000000000 : ℝ)*X 2 1+(66154651/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s9_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8084223058261203623889/2659000000000000000000000000 : ℝ) := by norm_num
    linear_combination (87941507/10000000000000 : ℝ)*(base19) + (960984221/100000000000000 : ℝ)*(base23) + (294866173/100000000000000 : ℝ)*(lower1) + (32512449/100000000000000 : ℝ)*(upper2) + (12196983/12500000000000 : ℝ)*(upper3) + (10017753/10000000000000 : ℝ)*(upper5) + (2998906752885083/50000000000000 : ℝ)*(major0) + (2998906752885083/50000000000000 : ℝ)*(major1) + (2998906752885083/50000000000000 : ℝ)*(major2) + (2387519961/100000000000000 : ℝ)*(sp0) + (8009567555654303/100000000000000 : ℝ)*(sp1) + (8009566676239233/100000000000000 : ℝ)*(sp2) + (4004782103575061/50000000000000 : ℝ)*(sp3) + (1993029677270933/50000000000000 : ℝ)*(sp4) + (1993029677270933/50000000000000 : ℝ)*(f.failure) + (8009567555654303/100000000000000 : ℝ)*(f.sum) + (16137505540143/2659000000000000000000000000 : ℝ)*base66 + (12677872373883353653/1329500000000000000000000000000000 : ℝ)*base68 + (49695648211804146347/1329500000000000000000000000000000 : ℝ)*base69 + (7786480471974646347/1329500000000000000000000000000000 : ℝ)*base71 + (2610492396263/1329500000000000000000000000 : ℝ)*base73 + (10624906876989853653/1329500000000000000000000000000000 : ℝ)*base76 + (4766412481448853653/1329500000000000000000000000000000 : ℝ)*base78 + (3331690169886646347/1329500000000000000000000000000000 : ℝ)*base79 + (31767054690393/2659000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (6494183/5000000000000000000000 : ℝ)*base90 + (6494183/5000000000000000000000 : ℝ)*base92 + (6494183/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1193_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150469749/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7039/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11419/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11419/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14077/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1193_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1193_box_0 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1008751967/5000000000 : ℝ)*x 0 + (5375569603/10000000000 : ℝ)*x 1 + (5375569533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1008751967/5000000000 : ℝ)^4193 ≤ (12027596172663/100000000000000 : ℝ)^3169 := by
    have hnat : (1008751967 : ℕ)^4193*100000000000000^3169 ≤ 12027596172663^3169*5000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008751967 5000000000 12027596172663 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5375569603/10000000000 : ℝ)^4193 ≤ (10996550571659/25000000000000 : ℝ)^3169 := by
    have hnat : (5375569603 : ℕ)^4193*25000000000000^3169 ≤ 10996550571659^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375569603 10000000000 10996550571659 25000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5375569533/10000000000 : ℝ)^4193 ≤ (43986201528769/100000000000000 : ℝ)^3169 := by
    have hnat : (5375569533 : ℕ)^4193*100000000000000^3169 ≤ 43986201528769^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375569533 10000000000 43986201528769 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1008751967/5000000000 : ℝ), (5375569603/10000000000 : ℝ), (5375569533/10000000000 : ℝ)] ![(12027596172663/100000000000000 : ℝ), (10996550571659/25000000000000 : ℝ), (43986201528769/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1008751967/5000000000 : ℝ)|^4193 ≤ (12027596172663/100000000000000 : ℝ)^3169
        have hw : |(-1008751967/5000000000 : ℝ)|=(1008751967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5375569603/10000000000 : ℝ)|^4193 ≤ (10996550571659/25000000000000 : ℝ)^3169
        have hw : |(5375569603/10000000000 : ℝ)|=(5375569603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5375569533/10000000000 : ℝ)|^4193 ≤ (43986201528769/100000000000000 : ℝ)^3169
        have hw : |(5375569533/10000000000 : ℝ)|=(5375569533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_box_1 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (662053547/1250000000 : ℝ)*x 0 + (-2124955901/10000000000 : ℝ)*x 1 + (5375569659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (662053547/1250000000 : ℝ)^4193 ≤ (5391426478751/12500000000000 : ℝ)^3169 := by
    have hnat : (662053547 : ℕ)^4193*12500000000000^3169 ≤ 5391426478751^3169*1250000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662053547 1250000000 5391426478751 12500000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2124955901/10000000000 : ℝ)^4193 ≤ (6441192632189/50000000000000 : ℝ)^3169 := by
    have hnat : (2124955901 : ℕ)^4193*50000000000000^3169 ≤ 6441192632189^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124955901 10000000000 6441192632189 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5375569659/10000000000 : ℝ)^4193 ≤ (43986202892929/100000000000000 : ℝ)^3169 := by
    have hnat : (5375569659 : ℕ)^4193*100000000000000^3169 ≤ 43986202892929^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375569659 10000000000 43986202892929 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(662053547/1250000000 : ℝ), (-2124955901/10000000000 : ℝ), (5375569659/10000000000 : ℝ)] ![(5391426478751/12500000000000 : ℝ), (6441192632189/50000000000000 : ℝ), (43986202892929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(662053547/1250000000 : ℝ)|^4193 ≤ (5391426478751/12500000000000 : ℝ)^3169
        have hw : |(662053547/1250000000 : ℝ)|=(662053547/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2124955901/10000000000 : ℝ)|^4193 ≤ (6441192632189/50000000000000 : ℝ)^3169
        have hw : |(-2124955901/10000000000 : ℝ)|=(2124955901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5375569659/10000000000 : ℝ)|^4193 ≤ (43986202892929/100000000000000 : ℝ)^3169
        have hw : |(5375569659/10000000000 : ℝ)|=(5375569659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_box_2 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5296428039/10000000000 : ℝ)*x 0 + (5375569893/10000000000 : ℝ)*x 1 + (-1062478019/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296428039/10000000000 : ℝ)^4193 ≤ (10782852049717/25000000000000 : ℝ)^3169 := by
    have hnat : (5296428039 : ℕ)^4193*25000000000000^3169 ≤ 10782852049717^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296428039 10000000000 10782852049717 25000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5375569893/10000000000 : ℝ)^4193 ≤ (687284459787/1562500000000 : ℝ)^3169 := by
    have hnat : (5375569893 : ℕ)^4193*1562500000000^3169 ≤ 687284459787^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375569893 10000000000 687284459787 1562500000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1062478019/5000000000 : ℝ)^4193 ≤ (12882386363307/100000000000000 : ℝ)^3169 := by
    have hnat : (1062478019 : ℕ)^4193*100000000000000^3169 ≤ 12882386363307^3169*5000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062478019 5000000000 12882386363307 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296428039/10000000000 : ℝ), (5375569893/10000000000 : ℝ), (-1062478019/5000000000 : ℝ)] ![(10782852049717/25000000000000 : ℝ), (687284459787/1562500000000 : ℝ), (12882386363307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296428039/10000000000 : ℝ)|^4193 ≤ (10782852049717/25000000000000 : ℝ)^3169
        have hw : |(5296428039/10000000000 : ℝ)|=(5296428039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5375569893/10000000000 : ℝ)|^4193 ≤ (687284459787/1562500000000 : ℝ)^3169
        have hw : |(5375569893/10000000000 : ℝ)|=(5375569893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1062478019/5000000000 : ℝ)|^4193 ≤ (12882386363307/100000000000000 : ℝ)^3169
        have hw : |(-1062478019/5000000000 : ℝ)|=(1062478019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_box_3 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (279034381/625000000 : ℝ)*x 0 + (4306108023/10000000000 : ℝ)*x 1 + (2153054083/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (279034381/625000000 : ℝ)^4193 ≤ (8601026062947/25000000000000 : ℝ)^3169 := by
    have hnat : (279034381 : ℕ)^4193*25000000000000^3169 ≤ 8601026062947^3169*625000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279034381 625000000 8601026062947 25000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4306108023/10000000000 : ℝ)^4193 ≤ (32797947149171/100000000000000 : ℝ)^3169 := by
    have hnat : (4306108023 : ℕ)^4193*100000000000000^3169 ≤ 32797947149171^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4306108023 10000000000 32797947149171 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2153054083/5000000000 : ℝ)^4193 ≤ (8199487147573/25000000000000 : ℝ)^3169 := by
    have hnat : (2153054083 : ℕ)^4193*25000000000000^3169 ≤ 8199487147573^3169*5000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153054083 5000000000 8199487147573 25000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(279034381/625000000 : ℝ), (4306108023/10000000000 : ℝ), (2153054083/5000000000 : ℝ)] ![(8601026062947/25000000000000 : ℝ), (32797947149171/100000000000000 : ℝ), (8199487147573/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(279034381/625000000 : ℝ)|^4193 ≤ (8601026062947/25000000000000 : ℝ)^3169
        have hw : |(279034381/625000000 : ℝ)|=(279034381/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4306108023/10000000000 : ℝ)|^4193 ≤ (32797947149171/100000000000000 : ℝ)^3169
        have hw : |(4306108023/10000000000 : ℝ)|=(4306108023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2153054083/5000000000 : ℝ)|^4193 ≤ (8199487147573/25000000000000 : ℝ)^3169
        have hw : |(2153054083/5000000000 : ℝ)|=(2153054083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_box_4 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1134676473/5000000000 : ℝ)*x 0 + (264087907/500000000 : ℝ)*x 1 + (82527471/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1134676473/5000000000 : ℝ)^4193 ≤ (2810635064557/20000000000000 : ℝ)^3169 := by
    have hnat : (1134676473 : ℕ)^4193*20000000000000^3169 ≤ 2810635064557^3169*5000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134676473 5000000000 2810635064557 20000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (264087907/500000000 : ℝ)^4193 ≤ (8594682461217/20000000000000 : ℝ)^3169 := by
    have hnat : (264087907 : ℕ)^4193*20000000000000^3169 ≤ 8594682461217^3169*500000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264087907 500000000 8594682461217 20000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (82527471/156250000 : ℝ)^4193 ≤ (8594682469829/20000000000000 : ℝ)^3169 := by
    have hnat : (82527471 : ℕ)^4193*20000000000000^3169 ≤ 8594682469829^3169*156250000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82527471 156250000 8594682469829 20000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1134676473/5000000000 : ℝ), (264087907/500000000 : ℝ), (82527471/156250000 : ℝ)] ![(2810635064557/20000000000000 : ℝ), (8594682461217/20000000000000 : ℝ), (8594682469829/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1134676473/5000000000 : ℝ)|^4193 ≤ (2810635064557/20000000000000 : ℝ)^3169
        have hw : |(-1134676473/5000000000 : ℝ)|=(1134676473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(264087907/500000000 : ℝ)|^4193 ≤ (8594682461217/20000000000000 : ℝ)^3169
        have hw : |(264087907/500000000 : ℝ)|=(264087907/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(82527471/156250000 : ℝ)|^4193 ≤ (8594682469829/20000000000000 : ℝ)^3169
        have hw : |(82527471/156250000 : ℝ)|=(82527471/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_box_5 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1072525999/2000000000 : ℝ)*x 0 + (-2162007559/10000000000 : ℝ)*x 1 + (5281758051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072525999/2000000000 : ℝ)^4193 ≤ (21923082014869/50000000000000 : ℝ)^3169 := by
    have hnat : (1072525999 : ℕ)^4193*50000000000000^3169 ≤ 21923082014869^3169*2000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072525999 2000000000 21923082014869 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2162007559/10000000000 : ℝ)^4193 ≤ (6590212306793/50000000000000 : ℝ)^3169 := by
    have hnat : (2162007559 : ℕ)^4193*50000000000000^3169 ≤ 6590212306793^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162007559 10000000000 6590212306793 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5281758051/10000000000 : ℝ)^4193 ≤ (21486705673989/50000000000000 : ℝ)^3169 := by
    have hnat : (5281758051 : ℕ)^4193*50000000000000^3169 ≤ 21486705673989^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281758051 10000000000 21486705673989 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072525999/2000000000 : ℝ), (-2162007559/10000000000 : ℝ), (5281758051/10000000000 : ℝ)] ![(21923082014869/50000000000000 : ℝ), (6590212306793/50000000000000 : ℝ), (21486705673989/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072525999/2000000000 : ℝ)|^4193 ≤ (21923082014869/50000000000000 : ℝ)^3169
        have hw : |(1072525999/2000000000 : ℝ)|=(1072525999/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2162007559/10000000000 : ℝ)|^4193 ≤ (6590212306793/50000000000000 : ℝ)^3169
        have hw : |(-2162007559/10000000000 : ℝ)|=(2162007559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5281758051/10000000000 : ℝ)|^4193 ≤ (21486705673989/50000000000000 : ℝ)^3169
        have hw : |(5281758051/10000000000 : ℝ)|=(5281758051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_box_6 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1340657641/2500000000 : ℝ)*x 0 + (5281758117/10000000000 : ℝ)*x 1 + (-1081003353/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1340657641/2500000000 : ℝ)^4193 ≤ (21923085092657/50000000000000 : ℝ)^3169 := by
    have hnat : (1340657641 : ℕ)^4193*50000000000000^3169 ≤ 21923085092657^3169*2500000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1340657641 2500000000 21923085092657 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5281758117/10000000000 : ℝ)^4193 ≤ (10743353014621/25000000000000 : ℝ)^3169 := by
    have hnat : (5281758117 : ℕ)^4193*25000000000000^3169 ≤ 10743353014621^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281758117 10000000000 10743353014621 25000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081003353/5000000000 : ℝ)^4193 ≤ (527216709321/4000000000000 : ℝ)^3169 := by
    have hnat : (1081003353 : ℕ)^4193*4000000000000^3169 ≤ 527216709321^3169*5000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081003353 5000000000 527216709321 4000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1340657641/2500000000 : ℝ), (5281758117/10000000000 : ℝ), (-1081003353/5000000000 : ℝ)] ![(21923085092657/50000000000000 : ℝ), (10743353014621/25000000000000 : ℝ), (527216709321/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1340657641/2500000000 : ℝ)|^4193 ≤ (21923085092657/50000000000000 : ℝ)^3169
        have hw : |(1340657641/2500000000 : ℝ)|=(1340657641/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5281758117/10000000000 : ℝ)|^4193 ≤ (10743353014621/25000000000000 : ℝ)^3169
        have hw : |(5281758117/10000000000 : ℝ)|=(5281758117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1081003353/5000000000 : ℝ)|^4193 ≤ (527216709321/4000000000000 : ℝ)^3169
        have hw : |(-1081003353/5000000000 : ℝ)|=(1081003353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_box_7 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4250147057/10000000000 : ℝ)*x 0 + (882657951/2000000000 : ℝ)*x 1 + (4413288571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4250147057/10000000000 : ℝ)^4193 ≤ (6447034624413/20000000000000 : ℝ)^3169 := by
    have hnat : (4250147057 : ℕ)^4193*20000000000000^3169 ≤ 6447034624413^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4250147057 10000000000 6447034624413 20000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (882657951/2000000000 : ℝ)^4193 ≤ (16941209722301/50000000000000 : ℝ)^3169 := by
    have hnat : (882657951 : ℕ)^4193*50000000000000^3169 ≤ 16941209722301^3169*2000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      882657951 2000000000 16941209722301 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4413288571/10000000000 : ℝ)^4193 ≤ (33882407417353/100000000000000 : ℝ)^3169 := by
    have hnat : (4413288571 : ℕ)^4193*100000000000000^3169 ≤ 33882407417353^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4413288571 10000000000 33882407417353 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4250147057/10000000000 : ℝ), (882657951/2000000000 : ℝ), (4413288571/10000000000 : ℝ)] ![(6447034624413/20000000000000 : ℝ), (16941209722301/50000000000000 : ℝ), (33882407417353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4250147057/10000000000 : ℝ)|^4193 ≤ (6447034624413/20000000000000 : ℝ)^3169
        have hw : |(4250147057/10000000000 : ℝ)|=(4250147057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(882657951/2000000000 : ℝ)|^4193 ≤ (16941209722301/50000000000000 : ℝ)^3169
        have hw : |(882657951/2000000000 : ℝ)|=(882657951/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4413288571/10000000000 : ℝ)|^4193 ≤ (33882407417353/100000000000000 : ℝ)^3169
        have hw : |(4413288571/10000000000 : ℝ)|=(4413288571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_box_8 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-554157659/2500000000 : ℝ)*x 0 + (2608930307/5000000000 : ℝ)*x 1 + (2692590537/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (554157659/2500000000 : ℝ)^4193 ≤ (13622819577307/100000000000000 : ℝ)^3169 := by
    have hnat : (554157659 : ℕ)^4193*100000000000000^3169 ≤ 13622819577307^3169*2500000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554157659 2500000000 13622819577307 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608930307/5000000000 : ℝ)^4193 ≤ (42286887918323/100000000000000 : ℝ)^3169 := by
    have hnat : (2608930307 : ℕ)^4193*100000000000000^3169 ≤ 42286887918323^3169*5000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608930307 5000000000 42286887918323 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2692590537/5000000000 : ℝ)^4193 ≤ (22045146244139/50000000000000 : ℝ)^3169 := by
    have hnat : (2692590537 : ℕ)^4193*50000000000000^3169 ≤ 22045146244139^3169*5000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692590537 5000000000 22045146244139 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-554157659/2500000000 : ℝ), (2608930307/5000000000 : ℝ), (2692590537/5000000000 : ℝ)] ![(13622819577307/100000000000000 : ℝ), (42286887918323/100000000000000 : ℝ), (22045146244139/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-554157659/2500000000 : ℝ)|^4193 ≤ (13622819577307/100000000000000 : ℝ)^3169
        have hw : |(-554157659/2500000000 : ℝ)|=(554157659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608930307/5000000000 : ℝ)|^4193 ≤ (42286887918323/100000000000000 : ℝ)^3169
        have hw : |(2608930307/5000000000 : ℝ)|=(2608930307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2692590537/5000000000 : ℝ)|^4193 ≤ (22045146244139/50000000000000 : ℝ)^3169
        have hw : |(2692590537/5000000000 : ℝ)|=(2692590537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_box_9 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289642267/10000000000 : ℝ)*x 0 + (-424218423/2000000000 : ℝ)*x 1 + (673147619/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289642267/10000000000 : ℝ)^4193 ≤ (43058307333981/100000000000000 : ℝ)^3169 := by
    have hnat : (5289642267 : ℕ)^4193*100000000000000^3169 ≤ 43058307333981^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289642267 10000000000 43058307333981 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (424218423/2000000000 : ℝ)^4193 ≤ (6425700742397/50000000000000 : ℝ)^3169 := by
    have hnat : (424218423 : ℕ)^4193*50000000000000^3169 ≤ 6425700742397^3169*2000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424218423 2000000000 6425700742397 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673147619/1250000000 : ℝ)^4193 ≤ (22045145583331/50000000000000 : ℝ)^3169 := by
    have hnat : (673147619 : ℕ)^4193*50000000000000^3169 ≤ 22045145583331^3169*1250000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673147619 1250000000 22045145583331 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289642267/10000000000 : ℝ), (-424218423/2000000000 : ℝ), (673147619/1250000000 : ℝ)] ![(43058307333981/100000000000000 : ℝ), (6425700742397/50000000000000 : ℝ), (22045145583331/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289642267/10000000000 : ℝ)|^4193 ≤ (43058307333981/100000000000000 : ℝ)^3169
        have hw : |(5289642267/10000000000 : ℝ)|=(5289642267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-424218423/2000000000 : ℝ)|^4193 ≤ (6425700742397/50000000000000 : ℝ)^3169
        have hw : |(-424218423/2000000000 : ℝ)|=(424218423/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673147619/1250000000 : ℝ)|^4193 ≤ (22045145583331/50000000000000 : ℝ)^3169
        have hw : |(673147619/1250000000 : ℝ)|=(673147619/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_box_10 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289642351/10000000000 : ℝ)*x 0 + (5385181321/10000000000 : ℝ)*x 1 + (-132568219/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289642351/10000000000 : ℝ)^4193 ≤ (21529154119349/50000000000000 : ℝ)^3169 := by
    have hnat : (5289642351 : ℕ)^4193*50000000000000^3169 ≤ 21529154119349^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289642351 10000000000 21529154119349 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5385181321/10000000000 : ℝ)^4193 ≤ (5511286895501/12500000000000 : ℝ)^3169 := by
    have hnat : (5385181321 : ℕ)^4193*12500000000000^3169 ≤ 5511286895501^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385181321 10000000000 5511286895501 12500000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (132568219/625000000 : ℝ)^4193 ≤ (6425698293307/50000000000000 : ℝ)^3169 := by
    have hnat : (132568219 : ℕ)^4193*50000000000000^3169 ≤ 6425698293307^3169*625000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132568219 625000000 6425698293307 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289642351/10000000000 : ℝ), (5385181321/10000000000 : ℝ), (-132568219/625000000 : ℝ)] ![(21529154119349/50000000000000 : ℝ), (5511286895501/12500000000000 : ℝ), (6425698293307/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289642351/10000000000 : ℝ)|^4193 ≤ (21529154119349/50000000000000 : ℝ)^3169
        have hw : |(5289642351/10000000000 : ℝ)|=(5289642351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5385181321/10000000000 : ℝ)|^4193 ≤ (5511286895501/12500000000000 : ℝ)^3169
        have hw : |(5385181321/10000000000 : ℝ)|=(5385181321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-132568219/625000000 : ℝ)|^4193 ≤ (6425698293307/50000000000000 : ℝ)^3169
        have hw : |(-132568219/625000000 : ℝ)|=(132568219/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_box_11 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2243121701/5000000000 : ℝ)*x 0 + (1073780201/2500000000 : ℝ)*x 1 + (1073780257/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2243121701/5000000000 : ℝ)^4193 ≤ (17312732688891/50000000000000 : ℝ)^3169 := by
    have hnat : (2243121701 : ℕ)^4193*50000000000000^3169 ≤ 17312732688891^3169*5000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243121701 5000000000 17312732688891 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1073780201/2500000000 : ℝ)^4193 ≤ (6537453235061/20000000000000 : ℝ)^3169 := by
    have hnat : (1073780201 : ℕ)^4193*20000000000000^3169 ≤ 6537453235061^3169*2500000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073780201 2500000000 6537453235061 20000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1073780257/2500000000 : ℝ)^4193 ≤ (16343634215431/50000000000000 : ℝ)^3169 := by
    have hnat : (1073780257 : ℕ)^4193*50000000000000^3169 ≤ 16343634215431^3169*2500000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073780257 2500000000 16343634215431 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2243121701/5000000000 : ℝ), (1073780201/2500000000 : ℝ), (1073780257/2500000000 : ℝ)] ![(17312732688891/50000000000000 : ℝ), (6537453235061/20000000000000 : ℝ), (16343634215431/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2243121701/5000000000 : ℝ)|^4193 ≤ (17312732688891/50000000000000 : ℝ)^3169
        have hw : |(2243121701/5000000000 : ℝ)|=(2243121701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1073780201/2500000000 : ℝ)|^4193 ≤ (6537453235061/20000000000000 : ℝ)^3169
        have hw : |(1073780201/2500000000 : ℝ)|=(1073780201/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1073780257/2500000000 : ℝ)|^4193 ≤ (16343634215431/50000000000000 : ℝ)^3169
        have hw : |(1073780257/2500000000 : ℝ)|=(1073780257/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_box_12 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1035257169/5000000000 : ℝ)*x 0 + (5438225441/10000000000 : ℝ)*x 1 + (5273697867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1035257169/5000000000 : ℝ)^4193 ≤ (155593838657/1250000000000 : ℝ)^3169 := by
    have hnat : (1035257169 : ℕ)^4193*1250000000000^3169 ≤ 155593838657^3169*5000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035257169 5000000000 155593838657 1250000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5438225441/10000000000 : ℝ)^4193 ≤ (44665829999823/100000000000000 : ℝ)^3169 := by
    have hnat : (5438225441 : ℕ)^4193*100000000000000^3169 ≤ 44665829999823^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438225441 10000000000 44665829999823 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5273697867/10000000000 : ℝ)^4193 ≤ (42886662886881/100000000000000 : ℝ)^3169 := by
    have hnat : (5273697867 : ℕ)^4193*100000000000000^3169 ≤ 42886662886881^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273697867 10000000000 42886662886881 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1035257169/5000000000 : ℝ), (5438225441/10000000000 : ℝ), (5273697867/10000000000 : ℝ)] ![(155593838657/1250000000000 : ℝ), (44665829999823/100000000000000 : ℝ), (42886662886881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1035257169/5000000000 : ℝ)|^4193 ≤ (155593838657/1250000000000 : ℝ)^3169
        have hw : |(-1035257169/5000000000 : ℝ)|=(1035257169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5438225441/10000000000 : ℝ)|^4193 ≤ (44665829999823/100000000000000 : ℝ)^3169
        have hw : |(5438225441/10000000000 : ℝ)|=(5438225441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5273697867/10000000000 : ℝ)|^4193 ≤ (42886662886881/100000000000000 : ℝ)^3169
        have hw : |(5273697867/10000000000 : ℝ)|=(5273697867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_box_13 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1073663309/2000000000 : ℝ)*x 0 + (-433026677/2000000000 : ℝ)*x 1 + (5273697841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073663309/2000000000 : ℝ)^4193 ≤ (43907692998679/100000000000000 : ℝ)^3169 := by
    have hnat : (1073663309 : ℕ)^4193*100000000000000^3169 ≤ 43907692998679^3169*2000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073663309 2000000000 43907692998679 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (433026677/2000000000 : ℝ)^4193 ≤ (1650705547197/12500000000000 : ℝ)^3169 := by
    have hnat : (433026677 : ℕ)^4193*12500000000000^3169 ≤ 1650705547197^3169*2000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433026677 2000000000 1650705547197 12500000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5273697841/10000000000 : ℝ)^4193 ≤ (42886662607123/100000000000000 : ℝ)^3169 := by
    have hnat : (5273697841 : ℕ)^4193*100000000000000^3169 ≤ 42886662607123^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273697841 10000000000 42886662607123 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073663309/2000000000 : ℝ), (-433026677/2000000000 : ℝ), (5273697841/10000000000 : ℝ)] ![(43907692998679/100000000000000 : ℝ), (1650705547197/12500000000000 : ℝ), (42886662607123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073663309/2000000000 : ℝ)|^4193 ≤ (43907692998679/100000000000000 : ℝ)^3169
        have hw : |(1073663309/2000000000 : ℝ)|=(1073663309/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-433026677/2000000000 : ℝ)|^4193 ≤ (1650705547197/12500000000000 : ℝ)^3169
        have hw : |(-433026677/2000000000 : ℝ)|=(433026677/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5273697841/10000000000 : ℝ)|^4193 ≤ (42886662607123/100000000000000 : ℝ)^3169
        have hw : |(5273697841/10000000000 : ℝ)|=(5273697841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_box_14 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1073663313/2000000000 : ℝ)*x 0 + (1054739559/2000000000 : ℝ)*x 1 + (-108256671/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073663313/2000000000 : ℝ)^4193 ≤ (43907693215117/100000000000000 : ℝ)^3169 := by
    have hnat : (1073663313 : ℕ)^4193*100000000000000^3169 ≤ 43907693215117^3169*2000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073663313 2000000000 43907693215117 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1054739559/2000000000 : ℝ)^4193 ≤ (21443331056083/50000000000000 : ℝ)^3169 := by
    have hnat : (1054739559 : ℕ)^4193*50000000000000^3169 ≤ 21443331056083^3169*2000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054739559 2000000000 21443331056083 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (108256671/500000000 : ℝ)^4193 ≤ (3301411165007/25000000000000 : ℝ)^3169 := by
    have hnat : (108256671 : ℕ)^4193*25000000000000^3169 ≤ 3301411165007^3169*500000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108256671 500000000 3301411165007 25000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073663313/2000000000 : ℝ), (1054739559/2000000000 : ℝ), (-108256671/500000000 : ℝ)] ![(43907693215117/100000000000000 : ℝ), (21443331056083/50000000000000 : ℝ), (3301411165007/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073663313/2000000000 : ℝ)|^4193 ≤ (43907693215117/100000000000000 : ℝ)^3169
        have hw : |(1073663313/2000000000 : ℝ)|=(1073663313/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1054739559/2000000000 : ℝ)|^4193 ≤ (21443331056083/50000000000000 : ℝ)^3169
        have hw : |(1054739559/2000000000 : ℝ)|=(1054739559/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-108256671/500000000 : ℝ)|^4193 ≤ (3301411165007/25000000000000 : ℝ)^3169
        have hw : |(-108256671/500000000 : ℝ)|=(108256671/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_box_15 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4231494083/10000000000 : ℝ)*x 0 + (4422493281/10000000000 : ℝ)*x 1 + (4422493087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4231494083/10000000000 : ℝ)^4193 ≤ (320481185207/1000000000000 : ℝ)^3169 := by
    have hnat : (4231494083 : ℕ)^4193*1000000000000^3169 ≤ 320481185207^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4231494083 10000000000 320481185207 1000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4422493281/10000000000 : ℝ)^4193 ≤ (16987970860849/50000000000000 : ℝ)^3169 := by
    have hnat : (4422493281 : ℕ)^4193*50000000000000^3169 ≤ 16987970860849^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4422493281 10000000000 16987970860849 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4422493087/10000000000 : ℝ)^4193 ≤ (3397593974969/10000000000000 : ℝ)^3169 := by
    have hnat : (4422493087 : ℕ)^4193*10000000000000^3169 ≤ 3397593974969^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4422493087 10000000000 3397593974969 10000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4231494083/10000000000 : ℝ), (4422493281/10000000000 : ℝ), (4422493087/10000000000 : ℝ)] ![(320481185207/1000000000000 : ℝ), (16987970860849/50000000000000 : ℝ), (3397593974969/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4231494083/10000000000 : ℝ)|^4193 ≤ (320481185207/1000000000000 : ℝ)^3169
        have hw : |(4231494083/10000000000 : ℝ)|=(4231494083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4422493281/10000000000 : ℝ)|^4193 ≤ (16987970860849/50000000000000 : ℝ)^3169
        have hw : |(4422493281/10000000000 : ℝ)|=(4422493281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4422493087/10000000000 : ℝ)|^4193 ≤ (3397593974969/10000000000000 : ℝ)^3169
        have hw : |(4422493087/10000000000 : ℝ)|=(4422493087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1193_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150469749/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14077/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11419/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31119/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29669/50000 : ℝ) ∧ (79963/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (41619/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14077/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11419/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14077/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11419/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14077/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11419/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14077/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11419/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14077/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11419/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14077/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11419/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11419/100000 : ℝ) ^ (8385/2048 : ℝ) ≤ (13858134789110449/100000000000000000000 : ℝ) := by
    have hpowers : (11419/100000 : ℝ)^8385 ≤ (13858134789110449/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11419 : ℕ)^8385*100000000000000000000^2048 ≤ 13858134789110449^2048*100000^8385 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11419 100000 13858134789110449 100000000000000000000 8385 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11419/100000 : ℝ)) (X := (13858134789110449/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8385 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14077/100000 : ℝ) ^ (8385/2048 : ℝ) ≤ (8160889687396873/25000000000000000000 : ℝ) := by
    have hpowers : (14077/100000 : ℝ)^8385 ≤ (8160889687396873/25000000000000000000 : ℝ)^2048 := by
      have hnat : (14077 : ℕ)^8385*25000000000000000000^2048 ≤ 8160889687396873^2048*100000^8385 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14077 100000 8160889687396873 25000000000000000000 8385 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14077/100000 : ℝ)) (X := (8160889687396873/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8385 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013858134789110449/50000000000000000000 : ℝ) ≤ (10000676887013521/10000000000000000 : ℝ) ^ (8385/2048 : ℝ) := by
    have hpowers : (50013858134789110449/50000000000000000000 : ℝ)^2048 ≤ (10000676887013521/10000000000000000 : ℝ)^8385 := by
      have hnat : (50013858134789110449 : ℕ)^2048*10000000000000000^8385 ≤ 10000676887013521^8385*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013858134789110449 50000000000000000000 10000676887013521 10000000000000000 2048 8385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000676887013521/10000000000000000 : ℝ)) (X := (50013858134789110449/50000000000000000000 : ℝ)) (by norm_num) 8385 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046501693538697941/100000000000000000000 : ℝ) ≤ (10001135584236283/10000000000000000 : ℝ) ^ (8385/2048 : ℝ) := by
    have hpowers : (100046501693538697941/100000000000000000000 : ℝ)^2048 ≤ (10001135584236283/10000000000000000 : ℝ)^8385 := by
      have hnat : (100046501693538697941 : ℕ)^2048*10000000000000000^8385 ≤ 10001135584236283^8385*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046501693538697941 100000000000000000000 10001135584236283 10000000000000000 2048 8385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001135584236283/10000000000000000 : ℝ)) (X := (100046501693538697941/100000000000000000000 : ℝ)) (by norm_num) 8385 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508160889687396873/12500000000000000000 : ℝ) ≤ (2000318856291809/2000000000000000 : ℝ) ^ (8385/2048 : ℝ) := by
    have hpowers : (12508160889687396873/12500000000000000000 : ℝ)^2048 ≤ (2000318856291809/2000000000000000 : ℝ)^8385 := by
      have hnat : (12508160889687396873 : ℕ)^2048*2000000000000000^8385 ≤ 2000318856291809^8385*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508160889687396873 12500000000000000000 2000318856291809 2000000000000000 2048 8385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000318856291809/2000000000000000 : ℝ)) (X := (12508160889687396873/12500000000000000000 : ℝ)) (by norm_num) 8385 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13858134789110449/100000000000000000000 : ℝ) ≤ ((4428553906418083377/4430000000000000000 : ℝ)+2*(76449537127/44300000000000 : ℝ)*(11419/100000 : ℝ))^(8385/2048 : ℝ) := by
    rw [show (4428553906418083377/4430000000000000000 : ℝ)+2*(76449537127/44300000000000 : ℝ)*(11419/100000 : ℝ)=(10000676887013521/10000000000000000 : ℝ) by norm_num, show 1+2*(13858134789110449/100000000000000000000 : ℝ)=(50013858134789110449/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8160889687396873/25000000000000000000 : ℝ)+(13858134789110449/100000000000000000000 : ℝ) ≤ ((4428553906418083377/4430000000000000000 : ℝ)+(76449537127/44300000000000 : ℝ)*((14077/100000 : ℝ)+(11419/100000 : ℝ)))^(8385/2048 : ℝ) := by
    rw [show (4428553906418083377/4430000000000000000 : ℝ)+(76449537127/44300000000000 : ℝ)*((14077/100000 : ℝ)+(11419/100000 : ℝ))=(10001135584236283/10000000000000000 : ℝ) by norm_num, show 1+(8160889687396873/25000000000000000000 : ℝ)+(13858134789110449/100000000000000000000 : ℝ)=(100046501693538697941/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8160889687396873/25000000000000000000 : ℝ) ≤ ((4428553906418083377/4430000000000000000 : ℝ)+2*(76449537127/44300000000000 : ℝ)*(14077/100000 : ℝ))^(8385/2048 : ℝ) := by
    rw [show (4428553906418083377/4430000000000000000 : ℝ)+2*(76449537127/44300000000000 : ℝ)*(14077/100000 : ℝ)=(2000318856291809/2000000000000000 : ℝ) by norm_num, show 1+2*(8160889687396873/25000000000000000000 : ℝ)=(12508160889687396873/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4428553906418083377/4430000000000000000 : ℝ)*(X 1 0+X 2 0)+(76449537127/44300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8385/2048 : ℝ)) (lo := (11419/100000 : ℝ)) (hi := (14077/100000 : ℝ)) (c := (4428553906418083377/4430000000000000000 : ℝ)) (alpha := (76449537127/44300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4428553906418083377/4430000000000000000 : ℝ)*(X 0 1+X 2 1)+(76449537127/44300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8385/2048 : ℝ)) (lo := (11419/100000 : ℝ)) (hi := (14077/100000 : ℝ)) (c := (4428553906418083377/4430000000000000000 : ℝ)) (alpha := (76449537127/44300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4428553906418083377/4430000000000000000 : ℝ)*(X 0 2+X 1 2)+(76449537127/44300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8385/2048 : ℝ)) (lo := (11419/100000 : ℝ)) (hi := (14077/100000 : ℝ)) (c := (4428553906418083377/4430000000000000000 : ℝ)) (alpha := (76449537127/44300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1008751967/5000000000 : ℝ)*X 0 0+(5375569603/10000000000 : ℝ)*X 0 1+(5375569533/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((662053547/1250000000 : ℝ)*X 1 0+(-2124955901/10000000000 : ℝ)*X 1 1+(5375569659/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5296428039/10000000000 : ℝ)*X 2 0+(5375569893/10000000000 : ℝ)*X 2 1+(-1062478019/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((279034381/625000000 : ℝ)*X 0 0+(4306108023/10000000000 : ℝ)*X 0 1+(2153054083/5000000000 : ℝ)*X 0 2+(279034381/625000000 : ℝ)*X 1 0+(4306108023/10000000000 : ℝ)*X 1 1+(2153054083/5000000000 : ℝ)*X 1 2+(279034381/625000000 : ℝ)*X 2 0+(4306108023/10000000000 : ℝ)*X 2 1+(2153054083/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1134676473/5000000000 : ℝ)*X 0 0+(264087907/500000000 : ℝ)*X 0 1+(82527471/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1072525999/2000000000 : ℝ)*X 1 0+(-2162007559/10000000000 : ℝ)*X 1 1+(5281758051/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1340657641/2500000000 : ℝ)*X 2 0+(5281758117/10000000000 : ℝ)*X 2 1+(-1081003353/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4250147057/10000000000 : ℝ)*X 0 0+(882657951/2000000000 : ℝ)*X 0 1+(4413288571/10000000000 : ℝ)*X 0 2+(4250147057/10000000000 : ℝ)*X 1 0+(882657951/2000000000 : ℝ)*X 1 1+(4413288571/10000000000 : ℝ)*X 1 2+(4250147057/10000000000 : ℝ)*X 2 0+(882657951/2000000000 : ℝ)*X 2 1+(4413288571/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-554157659/2500000000 : ℝ)*X 0 0+(2608930307/5000000000 : ℝ)*X 0 1+(2692590537/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5289642267/10000000000 : ℝ)*X 1 0+(-424218423/2000000000 : ℝ)*X 1 1+(673147619/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5289642351/10000000000 : ℝ)*X 2 0+(5385181321/10000000000 : ℝ)*X 2 1+(-132568219/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2243121701/5000000000 : ℝ)*X 0 0+(1073780201/2500000000 : ℝ)*X 0 1+(1073780257/2500000000 : ℝ)*X 0 2+(2243121701/5000000000 : ℝ)*X 1 0+(1073780201/2500000000 : ℝ)*X 1 1+(1073780257/2500000000 : ℝ)*X 1 2+(2243121701/5000000000 : ℝ)*X 2 0+(1073780201/2500000000 : ℝ)*X 2 1+(1073780257/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1035257169/5000000000 : ℝ)*X 0 0+(5438225441/10000000000 : ℝ)*X 0 1+(5273697867/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1073663309/2000000000 : ℝ)*X 1 0+(-433026677/2000000000 : ℝ)*X 1 1+(5273697841/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1073663313/2000000000 : ℝ)*X 2 0+(1054739559/2000000000 : ℝ)*X 2 1+(-108256671/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4231494083/10000000000 : ℝ)*X 0 0+(4422493281/10000000000 : ℝ)*X 0 1+(4422493087/10000000000 : ℝ)*X 0 2+(4231494083/10000000000 : ℝ)*X 1 0+(4422493281/10000000000 : ℝ)*X 1 1+(4422493087/10000000000 : ℝ)*X 1 2+(4231494083/10000000000 : ℝ)*X 2 0+(4422493281/10000000000 : ℝ)*X 2 1+(4422493087/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31119/50000 : ℝ) ≤ (-8615735317771721801528246478783/13843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (81626473/100000000000000 : ℝ)*(upper1) + (55268529/10000000000000 : ℝ)*(upper4) + (20867959/25000000000000 : ℝ)*(upper5) + (247688418109981/6250000000000 : ℝ)*(major0) + (247688418109981/6250000000000 : ℝ)*(major1) + (247688418109981/6250000000000 : ℝ)*(major2) + (14186383167/50000000000000 : ℝ)*(sp1) + (3894862227/100000000000000 : ℝ)*(sp3) + (1062596793666329/20000000000000 : ℝ)*(sp4) + (5312984446511249/100000000000000 : ℝ)*(sp5) + (5312902825357303/100000000000000 : ℝ)*(sp6) + (329219731499841/12500000000000 : ℝ)*(sp7) + (14425472969/50000000000000 : ℝ)*(sp8) + (2749848007/2500000000000 : ℝ)*(sp14) + (658440436715239/25000000000000 : ℝ)*(f.failure) + (332063301204849/6250000000000 : ℝ)*(f.sum) + (5414270352571/1107500000000000000000000000 : ℝ)*base65 + (525019555260148337/27687500000000000000000000000000 : ℝ)*base67 + (647309080380960837/27687500000000000000000000000000 : ℝ)*base69 + (487633967537523337/27687500000000000000000000000000 : ℝ)*base71 + (42441857911/69218750000000000000000000 : ℝ)*base73 + (402871882864773337/27687500000000000000000000000000 : ℝ)*base75 + (440719166876335837/27687500000000000000000000000000 : ℝ)*base77 + (584397203709085837/27687500000000000000000000000000 : ℝ)*base79 + (413216220303/553750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (3194989/2500000000000000000000 : ℝ)*base90 + (3194989/2500000000000000000000 : ℝ)*base92 + (3194989/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (29669/50000 : ℝ) ≤ (131439936497832999646881999/221500000000000000000000000 : ℝ) := by norm_num
    linear_combination (22104093/50000000000000 : ℝ)*(lower0) + (22348509/50000000000000 : ℝ)*(upper2) + (59854091/50000000000000 : ℝ)*(lower4) + (402798480361003/10000000000000 : ℝ)*(major0) + (402798480361003/10000000000000 : ℝ)*(major1) + (402798480361003/10000000000000 : ℝ)*(major2) + (5359248134418559/100000000000000 : ℝ)*(sp0) + (5359240828083549/100000000000000 : ℝ)*(sp1) + (2679619190468951/50000000000000 : ℝ)*(sp2) + (669233628005251/25000000000000 : ℝ)*(sp3) + (8566079033/100000000000000 : ℝ)*(sp5) + (275330617/2500000000000 : ℝ)*(sp6) + (1084932713/20000000000000 : ℝ)*(sp7) + (1259744023/100000000000000 : ℝ)*(sp12) + (334617492085571/12500000000000 : ℝ)*(f.failure) + (2679624697081291/50000000000000 : ℝ)*(f.sum) + (607484563213/17720000000000000000000000 : ℝ)*base66 + (684544129742652869/44300000000000000000000000000000 : ℝ)*base68 + (187844549953347131/44300000000000000000000000000000 : ℝ)*base69 + (2946144759914952869/44300000000000000000000000000000 : ℝ)*base72 + (2730673519809/443000000000000000000000000 : ℝ)*base73 + (290610689393547131/44300000000000000000000000000000 : ℝ)*base75 + (106912238962652869/44300000000000000000000000000000 : ℝ)*base78 + (194245565665547131/44300000000000000000000000000000 : ℝ)*base79 + (550816996873/443000000000000000000000000 : ℝ)*base81 + (20108321/1250000000000000000000 : ℝ)*base90 + (20108321/1250000000000000000000 : ℝ)*base92 + (20108321/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (79963/100000 : ℝ) ≤ (442808502876932599475295837/553750000000000000000000000 : ℝ) := by norm_num
    linear_combination (20010749/100000000000000 : ℝ)*(upper0) + (10214909/10000000000000 : ℝ)*(lower1) + (174746941/100000000000000 : ℝ)*(lower3) + (35945981/12500000000000 : ℝ)*(upper4) + (2247699322043031/50000000000000 : ℝ)*(major0) + (2247699322043031/50000000000000 : ℝ)*(major1) + (2247699322043031/50000000000000 : ℝ)*(major2) + (329027471/100000000000000 : ℝ)*(sp0) + (3498019589/1000000000000 : ℝ)*(sp2) + (5874253703/5000000000000 : ℝ)*(sp3) + (2988282731874717/50000000000000 : ℝ)*(sp8) + (747070724097113/12500000000000 : ℝ)*(sp9) + (1494053997704501/25000000000000 : ℝ)*(sp10) + (746864717736389/25000000000000 : ℝ)*(sp11) + (93361761125613/3125000000000 : ℝ)*(f.failure) + (747070724097113/12500000000000 : ℝ)*(f.sum) + (151496031001/34609375000000000000000000 : ℝ)*base65 + (1508789538666004313/221500000000000000000000000000000 : ℝ)*base68 + (8483734121037004313/221500000000000000000000000000000 : ℝ)*base70 + (443324128373495687/221500000000000000000000000000000 : ℝ)*base71 + (9478656314793/1107500000000000000000000000 : ℝ)*base74 + (5044670881009495687/221500000000000000000000000000000 : ℝ)*base75 + (116061613749495687/221500000000000000000000000000000 : ℝ)*base77 + (1469305944308504313/221500000000000000000000000000000 : ℝ)*base80 + (75346506498897/1107500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1831137/312500000000000000000 : ℝ)*base89 + (1831137/312500000000000000000 : ℝ)*base91 + (1831137/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-41619/50000 : ℝ) ≤ (-184366557930983752033707327884673/221500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3882397/12500000000000 : ℝ)*(lower0) + (30174059/100000000000000 : ℝ)*(upper1) + (5727001/100000000000000 : ℝ)*(upper3) + (11004539/100000000000000 : ℝ)*(lower4) + (4530631223350117/100000000000000 : ℝ)*(major0) + (4530631223350117/100000000000000 : ℝ)*(major1) + (4530631223350117/100000000000000 : ℝ)*(major2) + (10724458873/100000000000000 : ℝ)*(sp4) + (20366309131/50000000000000 : ℝ)*(sp6) + (12464917067/12500000000000 : ℝ)*(sp7) + (6078005463491627/100000000000000 : ℝ)*(sp12) + (12156032375901/200000000000 : ℝ)*(sp13) + (3038987727666119/50000000000000 : ℝ)*(sp14) + (188180730928627/6250000000000 : ℝ)*(sp15) + (376373926774321/12500000000000 : ℝ)*(f.failure) + (12156032375901/200000000000 : ℝ)*(f.sum) + (8512438739699/2215000000000000000000000000 : ℝ)*base65 + (1359071477202394891/443000000000000000000000000000000 : ℝ)*base68 + (18206867100231605109/443000000000000000000000000000000 : ℝ)*base69 + (401813072910605109/443000000000000000000000000000000 : ℝ)*base71 + (2022694322121/2215000000000000000000000000 : ℝ)*base74 + (3908489936065394891/443000000000000000000000000000000 : ℝ)*base76 + (2073963191023394891/443000000000000000000000000000000 : ℝ)*base78 + (3267997964893394891/443000000000000000000000000000000 : ℝ)*base80 + (31863999857639/2215000000000000000000000000 : ℝ)*base81 + (1984571/1250000000000000000000 : ℝ)*base90 + (1984571/1250000000000000000000 : ℝ)*base92 + (1984571/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1193_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150469749/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14077/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11419/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31119/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29669/50000 : ℝ) else (79963/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41619/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1193_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1193_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150469749/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7039/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11419/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31119/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29669/50000 : ℝ) else (79963/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41619/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1193_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1193_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150469749/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7039/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11419/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31119/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29669/50000 : ℝ) else (79963/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41619/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1193_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
