-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1587_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:31:34.501982+00:00
-- url     : https://prove2.me/submissions/49c72987-a1c1-412e-9dda-56a373e2da60

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
theorem support_rectangle_w1587_s3_0 (p : ℝ) (hpa : (4669/1024 : ℝ) ≤ p) (hpb : p ≤ (4671/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-352489297/2000000000 : ℝ)*x 0 + (5425013301/10000000000 : ℝ)*x 1 + (5219366019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (352489297/2000000000 : ℝ)^4671 ≤ (5412667383679/50000000000000 : ℝ)^3647 := by
    have hnat : (352489297 : ℕ)^4671*50000000000000^3647 ≤ 5412667383679^3647*2000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      352489297 2000000000 5412667383679 50000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5425013301/10000000000 : ℝ)^4671 ≤ (45690531006739/100000000000000 : ℝ)^3647 := by
    have hnat : (5425013301 : ℕ)^4671*100000000000000^3647 ≤ 45690531006739^3647*10000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425013301 10000000000 45690531006739 100000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219366019/10000000000 : ℝ)^4671 ≤ (21742067103103/50000000000000 : ℝ)^3647 := by
    have hnat : (5219366019 : ℕ)^4671*50000000000000^3647 ≤ 21742067103103^3647*10000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219366019 10000000000 21742067103103 50000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4671/1024 : ℝ)) 4671 3647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-352489297/2000000000 : ℝ), (5425013301/10000000000 : ℝ), (5219366019/10000000000 : ℝ)] ![(5412667383679/50000000000000 : ℝ), (45690531006739/100000000000000 : ℝ), (21742067103103/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-352489297/2000000000 : ℝ)|^4671 ≤ (5412667383679/50000000000000 : ℝ)^3647
        have hw : |(-352489297/2000000000 : ℝ)|=(352489297/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5425013301/10000000000 : ℝ)|^4671 ≤ (45690531006739/100000000000000 : ℝ)^3647
        have hw : |(5425013301/10000000000 : ℝ)|=(5425013301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219366019/10000000000 : ℝ)|^4671 ≤ (21742067103103/50000000000000 : ℝ)^3647
        have hw : |(5219366019/10000000000 : ℝ)|=(5219366019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1587_s3_1 (p : ℝ) (hpa : (4669/1024 : ℝ) ≤ p) (hpb : p ≤ (4671/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347499019/10000000000 : ℝ)*x 0 + (-933826131/5000000000 : ℝ)*x 1 + (2609682391/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347499019/10000000000 : ℝ)^4671 ≤ (44856069737647/100000000000000 : ℝ)^3647 := by
    have hnat : (5347499019 : ℕ)^4671*100000000000000^3647 ≤ 44856069737647^3647*10000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347499019 10000000000 44856069737647 100000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (933826131/5000000000 : ℝ)^4671 ≤ (11659809241267/100000000000000 : ℝ)^3647 := by
    have hnat : (933826131 : ℕ)^4671*100000000000000^3647 ≤ 11659809241267^3647*5000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      933826131 5000000000 11659809241267 100000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609682391/5000000000 : ℝ)^4671 ≤ (10871030251681/25000000000000 : ℝ)^3647 := by
    have hnat : (2609682391 : ℕ)^4671*25000000000000^3647 ≤ 10871030251681^3647*5000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609682391 5000000000 10871030251681 25000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4671/1024 : ℝ)) 4671 3647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347499019/10000000000 : ℝ), (-933826131/5000000000 : ℝ), (2609682391/5000000000 : ℝ)] ![(44856069737647/100000000000000 : ℝ), (11659809241267/100000000000000 : ℝ), (10871030251681/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347499019/10000000000 : ℝ)|^4671 ≤ (44856069737647/100000000000000 : ℝ)^3647
        have hw : |(5347499019/10000000000 : ℝ)|=(5347499019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-933826131/5000000000 : ℝ)|^4671 ≤ (11659809241267/100000000000000 : ℝ)^3647
        have hw : |(-933826131/5000000000 : ℝ)|=(933826131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609682391/5000000000 : ℝ)|^4671 ≤ (10871030251681/25000000000000 : ℝ)^3647
        have hw : |(2609682391/5000000000 : ℝ)|=(2609682391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1587_s3_2 (p : ℝ) (hpa : (4669/1024 : ℝ) ≤ p) (hpb : p ≤ (4671/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069499903/2000000000 : ℝ)*x 0 + (5219364751/10000000000 : ℝ)*x 1 + (-1867651637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069499903/2000000000 : ℝ)^4671 ≤ (5607009383301/12500000000000 : ℝ)^3647 := by
    have hnat : (1069499903 : ℕ)^4671*12500000000000^3647 ≤ 5607009383301^3647*2000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069499903 2000000000 5607009383301 12500000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219364751/10000000000 : ℝ)^4671 ≤ (43484120675937/100000000000000 : ℝ)^3647 := by
    have hnat : (5219364751 : ℕ)^4671*100000000000000^3647 ≤ 43484120675937^3647*10000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219364751 10000000000 43484120675937 100000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1867651637/10000000000 : ℝ)^4671 ≤ (2914951060951/25000000000000 : ℝ)^3647 := by
    have hnat : (1867651637 : ℕ)^4671*25000000000000^3647 ≤ 2914951060951^3647*10000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1867651637 10000000000 2914951060951 25000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4671/1024 : ℝ)) 4671 3647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069499903/2000000000 : ℝ), (5219364751/10000000000 : ℝ), (-1867651637/10000000000 : ℝ)] ![(5607009383301/12500000000000 : ℝ), (43484120675937/100000000000000 : ℝ), (2914951060951/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069499903/2000000000 : ℝ)|^4671 ≤ (5607009383301/12500000000000 : ℝ)^3647
        have hw : |(1069499903/2000000000 : ℝ)|=(1069499903/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219364751/10000000000 : ℝ)|^4671 ≤ (43484120675937/100000000000000 : ℝ)^3647
        have hw : |(5219364751/10000000000 : ℝ)|=(5219364751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1867651637/10000000000 : ℝ)|^4671 ≤ (2914951060951/25000000000000 : ℝ)^3647
        have hw : |(-1867651637/10000000000 : ℝ)|=(1867651637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1587_s3_3 (p : ℝ) (hpa : (4669/1024 : ℝ) ≤ p) (hpb : p ≤ (4671/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (264746939/625000000 : ℝ)*x 0 + (3996100113/10000000000 : ℝ)*x 1 + (4487171913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264746939/625000000 : ℝ)^4671 ≤ (8320447749403/25000000000000 : ℝ)^3647 := by
    have hnat : (264746939 : ℕ)^4671*25000000000000^3647 ≤ 8320447749403^3647*625000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264746939 625000000 8320447749403 25000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3996100113/10000000000 : ℝ)^4671 ≤ (3088761149489/10000000000000 : ℝ)^3647 := by
    have hnat : (3996100113 : ℕ)^4671*10000000000000^3647 ≤ 3088761149489^3647*10000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3996100113 10000000000 3088761149489 10000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4487171913/10000000000 : ℝ)^4671 ≤ (4478824687639/12500000000000 : ℝ)^3647 := by
    have hnat : (4487171913 : ℕ)^4671*12500000000000^3647 ≤ 4478824687639^3647*10000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487171913 10000000000 4478824687639 12500000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4671/1024 : ℝ)) 4671 3647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264746939/625000000 : ℝ), (3996100113/10000000000 : ℝ), (4487171913/10000000000 : ℝ)] ![(8320447749403/25000000000000 : ℝ), (3088761149489/10000000000000 : ℝ), (4478824687639/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264746939/625000000 : ℝ)|^4671 ≤ (8320447749403/25000000000000 : ℝ)^3647
        have hw : |(264746939/625000000 : ℝ)|=(264746939/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3996100113/10000000000 : ℝ)|^4671 ≤ (3088761149489/10000000000000 : ℝ)^3647
        have hw : |(3996100113/10000000000 : ℝ)|=(3996100113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4487171913/10000000000 : ℝ)|^4671 ≤ (4478824687639/12500000000000 : ℝ)^3647
        have hw : |(4487171913/10000000000 : ℝ)|=(4487171913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1587_s3_4 (p : ℝ) (hpa : (4669/1024 : ℝ) ≤ p) (hpb : p ≤ (4671/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-881236431/5000000000 : ℝ)*x 0 + (5220454791/10000000000 : ℝ)*x 1 + (271195849/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (881236431/5000000000 : ℝ)^4671 ≤ (10825542271043/100000000000000 : ℝ)^3647 := by
    have hnat : (881236431 : ℕ)^4671*100000000000000^3647 ≤ 10825542271043^3647*5000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      881236431 5000000000 10825542271043 100000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5220454791/10000000000 : ℝ)^4671 ≤ (10873938088113/25000000000000 : ℝ)^3647 := by
    have hnat : (5220454791 : ℕ)^4671*25000000000000^3647 ≤ 10873938088113^3647*10000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220454791 10000000000 10873938088113 25000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271195849/500000000 : ℝ)^4671 ≤ (45678705359683/100000000000000 : ℝ)^3647 := by
    have hnat : (271195849 : ℕ)^4671*100000000000000^3647 ≤ 45678705359683^3647*500000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271195849 500000000 45678705359683 100000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4671/1024 : ℝ)) 4671 3647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-881236431/5000000000 : ℝ), (5220454791/10000000000 : ℝ), (271195849/500000000 : ℝ)] ![(10825542271043/100000000000000 : ℝ), (10873938088113/25000000000000 : ℝ), (45678705359683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-881236431/5000000000 : ℝ)|^4671 ≤ (10825542271043/100000000000000 : ℝ)^3647
        have hw : |(-881236431/5000000000 : ℝ)|=(881236431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5220454791/10000000000 : ℝ)|^4671 ≤ (10873938088113/25000000000000 : ℝ)^3647
        have hw : |(5220454791/10000000000 : ℝ)|=(5220454791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(271195849/500000000 : ℝ)|^4671 ≤ (45678705359683/100000000000000 : ℝ)^3647
        have hw : |(271195849/500000000 : ℝ)|=(271195849/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1587_s3_5 (p : ℝ) (hpa : (4669/1024 : ℝ) ≤ p) (hpb : p ≤ (4671/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (132324579/250000000 : ℝ)*x 0 + (-83154981/500000000 : ℝ)*x 1 + (5423918213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132324579/250000000 : ℝ)^4671 ≤ (1383475640793/3125000000000 : ℝ)^3647 := by
    have hnat : (132324579 : ℕ)^4671*3125000000000^3647 ≤ 1383475640793^3647*250000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132324579 250000000 1383475640793 3125000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (83154981/500000000 : ℝ)^4671 ≤ (10050060821789/100000000000000 : ℝ)^3647 := by
    have hnat : (83154981 : ℕ)^4671*100000000000000^3647 ≤ 10050060821789^3647*500000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83154981 500000000 10050060821789 100000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5423918213/10000000000 : ℝ)^4671 ≤ (45678718659263/100000000000000 : ℝ)^3647 := by
    have hnat : (5423918213 : ℕ)^4671*100000000000000^3647 ≤ 45678718659263^3647*10000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423918213 10000000000 45678718659263 100000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4671/1024 : ℝ)) 4671 3647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132324579/250000000 : ℝ), (-83154981/500000000 : ℝ), (5423918213/10000000000 : ℝ)] ![(1383475640793/3125000000000 : ℝ), (10050060821789/100000000000000 : ℝ), (45678718659263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132324579/250000000 : ℝ)|^4671 ≤ (1383475640793/3125000000000 : ℝ)^3647
        have hw : |(132324579/250000000 : ℝ)|=(132324579/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-83154981/500000000 : ℝ)|^4671 ≤ (10050060821789/100000000000000 : ℝ)^3647
        have hw : |(-83154981/500000000 : ℝ)|=(83154981/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5423918213/10000000000 : ℝ)|^4671 ≤ (45678718659263/100000000000000 : ℝ)^3647
        have hw : |(5423918213/10000000000 : ℝ)|=(5423918213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1587_s3_6 (p : ℝ) (hpa : (4669/1024 : ℝ) ≤ p) (hpb : p ≤ (4671/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646491839/5000000000 : ℝ)*x 0 + (5423916753/10000000000 : ℝ)*x 1 + (-1663100939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646491839/5000000000 : ℝ)^4671 ≤ (8854245210901/20000000000000 : ℝ)^3647 := by
    have hnat : (2646491839 : ℕ)^4671*20000000000000^3647 ≤ 8854245210901^3647*5000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646491839 5000000000 8854245210901 20000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5423916753/10000000000 : ℝ)^4671 ≤ (45678702911179/100000000000000 : ℝ)^3647 := by
    have hnat : (5423916753 : ℕ)^4671*100000000000000^3647 ≤ 45678702911179^3647*10000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423916753 10000000000 45678702911179 100000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1663100939/10000000000 : ℝ)^4671 ≤ (157032359851/1562500000000 : ℝ)^3647 := by
    have hnat : (1663100939 : ℕ)^4671*1562500000000^3647 ≤ 157032359851^3647*10000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1663100939 10000000000 157032359851 1562500000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4671/1024 : ℝ)) 4671 3647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646491839/5000000000 : ℝ), (5423916753/10000000000 : ℝ), (-1663100939/10000000000 : ℝ)] ![(8854245210901/20000000000000 : ℝ), (45678702911179/100000000000000 : ℝ), (157032359851/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646491839/5000000000 : ℝ)|^4671 ≤ (8854245210901/20000000000000 : ℝ)^3647
        have hw : |(2646491839/5000000000 : ℝ)|=(2646491839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5423916753/10000000000 : ℝ)|^4671 ≤ (45678702911179/100000000000000 : ℝ)^3647
        have hw : |(5423916753/10000000000 : ℝ)|=(5423916753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1663100939/10000000000 : ℝ)|^4671 ≤ (157032359851/1562500000000 : ℝ)^3647
        have hw : |(-1663100939/10000000000 : ℝ)|=(1663100939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1587_s3_7 (p : ℝ) (hpa : (4669/1024 : ℝ) ≤ p) (hpb : p ≤ (4671/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (16546939/39062500 : ℝ)*x 0 + (4484573407/10000000000 : ℝ)*x 1 + (999679419/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16546939/39062500 : ℝ)^4671 ≤ (33282448720337/100000000000000 : ℝ)^3647 := by
    have hnat : (16546939 : ℕ)^4671*100000000000000^3647 ≤ 33282448720337^3647*39062500^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16546939 39062500 33282448720337 100000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4484573407/10000000000 : ℝ)^4671 ≤ (35804024301143/100000000000000 : ℝ)^3647 := by
    have hnat : (4484573407 : ℕ)^4671*100000000000000^3647 ≤ 35804024301143^3647*10000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484573407 10000000000 35804024301143 100000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (999679419/2500000000 : ℝ)^4671 ≤ (30913526968051/100000000000000 : ℝ)^3647 := by
    have hnat : (999679419 : ℕ)^4671*100000000000000^3647 ≤ 30913526968051^3647*2500000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      999679419 2500000000 30913526968051 100000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4671/1024 : ℝ)) 4671 3647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16546939/39062500 : ℝ), (4484573407/10000000000 : ℝ), (999679419/2500000000 : ℝ)] ![(33282448720337/100000000000000 : ℝ), (35804024301143/100000000000000 : ℝ), (30913526968051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16546939/39062500 : ℝ)|^4671 ≤ (33282448720337/100000000000000 : ℝ)^3647
        have hw : |(16546939/39062500 : ℝ)|=(16546939/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4484573407/10000000000 : ℝ)|^4671 ≤ (35804024301143/100000000000000 : ℝ)^3647
        have hw : |(4484573407/10000000000 : ℝ)|=(4484573407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(999679419/2500000000 : ℝ)|^4671 ≤ (30913526968051/100000000000000 : ℝ)^3647
        have hw : |(999679419/2500000000 : ℝ)|=(999679419/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1587_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4669/1024 : ℝ) ≤ p) (hpb : p ≤ (4671/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169396193/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15769/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10911/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2787/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1939/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15769/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10911/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15769/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10911/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15769/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10911/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15769/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10911/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15769/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10911/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15769/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10911/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10911/100000 : ℝ) ^ (4669/1024 : ℝ) ≤ (820551393900649/20000000000000000000 : ℝ) := by
    have hpowers : (10911/100000 : ℝ)^4669 ≤ (820551393900649/20000000000000000000 : ℝ)^1024 := by
      have hnat : (10911 : ℕ)^4669*20000000000000000000^1024 ≤ 820551393900649^1024*100000^4669 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10911 100000 820551393900649 20000000000000000000 4669 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10911/100000 : ℝ)) (X := (820551393900649/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4669 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15769/100000 : ℝ) ^ (4669/1024 : ℝ) ≤ (1099769411741829/5000000000000000000 : ℝ) := by
    have hpowers : (15769/100000 : ℝ)^4669 ≤ (1099769411741829/5000000000000000000 : ℝ)^1024 := by
      have hnat : (15769 : ℕ)^4669*5000000000000000000^1024 ≤ 1099769411741829^1024*100000^4669 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15769 100000 1099769411741829 5000000000000000000 4669 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15769/100000 : ℝ)) (X := (1099769411741829/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4669 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000820551393900649/10000000000000000000 : ℝ) ≤ (1250022494584389/1250000000000000 : ℝ) ^ (4669/1024 : ℝ) := by
    have hpowers : (10000820551393900649/10000000000000000000 : ℝ)^1024 ≤ (1250022494584389/1250000000000000 : ℝ)^4669 := by
      have hnat : (10000820551393900649 : ℕ)^1024*1250000000000000^4669 ≤ 1250022494584389^4669*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000820551393900649 10000000000000000000 1250022494584389 1250000000000000 1024 4669 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250022494584389/1250000000000000 : ℝ)) (X := (10000820551393900649/10000000000000000000 : ℝ)) (by norm_num) 4669 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4001043925808173593/4000000000000000000 : ℝ) ≤ (5000286161690321/5000000000000000 : ℝ) ^ (4669/1024 : ℝ) := by
    have hpowers : (4001043925808173593/4000000000000000000 : ℝ)^1024 ≤ (5000286161690321/5000000000000000 : ℝ)^4669 := by
      have hnat : (4001043925808173593 : ℕ)^1024*5000000000000000^4669 ≤ 5000286161690321^4669*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4001043925808173593 4000000000000000000 5000286161690321 5000000000000000 1024 4669 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000286161690321/5000000000000000 : ℝ)) (X := (4001043925808173593/4000000000000000000 : ℝ)) (by norm_num) 4669 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501099769411741829/2500000000000000000 : ℝ) ≤ (2500241172521543/2500000000000000 : ℝ) ^ (4669/1024 : ℝ) := by
    have hpowers : (2501099769411741829/2500000000000000000 : ℝ)^1024 ≤ (2500241172521543/2500000000000000 : ℝ)^4669 := by
      have hnat : (2501099769411741829 : ℕ)^1024*2500000000000000^4669 ≤ 2500241172521543^4669*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501099769411741829 2500000000000000000 2500241172521543 2500000000000000 1024 4669 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500241172521543/2500000000000000 : ℝ)) (X := (2501099769411741829/2500000000000000000 : ℝ)) (by norm_num) 4669 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(820551393900649/20000000000000000000 : ℝ) ≤ ((12143078000819904609/12145000000000000000 : ℝ)+2*(39236670553/48580000000000 : ℝ)*(10911/100000 : ℝ))^(4669/1024 : ℝ) := by
    rw [show (12143078000819904609/12145000000000000000 : ℝ)+2*(39236670553/48580000000000 : ℝ)*(10911/100000 : ℝ)=(1250022494584389/1250000000000000 : ℝ) by norm_num, show 1+2*(820551393900649/20000000000000000000 : ℝ)=(10000820551393900649/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1099769411741829/5000000000000000000 : ℝ)+(820551393900649/20000000000000000000 : ℝ) ≤ ((12143078000819904609/12145000000000000000 : ℝ)+(39236670553/48580000000000 : ℝ)*((15769/100000 : ℝ)+(10911/100000 : ℝ)))^(4669/1024 : ℝ) := by
    rw [show (12143078000819904609/12145000000000000000 : ℝ)+(39236670553/48580000000000 : ℝ)*((15769/100000 : ℝ)+(10911/100000 : ℝ))=(5000286161690321/5000000000000000 : ℝ) by norm_num, show 1+(1099769411741829/5000000000000000000 : ℝ)+(820551393900649/20000000000000000000 : ℝ)=(4001043925808173593/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1099769411741829/5000000000000000000 : ℝ) ≤ ((12143078000819904609/12145000000000000000 : ℝ)+2*(39236670553/48580000000000 : ℝ)*(15769/100000 : ℝ))^(4669/1024 : ℝ) := by
    rw [show (12143078000819904609/12145000000000000000 : ℝ)+2*(39236670553/48580000000000 : ℝ)*(15769/100000 : ℝ)=(2500241172521543/2500000000000000 : ℝ) by norm_num, show 1+2*(1099769411741829/5000000000000000000 : ℝ)=(2501099769411741829/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12143078000819904609/12145000000000000000 : ℝ)*(X 1 0+X 2 0)+(39236670553/48580000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4669/1024 : ℝ)) (lo := (10911/100000 : ℝ)) (hi := (15769/100000 : ℝ)) (c := (12143078000819904609/12145000000000000000 : ℝ)) (alpha := (39236670553/48580000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12143078000819904609/12145000000000000000 : ℝ)*(X 0 1+X 2 1)+(39236670553/48580000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4669/1024 : ℝ)) (lo := (10911/100000 : ℝ)) (hi := (15769/100000 : ℝ)) (c := (12143078000819904609/12145000000000000000 : ℝ)) (alpha := (39236670553/48580000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12143078000819904609/12145000000000000000 : ℝ)*(X 0 2+X 1 2)+(39236670553/48580000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4669/1024 : ℝ)) (lo := (10911/100000 : ℝ)) (hi := (15769/100000 : ℝ)) (c := (12143078000819904609/12145000000000000000 : ℝ)) (alpha := (39236670553/48580000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-352489297/2000000000 : ℝ)*X 0 0+(5425013301/10000000000 : ℝ)*X 0 1+(5219366019/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1587_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347499019/10000000000 : ℝ)*X 1 0+(-933826131/5000000000 : ℝ)*X 1 1+(2609682391/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1587_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069499903/2000000000 : ℝ)*X 2 0+(5219364751/10000000000 : ℝ)*X 2 1+(-1867651637/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1587_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((264746939/625000000 : ℝ)*X 0 0+(3996100113/10000000000 : ℝ)*X 0 1+(4487171913/10000000000 : ℝ)*X 0 2+(264746939/625000000 : ℝ)*X 1 0+(3996100113/10000000000 : ℝ)*X 1 1+(4487171913/10000000000 : ℝ)*X 1 2+(264746939/625000000 : ℝ)*X 2 0+(3996100113/10000000000 : ℝ)*X 2 1+(4487171913/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1587_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-881236431/5000000000 : ℝ)*X 0 0+(5220454791/10000000000 : ℝ)*X 0 1+(271195849/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1587_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((132324579/250000000 : ℝ)*X 1 0+(-83154981/500000000 : ℝ)*X 1 1+(5423918213/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1587_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2646491839/5000000000 : ℝ)*X 2 0+(5423916753/10000000000 : ℝ)*X 2 1+(-1663100939/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1587_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((16546939/39062500 : ℝ)*X 0 0+(4484573407/10000000000 : ℝ)*X 0 1+(999679419/2500000000 : ℝ)*X 0 2+(16546939/39062500 : ℝ)*X 1 0+(4484573407/10000000000 : ℝ)*X 1 1+(999679419/2500000000 : ℝ)*X 1 2+(16546939/39062500 : ℝ)*X 2 0+(4484573407/10000000000 : ℝ)*X 2 1+(999679419/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1587_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (320408852612550333122696559/30362500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2383512407/100000000000000 : ℝ)*(base19) + (1413752007/50000000000000 : ℝ)*(base23) + (5490983/100000000000000 : ℝ)*(lower2) + (339353747/50000000000000 : ℝ)*(upper5) + (172477656300483/5000000000000 : ℝ)*(major0) + (172477656300483/5000000000000 : ℝ)*(major1) + (172477656300483/5000000000000 : ℝ)*(major2) + (243134877726707/5000000000000 : ℝ)*(sp0) + (2431360735080793/50000000000000 : ℝ)*(sp1) + (4862721342494889/100000000000000 : ℝ)*(sp2) + (254546864324713/12500000000000 : ℝ)*(sp3) + (26615464763/100000000000000 : ℝ)*(sp4) + (316324911/100000000000000 : ℝ)*(sp5) + (1363132659/20000000000000 : ℝ)*(sp7) + (2036381730260999/100000000000000 : ℝ)*(f.failure) + (607840521249863/12500000000000 : ℝ)*(f.sum) + (284928916971/48580000000000000000000000 : ℝ)*base66 + (193243390615126147/60725000000000000000000000000000 : ℝ)*base67 + (268403191790676147/60725000000000000000000000000000 : ℝ)*base69 + (15674582400373853/60725000000000000000000000000000 : ℝ)*base72 + (980844411341/485800000000000000000000000 : ℝ)*base74 + (551226659733198853/60725000000000000000000000000000 : ℝ)*base76 + (476228526582401147/60725000000000000000000000000000 : ℝ)*base77 + (11637264479776147/60725000000000000000000000000000 : ℝ)*base79 + (10032112167111/2429000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (126976807/10000000000000000000000 : ℝ)*base89 + (126976807/10000000000000000000000 : ℝ)*base91 + (126976807/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (528496873249816932903533547/43375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (99087551/12500000000000 : ℝ)*(base23) + (66803967/50000000000000 : ℝ)*(lower2) + (216838039/50000000000000 : ℝ)*(upper3) + (18472247/5000000000000 : ℝ)*(lower4) + (1743286687458491/50000000000000 : ℝ)*(major0) + (1743286687458491/50000000000000 : ℝ)*(major1) + (1743286687458491/50000000000000 : ℝ)*(major2) + (4572258343/100000000000000 : ℝ)*(sp0) + (12997012769/100000000000000 : ℝ)*(sp1) + (4002873111/100000000000000 : ℝ)*(sp3) + (614363225268759/12500000000000 : ℝ)*(sp4) + (2457448688697823/50000000000000 : ℝ)*(sp5) + (4914909581708007/100000000000000 : ℝ)*(sp6) + (128639497900431/6250000000000 : ℝ)*(sp7) + (2058235969280007/100000000000000 : ℝ)*(f.failure) + (982982074881683/20000000000000 : ℝ)*(f.sum) + (596731708271/69400000000000000000000000 : ℝ)*base65 + (1062842400632190717/86750000000000000000000000000000 : ℝ)*base67 + (24540886690717/86750000000000000000000000000000 : ℝ)*base69 + (883980965311440717/86750000000000000000000000000000 : ℝ)*base71 + (432754350279/347000000000000000000000000 : ℝ)*base73 + (434057963633440717/86750000000000000000000000000000 : ℝ)*base75 + (1116504383580190717/86750000000000000000000000000000 : ℝ)*base77 + (1612410063539190717/86750000000000000000000000000000 : ℝ)*base79 + (147144270531/86750000000000000000000000 : ℝ)*base82 + (63186649/10000000000000000000000 : ℝ)*base90 + (63186649/10000000000000000000000 : ℝ)*base92 + (63186649/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1587_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4669/1024 : ℝ) ≤ p) (hpb : p ≤ (4671/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169396193/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15769/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10911/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2787/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1939/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1587_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1587_s4_0 (p : ℝ) (hpa : (4669/1024 : ℝ) ≤ p) (hpb : p ≤ (4671/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-14101049/80000000 : ℝ)*x 0 + (5423768333/10000000000 : ℝ)*x 1 + (326280523/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (14101049/80000000 : ℝ)^4671 ≤ (10826787319327/100000000000000 : ℝ)^3647 := by
    have hnat : (14101049 : ℕ)^4671*100000000000000^3647 ≤ 10826787319327^3647*80000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14101049 80000000 10826787319327 100000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5423768333/10000000000 : ℝ)^4671 ≤ (11419275501499/25000000000000 : ℝ)^3647 := by
    have hnat : (5423768333 : ℕ)^4671*25000000000000^3647 ≤ 11419275501499^3647*10000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423768333 10000000000 11419275501499 25000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (326280523/625000000 : ℝ)^4671 ≤ (10874027664781/25000000000000 : ℝ)^3647 := by
    have hnat : (326280523 : ℕ)^4671*25000000000000^3647 ≤ 10874027664781^3647*625000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326280523 625000000 10874027664781 25000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4671/1024 : ℝ)) 4671 3647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-14101049/80000000 : ℝ), (5423768333/10000000000 : ℝ), (326280523/625000000 : ℝ)] ![(10826787319327/100000000000000 : ℝ), (11419275501499/25000000000000 : ℝ), (10874027664781/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-14101049/80000000 : ℝ)|^4671 ≤ (10826787319327/100000000000000 : ℝ)^3647
        have hw : |(-14101049/80000000 : ℝ)|=(14101049/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5423768333/10000000000 : ℝ)|^4671 ≤ (11419275501499/25000000000000 : ℝ)^3647
        have hw : |(5423768333/10000000000 : ℝ)|=(5423768333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(326280523/625000000 : ℝ)|^4671 ≤ (10874027664781/25000000000000 : ℝ)^3647
        have hw : |(326280523/625000000 : ℝ)|=(326280523/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1587_s4_1 (p : ℝ) (hpa : (4669/1024 : ℝ) ≤ p) (hpb : p ≤ (4671/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673583941/5000000000 : ℝ)*x 0 + (-466649421/2500000000 : ℝ)*x 1 + (2610244163/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673583941/5000000000 : ℝ)^4671 ≤ (44852512207877/100000000000000 : ℝ)^3647 := by
    have hnat : (2673583941 : ℕ)^4671*100000000000000^3647 ≤ 44852512207877^3647*5000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673583941 5000000000 44852512207877 100000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (466649421/2500000000 : ℝ)^4671 ≤ (11651377567301/100000000000000 : ℝ)^3647 := by
    have hnat : (466649421 : ℕ)^4671*100000000000000^3647 ≤ 11651377567301^3647*2500000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      466649421 2500000000 11651377567301 100000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2610244163/5000000000 : ℝ)^4671 ≤ (21748055105467/50000000000000 : ℝ)^3647 := by
    have hnat : (2610244163 : ℕ)^4671*50000000000000^3647 ≤ 21748055105467^3647*5000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610244163 5000000000 21748055105467 50000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4671/1024 : ℝ)) 4671 3647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673583941/5000000000 : ℝ), (-466649421/2500000000 : ℝ), (2610244163/5000000000 : ℝ)] ![(44852512207877/100000000000000 : ℝ), (11651377567301/100000000000000 : ℝ), (21748055105467/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673583941/5000000000 : ℝ)|^4671 ≤ (44852512207877/100000000000000 : ℝ)^3647
        have hw : |(2673583941/5000000000 : ℝ)|=(2673583941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-466649421/2500000000 : ℝ)|^4671 ≤ (11651377567301/100000000000000 : ℝ)^3647
        have hw : |(-466649421/2500000000 : ℝ)|=(466649421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2610244163/5000000000 : ℝ)|^4671 ≤ (21748055105467/50000000000000 : ℝ)^3647
        have hw : |(2610244163/5000000000 : ℝ)|=(2610244163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1587_s4_2 (p : ℝ) (hpa : (4669/1024 : ℝ) ≤ p) (hpb : p ≤ (4671/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673583937/5000000000 : ℝ)*x 0 + (5220488337/10000000000 : ℝ)*x 1 + (-1866597679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673583937/5000000000 : ℝ)^4671 ≤ (44852512121931/100000000000000 : ℝ)^3647 := by
    have hnat : (2673583937 : ℕ)^4671*100000000000000^3647 ≤ 44852512121931^3647*5000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673583937 5000000000 44852512121931 100000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5220488337/10000000000 : ℝ)^4671 ≤ (43496110328317/100000000000000 : ℝ)^3647 := by
    have hnat : (5220488337 : ℕ)^4671*100000000000000^3647 ≤ 43496110328317^3647*10000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220488337 10000000000 43496110328317 100000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1866597679/10000000000 : ℝ)^4671 ≤ (364105547729/3125000000000 : ℝ)^3647 := by
    have hnat : (1866597679 : ℕ)^4671*3125000000000^3647 ≤ 364105547729^3647*10000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1866597679 10000000000 364105547729 3125000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4671/1024 : ℝ)) 4671 3647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673583937/5000000000 : ℝ), (5220488337/10000000000 : ℝ), (-1866597679/10000000000 : ℝ)] ![(44852512121931/100000000000000 : ℝ), (43496110328317/100000000000000 : ℝ), (364105547729/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673583937/5000000000 : ℝ)|^4671 ≤ (44852512121931/100000000000000 : ℝ)^3647
        have hw : |(2673583937/5000000000 : ℝ)|=(2673583937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5220488337/10000000000 : ℝ)|^4671 ≤ (43496110328317/100000000000000 : ℝ)^3647
        have hw : |(5220488337/10000000000 : ℝ)|=(5220488337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1866597679/10000000000 : ℝ)|^4671 ≤ (364105547729/3125000000000 : ℝ)^3647
        have hw : |(-1866597679/10000000000 : ℝ)|=(1866597679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1587_s4_3 (p : ℝ) (hpa : (4669/1024 : ℝ) ≤ p) (hpb : p ≤ (4671/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2118033881/5000000000 : ℝ)*x 0 + (1999457377/5000000000 : ℝ)*x 1 + (560541501/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2118033881/5000000000 : ℝ)^4671 ≤ (33282965743117/100000000000000 : ℝ)^3647 := by
    have hnat : (2118033881 : ℕ)^4671*100000000000000^3647 ≤ 33282965743117^3647*5000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118033881 5000000000 33282965743117 100000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1999457377/5000000000 : ℝ)^4671 ≤ (15457739176767/50000000000000 : ℝ)^3647 := by
    have hnat : (1999457377 : ℕ)^4671*50000000000000^3647 ≤ 15457739176767^3647*5000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1999457377 5000000000 15457739176767 50000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (560541501/1250000000 : ℝ)^4671 ≤ (35801555892863/100000000000000 : ℝ)^3647 := by
    have hnat : (560541501 : ℕ)^4671*100000000000000^3647 ≤ 35801555892863^3647*1250000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560541501 1250000000 35801555892863 100000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4671/1024 : ℝ)) 4671 3647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2118033881/5000000000 : ℝ), (1999457377/5000000000 : ℝ), (560541501/1250000000 : ℝ)] ![(33282965743117/100000000000000 : ℝ), (15457739176767/50000000000000 : ℝ), (35801555892863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2118033881/5000000000 : ℝ)|^4671 ≤ (33282965743117/100000000000000 : ℝ)^3647
        have hw : |(2118033881/5000000000 : ℝ)|=(2118033881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1999457377/5000000000 : ℝ)|^4671 ≤ (15457739176767/50000000000000 : ℝ)^3647
        have hw : |(1999457377/5000000000 : ℝ)|=(1999457377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(560541501/1250000000 : ℝ)|^4671 ≤ (35801555892863/100000000000000 : ℝ)^3647
        have hw : |(560541501/1250000000 : ℝ)|=(560541501/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1587_s4_4 (p : ℝ) (hpa : (4669/1024 : ℝ) ≤ p) (hpb : p ≤ (4671/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1762657423/10000000000 : ℝ)*x 0 + (5221552201/10000000000 : ℝ)*x 1 + (5422696609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1762657423/10000000000 : ℝ)^4671 ≤ (2165398841523/20000000000000 : ℝ)^3647 := by
    have hnat : (1762657423 : ℕ)^4671*20000000000000^3647 ≤ 2165398841523^3647*10000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1762657423 10000000000 2165398841523 20000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5221552201/10000000000 : ℝ)^4671 ≤ (10876865840543/25000000000000 : ℝ)^3647 := by
    have hnat : (5221552201 : ℕ)^4671*25000000000000^3647 ≤ 10876865840543^3647*10000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5221552201 10000000000 10876865840543 25000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5422696609/10000000000 : ℝ)^4671 ≤ (45665542416197/100000000000000 : ℝ)^3647 := by
    have hnat : (5422696609 : ℕ)^4671*100000000000000^3647 ≤ 45665542416197^3647*10000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422696609 10000000000 45665542416197 100000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4671/1024 : ℝ)) 4671 3647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1762657423/10000000000 : ℝ), (5221552201/10000000000 : ℝ), (5422696609/10000000000 : ℝ)] ![(2165398841523/20000000000000 : ℝ), (10876865840543/25000000000000 : ℝ), (45665542416197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1762657423/10000000000 : ℝ)|^4671 ≤ (2165398841523/20000000000000 : ℝ)^3647
        have hw : |(-1762657423/10000000000 : ℝ)|=(1762657423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5221552201/10000000000 : ℝ)|^4671 ≤ (10876865840543/25000000000000 : ℝ)^3647
        have hw : |(5221552201/10000000000 : ℝ)|=(5221552201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5422696609/10000000000 : ℝ)|^4671 ≤ (45665542416197/100000000000000 : ℝ)^3647
        have hw : |(5422696609/10000000000 : ℝ)|=(5422696609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1587_s4_5 (p : ℝ) (hpa : (4669/1024 : ℝ) ≤ p) (hpb : p ≤ (4671/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323320293/2500000000 : ℝ)*x 0 + (-208048677/1250000000 : ℝ)*x 1 + (5422696609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323320293/2500000000 : ℝ)^4671 ≤ (5534301626927/12500000000000 : ℝ)^3647 := by
    have hnat : (1323320293 : ℕ)^4671*12500000000000^3647 ≤ 5534301626927^3647*2500000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323320293 2500000000 5534301626927 12500000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (208048677/1250000000 : ℝ)^4671 ≤ (5030022275911/50000000000000 : ℝ)^3647 := by
    have hnat : (208048677 : ℕ)^4671*50000000000000^3647 ≤ 5030022275911^3647*1250000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208048677 1250000000 5030022275911 50000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5422696609/10000000000 : ℝ)^4671 ≤ (45665542416197/100000000000000 : ℝ)^3647 := by
    have hnat : (5422696609 : ℕ)^4671*100000000000000^3647 ≤ 45665542416197^3647*10000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422696609 10000000000 45665542416197 100000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4671/1024 : ℝ)) 4671 3647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323320293/2500000000 : ℝ), (-208048677/1250000000 : ℝ), (5422696609/10000000000 : ℝ)] ![(5534301626927/12500000000000 : ℝ), (5030022275911/50000000000000 : ℝ), (45665542416197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323320293/2500000000 : ℝ)|^4671 ≤ (5534301626927/12500000000000 : ℝ)^3647
        have hw : |(1323320293/2500000000 : ℝ)|=(1323320293/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-208048677/1250000000 : ℝ)|^4671 ≤ (5030022275911/50000000000000 : ℝ)^3647
        have hw : |(-208048677/1250000000 : ℝ)|=(208048677/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5422696609/10000000000 : ℝ)|^4671 ≤ (45665542416197/100000000000000 : ℝ)^3647
        have hw : |(5422696609/10000000000 : ℝ)|=(5422696609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1587_s4_6 (p : ℝ) (hpa : (4669/1024 : ℝ) ≤ p) (hpb : p ≤ (4671/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293281171/10000000000 : ℝ)*x 0 + (5422696609/10000000000 : ℝ)*x 1 + (-1664389417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293281171/10000000000 : ℝ)^4671 ≤ (44274413004703/100000000000000 : ℝ)^3647 := by
    have hnat : (5293281171 : ℕ)^4671*100000000000000^3647 ≤ 44274413004703^3647*10000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293281171 10000000000 44274413004703 100000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5422696609/10000000000 : ℝ)^4671 ≤ (45665542416197/100000000000000 : ℝ)^3647 := by
    have hnat : (5422696609 : ℕ)^4671*100000000000000^3647 ≤ 45665542416197^3647*10000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422696609 10000000000 45665542416197 100000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1664389417/10000000000 : ℝ)^4671 ≤ (10060044559563/100000000000000 : ℝ)^3647 := by
    have hnat : (1664389417 : ℕ)^4671*100000000000000^3647 ≤ 10060044559563^3647*10000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1664389417 10000000000 10060044559563 100000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4671/1024 : ℝ)) 4671 3647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293281171/10000000000 : ℝ), (5422696609/10000000000 : ℝ), (-1664389417/10000000000 : ℝ)] ![(44274413004703/100000000000000 : ℝ), (45665542416197/100000000000000 : ℝ), (10060044559563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293281171/10000000000 : ℝ)|^4671 ≤ (44274413004703/100000000000000 : ℝ)^3647
        have hw : |(5293281171/10000000000 : ℝ)|=(5293281171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5422696609/10000000000 : ℝ)|^4671 ≤ (45665542416197/100000000000000 : ℝ)^3647
        have hw : |(5422696609/10000000000 : ℝ)|=(5422696609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1664389417/10000000000 : ℝ)|^4671 ≤ (10060044559563/100000000000000 : ℝ)^3647
        have hw : |(-1664389417/10000000000 : ℝ)|=(1664389417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1587_s4_7 (p : ℝ) (hpa : (4669/1024 : ℝ) ≤ p) (hpb : p ≤ (4671/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2118065269/5000000000 : ℝ)*x 0 + (4481791553/10000000000 : ℝ)*x 1 + (200073701/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2118065269/5000000000 : ℝ)^4671 ≤ (8320899366921/25000000000000 : ℝ)^3647 := by
    have hnat : (2118065269 : ℕ)^4671*25000000000000^3647 ≤ 8320899366921^3647*5000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118065269 5000000000 8320899366921 25000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4481791553/10000000000 : ℝ)^4671 ≤ (17887790456921/50000000000000 : ℝ)^3647 := by
    have hnat : (4481791553 : ℕ)^4671*50000000000000^3647 ≤ 17887790456921^3647*10000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4481791553 10000000000 17887790456921 50000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (200073701/500000000 : ℝ)^4671 ≤ (15470410803531/50000000000000 : ℝ)^3647 := by
    have hnat : (200073701 : ℕ)^4671*50000000000000^3647 ≤ 15470410803531^3647*500000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200073701 500000000 15470410803531 50000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4671/1024 : ℝ)) 4671 3647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2118065269/5000000000 : ℝ), (4481791553/10000000000 : ℝ), (200073701/500000000 : ℝ)] ![(8320899366921/25000000000000 : ℝ), (17887790456921/50000000000000 : ℝ), (15470410803531/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2118065269/5000000000 : ℝ)|^4671 ≤ (8320899366921/25000000000000 : ℝ)^3647
        have hw : |(2118065269/5000000000 : ℝ)|=(2118065269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4481791553/10000000000 : ℝ)|^4671 ≤ (17887790456921/50000000000000 : ℝ)^3647
        have hw : |(4481791553/10000000000 : ℝ)|=(4481791553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(200073701/500000000 : ℝ)|^4671 ≤ (15470410803531/50000000000000 : ℝ)^3647
        have hw : |(200073701/500000000 : ℝ)|=(200073701/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1587_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4669/1024 : ℝ) ≤ p) (hpb : p ≤ (4671/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169396193/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1939/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2787/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11173/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7743/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1939/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2787/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1939/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2787/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1939/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2787/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1939/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2787/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1939/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2787/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1939/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2787/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2787/25000 : ℝ) ^ (4669/1024 : ℝ) ≤ (565636671970147/12500000000000000000 : ℝ) := by
    have hpowers : (2787/25000 : ℝ)^4669 ≤ (565636671970147/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2787 : ℕ)^4669*12500000000000000000^1024 ≤ 565636671970147^1024*25000^4669 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2787 25000 565636671970147 12500000000000000000 4669 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2787/25000 : ℝ)) (X := (565636671970147/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4669 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1939/12500 : ℝ) ^ (4669/1024 : ℝ) ≤ (408152917941343/2000000000000000000 : ℝ) := by
    have hpowers : (1939/12500 : ℝ)^4669 ≤ (408152917941343/2000000000000000000 : ℝ)^1024 := by
      have hnat : (1939 : ℕ)^4669*2000000000000000000^1024 ≤ 408152917941343^1024*12500^4669 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1939 12500 408152917941343 2000000000000000000 4669 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1939/12500 : ℝ)) (X := (408152917941343/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4669 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250565636671970147/6250000000000000000 : ℝ) ≤ (10000198480699641/10000000000000000 : ℝ) ^ (4669/1024 : ℝ) := by
    have hpowers : (6250565636671970147/6250000000000000000 : ℝ)^1024 ≤ (10000198480699641/10000000000000000 : ℝ)^4669 := by
      have hnat : (6250565636671970147 : ℕ)^1024*10000000000000000^4669 ≤ 10000198480699641^4669*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250565636671970147 6250000000000000000 10000198480699641 10000000000000000 1024 4669 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000198480699641/10000000000000000 : ℝ)) (X := (6250565636671970147/6250000000000000000 : ℝ)) (by norm_num) 4669 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50012466369636414163/50000000000000000000 : ℝ) ≤ (10000546768914711/10000000000000000 : ℝ) ^ (4669/1024 : ℝ) := by
    have hpowers : (50012466369636414163/50000000000000000000 : ℝ)^1024 ≤ (10000546768914711/10000000000000000 : ℝ)^4669 := by
      have hnat : (50012466369636414163 : ℕ)^1024*10000000000000000^4669 ≤ 10000546768914711^4669*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50012466369636414163 50000000000000000000 10000546768914711 10000000000000000 1024 4669 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000546768914711/10000000000000000 : ℝ)) (X := (50012466369636414163/50000000000000000000 : ℝ)) (by norm_num) 4669 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1000408152917941343/1000000000000000000 : ℝ) ≤ (10000895057129781/10000000000000000 : ℝ) ^ (4669/1024 : ℝ) := by
    have hpowers : (1000408152917941343/1000000000000000000 : ℝ)^1024 ≤ (10000895057129781/10000000000000000 : ℝ)^4669 := by
      have hnat : (1000408152917941343 : ℕ)^1024*10000000000000000^4669 ≤ 10000895057129781^4669*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000408152917941343 1000000000000000000 10000895057129781 10000000000000000 1024 4669 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000895057129781/10000000000000000 : ℝ)) (X := (1000408152917941343/1000000000000000000 : ℝ)) (by norm_num) 4669 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(565636671970147/12500000000000000000 : ℝ) ≤ ((10908275183932508151/10910000000000000000 : ℝ)+2*(34828821507/43640000000000 : ℝ)*(2787/25000 : ℝ))^(4669/1024 : ℝ) := by
    rw [show (10908275183932508151/10910000000000000000 : ℝ)+2*(34828821507/43640000000000 : ℝ)*(2787/25000 : ℝ)=(10000198480699641/10000000000000000 : ℝ) by norm_num, show 1+2*(565636671970147/12500000000000000000 : ℝ)=(6250565636671970147/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(408152917941343/2000000000000000000 : ℝ)+(565636671970147/12500000000000000000 : ℝ) ≤ ((10908275183932508151/10910000000000000000 : ℝ)+(34828821507/43640000000000 : ℝ)*((1939/12500 : ℝ)+(2787/25000 : ℝ)))^(4669/1024 : ℝ) := by
    rw [show (10908275183932508151/10910000000000000000 : ℝ)+(34828821507/43640000000000 : ℝ)*((1939/12500 : ℝ)+(2787/25000 : ℝ))=(10000546768914711/10000000000000000 : ℝ) by norm_num, show 1+(408152917941343/2000000000000000000 : ℝ)+(565636671970147/12500000000000000000 : ℝ)=(50012466369636414163/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(408152917941343/2000000000000000000 : ℝ) ≤ ((10908275183932508151/10910000000000000000 : ℝ)+2*(34828821507/43640000000000 : ℝ)*(1939/12500 : ℝ))^(4669/1024 : ℝ) := by
    rw [show (10908275183932508151/10910000000000000000 : ℝ)+2*(34828821507/43640000000000 : ℝ)*(1939/12500 : ℝ)=(10000895057129781/10000000000000000 : ℝ) by norm_num, show 1+2*(408152917941343/2000000000000000000 : ℝ)=(1000408152917941343/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10908275183932508151/10910000000000000000 : ℝ)*(X 1 0+X 2 0)+(34828821507/43640000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4669/1024 : ℝ)) (lo := (2787/25000 : ℝ)) (hi := (1939/12500 : ℝ)) (c := (10908275183932508151/10910000000000000000 : ℝ)) (alpha := (34828821507/43640000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10908275183932508151/10910000000000000000 : ℝ)*(X 0 1+X 2 1)+(34828821507/43640000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4669/1024 : ℝ)) (lo := (2787/25000 : ℝ)) (hi := (1939/12500 : ℝ)) (c := (10908275183932508151/10910000000000000000 : ℝ)) (alpha := (34828821507/43640000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10908275183932508151/10910000000000000000 : ℝ)*(X 0 2+X 1 2)+(34828821507/43640000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4669/1024 : ℝ)) (lo := (2787/25000 : ℝ)) (hi := (1939/12500 : ℝ)) (c := (10908275183932508151/10910000000000000000 : ℝ)) (alpha := (34828821507/43640000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-14101049/80000000 : ℝ)*X 0 0+(5423768333/10000000000 : ℝ)*X 0 1+(326280523/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1587_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673583941/5000000000 : ℝ)*X 1 0+(-466649421/2500000000 : ℝ)*X 1 1+(2610244163/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1587_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673583937/5000000000 : ℝ)*X 2 0+(5220488337/10000000000 : ℝ)*X 2 1+(-1866597679/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1587_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2118033881/5000000000 : ℝ)*X 0 0+(1999457377/5000000000 : ℝ)*X 0 1+(560541501/1250000000 : ℝ)*X 0 2+(2118033881/5000000000 : ℝ)*X 1 0+(1999457377/5000000000 : ℝ)*X 1 1+(560541501/1250000000 : ℝ)*X 1 2+(2118033881/5000000000 : ℝ)*X 2 0+(1999457377/5000000000 : ℝ)*X 2 1+(560541501/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1587_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1762657423/10000000000 : ℝ)*X 0 0+(5221552201/10000000000 : ℝ)*X 0 1+(5422696609/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1587_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323320293/2500000000 : ℝ)*X 1 0+(-208048677/1250000000 : ℝ)*X 1 1+(5422696609/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1587_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293281171/10000000000 : ℝ)*X 2 0+(5422696609/10000000000 : ℝ)*X 2 1+(-1664389417/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1587_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2118065269/5000000000 : ℝ)*X 0 0+(4481791553/10000000000 : ℝ)*X 0 1+(200073701/500000000 : ℝ)*X 0 2+(2118065269/5000000000 : ℝ)*X 1 0+(4481791553/10000000000 : ℝ)*X 1 1+(200073701/500000000 : ℝ)*X 1 2+(2118065269/5000000000 : ℝ)*X 2 0+(4481791553/10000000000 : ℝ)*X 2 1+(200073701/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1587_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (44162362612022407039613541/17046875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (224589863/50000000000000 : ℝ)*(base19) + (20172447/5000000000000 : ℝ)*(base23) + (5129387/25000000000000 : ℝ)*(lower2) + (7658209/12500000000000 : ℝ)*(upper3) + (4664449/12500000000000 : ℝ)*(upper5) + (54526775114789/1562500000000 : ℝ)*(major0) + (54526775114789/1562500000000 : ℝ)*(major1) + (54526775114789/1562500000000 : ℝ)*(major2) + (4919330813781779/100000000000000 : ℝ)*(sp0) + (4919336930065677/100000000000000 : ℝ)*(sp1) + (2459668487898231/50000000000000 : ℝ)*(sp2) + (206008634470609/10000000000000 : ℝ)*(sp3) + (6565463623/100000000000000 : ℝ)*(sp4) + (1702193367/50000000000000 : ℝ)*(sp7) + (257511218636603/12500000000000 : ℝ)*(f.failure) + (4919337379245403/100000000000000 : ℝ)*(f.sum) + (602425719119/136375000000000000000000000 : ℝ)*base66 + (202945897120270139/17046875000000000000000000000000 : ℝ)*base67 + (68071454365471007/8523437500000000000000000000000 : ℝ)*base69 + (108851558953801389/17046875000000000000000000000000 : ℝ)*base71 + (714375679709/545500000000000000000000000 : ℝ)*base74 + (15181955561136111/17046875000000000000000000000000 : ℝ)*base76 + (43961327926417361/17046875000000000000000000000000 : ℝ)*base78 + (254373334701145139/17046875000000000000000000000000 : ℝ)*base79 + (538883290927/545500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (1347621/1250000000000000000000 : ℝ)*base90 + (1347621/1250000000000000000000 : ℝ)*base92 + (1347621/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5269373078044253373319412841/545500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1502876987/100000000000000 : ℝ)*(base19) + (1628899557/100000000000000 : ℝ)*(base23) + (9969141/5000000000000 : ℝ)*(upper3) + (144007/250000000000 : ℝ)*(lower4) + (99502533/50000000000000 : ℝ)*(upper5) + (3526753775514603/100000000000000 : ℝ)*(major0) + (3526753775514603/100000000000000 : ℝ)*(major1) + (3526753775514603/100000000000000 : ℝ)*(major2) + (754991287/3125000000000 : ℝ)*(sp1) + (12970772463/50000000000000 : ℝ)*(sp2) + (2485775740974561/50000000000000 : ℝ)*(sp4) + (4971525819350951/100000000000000 : ℝ)*(sp5) + (4971523911504639/100000000000000 : ℝ)*(sp6) + (1040977873544833/50000000000000 : ℝ)*(sp7) + (1040977873544833/50000000000000 : ℝ)*(f.failure) + (2485775740974561/50000000000000 : ℝ)*(f.sum) + (5682119400957/2182000000000000000000000000 : ℝ)*base65 + (8998712359577279053/1091000000000000000000000000000000 : ℝ)*base67 + (4063498756040720947/1091000000000000000000000000000000 : ℝ)*base70 + (3175261641909279053/1091000000000000000000000000000000 : ℝ)*base71 + (1158547288389/2182000000000000000000000000 : ℝ)*base73 + (6327626177064279053/1091000000000000000000000000000000 : ℝ)*base75 + (13229532810206279053/1091000000000000000000000000000000 : ℝ)*base77 + (4298918983303720947/1091000000000000000000000000000000 : ℝ)*base80 + (340075145921/87280000000000000000000000 : ℝ)*base82 + (24979231/5000000000000000000000 : ℝ)*base90 + (24979231/5000000000000000000000 : ℝ)*base92 + (24979231/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1587_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4669/1024 : ℝ) ≤ p) (hpb : p ≤ (4671/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169396193/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1939/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2787/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11173/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7743/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1587_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1587_s5_0 (p : ℝ) (hpa : (4669/1024 : ℝ) ≤ p) (hpb : p ≤ (4671/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-881323829/5000000000 : ℝ)*x 0 + (5423647843/10000000000 : ℝ)*x 1 + (5220597969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (881323829/5000000000 : ℝ)^4671 ≤ (2165383477109/20000000000000 : ℝ)^3647 := by
    have hnat : (881323829 : ℕ)^4671*20000000000000^3647 ≤ 2165383477109^3647*5000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      881323829 5000000000 2165383477109 20000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5423647843/10000000000 : ℝ)^4671 ≤ (9135160474339/20000000000000 : ℝ)^3647 := by
    have hnat : (5423647843 : ℕ)^4671*20000000000000^3647 ≤ 9135160474339^3647*10000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423647843 10000000000 9135160474339 20000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5220597969/10000000000 : ℝ)^4671 ≤ (43497280237131/100000000000000 : ℝ)^3647 := by
    have hnat : (5220597969 : ℕ)^4671*100000000000000^3647 ≤ 43497280237131^3647*10000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220597969 10000000000 43497280237131 100000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4671/1024 : ℝ)) 4671 3647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-881323829/5000000000 : ℝ), (5423647843/10000000000 : ℝ), (5220597969/10000000000 : ℝ)] ![(2165383477109/20000000000000 : ℝ), (9135160474339/20000000000000 : ℝ), (43497280237131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-881323829/5000000000 : ℝ)|^4671 ≤ (2165383477109/20000000000000 : ℝ)^3647
        have hw : |(-881323829/5000000000 : ℝ)|=(881323829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5423647843/10000000000 : ℝ)|^4671 ≤ (9135160474339/20000000000000 : ℝ)^3647
        have hw : |(5423647843/10000000000 : ℝ)|=(5423647843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5220597969/10000000000 : ℝ)|^4671 ≤ (43497280237131/100000000000000 : ℝ)^3647
        have hw : |(5220597969/10000000000 : ℝ)|=(5220597969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1587_s5_1 (p : ℝ) (hpa : (4669/1024 : ℝ) ≤ p) (hpb : p ≤ (4671/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347136203/10000000000 : ℝ)*x 0 + (-1866493877/10000000000 : ℝ)*x 1 + (1305149497/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347136203/10000000000 : ℝ)^4671 ≤ (8970434374333/20000000000000 : ℝ)^3647 := by
    have hnat : (5347136203 : ℕ)^4671*20000000000000^3647 ≤ 8970434374333^3647*10000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347136203 10000000000 8970434374333 20000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1866493877/10000000000 : ℝ)^4671 ≤ (11650547670851/100000000000000 : ℝ)^3647 := by
    have hnat : (1866493877 : ℕ)^4671*100000000000000^3647 ≤ 11650547670851^3647*10000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1866493877 10000000000 11650547670851 100000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1305149497/2500000000 : ℝ)^4671 ≤ (8699456087977/20000000000000 : ℝ)^3647 := by
    have hnat : (1305149497 : ℕ)^4671*20000000000000^3647 ≤ 8699456087977^3647*2500000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305149497 2500000000 8699456087977 20000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4671/1024 : ℝ)) 4671 3647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347136203/10000000000 : ℝ), (-1866493877/10000000000 : ℝ), (1305149497/2500000000 : ℝ)] ![(8970434374333/20000000000000 : ℝ), (11650547670851/100000000000000 : ℝ), (8699456087977/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347136203/10000000000 : ℝ)|^4671 ≤ (8970434374333/20000000000000 : ℝ)^3647
        have hw : |(5347136203/10000000000 : ℝ)|=(5347136203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1866493877/10000000000 : ℝ)|^4671 ≤ (11650547670851/100000000000000 : ℝ)^3647
        have hw : |(-1866493877/10000000000 : ℝ)|=(1866493877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1305149497/2500000000 : ℝ)|^4671 ≤ (8699456087977/20000000000000 : ℝ)^3647
        have hw : |(1305149497/2500000000 : ℝ)|=(1305149497/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1587_s5_2 (p : ℝ) (hpa : (4669/1024 : ℝ) ≤ p) (hpb : p ≤ (4671/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347136221/10000000000 : ℝ)*x 0 + (5220597967/10000000000 : ℝ)*x 1 + (-1866493881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347136221/10000000000 : ℝ)^4671 ≤ (11213043016261/25000000000000 : ℝ)^3647 := by
    have hnat : (5347136221 : ℕ)^4671*25000000000000^3647 ≤ 11213043016261^3647*10000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347136221 10000000000 11213043016261 25000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5220597967/10000000000 : ℝ)^4671 ≤ (43497280215789/100000000000000 : ℝ)^3647 := by
    have hnat : (5220597967 : ℕ)^4671*100000000000000^3647 ≤ 43497280215789^3647*10000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220597967 10000000000 43497280215789 100000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1866493881/10000000000 : ℝ)^4671 ≤ (1165054770283/10000000000000 : ℝ)^3647 := by
    have hnat : (1866493881 : ℕ)^4671*10000000000000^3647 ≤ 1165054770283^3647*10000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1866493881 10000000000 1165054770283 10000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4671/1024 : ℝ)) 4671 3647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347136221/10000000000 : ℝ), (5220597967/10000000000 : ℝ), (-1866493881/10000000000 : ℝ)] ![(11213043016261/25000000000000 : ℝ), (43497280215789/100000000000000 : ℝ), (1165054770283/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347136221/10000000000 : ℝ)|^4671 ≤ (11213043016261/25000000000000 : ℝ)^3647
        have hw : |(5347136221/10000000000 : ℝ)|=(5347136221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5220597967/10000000000 : ℝ)|^4671 ≤ (43497280215789/100000000000000 : ℝ)^3647
        have hw : |(5220597967/10000000000 : ℝ)|=(5220597967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1866493881/10000000000 : ℝ)|^4671 ≤ (1165054770283/10000000000000 : ℝ)^3647
        have hw : |(-1866493881/10000000000 : ℝ)|=(1866493881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1587_s5_3 (p : ℝ) (hpa : (4669/1024 : ℝ) ≤ p) (hpb : p ≤ (4671/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (264754943/625000000 : ℝ)*x 0 + (3999188329/10000000000 : ℝ)*x 1 + (4484055941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264754943/625000000 : ℝ)^4671 ≤ (33283079718207/100000000000000 : ℝ)^3647 := by
    have hnat : (264754943 : ℕ)^4671*100000000000000^3647 ≤ 33283079718207^3647*625000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264754943 625000000 33283079718207 100000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3999188329/10000000000 : ℝ)^4671 ≤ (30918187225679/100000000000000 : ℝ)^3647 := by
    have hnat : (3999188329 : ℕ)^4671*100000000000000^3647 ≤ 30918187225679^3647*10000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3999188329 10000000000 30918187225679 100000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4484055941/10000000000 : ℝ)^4671 ≤ (35798733035149/100000000000000 : ℝ)^3647 := by
    have hnat : (4484055941 : ℕ)^4671*100000000000000^3647 ≤ 35798733035149^3647*10000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484055941 10000000000 35798733035149 100000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4671/1024 : ℝ)) 4671 3647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264754943/625000000 : ℝ), (3999188329/10000000000 : ℝ), (4484055941/10000000000 : ℝ)] ![(33283079718207/100000000000000 : ℝ), (30918187225679/100000000000000 : ℝ), (35798733035149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264754943/625000000 : ℝ)|^4671 ≤ (33283079718207/100000000000000 : ℝ)^3647
        have hw : |(264754943/625000000 : ℝ)|=(264754943/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3999188329/10000000000 : ℝ)|^4671 ≤ (30918187225679/100000000000000 : ℝ)^3647
        have hw : |(3999188329/10000000000 : ℝ)|=(3999188329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4484055941/10000000000 : ℝ)|^4671 ≤ (35798733035149/100000000000000 : ℝ)^3647
        have hw : |(4484055941/10000000000 : ℝ)|=(4484055941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1587_s5_4 (p : ℝ) (hpa : (4669/1024 : ℝ) ≤ p) (hpb : p ≤ (4671/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1762674159/10000000000 : ℝ)*x 0 + (522165897/1000000000 : ℝ)*x 1 + (135564469/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1762674159/10000000000 : ℝ)^4671 ≤ (10827125871401/100000000000000 : ℝ)^3647 := by
    have hnat : (1762674159 : ℕ)^4671*100000000000000^3647 ≤ 10827125871401^3647*10000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1762674159 10000000000 10827125871401 100000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (522165897/1000000000 : ℝ)^4671 ≤ (2175430139217/5000000000000 : ℝ)^3647 := by
    have hnat : (522165897 : ℕ)^4671*5000000000000^3647 ≤ 2175430139217^3647*1000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522165897 1000000000 2175430139217 5000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135564469/250000000 : ℝ)^4671 ≤ (22832135669403/50000000000000 : ℝ)^3647 := by
    have hnat : (135564469 : ℕ)^4671*50000000000000^3647 ≤ 22832135669403^3647*250000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135564469 250000000 22832135669403 50000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4671/1024 : ℝ)) 4671 3647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1762674159/10000000000 : ℝ), (522165897/1000000000 : ℝ), (135564469/250000000 : ℝ)] ![(10827125871401/100000000000000 : ℝ), (2175430139217/5000000000000 : ℝ), (22832135669403/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1762674159/10000000000 : ℝ)|^4671 ≤ (10827125871401/100000000000000 : ℝ)^3647
        have hw : |(-1762674159/10000000000 : ℝ)|=(1762674159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(522165897/1000000000 : ℝ)|^4671 ≤ (2175430139217/5000000000000 : ℝ)^3647
        have hw : |(522165897/1000000000 : ℝ)|=(522165897/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135564469/250000000 : ℝ)|^4671 ≤ (22832135669403/50000000000000 : ℝ)^3647
        have hw : |(135564469/250000000 : ℝ)|=(135564469/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1587_s5_5 (p : ℝ) (hpa : (4669/1024 : ℝ) ≤ p) (hpb : p ≤ (4671/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646655837/5000000000 : ℝ)*x 0 + (-832256349/5000000000 : ℝ)*x 1 + (5422577827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646655837/5000000000 : ℝ)^4671 ≤ (553434247209/1250000000000 : ℝ)^3647 := by
    have hnat : (2646655837 : ℕ)^4671*1250000000000^3647 ≤ 553434247209^3647*5000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646655837 5000000000 553434247209 1250000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (832256349/5000000000 : ℝ)^4671 ≤ (5030499468021/50000000000000 : ℝ)^3647 := by
    have hnat : (832256349 : ℕ)^4671*50000000000000^3647 ≤ 5030499468021^3647*5000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      832256349 5000000000 5030499468021 50000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5422577827/10000000000 : ℝ)^4671 ≤ (4566426127583/10000000000000 : ℝ)^3647 := by
    have hnat : (5422577827 : ℕ)^4671*10000000000000^3647 ≤ 4566426127583^3647*10000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422577827 10000000000 4566426127583 10000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4671/1024 : ℝ)) 4671 3647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646655837/5000000000 : ℝ), (-832256349/5000000000 : ℝ), (5422577827/10000000000 : ℝ)] ![(553434247209/1250000000000 : ℝ), (5030499468021/50000000000000 : ℝ), (4566426127583/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646655837/5000000000 : ℝ)|^4671 ≤ (553434247209/1250000000000 : ℝ)^3647
        have hw : |(2646655837/5000000000 : ℝ)|=(2646655837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-832256349/5000000000 : ℝ)|^4671 ≤ (5030499468021/50000000000000 : ℝ)^3647
        have hw : |(-832256349/5000000000 : ℝ)|=(832256349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5422577827/10000000000 : ℝ)|^4671 ≤ (4566426127583/10000000000000 : ℝ)^3647
        have hw : |(5422577827/10000000000 : ℝ)|=(5422577827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1587_s5_6 (p : ℝ) (hpa : (4669/1024 : ℝ) ≤ p) (hpb : p ≤ (4671/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293310611/10000000000 : ℝ)*x 0 + (5422578017/10000000000 : ℝ)*x 1 + (-104032119/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293310611/10000000000 : ℝ)^4671 ≤ (44274728389023/100000000000000 : ℝ)^3647 := by
    have hnat : (5293310611 : ℕ)^4671*100000000000000^3647 ≤ 44274728389023^3647*10000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293310611 10000000000 44274728389023 100000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5422578017/10000000000 : ℝ)^4671 ≤ (45664263325097/100000000000000 : ℝ)^3647 := by
    have hnat : (5422578017 : ℕ)^4671*100000000000000^3647 ≤ 45664263325097^3647*10000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422578017 10000000000 45664263325097 100000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104032119/625000000 : ℝ)^4671 ≤ (2012201654471/20000000000000 : ℝ)^3647 := by
    have hnat : (104032119 : ℕ)^4671*20000000000000^3647 ≤ 2012201654471^3647*625000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104032119 625000000 2012201654471 20000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4671/1024 : ℝ)) 4671 3647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293310611/10000000000 : ℝ), (5422578017/10000000000 : ℝ), (-104032119/625000000 : ℝ)] ![(44274728389023/100000000000000 : ℝ), (45664263325097/100000000000000 : ℝ), (2012201654471/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293310611/10000000000 : ℝ)|^4671 ≤ (44274728389023/100000000000000 : ℝ)^3647
        have hw : |(5293310611/10000000000 : ℝ)|=(5293310611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5422578017/10000000000 : ℝ)|^4671 ≤ (45664263325097/100000000000000 : ℝ)^3647
        have hw : |(5422578017/10000000000 : ℝ)|=(5422578017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-104032119/625000000 : ℝ)|^4671 ≤ (2012201654471/20000000000000 : ℝ)^3647
        have hw : |(-104032119/625000000 : ℝ)|=(104032119/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1587_s5_7 (p : ℝ) (hpa : (4669/1024 : ℝ) ≤ p) (hpb : p ≤ (4671/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2118070557/5000000000 : ℝ)*x 0 + (4481521691/10000000000 : ℝ)*x 1 + (4001741857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2118070557/5000000000 : ℝ)^4671 ≤ (33283703895861/100000000000000 : ℝ)^3647 := by
    have hnat : (2118070557 : ℕ)^4671*100000000000000^3647 ≤ 33283703895861^3647*5000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118070557 5000000000 33283703895861 100000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4481521691/10000000000 : ℝ)^4671 ≤ (35772821942381/100000000000000 : ℝ)^3647 := by
    have hnat : (4481521691 : ℕ)^4671*100000000000000^3647 ≤ 35772821942381^3647*10000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4481521691 10000000000 35772821942381 100000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4001741857/10000000000 : ℝ)^4671 ≤ (30943474138849/100000000000000 : ℝ)^3647 := by
    have hnat : (4001741857 : ℕ)^4671*100000000000000^3647 ≤ 30943474138849^3647*10000000000^4671 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4001741857 10000000000 30943474138849 100000000000000 4671 3647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4671/1024 : ℝ)) 4671 3647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2118070557/5000000000 : ℝ), (4481521691/10000000000 : ℝ), (4001741857/10000000000 : ℝ)] ![(33283703895861/100000000000000 : ℝ), (35772821942381/100000000000000 : ℝ), (30943474138849/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2118070557/5000000000 : ℝ)|^4671 ≤ (33283703895861/100000000000000 : ℝ)^3647
        have hw : |(2118070557/5000000000 : ℝ)|=(2118070557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4481521691/10000000000 : ℝ)|^4671 ≤ (35772821942381/100000000000000 : ℝ)^3647
        have hw : |(4481521691/10000000000 : ℝ)|=(4481521691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4001741857/10000000000 : ℝ)|^4671 ≤ (30943474138849/100000000000000 : ℝ)^3647
        have hw : |(4001741857/10000000000 : ℝ)|=(4001741857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1587_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4669/1024 : ℝ) ≤ p) (hpb : p ≤ (4671/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169396193/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7743/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11173/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (447/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15483/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7743/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11173/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7743/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11173/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7743/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11173/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7743/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11173/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7743/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11173/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7743/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11173/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11173/100000 : ℝ) ^ (4669/1024 : ℝ) ≤ (914309574340581/20000000000000000000 : ℝ) := by
    have hpowers : (11173/100000 : ℝ)^4669 ≤ (914309574340581/20000000000000000000 : ℝ)^1024 := by
      have hnat : (11173 : ℕ)^4669*20000000000000000000^1024 ≤ 914309574340581^1024*100000^4669 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11173 100000 914309574340581 20000000000000000000 4669 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11173/100000 : ℝ)) (X := (914309574340581/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4669 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7743/50000 : ℝ) ^ (4669/1024 : ℝ) ≤ (2025214720507/10000000000000000 : ℝ) := by
    have hpowers : (7743/50000 : ℝ)^4669 ≤ (2025214720507/10000000000000000 : ℝ)^1024 := by
      have hnat : (7743 : ℕ)^4669*10000000000000000^1024 ≤ 2025214720507^1024*50000^4669 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7743 50000 2025214720507 10000000000000000 4669 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7743/50000 : ℝ)) (X := (2025214720507/10000000000000000 : ℝ)) (by norm_num) (by norm_num) 4669 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000914309574340581/10000000000000000000 : ℝ) ≤ (10000200518224847/10000000000000000 : ℝ) ^ (4669/1024 : ℝ) := by
    have hpowers : (10000914309574340581/10000000000000000000 : ℝ)^1024 ≤ (10000200518224847/10000000000000000 : ℝ)^4669 := by
      have hnat : (10000914309574340581 : ℕ)^1024*10000000000000000^4669 ≤ 10000200518224847^4669*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000914309574340581 10000000000000000000 10000200518224847 10000000000000000 1024 4669 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000200518224847/10000000000000000 : ℝ)) (X := (10000914309574340581/10000000000000000000 : ℝ)) (by norm_num) 4669 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20004964739015354581/20000000000000000000 : ℝ) ≤ (10000544377833649/10000000000000000 : ℝ) ^ (4669/1024 : ℝ) := by
    have hpowers : (20004964739015354581/20000000000000000000 : ℝ)^1024 ≤ (10000544377833649/10000000000000000 : ℝ)^4669 := by
      have hnat : (20004964739015354581 : ℕ)^1024*10000000000000000^4669 ≤ 10000544377833649^4669*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20004964739015354581 20000000000000000000 10000544377833649 10000000000000000 1024 4669 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000544377833649/10000000000000000 : ℝ)) (X := (20004964739015354581/20000000000000000000 : ℝ)) (by norm_num) 4669 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5002025214720507/5000000000000000 : ℝ) ≤ (10000888237442451/10000000000000000 : ℝ) ^ (4669/1024 : ℝ) := by
    have hpowers : (5002025214720507/5000000000000000 : ℝ)^1024 ≤ (10000888237442451/10000000000000000 : ℝ)^4669 := by
      have hnat : (5002025214720507 : ℕ)^1024*10000000000000000^4669 ≤ 10000888237442451^4669*5000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002025214720507 5000000000000000 10000888237442451 10000000000000000 1024 4669 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000888237442451/10000000000000000 : ℝ)) (X := (5002025214720507/5000000000000000 : ℝ)) (by norm_num) 4669 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(914309574340581/20000000000000000000 : ℝ) ≤ ((43123180948285475619/43130000000000000000 : ℝ)+2*(171929804401/215650000000000 : ℝ)*(11173/100000 : ℝ))^(4669/1024 : ℝ) := by
    rw [show (43123180948285475619/43130000000000000000 : ℝ)+2*(171929804401/215650000000000 : ℝ)*(11173/100000 : ℝ)=(10000200518224847/10000000000000000 : ℝ) by norm_num, show 1+2*(914309574340581/20000000000000000000 : ℝ)=(10000914309574340581/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2025214720507/10000000000000000 : ℝ)+(914309574340581/20000000000000000000 : ℝ) ≤ ((43123180948285475619/43130000000000000000 : ℝ)+(171929804401/215650000000000 : ℝ)*((7743/50000 : ℝ)+(11173/100000 : ℝ)))^(4669/1024 : ℝ) := by
    rw [show (43123180948285475619/43130000000000000000 : ℝ)+(171929804401/215650000000000 : ℝ)*((7743/50000 : ℝ)+(11173/100000 : ℝ))=(10000544377833649/10000000000000000 : ℝ) by norm_num, show 1+(2025214720507/10000000000000000 : ℝ)+(914309574340581/20000000000000000000 : ℝ)=(20004964739015354581/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2025214720507/10000000000000000 : ℝ) ≤ ((43123180948285475619/43130000000000000000 : ℝ)+2*(171929804401/215650000000000 : ℝ)*(7743/50000 : ℝ))^(4669/1024 : ℝ) := by
    rw [show (43123180948285475619/43130000000000000000 : ℝ)+2*(171929804401/215650000000000 : ℝ)*(7743/50000 : ℝ)=(10000888237442451/10000000000000000 : ℝ) by norm_num, show 1+2*(2025214720507/10000000000000000 : ℝ)=(5002025214720507/5000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (43123180948285475619/43130000000000000000 : ℝ)*(X 1 0+X 2 0)+(171929804401/215650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4669/1024 : ℝ)) (lo := (11173/100000 : ℝ)) (hi := (7743/50000 : ℝ)) (c := (43123180948285475619/43130000000000000000 : ℝ)) (alpha := (171929804401/215650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (43123180948285475619/43130000000000000000 : ℝ)*(X 0 1+X 2 1)+(171929804401/215650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4669/1024 : ℝ)) (lo := (11173/100000 : ℝ)) (hi := (7743/50000 : ℝ)) (c := (43123180948285475619/43130000000000000000 : ℝ)) (alpha := (171929804401/215650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (43123180948285475619/43130000000000000000 : ℝ)*(X 0 2+X 1 2)+(171929804401/215650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4669/1024 : ℝ)) (lo := (11173/100000 : ℝ)) (hi := (7743/50000 : ℝ)) (c := (43123180948285475619/43130000000000000000 : ℝ)) (alpha := (171929804401/215650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-881323829/5000000000 : ℝ)*X 0 0+(5423647843/10000000000 : ℝ)*X 0 1+(5220597969/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1587_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347136203/10000000000 : ℝ)*X 1 0+(-1866493877/10000000000 : ℝ)*X 1 1+(1305149497/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1587_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347136221/10000000000 : ℝ)*X 2 0+(5220597967/10000000000 : ℝ)*X 2 1+(-1866493881/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1587_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((264754943/625000000 : ℝ)*X 0 0+(3999188329/10000000000 : ℝ)*X 0 1+(4484055941/10000000000 : ℝ)*X 0 2+(264754943/625000000 : ℝ)*X 1 0+(3999188329/10000000000 : ℝ)*X 1 1+(4484055941/10000000000 : ℝ)*X 1 2+(264754943/625000000 : ℝ)*X 2 0+(3999188329/10000000000 : ℝ)*X 2 1+(4484055941/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1587_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1762674159/10000000000 : ℝ)*X 0 0+(522165897/1000000000 : ℝ)*X 0 1+(135564469/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1587_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2646655837/5000000000 : ℝ)*X 1 0+(-832256349/5000000000 : ℝ)*X 1 1+(5422577827/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1587_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293310611/10000000000 : ℝ)*X 2 0+(5422578017/10000000000 : ℝ)*X 2 1+(-104032119/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1587_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2118070557/5000000000 : ℝ)*X 0 0+(4481521691/10000000000 : ℝ)*X 0 1+(4001741857/10000000000 : ℝ)*X 0 2+(2118070557/5000000000 : ℝ)*X 1 0+(4481521691/10000000000 : ℝ)*X 1 1+(4001741857/10000000000 : ℝ)*X 1 2+(2118070557/5000000000 : ℝ)*X 2 0+(4481521691/10000000000 : ℝ)*X 2 1+(4001741857/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1587_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (681226636580428873279992723/107825000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (207682807/20000000000000 : ℝ)*(base19) + (978143087/100000000000000 : ℝ)*(base23) + (1643703/4000000000000 : ℝ)*(lower2) + (156892699/100000000000000 : ℝ)*(upper3) + (3136307/3125000000000 : ℝ)*(upper5) + (349368358932939/10000000000000 : ℝ)*(major0) + (349368358932939/10000000000000 : ℝ)*(major1) + (349368358932939/10000000000000 : ℝ)*(major2) + (492491634420033/10000000000000 : ℝ)*(sp0) + (4924932572997073/100000000000000 : ℝ)*(sp1) + (4924932633268021/100000000000000 : ℝ)*(sp2) + (1031212754787387/50000000000000 : ℝ)*(sp3) + (17267210777/100000000000000 : ℝ)*(sp4) + (245221141/3125000000000 : ℝ)*(sp7) + (1031216678325643/50000000000000 : ℝ)*(f.failure) + (4924933611411107/100000000000000 : ℝ)*(f.sum) + (743340358461/862600000000000000000000000 : ℝ)*base66 + (169156708094914241/431300000000000000000000000000000 : ℝ)*base67 + (5020667173422085759/431300000000000000000000000000000 : ℝ)*base70 + (4407165735310385759/431300000000000000000000000000000 : ℝ)*base72 + (821665660727/862600000000000000000000000 : ℝ)*base73 + (1097244433726285759/431300000000000000000000000000000 : ℝ)*base76 + (6752900690038985759/431300000000000000000000000000000 : ℝ)*base78 + (4588774712570185759/431300000000000000000000000000000 : ℝ)*base80 + (520628959593/862600000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (38477099/5000000000000000000000 : ℝ)*base89 + (38477099/5000000000000000000000 : ℝ)*base91 + (38477099/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (503095554973909899766951569/269562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (485068369/25000000000000 : ℝ)*(base19) + (1146492901/100000000000000 : ℝ)*(base23) + (49373123/20000000000000 : ℝ)*(upper2) + (13082413/20000000000000 : ℝ)*(upper3) + (950299/1562500000000 : ℝ)*(upper5) + (441337425064983/12500000000000 : ℝ)*(major0) + (441337425064983/12500000000000 : ℝ)*(major1) + (441337425064983/12500000000000 : ℝ)*(major2) + (789073063/10000000000000 : ℝ)*(sp0) + (1602096493/6250000000000 : ℝ)*(sp1) + (995421174430773/20000000000000 : ℝ)*(sp4) + (4977086189067131/100000000000000 : ℝ)*(sp5) + (2488556308195797/50000000000000 : ℝ)*(sp6) + (104214248797193/5000000000000 : ℝ)*(sp7) + (104214248797193/5000000000000 : ℝ)*(f.failure) + (995422752576899/20000000000000 : ℝ)*(f.sum) + (207421478132703/21565000000000000000000000000 : ℝ)*base65 + (3155952973398749477/539125000000000000000000000000000 : ℝ)*base67 + (4018899623772500523/539125000000000000000000000000000 : ℝ)*base70 + (443680707223000523/539125000000000000000000000000000 : ℝ)*base72 + (52110620795469/10782500000000000000000000000 : ℝ)*base73 + (3166232846622124477/539125000000000000000000000000000 : ℝ)*base75 + (1364954614190999477/539125000000000000000000000000000 : ℝ)*base77 + (4235799345166999477/539125000000000000000000000000000 : ℝ)*base79 + (3169906457733/5391250000000000000000000000 : ℝ)*base82 + (3286249/500000000000000000000 : ℝ)*base89 + (3286249/500000000000000000000 : ℝ)*base91 + (3286249/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1587_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4669/1024 : ℝ) ≤ p) (hpb : p ≤ (4671/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169396193/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7743/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11173/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (447/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1587_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1587_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4669/1024 : ℝ) ≤ p) (hpb : p ≤ (4671/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169396193/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15769/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10911/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (447/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1587_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1587_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1587_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4669/1024 : ℝ) ≤ p) (hpb : p ≤ (4671/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169396193/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15769/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10911/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (447/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1587_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
