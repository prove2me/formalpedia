-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1454_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:59:49.096982+00:00
-- url     : https://prove2.me/submissions/65842b35-da9c-4a2c-a519-2c2a350073ab

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
theorem support_rectangle_w1454_s0_0 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1744745787/10000000000 : ℝ)*x 0 + (5949932333/10000000000 : ℝ)*x 1 + (604615067/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1744745787/10000000000 : ℝ)^2207 ≤ (643525970681/6250000000000 : ℝ)^1695 := by
    have hnat : (1744745787 : ℕ)^2207*6250000000000^1695 ≤ 643525970681^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1744745787 10000000000 643525970681 6250000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5949932333/10000000000 : ℝ)^2207 ≤ (25431385993827/50000000000000 : ℝ)^1695 := by
    have hnat : (5949932333 : ℕ)^2207*50000000000000^1695 ≤ 25431385993827^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5949932333 10000000000 25431385993827 50000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (604615067/1250000000 : ℝ)^2207 ≤ (38840812463797/100000000000000 : ℝ)^1695 := by
    have hnat : (604615067 : ℕ)^2207*100000000000000^1695 ≤ 38840812463797^1695*1250000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      604615067 1250000000 38840812463797 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1744745787/10000000000 : ℝ), (5949932333/10000000000 : ℝ), (604615067/1250000000 : ℝ)] ![(643525970681/6250000000000 : ℝ), (25431385993827/50000000000000 : ℝ), (38840812463797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1744745787/10000000000 : ℝ)|^2207 ≤ (643525970681/6250000000000 : ℝ)^1695
        have hw : |(-1744745787/10000000000 : ℝ)|=(1744745787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5949932333/10000000000 : ℝ)|^2207 ≤ (25431385993827/50000000000000 : ℝ)^1695
        have hw : |(5949932333/10000000000 : ℝ)|=(5949932333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(604615067/1250000000 : ℝ)|^2207 ≤ (38840812463797/100000000000000 : ℝ)^1695
        have hw : |(604615067/1250000000 : ℝ)|=(604615067/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s0_1 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5489322937/10000000000 : ℝ)*x 0 + (-593100431/2500000000 : ℝ)*x 1 + (4836920429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5489322937/10000000000 : ℝ)^2207 ≤ (22898474626029/50000000000000 : ℝ)^1695 := by
    have hnat : (5489322937 : ℕ)^2207*50000000000000^1695 ≤ 22898474626029^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5489322937 10000000000 22898474626029 50000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (593100431/2500000000 : ℝ)^2207 ≤ (15362239390249/100000000000000 : ℝ)^1695 := by
    have hnat : (593100431 : ℕ)^2207*100000000000000^1695 ≤ 15362239390249^1695*2500000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      593100431 2500000000 15362239390249 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4836920429/10000000000 : ℝ)^2207 ≤ (485510141813/1250000000000 : ℝ)^1695 := by
    have hnat : (4836920429 : ℕ)^2207*1250000000000^1695 ≤ 485510141813^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4836920429 10000000000 485510141813 1250000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5489322937/10000000000 : ℝ), (-593100431/2500000000 : ℝ), (4836920429/10000000000 : ℝ)] ![(22898474626029/50000000000000 : ℝ), (15362239390249/100000000000000 : ℝ), (485510141813/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5489322937/10000000000 : ℝ)|^2207 ≤ (22898474626029/50000000000000 : ℝ)^1695
        have hw : |(5489322937/10000000000 : ℝ)|=(5489322937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-593100431/2500000000 : ℝ)|^2207 ≤ (15362239390249/100000000000000 : ℝ)^1695
        have hw : |(-593100431/2500000000 : ℝ)|=(593100431/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4836920429/10000000000 : ℝ)|^2207 ≤ (485510141813/1250000000000 : ℝ)^1695
        have hw : |(4836920429/10000000000 : ℝ)|=(4836920429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s0_2 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5489322687/10000000000 : ℝ)*x 0 + (4836920413/10000000000 : ℝ)*x 1 + (-1186201033/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5489322687/10000000000 : ℝ)^2207 ≤ (9159389307261/20000000000000 : ℝ)^1695 := by
    have hnat : (5489322687 : ℕ)^2207*20000000000000^1695 ≤ 9159389307261^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5489322687 10000000000 9159389307261 20000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4836920413/10000000000 : ℝ)^2207 ≤ (38840811177749/100000000000000 : ℝ)^1695 := by
    have hnat : (4836920413 : ℕ)^2207*100000000000000^1695 ≤ 38840811177749^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4836920413 10000000000 38840811177749 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1186201033/5000000000 : ℝ)^2207 ≤ (15362242273783/100000000000000 : ℝ)^1695 := by
    have hnat : (1186201033 : ℕ)^2207*100000000000000^1695 ≤ 15362242273783^1695*5000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1186201033 5000000000 15362242273783 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5489322687/10000000000 : ℝ), (4836920413/10000000000 : ℝ), (-1186201033/5000000000 : ℝ)] ![(9159389307261/20000000000000 : ℝ), (38840811177749/100000000000000 : ℝ), (15362242273783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5489322687/10000000000 : ℝ)|^2207 ≤ (9159389307261/20000000000000 : ℝ)^1695
        have hw : |(5489322687/10000000000 : ℝ)|=(5489322687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4836920413/10000000000 : ℝ)|^2207 ≤ (38840811177749/100000000000000 : ℝ)^1695
        have hw : |(4836920413/10000000000 : ℝ)|=(4836920413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1186201033/5000000000 : ℝ)|^2207 ≤ (15362242273783/100000000000000 : ℝ)^1695
        have hw : |(-1186201033/5000000000 : ℝ)|=(1186201033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s0_3 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1040609087/2500000000 : ℝ)*x 0 + (387852881/1250000000 : ℝ)*x 1 + (1106542561/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1040609087/2500000000 : ℝ)^2207 ≤ (15971138776517/50000000000000 : ℝ)^1695 := by
    have hnat : (1040609087 : ℕ)^2207*50000000000000^1695 ≤ 15971138776517^1695*2500000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040609087 2500000000 15971138776517 50000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (387852881/1250000000 : ℝ)^2207 ≤ (871554668237/4000000000000 : ℝ)^1695 := by
    have hnat : (387852881 : ℕ)^2207*4000000000000^1695 ≤ 871554668237^1695*1250000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387852881 1250000000 871554668237 4000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1106542561/2000000000 : ℝ)^2207 ≤ (46268855730297/100000000000000 : ℝ)^1695 := by
    have hnat : (1106542561 : ℕ)^2207*100000000000000^1695 ≤ 46268855730297^1695*2000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106542561 2000000000 46268855730297 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1040609087/2500000000 : ℝ), (387852881/1250000000 : ℝ), (1106542561/2000000000 : ℝ)] ![(15971138776517/50000000000000 : ℝ), (871554668237/4000000000000 : ℝ), (46268855730297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1040609087/2500000000 : ℝ)|^2207 ≤ (15971138776517/50000000000000 : ℝ)^1695
        have hw : |(1040609087/2500000000 : ℝ)|=(1040609087/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(387852881/1250000000 : ℝ)|^2207 ≤ (871554668237/4000000000000 : ℝ)^1695
        have hw : |(387852881/1250000000 : ℝ)|=(387852881/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1106542561/2000000000 : ℝ)|^2207 ≤ (46268855730297/100000000000000 : ℝ)^1695
        have hw : |(1106542561/2000000000 : ℝ)|=(1106542561/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s0_4 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1748644853/10000000000 : ℝ)*x 0 + (194613661/400000000 : ℝ)*x 1 + (5920496549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1748644853/10000000000 : ℝ)^2207 ≤ (40337445329/390625000000 : ℝ)^1695 := by
    have hnat : (1748644853 : ℕ)^2207*390625000000^1695 ≤ 40337445329^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1748644853 10000000000 40337445329 390625000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (194613661/400000000 : ℝ)^2207 ≤ (9784559094709/25000000000000 : ℝ)^1695 := by
    have hnat : (194613661 : ℕ)^2207*25000000000000^1695 ≤ 9784559094709^1695*400000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      194613661 400000000 9784559094709 25000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5920496549/10000000000 : ℝ)^2207 ≤ (6316922199251/12500000000000 : ℝ)^1695 := by
    have hnat : (5920496549 : ℕ)^2207*12500000000000^1695 ≤ 6316922199251^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5920496549 10000000000 6316922199251 12500000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1748644853/10000000000 : ℝ), (194613661/400000000 : ℝ), (5920496549/10000000000 : ℝ)] ![(40337445329/390625000000 : ℝ), (9784559094709/25000000000000 : ℝ), (6316922199251/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1748644853/10000000000 : ℝ)|^2207 ≤ (40337445329/390625000000 : ℝ)^1695
        have hw : |(-1748644853/10000000000 : ℝ)|=(1748644853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(194613661/400000000 : ℝ)|^2207 ≤ (9784559094709/25000000000000 : ℝ)^1695
        have hw : |(194613661/400000000 : ℝ)|=(194613661/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5920496549/10000000000 : ℝ)|^2207 ≤ (6316922199251/12500000000000 : ℝ)^1695
        have hw : |(5920496549/10000000000 : ℝ)|=(5920496549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s0_5 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5185430881/10000000000 : ℝ)*x 0 + (-644412961/5000000000 : ℝ)*x 1 + (5920496619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5185430881/10000000000 : ℝ)^2207 ≤ (10630932813939/25000000000000 : ℝ)^1695 := by
    have hnat : (5185430881 : ℕ)^2207*25000000000000^1695 ≤ 10630932813939^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185430881 10000000000 10630932813939 25000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (644412961/5000000000 : ℝ)^2207 ≤ (6940890358719/100000000000000 : ℝ)^1695 := by
    have hnat : (644412961 : ℕ)^2207*100000000000000^1695 ≤ 6940890358719^1695*5000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      644412961 5000000000 6940890358719 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5920496619/10000000000 : ℝ)^2207 ≤ (50535378371987/100000000000000 : ℝ)^1695 := by
    have hnat : (5920496619 : ℕ)^2207*100000000000000^1695 ≤ 50535378371987^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5920496619 10000000000 50535378371987 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5185430881/10000000000 : ℝ), (-644412961/5000000000 : ℝ), (5920496619/10000000000 : ℝ)] ![(10630932813939/25000000000000 : ℝ), (6940890358719/100000000000000 : ℝ), (50535378371987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5185430881/10000000000 : ℝ)|^2207 ≤ (10630932813939/25000000000000 : ℝ)^1695
        have hw : |(5185430881/10000000000 : ℝ)|=(5185430881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-644412961/5000000000 : ℝ)|^2207 ≤ (6940890358719/100000000000000 : ℝ)^1695
        have hw : |(-644412961/5000000000 : ℝ)|=(644412961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5920496619/10000000000 : ℝ)|^2207 ≤ (50535378371987/100000000000000 : ℝ)^1695
        have hw : |(5920496619/10000000000 : ℝ)|=(5920496619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s0_6 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2592715457/5000000000 : ℝ)*x 0 + (2960248231/5000000000 : ℝ)*x 1 + (-32220653/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2592715457/5000000000 : ℝ)^2207 ≤ (42523731608121/100000000000000 : ℝ)^1695 := by
    have hnat : (2592715457 : ℕ)^2207*100000000000000^1695 ≤ 42523731608121^1695*5000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592715457 5000000000 42523731608121 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2960248231/5000000000 : ℝ)^2207 ≤ (5053537662709/10000000000000 : ℝ)^1695 := by
    have hnat : (2960248231 : ℕ)^2207*10000000000000^1695 ≤ 5053537662709^1695*5000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2960248231 5000000000 5053537662709 10000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32220653/250000000 : ℝ)^2207 ≤ (1735222936783/25000000000000 : ℝ)^1695 := by
    have hnat : (32220653 : ℕ)^2207*25000000000000^1695 ≤ 1735222936783^1695*250000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32220653 250000000 1735222936783 25000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2592715457/5000000000 : ℝ), (2960248231/5000000000 : ℝ), (-32220653/250000000 : ℝ)] ![(42523731608121/100000000000000 : ℝ), (5053537662709/10000000000000 : ℝ), (1735222936783/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2592715457/5000000000 : ℝ)|^2207 ≤ (42523731608121/100000000000000 : ℝ)^1695
        have hw : |(2592715457/5000000000 : ℝ)|=(2592715457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2960248231/5000000000 : ℝ)|^2207 ≤ (5053537662709/10000000000000 : ℝ)^1695
        have hw : |(2960248231/5000000000 : ℝ)|=(2960248231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-32220653/250000000 : ℝ)|^2207 ≤ (1735222936783/25000000000000 : ℝ)^1695
        have hw : |(-32220653/250000000 : ℝ)|=(32220653/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s0_7 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4170947481/10000000000 : ℝ)*x 0 + (1367666127/2500000000 : ℝ)*x 1 + (791771647/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4170947481/10000000000 : ℝ)^2207 ≤ (12510682323/39062500000 : ℝ)^1695 := by
    have hnat : (4170947481 : ℕ)^2207*39062500000^1695 ≤ 12510682323^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170947481 10000000000 12510682323 39062500000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1367666127/2500000000 : ℝ)^2207 ≤ (45594366583917/100000000000000 : ℝ)^1695 := by
    have hnat : (1367666127 : ℕ)^2207*100000000000000^1695 ≤ 45594366583917^1695*2500000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367666127 2500000000 45594366583917 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (791771647/2500000000 : ℝ)^2207 ≤ (174830364467/781250000000 : ℝ)^1695 := by
    have hnat : (791771647 : ℕ)^2207*781250000000^1695 ≤ 174830364467^1695*2500000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      791771647 2500000000 174830364467 781250000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4170947481/10000000000 : ℝ), (1367666127/2500000000 : ℝ), (791771647/2500000000 : ℝ)] ![(12510682323/39062500000 : ℝ), (45594366583917/100000000000000 : ℝ), (174830364467/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4170947481/10000000000 : ℝ)|^2207 ≤ (12510682323/39062500000 : ℝ)^1695
        have hw : |(4170947481/10000000000 : ℝ)|=(4170947481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1367666127/2500000000 : ℝ)|^2207 ≤ (45594366583917/100000000000000 : ℝ)^1695
        have hw : |(1367666127/2500000000 : ℝ)|=(1367666127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(791771647/2500000000 : ℝ)|^2207 ≤ (174830364467/781250000000 : ℝ)^1695
        have hw : |(791771647/2500000000 : ℝ)|=(791771647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1454_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79579139/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2223/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26087/100000 : ℝ)*pair X 0 0 := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (4413/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4413 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4413*1^1024 ≤ 0^1024*1^4413 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4413 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4413 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4413/1024 : ℝ) ≤ (1927744853981189701/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4413 ≤ (1927744853981189701/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4413*100000000000000000000^1024 ≤ 1927744853981189701^1024*5^4413 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1927744853981189701 100000000000000000000 4413 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1927744853981189701/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4413 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4413/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4413 := by
      have hnat : (1 : ℕ)^1024*1^4413 ≤ 1^4413*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4413 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101927744853981189701/100000000000000000000 : ℝ) ≤ (10044404320118219/10000000000000000 : ℝ) ^ (4413/1024 : ℝ) := by
    have hpowers : (101927744853981189701/100000000000000000000 : ℝ)^1024 ≤ (10044404320118219/10000000000000000 : ℝ)^4413 := by
      have hnat : (101927744853981189701 : ℕ)^1024*10000000000000000^4413 ≤ 10044404320118219^4413*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101927744853981189701 100000000000000000000 10044404320118219 10000000000000000 1024 4413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10044404320118219/10000000000000000 : ℝ)) (X := (101927744853981189701/100000000000000000000 : ℝ)) (by norm_num) 4413 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51927744853981189701/50000000000000000000 : ℝ) ≤ (5044404320118219/5000000000000000 : ℝ) ^ (4413/1024 : ℝ) := by
    have hpowers : (51927744853981189701/50000000000000000000 : ℝ)^1024 ≤ (5044404320118219/5000000000000000 : ℝ)^4413 := by
      have hnat : (51927744853981189701 : ℕ)^1024*5000000000000000^4413 ≤ 5044404320118219^4413*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51927744853981189701 50000000000000000000 5044404320118219 5000000000000000 1024 4413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5044404320118219/5000000000000000 : ℝ)) (X := (51927744853981189701/50000000000000000000 : ℝ)) (by norm_num) 4413 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(44404320118219/4000000000000000 : ℝ)*(0 : ℝ))^(4413/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(44404320118219/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1927744853981189701/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(44404320118219/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4413/1024 : ℝ) := by
    rw [show (1 : ℝ)+(44404320118219/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10044404320118219/10000000000000000 : ℝ) by norm_num, show 1+(1927744853981189701/100000000000000000000 : ℝ)+(0 : ℝ)=(101927744853981189701/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1927744853981189701/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(44404320118219/4000000000000000 : ℝ)*(2/5 : ℝ))^(4413/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(44404320118219/4000000000000000 : ℝ)*(2/5 : ℝ)=(5044404320118219/5000000000000000 : ℝ) by norm_num, show 1+2*(1927744853981189701/100000000000000000000 : ℝ)=(51927744853981189701/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(44404320118219/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4413/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (44404320118219/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(44404320118219/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4413/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (44404320118219/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(44404320118219/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4413/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (44404320118219/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1744745787/10000000000 : ℝ)*X 0 0+(5949932333/10000000000 : ℝ)*X 0 1+(604615067/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5489322937/10000000000 : ℝ)*X 1 0+(-593100431/2500000000 : ℝ)*X 1 1+(4836920429/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5489322687/10000000000 : ℝ)*X 2 0+(4836920413/10000000000 : ℝ)*X 2 1+(-1186201033/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1040609087/2500000000 : ℝ)*X 0 0+(387852881/1250000000 : ℝ)*X 0 1+(1106542561/2000000000 : ℝ)*X 0 2+(1040609087/2500000000 : ℝ)*X 1 0+(387852881/1250000000 : ℝ)*X 1 1+(1106542561/2000000000 : ℝ)*X 1 2+(1040609087/2500000000 : ℝ)*X 2 0+(387852881/1250000000 : ℝ)*X 2 1+(1106542561/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1748644853/10000000000 : ℝ)*X 0 0+(194613661/400000000 : ℝ)*X 0 1+(5920496549/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5185430881/10000000000 : ℝ)*X 1 0+(-644412961/5000000000 : ℝ)*X 1 1+(5920496619/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2592715457/5000000000 : ℝ)*X 2 0+(2960248231/5000000000 : ℝ)*X 2 1+(-32220653/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4170947481/10000000000 : ℝ)*X 0 0+(1367666127/2500000000 : ℝ)*X 0 1+(791771647/2500000000 : ℝ)*X 0 2+(4170947481/10000000000 : ℝ)*X 1 0+(1367666127/2500000000 : ℝ)*X 1 1+(791771647/2500000000 : ℝ)*X 1 2+(4170947481/10000000000 : ℝ)*X 2 0+(1367666127/2500000000 : ℝ)*X 2 1+(791771647/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (510298247107380518859/200000000000000000000000000 : ℝ) := by norm_num
    linear_combination (142411509/100000000000000 : ℝ)*(base1) + (470057/10000000000000 : ℝ)*(base16) + (113458031/20000000000000 : ℝ)*(base19) + (265535981/50000000000000 : ℝ)*(base23) + (8933029/10000000000000 : ℝ)*(upper3) + (2620017147013/400000000000 : ℝ)*(major0) + (2620017147013/400000000000 : ℝ)*(major1) + (2620017147013/400000000000 : ℝ)*(major2) + (56154049372491/6250000000000 : ℝ)*(sp0) + (898465208801647/100000000000000 : ℝ)*(sp1) + (898465249720411/100000000000000 : ℝ)*(sp2) + (411541804745909/100000000000000 : ℝ)*(sp3) + (45329761/4000000000000 : ℝ)*(sp4) + (47531687/6250000000000 : ℝ)*(sp7) + (41154270766441/10000000000000 : ℝ)*(f.failure) + (224616445198093/25000000000000 : ℝ)*(f.sum) + (1761816740247/800000000000000000000000000 : ℝ)*base65 + (11741322344247/1600000000000000000000000000 : ℝ)*base67 + (6937725798647/1600000000000000000000000000 : ℝ)*base69 + (6900599173047/1600000000000000000000000000 : ℝ)*base71 + (797413817847/800000000000000000000000000 : ℝ)*base73 + (17027687363447/1600000000000000000000000000 : ℝ)*base75 + (11142539784247/1600000000000000000000000000 : ℝ)*base77 + (4170782232247/1600000000000000000000000000 : ℝ)*base79 + (664992402153/800000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (5125701/500000000000000000000 : ℝ)*base90 + (5125701/500000000000000000000 : ℝ)*base92 + (5125701/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2186793643015492791/250000000000000000000000 : ℝ) := by norm_num
    linear_combination (39947211/2000000000000 : ℝ)*(base19) + (125941971/6250000000000 : ℝ)*(base23) + (174796711/100000000000000 : ℝ)*(base32) + (299831977/100000000000000 : ℝ)*(upper3) + (93809597/50000000000000 : ℝ)*(upper5) + (69091729215091/10000000000000 : ℝ)*(major0) + (69091729215091/10000000000000 : ℝ)*(major1) + (69091729215091/10000000000000 : ℝ)*(major2) + (4813930303/100000000000000 : ℝ)*(sp1) + (1253307487/25000000000000 : ℝ)*(sp2) + (189545450217873/20000000000000 : ℝ)*(sp4) + (59232527487407/6250000000000 : ℝ)*(sp5) + (473860111393941/50000000000000 : ℝ)*(sp6) + (434106866843253/100000000000000 : ℝ)*(sp7) + (108526760409991/25000000000000 : ℝ)*(f.failure) + (189545450217873/20000000000000 : ℝ)*(f.sum) + (30708948117071/20000000000000000000000000000 : ℝ)*base66 + (316459352882929/40000000000000000000000000000 : ℝ)*base67 + (26821512882929/40000000000000000000000000000 : ℝ)*base69 + (67045011802929/40000000000000000000000000000 : ℝ)*base71 + (136515317082929/20000000000000000000000000000 : ℝ)*base73 + (117741931682929/40000000000000000000000000000 : ℝ)*base75 + (107823205837071/40000000000000000000000000000 : ℝ)*base78 + (30789462437071/40000000000000000000000000000 : ℝ)*base80 + (14575608277071/20000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (4222251/1250000000000000000000 : ℝ)*base90 + (4222251/1250000000000000000000 : ℝ)*base92 + (4222251/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1454_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79579139/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2223/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26087/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1454_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1454_s1_0 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1913567701/10000000000 : ℝ)*x 0 + (5595377103/10000000000 : ℝ)*x 1 + (79425067/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1913567701/10000000000 : ℝ)^2207 ≤ (5806094063959/50000000000000 : ℝ)^1695 := by
    have hnat : (1913567701 : ℕ)^2207*50000000000000^1695 ≤ 5806094063959^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1913567701 10000000000 5806094063959 50000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5595377103/10000000000 : ℝ)^2207 ≤ (46952363998611/100000000000000 : ℝ)^1695 := by
    have hnat : (5595377103 : ℕ)^2207*100000000000000^1695 ≤ 46952363998611^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5595377103 10000000000 46952363998611 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (79425067/156250000 : ℝ)^2207 ≤ (41435447866597/100000000000000 : ℝ)^1695 := by
    have hnat : (79425067 : ℕ)^2207*100000000000000^1695 ≤ 41435447866597^1695*156250000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79425067 156250000 41435447866597 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1913567701/10000000000 : ℝ), (5595377103/10000000000 : ℝ), (79425067/156250000 : ℝ)] ![(5806094063959/50000000000000 : ℝ), (46952363998611/100000000000000 : ℝ), (41435447866597/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1913567701/10000000000 : ℝ)|^2207 ≤ (5806094063959/50000000000000 : ℝ)^1695
        have hw : |(-1913567701/10000000000 : ℝ)|=(1913567701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5595377103/10000000000 : ℝ)|^2207 ≤ (46952363998611/100000000000000 : ℝ)^1695
        have hw : |(5595377103/10000000000 : ℝ)|=(5595377103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(79425067/156250000 : ℝ)|^2207 ≤ (41435447866597/100000000000000 : ℝ)^1695
        have hw : |(79425067/156250000 : ℝ)|=(79425067/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s1_1 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1078863887/2000000000 : ℝ)*x 0 + (-2184453683/10000000000 : ℝ)*x 1 + (5083206097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078863887/2000000000 : ℝ)^2207 ≤ (895352666083/2000000000000 : ℝ)^1695 := by
    have hnat : (1078863887 : ℕ)^2207*2000000000000^1695 ≤ 895352666083^1695*2000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078863887 2000000000 895352666083 2000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2184453683/10000000000 : ℝ)^2207 ≤ (13796899608239/100000000000000 : ℝ)^1695 := by
    have hnat : (2184453683 : ℕ)^2207*100000000000000^1695 ≤ 13796899608239^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184453683 10000000000 13796899608239 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5083206097/10000000000 : ℝ)^2207 ≤ (8287093413359/20000000000000 : ℝ)^1695 := by
    have hnat : (5083206097 : ℕ)^2207*20000000000000^1695 ≤ 8287093413359^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5083206097 10000000000 8287093413359 20000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1078863887/2000000000 : ℝ), (-2184453683/10000000000 : ℝ), (5083206097/10000000000 : ℝ)] ![(895352666083/2000000000000 : ℝ), (13796899608239/100000000000000 : ℝ), (8287093413359/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1078863887/2000000000 : ℝ)|^2207 ≤ (895352666083/2000000000000 : ℝ)^1695
        have hw : |(1078863887/2000000000 : ℝ)|=(1078863887/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2184453683/10000000000 : ℝ)|^2207 ≤ (13796899608239/100000000000000 : ℝ)^1695
        have hw : |(-2184453683/10000000000 : ℝ)|=(2184453683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5083206097/10000000000 : ℝ)|^2207 ≤ (8287093413359/20000000000000 : ℝ)^1695
        have hw : |(5083206097/10000000000 : ℝ)|=(5083206097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s1_2 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5394320939/10000000000 : ℝ)*x 0 + (2541602209/5000000000 : ℝ)*x 1 + (-17475631/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5394320939/10000000000 : ℝ)^2207 ≤ (44767649556193/100000000000000 : ℝ)^1695 := by
    have hnat : (5394320939 : ℕ)^2207*100000000000000^1695 ≤ 44767649556193^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394320939 10000000000 44767649556193 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2541602209/5000000000 : ℝ)^2207 ≤ (41435449246379/100000000000000 : ℝ)^1695 := by
    have hnat : (2541602209 : ℕ)^2207*100000000000000^1695 ≤ 41435449246379^1695*5000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2541602209 5000000000 41435449246379 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17475631/80000000 : ℝ)^2207 ≤ (3449225296801/25000000000000 : ℝ)^1695 := by
    have hnat : (17475631 : ℕ)^2207*25000000000000^1695 ≤ 3449225296801^1695*80000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17475631 80000000 3449225296801 25000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5394320939/10000000000 : ℝ), (2541602209/5000000000 : ℝ), (-17475631/80000000 : ℝ)] ![(44767649556193/100000000000000 : ℝ), (41435449246379/100000000000000 : ℝ), (3449225296801/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5394320939/10000000000 : ℝ)|^2207 ≤ (44767649556193/100000000000000 : ℝ)^1695
        have hw : |(5394320939/10000000000 : ℝ)|=(5394320939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2541602209/5000000000 : ℝ)|^2207 ≤ (41435449246379/100000000000000 : ℝ)^1695
        have hw : |(2541602209/5000000000 : ℝ)|=(2541602209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-17475631/80000000 : ℝ)|^2207 ≤ (3449225296801/25000000000000 : ℝ)^1695
        have hw : |(-17475631/80000000 : ℝ)|=(17475631/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s1_3 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4272084129/10000000000 : ℝ)*x 0 + (374532161/1000000000 : ℝ)*x 1 + (194539033/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4272084129/10000000000 : ℝ)^2207 ≤ (33042206788743/100000000000000 : ℝ)^1695 := by
    have hnat : (4272084129 : ℕ)^2207*100000000000000^1695 ≤ 33042206788743^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4272084129 10000000000 33042206788743 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (374532161/1000000000 : ℝ)^2207 ≤ (27186618551/97656250000 : ℝ)^1695 := by
    have hnat : (374532161 : ℕ)^2207*97656250000^1695 ≤ 27186618551^1695*1000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      374532161 1000000000 27186618551 97656250000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (194539033/400000000 : ℝ)^2207 ≤ (4889836976221/12500000000000 : ℝ)^1695 := by
    have hnat : (194539033 : ℕ)^2207*12500000000000^1695 ≤ 4889836976221^1695*400000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      194539033 400000000 4889836976221 12500000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4272084129/10000000000 : ℝ), (374532161/1000000000 : ℝ), (194539033/400000000 : ℝ)] ![(33042206788743/100000000000000 : ℝ), (27186618551/97656250000 : ℝ), (4889836976221/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4272084129/10000000000 : ℝ)|^2207 ≤ (33042206788743/100000000000000 : ℝ)^1695
        have hw : |(4272084129/10000000000 : ℝ)|=(4272084129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(374532161/1000000000 : ℝ)|^2207 ≤ (27186618551/97656250000 : ℝ)^1695
        have hw : |(374532161/1000000000 : ℝ)|=(374532161/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(194539033/400000000 : ℝ)|^2207 ≤ (4889836976221/12500000000000 : ℝ)^1695
        have hw : |(194539033/400000000 : ℝ)|=(194539033/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s1_4 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1913933053/10000000000 : ℝ)*x 0 + (1017818699/2000000000 : ℝ)*x 1 + (5589390029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1913933053/10000000000 : ℝ)^2207 ≤ (5807537497783/50000000000000 : ℝ)^1695 := by
    have hnat : (1913933053 : ℕ)^2207*50000000000000^1695 ≤ 5807537497783^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1913933053 10000000000 5807537497783 50000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1017818699/2000000000 : ℝ)^2207 ≤ (20748982560001/50000000000000 : ℝ)^1695 := by
    have hnat : (1017818699 : ℕ)^2207*50000000000000^1695 ≤ 20748982560001^1695*2000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1017818699 2000000000 20748982560001 50000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5589390029/10000000000 : ℝ)^2207 ≤ (11721739967973/25000000000000 : ℝ)^1695 := by
    have hnat : (5589390029 : ℕ)^2207*25000000000000^1695 ≤ 11721739967973^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5589390029 10000000000 11721739967973 25000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1913933053/10000000000 : ℝ), (1017818699/2000000000 : ℝ), (5589390029/10000000000 : ℝ)] ![(5807537497783/50000000000000 : ℝ), (20748982560001/50000000000000 : ℝ), (11721739967973/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1913933053/10000000000 : ℝ)|^2207 ≤ (5807537497783/50000000000000 : ℝ)^1695
        have hw : |(-1913933053/10000000000 : ℝ)|=(1913933053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1017818699/2000000000 : ℝ)|^2207 ≤ (20748982560001/50000000000000 : ℝ)^1695
        have hw : |(1017818699/2000000000 : ℝ)|=(1017818699/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5589390029/10000000000 : ℝ)|^2207 ≤ (11721739967973/25000000000000 : ℝ)^1695
        have hw : |(5589390029/10000000000 : ℝ)|=(5589390029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s1_5 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5260259259/10000000000 : ℝ)*x 0 + (-1678269067/10000000000 : ℝ)*x 1 + (5589390063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5260259259/10000000000 : ℝ)^2207 ≤ (21662232222067/50000000000000 : ℝ)^1695 := by
    have hnat : (5260259259 : ℕ)^2207*50000000000000^1695 ≤ 21662232222067^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260259259 10000000000 21662232222067 50000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1678269067/10000000000 : ℝ)^2207 ≤ (611785956399/6250000000000 : ℝ)^1695 := by
    have hnat : (1678269067 : ℕ)^2207*6250000000000^1695 ≤ 611785956399^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1678269067 10000000000 611785956399 6250000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5589390063/10000000000 : ℝ)^2207 ≤ (5860870030407/12500000000000 : ℝ)^1695 := by
    have hnat : (5589390063 : ℕ)^2207*12500000000000^1695 ≤ 5860870030407^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5589390063 10000000000 5860870030407 12500000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5260259259/10000000000 : ℝ), (-1678269067/10000000000 : ℝ), (5589390063/10000000000 : ℝ)] ![(21662232222067/50000000000000 : ℝ), (611785956399/6250000000000 : ℝ), (5860870030407/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5260259259/10000000000 : ℝ)|^2207 ≤ (21662232222067/50000000000000 : ℝ)^1695
        have hw : |(5260259259/10000000000 : ℝ)|=(5260259259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1678269067/10000000000 : ℝ)|^2207 ≤ (611785956399/6250000000000 : ℝ)^1695
        have hw : |(-1678269067/10000000000 : ℝ)|=(1678269067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5589390063/10000000000 : ℝ)|^2207 ≤ (5860870030407/12500000000000 : ℝ)^1695
        have hw : |(5589390063/10000000000 : ℝ)|=(5589390063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s1_6 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5260259153/10000000000 : ℝ)*x 0 + (698673753/1250000000 : ℝ)*x 1 + (-209783659/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5260259153/10000000000 : ℝ)^2207 ≤ (8664892661477/20000000000000 : ℝ)^1695 := by
    have hnat : (5260259153 : ℕ)^2207*20000000000000^1695 ≤ 8664892661477^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260259153 10000000000 8664892661477 20000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (698673753/1250000000 : ℝ)^2207 ≤ (146521749429/312500000000 : ℝ)^1695 := by
    have hnat : (698673753 : ℕ)^2207*312500000000^1695 ≤ 146521749429^1695*1250000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      698673753 1250000000 146521749429 312500000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209783659/1250000000 : ℝ)^2207 ≤ (391543074369/4000000000000 : ℝ)^1695 := by
    have hnat : (209783659 : ℕ)^2207*4000000000000^1695 ≤ 391543074369^1695*1250000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209783659 1250000000 391543074369 4000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5260259153/10000000000 : ℝ), (698673753/1250000000 : ℝ), (-209783659/1250000000 : ℝ)] ![(8664892661477/20000000000000 : ℝ), (146521749429/312500000000 : ℝ), (391543074369/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5260259153/10000000000 : ℝ)|^2207 ≤ (8664892661477/20000000000000 : ℝ)^1695
        have hw : |(5260259153/10000000000 : ℝ)|=(5260259153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(698673753/1250000000 : ℝ)|^2207 ≤ (146521749429/312500000000 : ℝ)^1695
        have hw : |(698673753/1250000000 : ℝ)|=(698673753/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-209783659/1250000000 : ℝ)|^2207 ≤ (391543074369/4000000000000 : ℝ)^1695
        have hw : |(-209783659/1250000000 : ℝ)|=(209783659/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s1_7 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2136441197/5000000000 : ℝ)*x 0 + (606327537/1250000000 : ℝ)*x 1 + (1879194807/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2136441197/5000000000 : ℝ)^2207 ≤ (826256153601/2500000000000 : ℝ)^1695 := by
    have hnat : (2136441197 : ℕ)^2207*2500000000000^1695 ≤ 826256153601^1695*5000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136441197 5000000000 826256153601 2500000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (606327537/1250000000 : ℝ)^2207 ≤ (38984113905851/100000000000000 : ℝ)^1695 := by
    have hnat : (606327537 : ℕ)^2207*100000000000000^1695 ≤ 38984113905851^1695*1250000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      606327537 1250000000 38984113905851 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1879194807/5000000000 : ℝ)^2207 ≤ (27965639934097/100000000000000 : ℝ)^1695 := by
    have hnat : (1879194807 : ℕ)^2207*100000000000000^1695 ≤ 27965639934097^1695*5000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1879194807 5000000000 27965639934097 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2136441197/5000000000 : ℝ), (606327537/1250000000 : ℝ), (1879194807/5000000000 : ℝ)] ![(826256153601/2500000000000 : ℝ), (38984113905851/100000000000000 : ℝ), (27965639934097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2136441197/5000000000 : ℝ)|^2207 ≤ (826256153601/2500000000000 : ℝ)^1695
        have hw : |(2136441197/5000000000 : ℝ)|=(2136441197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(606327537/1250000000 : ℝ)|^2207 ≤ (38984113905851/100000000000000 : ℝ)^1695
        have hw : |(606327537/1250000000 : ℝ)|=(606327537/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1879194807/5000000000 : ℝ)|^2207 ≤ (27965639934097/100000000000000 : ℝ)^1695
        have hw : |(1879194807/5000000000 : ℝ)|=(1879194807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1454_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79579139/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26087/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2223/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (3927/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18683/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26087/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2223/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26087/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2223/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26087/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2223/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26087/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2223/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26087/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2223/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26087/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2223/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2223/100000 : ℝ) ^ (4413/1024 : ℝ) ≤ (3758282208171/50000000000000000000 : ℝ) := by
    have hpowers : (2223/100000 : ℝ)^4413 ≤ (3758282208171/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2223 : ℕ)^4413*50000000000000000000^1024 ≤ 3758282208171^1024*100000^4413 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2223 100000 3758282208171 50000000000000000000 4413 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2223/100000 : ℝ)) (X := (3758282208171/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4413 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (26087/100000 : ℝ) ^ (4413/1024 : ℝ) ≤ (305519398861402259/100000000000000000000 : ℝ) := by
    have hpowers : (26087/100000 : ℝ)^4413 ≤ (305519398861402259/100000000000000000000 : ℝ)^1024 := by
      have hnat : (26087 : ℕ)^4413*100000000000000000000^1024 ≤ 305519398861402259^1024*100000^4413 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26087 100000 305519398861402259 100000000000000000000 4413 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26087/100000 : ℝ)) (X := (305519398861402259/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4413 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000003758282208171/25000000000000000000 : ℝ) ≤ (1600000055813/1600000000000 : ℝ) ^ (4413/1024 : ℝ) := by
    have hpowers : (25000003758282208171/25000000000000000000 : ℝ)^1024 ≤ (1600000055813/1600000000000 : ℝ)^4413 := by
      have hnat : (25000003758282208171 : ℕ)^1024*1600000000000^4413 ≤ 1600000055813^4413*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000003758282208171 25000000000000000000 1600000055813 1600000000000 1024 4413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1600000055813/1600000000000 : ℝ)) (X := (25000003758282208171/25000000000000000000 : ℝ)) (by norm_num) 4413 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100305526915425818601/100000000000000000000 : ℝ) ≤ (5003540598081137/5000000000000000 : ℝ) ^ (4413/1024 : ℝ) := by
    have hpowers : (100305526915425818601/100000000000000000000 : ℝ)^1024 ≤ (5003540598081137/5000000000000000 : ℝ)^4413 := by
      have hnat : (100305526915425818601 : ℕ)^1024*5000000000000000^4413 ≤ 5003540598081137^4413*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100305526915425818601 100000000000000000000 5003540598081137 5000000000000000 1024 4413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003540598081137/5000000000000000 : ℝ)) (X := (100305526915425818601/100000000000000000000 : ℝ)) (by norm_num) 4413 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50305519398861402259/50000000000000000000 : ℝ) ≤ (5007081021746649/5000000000000000 : ℝ) ^ (4413/1024 : ℝ) := by
    have hpowers : (50305519398861402259/50000000000000000000 : ℝ)^1024 ≤ (5007081021746649/5000000000000000 : ℝ)^4413 := by
      have hnat : (50305519398861402259 : ℕ)^1024*5000000000000000^4413 ≤ 5007081021746649^4413*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50305519398861402259 50000000000000000000 5007081021746649 5000000000000000 1024 4413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5007081021746649/5000000000000000 : ℝ)) (X := (50305519398861402259/50000000000000000000 : ℝ)) (by norm_num) 4413 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3758282208171/50000000000000000000 : ℝ) ≤ ((784896469991036899/785000000000000000 : ℝ)+2*(442552958189/149150000000000 : ℝ)*(2223/100000 : ℝ))^(4413/1024 : ℝ) := by
    rw [show (784896469991036899/785000000000000000 : ℝ)+2*(442552958189/149150000000000 : ℝ)*(2223/100000 : ℝ)=(1600000055813/1600000000000 : ℝ) by norm_num, show 1+2*(3758282208171/50000000000000000000 : ℝ)=(25000003758282208171/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(305519398861402259/100000000000000000000 : ℝ)+(3758282208171/50000000000000000000 : ℝ) ≤ ((784896469991036899/785000000000000000 : ℝ)+(442552958189/149150000000000 : ℝ)*((26087/100000 : ℝ)+(2223/100000 : ℝ)))^(4413/1024 : ℝ) := by
    rw [show (784896469991036899/785000000000000000 : ℝ)+(442552958189/149150000000000 : ℝ)*((26087/100000 : ℝ)+(2223/100000 : ℝ))=(5003540598081137/5000000000000000 : ℝ) by norm_num, show 1+(305519398861402259/100000000000000000000 : ℝ)+(3758282208171/50000000000000000000 : ℝ)=(100305526915425818601/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(305519398861402259/100000000000000000000 : ℝ) ≤ ((784896469991036899/785000000000000000 : ℝ)+2*(442552958189/149150000000000 : ℝ)*(26087/100000 : ℝ))^(4413/1024 : ℝ) := by
    rw [show (784896469991036899/785000000000000000 : ℝ)+2*(442552958189/149150000000000 : ℝ)*(26087/100000 : ℝ)=(5007081021746649/5000000000000000 : ℝ) by norm_num, show 1+2*(305519398861402259/100000000000000000000 : ℝ)=(50305519398861402259/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (784896469991036899/785000000000000000 : ℝ)*(X 1 0+X 2 0)+(442552958189/149150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4413/1024 : ℝ)) (lo := (2223/100000 : ℝ)) (hi := (26087/100000 : ℝ)) (c := (784896469991036899/785000000000000000 : ℝ)) (alpha := (442552958189/149150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (784896469991036899/785000000000000000 : ℝ)*(X 0 1+X 2 1)+(442552958189/149150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4413/1024 : ℝ)) (lo := (2223/100000 : ℝ)) (hi := (26087/100000 : ℝ)) (c := (784896469991036899/785000000000000000 : ℝ)) (alpha := (442552958189/149150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (784896469991036899/785000000000000000 : ℝ)*(X 0 2+X 1 2)+(442552958189/149150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4413/1024 : ℝ)) (lo := (2223/100000 : ℝ)) (hi := (26087/100000 : ℝ)) (c := (784896469991036899/785000000000000000 : ℝ)) (alpha := (442552958189/149150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1913567701/10000000000 : ℝ)*X 0 0+(5595377103/10000000000 : ℝ)*X 0 1+(79425067/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1078863887/2000000000 : ℝ)*X 1 0+(-2184453683/10000000000 : ℝ)*X 1 1+(5083206097/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5394320939/10000000000 : ℝ)*X 2 0+(2541602209/5000000000 : ℝ)*X 2 1+(-17475631/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4272084129/10000000000 : ℝ)*X 0 0+(374532161/1000000000 : ℝ)*X 0 1+(194539033/400000000 : ℝ)*X 0 2+(4272084129/10000000000 : ℝ)*X 1 0+(374532161/1000000000 : ℝ)*X 1 1+(194539033/400000000 : ℝ)*X 1 2+(4272084129/10000000000 : ℝ)*X 2 0+(374532161/1000000000 : ℝ)*X 2 1+(194539033/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1913933053/10000000000 : ℝ)*X 0 0+(1017818699/2000000000 : ℝ)*X 0 1+(5589390029/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5260259259/10000000000 : ℝ)*X 1 0+(-1678269067/10000000000 : ℝ)*X 1 1+(5589390063/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5260259153/10000000000 : ℝ)*X 2 0+(698673753/1250000000 : ℝ)*X 2 1+(-209783659/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2136441197/5000000000 : ℝ)*X 0 0+(606327537/1250000000 : ℝ)*X 0 1+(1879194807/5000000000 : ℝ)*X 0 2+(2136441197/5000000000 : ℝ)*X 1 0+(606327537/1250000000 : ℝ)*X 1 1+(1879194807/5000000000 : ℝ)*X 1 2+(2136441197/5000000000 : ℝ)*X 2 0+(606327537/1250000000 : ℝ)*X 2 1+(1879194807/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (39001551846319254640864881/9812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (114935481/20000000000000 : ℝ)*(base19) + (1031455763/100000000000000 : ℝ)*(base23) + (23934619/50000000000000 : ℝ)*(upper3) + (11813289/25000000000000 : ℝ)*(upper4) + (9156559/100000000000000 : ℝ)*(upper5) + (355853221247073/25000000000000 : ℝ)*(major0) + (355853221247073/25000000000000 : ℝ)*(major1) + (355853221247073/25000000000000 : ℝ)*(major2) + (488119017658463/25000000000000 : ℝ)*(sp0) + (39049742202567/2000000000000 : ℝ)*(sp1) + (244060831668749/12500000000000 : ℝ)*(sp2) + (447166994449307/50000000000000 : ℝ)*(sp3) + (45367859/390625000000 : ℝ)*(sp4) + (1981891431/50000000000000 : ℝ)*(sp7) + (223584488170369/25000000000000 : ℝ)*(f.failure) + (390497536961151/20000000000000 : ℝ)*(f.sum) + (2768924544163/7457500000000000000000000000 : ℝ)*base65 + (1394726488562114087/372875000000000000000000000000000 : ℝ)*base68 + (4183060935662864087/372875000000000000000000000000000 : ℝ)*base70 + (1228886661730614087/372875000000000000000000000000000 : ℝ)*base72 + (32278766820473/7457500000000000000000000000 : ℝ)*base73 + (851255930722885913/372875000000000000000000000000000 : ℝ)*base75 + (1533520399525135913/372875000000000000000000000000000 : ℝ)*base77 + (1841807126044614087/372875000000000000000000000000000 : ℝ)*base80 + (33303831842047/7457500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (332291/1250000000000000000000 : ℝ)*base89 + (332291/1250000000000000000000 : ℝ)*base91 + (332291/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (981673228189038196937415681/186437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (242405799/20000000000000 : ℝ)*(base19) + (1200157907/100000000000000 : ℝ)*(base23) + (28945137/20000000000000 : ℝ)*(upper3) + (18070203/100000000000000 : ℝ)*(lower4) + (100380519/100000000000000 : ℝ)*(upper5) + (728592877016367/50000000000000 : ℝ)*(major0) + (728592877016367/50000000000000 : ℝ)*(major1) + (728592877016367/50000000000000 : ℝ)*(major2) + (7836063983/100000000000000 : ℝ)*(sp1) + (304107903/4000000000000 : ℝ)*(sp2) + (99940685252369/5000000000000 : ℝ)*(sp4) + (999402328477201/50000000000000 : ℝ)*(sp5) + (999402451095949/50000000000000 : ℝ)*(sp6) + (45777881375191/5000000000000 : ℝ)*(sp7) + (45777881375191/5000000000000 : ℝ)*(f.failure) + (99940685252369/5000000000000 : ℝ)*(f.sum) + (2041996787647/932187500000000000000000000 : ℝ)*base65 + (54879573074107273/745750000000000000000000000000000 : ℝ)*base68 + (2974248961434107273/745750000000000000000000000000000 : ℝ)*base70 + (666529905353642727/745750000000000000000000000000000 : ℝ)*base71 + (20997165876197/14915000000000000000000000000 : ℝ)*base73 + (3351626544141857273/745750000000000000000000000000000 : ℝ)*base76 + (2064591239363357273/745750000000000000000000000000000 : ℝ)*base78 + (1656690019665607273/745750000000000000000000000000000 : ℝ)*base80 + (7270722069133/14915000000000000000000000000 : ℝ)*base82 + (740549/250000000000000000000 : ℝ)*base89 + (740549/250000000000000000000 : ℝ)*base91 + (740549/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1454_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79579139/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26087/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2223/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3927/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18683/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1454_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1454_s2_0 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-388976367/2000000000 : ℝ)*x 0 + (5452731667/10000000000 : ℝ)*x 1 + (2602832793/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (388976367/2000000000 : ℝ)^2207 ≤ (593011107883/5000000000000 : ℝ)^1695 := by
    have hnat : (388976367 : ℕ)^2207*5000000000000^1695 ≤ 593011107883^1695*2000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      388976367 2000000000 593011107883 5000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5452731667/10000000000 : ℝ)^2207 ≤ (45399858523591/100000000000000 : ℝ)^1695 := by
    have hnat : (5452731667 : ℕ)^2207*100000000000000^1695 ≤ 45399858523591^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5452731667 10000000000 45399858523591 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2602832793/5000000000 : ℝ)^2207 ≤ (2671244956243/6250000000000 : ℝ)^1695 := by
    have hnat : (2602832793 : ℕ)^2207*6250000000000^1695 ≤ 2671244956243^1695*5000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2602832793 5000000000 2671244956243 6250000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-388976367/2000000000 : ℝ), (5452731667/10000000000 : ℝ), (2602832793/5000000000 : ℝ)] ![(593011107883/5000000000000 : ℝ), (45399858523591/100000000000000 : ℝ), (2671244956243/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-388976367/2000000000 : ℝ)|^2207 ≤ (593011107883/5000000000000 : ℝ)^1695
        have hw : |(-388976367/2000000000 : ℝ)|=(388976367/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5452731667/10000000000 : ℝ)|^2207 ≤ (45399858523591/100000000000000 : ℝ)^1695
        have hw : |(5452731667/10000000000 : ℝ)|=(5452731667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2602832793/5000000000 : ℝ)|^2207 ≤ (2671244956243/6250000000000 : ℝ)^1695
        have hw : |(2602832793/5000000000 : ℝ)|=(2602832793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s2_1 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1339645097/2500000000 : ℝ)*x 0 + (-2071860157/10000000000 : ℝ)*x 1 + (325354099/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1339645097/2500000000 : ℝ)^2207 ≤ (44381828516981/100000000000000 : ℝ)^1695 := by
    have hnat : (1339645097 : ℕ)^2207*100000000000000^1695 ≤ 44381828516981^1695*2500000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1339645097 2500000000 44381828516981 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2071860157/10000000000 : ℝ)^2207 ≤ (12878252184753/100000000000000 : ℝ)^1695 := by
    have hnat : (2071860157 : ℕ)^2207*100000000000000^1695 ≤ 12878252184753^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2071860157 10000000000 12878252184753 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (325354099/625000000 : ℝ)^2207 ≤ (42739919278507/100000000000000 : ℝ)^1695 := by
    have hnat : (325354099 : ℕ)^2207*100000000000000^1695 ≤ 42739919278507^1695*625000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325354099 625000000 42739919278507 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1339645097/2500000000 : ℝ), (-2071860157/10000000000 : ℝ), (325354099/625000000 : ℝ)] ![(44381828516981/100000000000000 : ℝ), (12878252184753/100000000000000 : ℝ), (42739919278507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1339645097/2500000000 : ℝ)|^2207 ≤ (44381828516981/100000000000000 : ℝ)^1695
        have hw : |(1339645097/2500000000 : ℝ)|=(1339645097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2071860157/10000000000 : ℝ)|^2207 ≤ (12878252184753/100000000000000 : ℝ)^1695
        have hw : |(-2071860157/10000000000 : ℝ)|=(2071860157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(325354099/625000000 : ℝ)|^2207 ≤ (42739919278507/100000000000000 : ℝ)^1695
        have hw : |(325354099/625000000 : ℝ)|=(325354099/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s2_2 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (535858053/1000000000 : ℝ)*x 0 + (5205665417/10000000000 : ℝ)*x 1 + (-2071860189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535858053/1000000000 : ℝ)^2207 ≤ (22190915024169/50000000000000 : ℝ)^1695 := by
    have hnat : (535858053 : ℕ)^2207*50000000000000^1695 ≤ 22190915024169^1695*1000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535858053 1000000000 22190915024169 50000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5205665417/10000000000 : ℝ)^2207 ≤ (21369958746613/50000000000000 : ℝ)^1695 := by
    have hnat : (5205665417 : ℕ)^2207*50000000000000^1695 ≤ 21369958746613^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5205665417 10000000000 21369958746613 50000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2071860189/10000000000 : ℝ)^2207 ≤ (643912622187/5000000000000 : ℝ)^1695 := by
    have hnat : (2071860189 : ℕ)^2207*5000000000000^1695 ≤ 643912622187^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2071860189 10000000000 643912622187 5000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535858053/1000000000 : ℝ), (5205665417/10000000000 : ℝ), (-2071860189/10000000000 : ℝ)] ![(22190915024169/50000000000000 : ℝ), (21369958746613/50000000000000 : ℝ), (643912622187/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535858053/1000000000 : ℝ)|^2207 ≤ (22190915024169/50000000000000 : ℝ)^1695
        have hw : |(535858053/1000000000 : ℝ)|=(535858053/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5205665417/10000000000 : ℝ)|^2207 ≤ (21369958746613/50000000000000 : ℝ)^1695
        have hw : |(5205665417/10000000000 : ℝ)|=(5205665417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2071860189/10000000000 : ℝ)|^2207 ≤ (643912622187/5000000000000 : ℝ)^1695
        have hw : |(-2071860189/10000000000 : ℝ)|=(2071860189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s2_3 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (536780581/1250000000 : ℝ)*x 0 + (4032073139/10000000000 : ℝ)*x 1 + (914291887/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536780581/1250000000 : ℝ)^2207 ≤ (4158194312793/12500000000000 : ℝ)^1695 := by
    have hnat : (536780581 : ℕ)^2207*12500000000000^1695 ≤ 4158194312793^1695*1250000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536780581 1250000000 4158194312793 12500000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4032073139/10000000000 : ℝ)^2207 ≤ (3830737486467/12500000000000 : ℝ)^1695 := by
    have hnat : (4032073139 : ℕ)^2207*12500000000000^1695 ≤ 3830737486467^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4032073139 10000000000 3830737486467 12500000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (914291887/2000000000 : ℝ)^2207 ≤ (36088545596121/100000000000000 : ℝ)^1695 := by
    have hnat : (914291887 : ℕ)^2207*100000000000000^1695 ≤ 36088545596121^1695*2000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      914291887 2000000000 36088545596121 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536780581/1250000000 : ℝ), (4032073139/10000000000 : ℝ), (914291887/2000000000 : ℝ)] ![(4158194312793/12500000000000 : ℝ), (3830737486467/12500000000000 : ℝ), (36088545596121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536780581/1250000000 : ℝ)|^2207 ≤ (4158194312793/12500000000000 : ℝ)^1695
        have hw : |(536780581/1250000000 : ℝ)|=(536780581/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4032073139/10000000000 : ℝ)|^2207 ≤ (3830737486467/12500000000000 : ℝ)^1695
        have hw : |(4032073139/10000000000 : ℝ)|=(4032073139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(914291887/2000000000 : ℝ)|^2207 ≤ (36088545596121/100000000000000 : ℝ)^1695
        have hw : |(914291887/2000000000 : ℝ)|=(914291887/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s2_4 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-972461151/5000000000 : ℝ)*x 0 + (5207045803/10000000000 : ℝ)*x 1 + (5451340901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (972461151/5000000000 : ℝ)^2207 ≤ (1186054347533/10000000000000 : ℝ)^1695 := by
    have hnat : (972461151 : ℕ)^2207*10000000000000^1695 ≤ 1186054347533^1695*5000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      972461151 5000000000 1186054347533 10000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5207045803/10000000000 : ℝ)^2207 ≤ (42754674830277/100000000000000 : ℝ)^1695 := by
    have hnat : (5207045803 : ℕ)^2207*100000000000000^1695 ≤ 42754674830277^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5207045803 10000000000 42754674830277 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5451340901/10000000000 : ℝ)^2207 ≤ (45384781683189/100000000000000 : ℝ)^1695 := by
    have hnat : (5451340901 : ℕ)^2207*100000000000000^1695 ≤ 45384781683189^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5451340901 10000000000 45384781683189 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-972461151/5000000000 : ℝ), (5207045803/10000000000 : ℝ), (5451340901/10000000000 : ℝ)] ![(1186054347533/10000000000000 : ℝ), (42754674830277/100000000000000 : ℝ), (45384781683189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-972461151/5000000000 : ℝ)|^2207 ≤ (1186054347533/10000000000000 : ℝ)^1695
        have hw : |(-972461151/5000000000 : ℝ)|=(972461151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5207045803/10000000000 : ℝ)|^2207 ≤ (42754674830277/100000000000000 : ℝ)^1695
        have hw : |(5207045803/10000000000 : ℝ)|=(5207045803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5451340901/10000000000 : ℝ)|^2207 ≤ (45384781683189/100000000000000 : ℝ)^1695
        have hw : |(5451340901/10000000000 : ℝ)|=(5451340901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s2_5 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5294186937/10000000000 : ℝ)*x 0 + (-45654577/250000000 : ℝ)*x 1 + (2725671147/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294186937/10000000000 : ℝ)^2207 ≤ (5461082542031/12500000000000 : ℝ)^1695 := by
    have hnat : (5294186937 : ℕ)^2207*12500000000000^1695 ≤ 5461082542031^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294186937 10000000000 5461082542031 12500000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (45654577/250000000 : ℝ)^2207 ≤ (437061715039/4000000000000 : ℝ)^1695 := by
    have hnat : (45654577 : ℕ)^2207*4000000000000^1695 ≤ 437061715039^1695*250000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45654577 250000000 437061715039 4000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2725671147/5000000000 : ℝ)^2207 ≤ (22692398391833/50000000000000 : ℝ)^1695 := by
    have hnat : (2725671147 : ℕ)^2207*50000000000000^1695 ≤ 22692398391833^1695*5000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725671147 5000000000 22692398391833 50000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294186937/10000000000 : ℝ), (-45654577/250000000 : ℝ), (2725671147/5000000000 : ℝ)] ![(5461082542031/12500000000000 : ℝ), (437061715039/4000000000000 : ℝ), (22692398391833/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294186937/10000000000 : ℝ)|^2207 ≤ (5461082542031/12500000000000 : ℝ)^1695
        have hw : |(5294186937/10000000000 : ℝ)|=(5294186937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-45654577/250000000 : ℝ)|^2207 ≤ (437061715039/4000000000000 : ℝ)^1695
        have hw : |(-45654577/250000000 : ℝ)|=(45654577/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2725671147/5000000000 : ℝ)|^2207 ≤ (22692398391833/50000000000000 : ℝ)^1695
        have hw : |(2725671147/5000000000 : ℝ)|=(2725671147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s2_6 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (661773233/1250000000 : ℝ)*x 0 + (681417693/1250000000 : ℝ)*x 1 + (-1826185603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661773233/1250000000 : ℝ)^2207 ≤ (43688648806979/100000000000000 : ℝ)^1695 := by
    have hnat : (661773233 : ℕ)^2207*100000000000000^1695 ≤ 43688648806979^1695*1250000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661773233 1250000000 43688648806979 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (681417693/1250000000 : ℝ)^2207 ≤ (45384788653473/100000000000000 : ℝ)^1695 := by
    have hnat : (681417693 : ℕ)^2207*100000000000000^1695 ≤ 45384788653473^1695*1250000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681417693 1250000000 45384788653473 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1826185603/10000000000 : ℝ)^2207 ≤ (10926562531671/100000000000000 : ℝ)^1695 := by
    have hnat : (1826185603 : ℕ)^2207*100000000000000^1695 ≤ 10926562531671^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1826185603 10000000000 10926562531671 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661773233/1250000000 : ℝ), (681417693/1250000000 : ℝ), (-1826185603/10000000000 : ℝ)] ![(43688648806979/100000000000000 : ℝ), (45384788653473/100000000000000 : ℝ), (10926562531671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661773233/1250000000 : ℝ)|^2207 ≤ (43688648806979/100000000000000 : ℝ)^1695
        have hw : |(661773233/1250000000 : ℝ)|=(661773233/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(681417693/1250000000 : ℝ)|^2207 ≤ (45384788653473/100000000000000 : ℝ)^1695
        have hw : |(681417693/1250000000 : ℝ)|=(681417693/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1826185603/10000000000 : ℝ)|^2207 ≤ (10926562531671/100000000000000 : ℝ)^1695
        have hw : |(-1826185603/10000000000 : ℝ)|=(1826185603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s2_7 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2147167247/5000000000 : ℝ)*x 0 + (2284224897/5000000000 : ℝ)*x 1 + (4035106883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2147167247/5000000000 : ℝ)^2207 ≤ (33266460737141/100000000000000 : ℝ)^1695 := by
    have hnat : (2147167247 : ℕ)^2207*100000000000000^1695 ≤ 33266460737141^1695*5000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147167247 5000000000 33266460737141 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2284224897/5000000000 : ℝ)^2207 ≤ (180288064191/500000000000 : ℝ)^1695 := by
    have hnat : (2284224897 : ℕ)^2207*500000000000^1695 ≤ 180288064191^1695*5000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2284224897 5000000000 180288064191 500000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4035106883/10000000000 : ℝ)^2207 ≤ (30675926403263/100000000000000 : ℝ)^1695 := by
    have hnat : (4035106883 : ℕ)^2207*100000000000000^1695 ≤ 30675926403263^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4035106883 10000000000 30675926403263 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2147167247/5000000000 : ℝ), (2284224897/5000000000 : ℝ), (4035106883/10000000000 : ℝ)] ![(33266460737141/100000000000000 : ℝ), (180288064191/500000000000 : ℝ), (30675926403263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2147167247/5000000000 : ℝ)|^2207 ≤ (33266460737141/100000000000000 : ℝ)^1695
        have hw : |(2147167247/5000000000 : ℝ)|=(2147167247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2284224897/5000000000 : ℝ)|^2207 ≤ (180288064191/500000000000 : ℝ)^1695
        have hw : |(2284224897/5000000000 : ℝ)|=(2284224897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4035106883/10000000000 : ℝ)|^2207 ≤ (30675926403263/100000000000000 : ℝ)^1695
        have hw : |(4035106883/10000000000 : ℝ)|=(4035106883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1454_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79579139/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18683/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3927/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10497/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7863/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18683/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3927/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18683/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3927/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18683/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3927/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18683/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3927/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18683/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3927/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18683/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3927/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3927/50000 : ℝ) ^ (4413/1024 : ℝ) ≤ (108192348689619/6250000000000000000 : ℝ) := by
    have hpowers : (3927/50000 : ℝ)^4413 ≤ (108192348689619/6250000000000000000 : ℝ)^1024 := by
      have hnat : (3927 : ℕ)^4413*6250000000000000000^1024 ≤ 108192348689619^1024*50000^4413 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3927 50000 108192348689619 6250000000000000000 4413 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3927/50000 : ℝ)) (X := (108192348689619/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4413 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18683/100000 : ℝ) ^ (4413/1024 : ℝ) ≤ (18121242177472677/25000000000000000000 : ℝ) := by
    have hpowers : (18683/100000 : ℝ)^4413 ≤ (18121242177472677/25000000000000000000 : ℝ)^1024 := by
      have hnat : (18683 : ℕ)^4413*25000000000000000000^1024 ≤ 18121242177472677^1024*100000^4413 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18683 100000 18121242177472677 25000000000000000000 4413 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18683/100000 : ℝ)) (X := (18121242177472677/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4413 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125108192348689619/3125000000000000000 : ℝ) ≤ (5000040167683577/5000000000000000 : ℝ) ^ (4413/1024 : ℝ) := by
    have hpowers : (3125108192348689619/3125000000000000000 : ℝ)^1024 ≤ (5000040167683577/5000000000000000 : ℝ)^4413 := by
      have hnat : (3125108192348689619 : ℕ)^1024*5000000000000000^4413 ≤ 5000040167683577^4413*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125108192348689619 3125000000000000000 5000040167683577 5000000000000000 1024 4413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000040167683577/5000000000000000 : ℝ)) (X := (3125108192348689619/3125000000000000000 : ℝ)) (by norm_num) 4413 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25018554011572231153/25000000000000000000 : ℝ) ≤ (5000860815586009/5000000000000000 : ℝ) ^ (4413/1024 : ℝ) := by
    have hpowers : (25018554011572231153/25000000000000000000 : ℝ)^1024 ≤ (5000860815586009/5000000000000000 : ℝ)^4413 := by
      have hnat : (25018554011572231153 : ℕ)^1024*5000000000000000^4413 ≤ 5000860815586009^4413*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018554011572231153 25000000000000000000 5000860815586009 5000000000000000 1024 4413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000860815586009/5000000000000000 : ℝ)) (X := (25018554011572231153/25000000000000000000 : ℝ)) (by norm_num) 4413 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12518121242177472677/12500000000000000000 : ℝ) ≤ (5001681463488441/5000000000000000 : ℝ) ^ (4413/1024 : ℝ) := by
    have hpowers : (12518121242177472677/12500000000000000000 : ℝ)^1024 ≤ (5001681463488441/5000000000000000 : ℝ)^4413 := by
      have hnat : (12518121242177472677 : ℕ)^1024*5000000000000000^4413 ≤ 5001681463488441^4413*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12518121242177472677 12500000000000000000 5001681463488441 5000000000000000 1024 4413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001681463488441/5000000000000000 : ℝ)) (X := (12518121242177472677/12500000000000000000 : ℝ)) (by norm_num) 4413 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(108192348689619/6250000000000000000 : ℝ) ≤ ((454895329736084483/455000000000000000 : ℝ)+2*(25645246951/16920312500000 : ℝ)*(3927/50000 : ℝ))^(4413/1024 : ℝ) := by
    rw [show (454895329736084483/455000000000000000 : ℝ)+2*(25645246951/16920312500000 : ℝ)*(3927/50000 : ℝ)=(5000040167683577/5000000000000000 : ℝ) by norm_num, show 1+2*(108192348689619/6250000000000000000 : ℝ)=(3125108192348689619/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18121242177472677/25000000000000000000 : ℝ)+(108192348689619/6250000000000000000 : ℝ) ≤ ((454895329736084483/455000000000000000 : ℝ)+(25645246951/16920312500000 : ℝ)*((18683/100000 : ℝ)+(3927/50000 : ℝ)))^(4413/1024 : ℝ) := by
    rw [show (454895329736084483/455000000000000000 : ℝ)+(25645246951/16920312500000 : ℝ)*((18683/100000 : ℝ)+(3927/50000 : ℝ))=(5000860815586009/5000000000000000 : ℝ) by norm_num, show 1+(18121242177472677/25000000000000000000 : ℝ)+(108192348689619/6250000000000000000 : ℝ)=(25018554011572231153/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18121242177472677/25000000000000000000 : ℝ) ≤ ((454895329736084483/455000000000000000 : ℝ)+2*(25645246951/16920312500000 : ℝ)*(18683/100000 : ℝ))^(4413/1024 : ℝ) := by
    rw [show (454895329736084483/455000000000000000 : ℝ)+2*(25645246951/16920312500000 : ℝ)*(18683/100000 : ℝ)=(5001681463488441/5000000000000000 : ℝ) by norm_num, show 1+2*(18121242177472677/25000000000000000000 : ℝ)=(12518121242177472677/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (454895329736084483/455000000000000000 : ℝ)*(X 1 0+X 2 0)+(25645246951/16920312500000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4413/1024 : ℝ)) (lo := (3927/50000 : ℝ)) (hi := (18683/100000 : ℝ)) (c := (454895329736084483/455000000000000000 : ℝ)) (alpha := (25645246951/16920312500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (454895329736084483/455000000000000000 : ℝ)*(X 0 1+X 2 1)+(25645246951/16920312500000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4413/1024 : ℝ)) (lo := (3927/50000 : ℝ)) (hi := (18683/100000 : ℝ)) (c := (454895329736084483/455000000000000000 : ℝ)) (alpha := (25645246951/16920312500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (454895329736084483/455000000000000000 : ℝ)*(X 0 2+X 1 2)+(25645246951/16920312500000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4413/1024 : ℝ)) (lo := (3927/50000 : ℝ)) (hi := (18683/100000 : ℝ)) (c := (454895329736084483/455000000000000000 : ℝ)) (alpha := (25645246951/16920312500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-388976367/2000000000 : ℝ)*X 0 0+(5452731667/10000000000 : ℝ)*X 0 1+(2602832793/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1339645097/2500000000 : ℝ)*X 1 0+(-2071860157/10000000000 : ℝ)*X 1 1+(325354099/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((535858053/1000000000 : ℝ)*X 2 0+(5205665417/10000000000 : ℝ)*X 2 1+(-2071860189/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((536780581/1250000000 : ℝ)*X 0 0+(4032073139/10000000000 : ℝ)*X 0 1+(914291887/2000000000 : ℝ)*X 0 2+(536780581/1250000000 : ℝ)*X 1 0+(4032073139/10000000000 : ℝ)*X 1 1+(914291887/2000000000 : ℝ)*X 1 2+(536780581/1250000000 : ℝ)*X 2 0+(4032073139/10000000000 : ℝ)*X 2 1+(914291887/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-972461151/5000000000 : ℝ)*X 0 0+(5207045803/10000000000 : ℝ)*X 0 1+(5451340901/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294186937/10000000000 : ℝ)*X 1 0+(-45654577/250000000 : ℝ)*X 1 1+(2725671147/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((661773233/1250000000 : ℝ)*X 2 0+(681417693/1250000000 : ℝ)*X 2 1+(-1826185603/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2147167247/5000000000 : ℝ)*X 0 0+(2284224897/5000000000 : ℝ)*X 0 1+(4035106883/10000000000 : ℝ)*X 0 2+(2147167247/5000000000 : ℝ)*X 1 0+(2284224897/5000000000 : ℝ)*X 1 1+(4035106883/10000000000 : ℝ)*X 1 2+(2147167247/5000000000 : ℝ)*X 2 0+(2284224897/5000000000 : ℝ)*X 2 1+(4035106883/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9010494162239418841385831583/1353625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (142126967/10000000000000 : ℝ)*(base19) + (289235331/20000000000000 : ℝ)*(base23) + (11032111/25000000000000 : ℝ)*(lower2) + (9705551/5000000000000 : ℝ)*(upper3) + (30088021/25000000000000 : ℝ)*(upper5) + (1475379572258407/50000000000000 : ℝ)*(major0) + (1475379572258407/50000000000000 : ℝ)*(major1) + (1475379572258407/50000000000000 : ℝ)*(major2) + (202376023151613/5000000000000 : ℝ)*(sp0) + (2023769421828827/50000000000000 : ℝ)*(sp1) + (4047538818750669/100000000000000 : ℝ)*(sp2) + (1853967660539229/100000000000000 : ℝ)*(sp3) + (19801895063/100000000000000 : ℝ)*(sp4) + (2028336307/20000000000000 : ℝ)*(sp7) + (463494450555191/25000000000000 : ℝ)*(f.failure) + (1011885066231831/25000000000000 : ℝ)*(f.sum) + (45076444609669/13536250000000000000000000000 : ℝ)*base65 + (1655077444206594703/208250000000000000000000000000000 : ℝ)*base67 + (2250904536124344703/208250000000000000000000000000000 : ℝ)*base69 + (99092024726405297/208250000000000000000000000000000 : ℝ)*base72 + (19762637929561/54145000000000000000000000000 : ℝ)*base73 + (7155767067094703/208250000000000000000000000000000 : ℝ)*base75 + (1792362586925094703/208250000000000000000000000000000 : ℝ)*base77 + (963409317796405297/208250000000000000000000000000000 : ℝ)*base80 + (267008598853341/54145000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (3239451/1250000000000000000000 : ℝ)*base90 + (3239451/1250000000000000000000 : ℝ)*base92 + (3239451/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (914397799079359671225081/81250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1018602079/100000000000000 : ℝ)*(base19) + (121214371/25000000000000 : ℝ)*(base23) + (119142629/50000000000000 : ℝ)*(upper3) + (177539667/50000000000000 : ℝ)*(lower4) + (74604654062239/2500000000000 : ℝ)*(major0) + (74604654062239/2500000000000 : ℝ)*(major1) + (74604654062239/2500000000000 : ℝ)*(major2) + (32369834149/100000000000000 : ℝ)*(sp1) + (1554122121/100000000000000 : ℝ)*(sp2) + (4071119581/50000000000000 : ℝ)*(sp3) + (2046695886441193/50000000000000 : ℝ)*(sp4) + (2046679192223079/50000000000000 : ℝ)*(sp5) + (2046694866951391/50000000000000 : ℝ)*(sp6) + (1874972034720003/100000000000000 : ℝ)*(sp7) + (374996035391833/20000000000000 : ℝ)*(f.failure) + (2046695886441193/50000000000000 : ℝ)*(f.sum) + (3259921556109/773500000000000000000000000 : ℝ)*base66 + (18028702900397033/1487500000000000000000000000000 : ℝ)*base67 + (24063908317984533/1487500000000000000000000000000 : ℝ)*base69 + (16099309106622033/1487500000000000000000000000000 : ℝ)*base71 + (58481704313/61880000000000000000000000 : ℝ)*base74 + (26080713353509533/1487500000000000000000000000000 : ℝ)*base75 + (13808455100622033/1487500000000000000000000000000 : ℝ)*base77 + (14125147526234533/1487500000000000000000000000000 : ℝ)*base79 + (444758115083/193375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (2228213/1000000000000000000000 : ℝ)*base90 + (2228213/1000000000000000000000 : ℝ)*base92 + (2228213/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1454_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79579139/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18683/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3927/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10497/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7863/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1454_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1454_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79579139/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10497/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7863/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1454_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1454_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1454_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79579139/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10497/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7863/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1454_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
