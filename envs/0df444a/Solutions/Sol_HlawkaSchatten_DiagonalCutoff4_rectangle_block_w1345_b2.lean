-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1345_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:05:29.900982+00:00
-- url     : https://prove2.me/submissions/59316f6b-6543-4119-aa3e-b6b756f29763

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
theorem support_rectangle_w1345_s6_0 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-510344663/2500000000 : ℝ)*x 0 + (5412567661/10000000000 : ℝ)*x 1 + (1311171659/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (510344663/2500000000 : ℝ)^4305 ≤ (99458229203/800000000000 : ℝ)^3281 := by
    have hnat : (510344663 : ℕ)^4305*800000000000^3281 ≤ 99458229203^3281*2500000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      510344663 2500000000 99458229203 800000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412567661/10000000000 : ℝ)^4305 ≤ (22344391533607/50000000000000 : ℝ)^3281 := by
    have hnat : (5412567661 : ℕ)^4305*50000000000000^3281 ≤ 22344391533607^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412567661 10000000000 22344391533607 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311171659/2500000000 : ℝ)^4305 ≤ (42878938264969/100000000000000 : ℝ)^3281 := by
    have hnat : (1311171659 : ℕ)^4305*100000000000000^3281 ≤ 42878938264969^3281*2500000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311171659 2500000000 42878938264969 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-510344663/2500000000 : ℝ), (5412567661/10000000000 : ℝ), (1311171659/2500000000 : ℝ)] ![(99458229203/800000000000 : ℝ), (22344391533607/50000000000000 : ℝ), (42878938264969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-510344663/2500000000 : ℝ)|^4305 ≤ (99458229203/800000000000 : ℝ)^3281
        have hw : |(-510344663/2500000000 : ℝ)|=(510344663/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412567661/10000000000 : ℝ)|^4305 ≤ (22344391533607/50000000000000 : ℝ)^3281
        have hw : |(5412567661/10000000000 : ℝ)|=(5412567661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311171659/2500000000 : ℝ)|^4305 ≤ (42878938264969/100000000000000 : ℝ)^3281
        have hw : |(1311171659/2500000000 : ℝ)|=(1311171659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s6_1 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337237553/2500000000 : ℝ)*x 0 + (-1063456549/5000000000 : ℝ)*x 1 + (1311171659/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337237553/2500000000 : ℝ)^4305 ≤ (22000430763481/50000000000000 : ℝ)^3281 := by
    have hnat : (1337237553 : ℕ)^4305*50000000000000^3281 ≤ 22000430763481^3281*2500000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337237553 2500000000 22000430763481 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1063456549/5000000000 : ℝ)^4305 ≤ (2624040039547/20000000000000 : ℝ)^3281 := by
    have hnat : (1063456549 : ℕ)^4305*20000000000000^3281 ≤ 2624040039547^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063456549 5000000000 2624040039547 20000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311171659/2500000000 : ℝ)^4305 ≤ (42878938264969/100000000000000 : ℝ)^3281 := by
    have hnat : (1311171659 : ℕ)^4305*100000000000000^3281 ≤ 42878938264969^3281*2500000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311171659 2500000000 42878938264969 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337237553/2500000000 : ℝ), (-1063456549/5000000000 : ℝ), (1311171659/2500000000 : ℝ)] ![(22000430763481/50000000000000 : ℝ), (2624040039547/20000000000000 : ℝ), (42878938264969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337237553/2500000000 : ℝ)|^4305 ≤ (22000430763481/50000000000000 : ℝ)^3281
        have hw : |(1337237553/2500000000 : ℝ)|=(1337237553/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1063456549/5000000000 : ℝ)|^4305 ≤ (2624040039547/20000000000000 : ℝ)^3281
        have hw : |(-1063456549/5000000000 : ℝ)|=(1063456549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311171659/2500000000 : ℝ)|^4305 ≤ (42878938264969/100000000000000 : ℝ)^3281
        have hw : |(1311171659/2500000000 : ℝ)|=(1311171659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s6_2 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337237553/2500000000 : ℝ)*x 0 + (1311171659/2500000000 : ℝ)*x 1 + (-2126913097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337237553/2500000000 : ℝ)^4305 ≤ (22000430763481/50000000000000 : ℝ)^3281 := by
    have hnat : (1337237553 : ℕ)^4305*50000000000000^3281 ≤ 22000430763481^3281*2500000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337237553 2500000000 22000430763481 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311171659/2500000000 : ℝ)^4305 ≤ (42878938264969/100000000000000 : ℝ)^3281 := by
    have hnat : (1311171659 : ℕ)^4305*100000000000000^3281 ≤ 42878938264969^3281*2500000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311171659 2500000000 42878938264969 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2126913097/10000000000 : ℝ)^4305 ≤ (13120200189641/100000000000000 : ℝ)^3281 := by
    have hnat : (2126913097 : ℕ)^4305*100000000000000^3281 ≤ 13120200189641^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126913097 10000000000 13120200189641 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337237553/2500000000 : ℝ), (1311171659/2500000000 : ℝ), (-2126913097/10000000000 : ℝ)] ![(22000430763481/50000000000000 : ℝ), (42878938264969/100000000000000 : ℝ), (13120200189641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337237553/2500000000 : ℝ)|^4305 ≤ (22000430763481/50000000000000 : ℝ)^3281
        have hw : |(1337237553/2500000000 : ℝ)|=(1337237553/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311171659/2500000000 : ℝ)|^4305 ≤ (42878938264969/100000000000000 : ℝ)^3281
        have hw : |(1311171659/2500000000 : ℝ)|=(1311171659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2126913097/10000000000 : ℝ)|^4305 ≤ (13120200189641/100000000000000 : ℝ)^3281
        have hw : |(-2126913097/10000000000 : ℝ)|=(2126913097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s6_3 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (865166777/2000000000 : ℝ)*x 0 + (2076579153/5000000000 : ℝ)*x 1 + (563149277/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (865166777/2000000000 : ℝ)^4305 ≤ (3330329817873/10000000000000 : ℝ)^3281 := by
    have hnat : (865166777 : ℕ)^4305*10000000000000^3281 ≤ 3330329817873^3281*2000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      865166777 2000000000 3330329817873 10000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2076579153/5000000000 : ℝ)^4305 ≤ (31569988403947/100000000000000 : ℝ)^3281 := by
    have hnat : (2076579153 : ℕ)^4305*100000000000000^3281 ≤ 31569988403947^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2076579153 5000000000 31569988403947 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (563149277/1250000000 : ℝ)^4305 ≤ (8781678350849/25000000000000 : ℝ)^3281 := by
    have hnat : (563149277 : ℕ)^4305*25000000000000^3281 ≤ 8781678350849^3281*1250000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563149277 1250000000 8781678350849 25000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(865166777/2000000000 : ℝ), (2076579153/5000000000 : ℝ), (563149277/1250000000 : ℝ)] ![(3330329817873/10000000000000 : ℝ), (31569988403947/100000000000000 : ℝ), (8781678350849/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(865166777/2000000000 : ℝ)|^4305 ≤ (3330329817873/10000000000000 : ℝ)^3281
        have hw : |(865166777/2000000000 : ℝ)|=(865166777/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2076579153/5000000000 : ℝ)|^4305 ≤ (31569988403947/100000000000000 : ℝ)^3281
        have hw : |(2076579153/5000000000 : ℝ)|=(2076579153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(563149277/1250000000 : ℝ)|^4305 ≤ (8781678350849/25000000000000 : ℝ)^3281
        have hw : |(563149277/1250000000 : ℝ)|=(563149277/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s6_4 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-510347701/2500000000 : ℝ)*x 0 + (5245287921/10000000000 : ℝ)*x 1 + (216478531/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (510347701/2500000000 : ℝ)^4305 ≤ (12432375755523/100000000000000 : ℝ)^3281 := by
    have hnat : (510347701 : ℕ)^4305*100000000000000^3281 ≤ 12432375755523^3281*2500000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      510347701 2500000000 12432375755523 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245287921/10000000000 : ℝ)^4305 ≤ (42885388559463/100000000000000 : ℝ)^3281 := by
    have hnat : (5245287921 : ℕ)^4305*100000000000000^3281 ≤ 42885388559463^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245287921 10000000000 42885388559463 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216478531/400000000 : ℝ)^4305 ≤ (44682235666169/100000000000000 : ℝ)^3281 := by
    have hnat : (216478531 : ℕ)^4305*100000000000000^3281 ≤ 44682235666169^3281*400000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216478531 400000000 44682235666169 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-510347701/2500000000 : ℝ), (5245287921/10000000000 : ℝ), (216478531/400000000 : ℝ)] ![(12432375755523/100000000000000 : ℝ), (42885388559463/100000000000000 : ℝ), (44682235666169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-510347701/2500000000 : ℝ)|^4305 ≤ (12432375755523/100000000000000 : ℝ)^3281
        have hw : |(-510347701/2500000000 : ℝ)|=(510347701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245287921/10000000000 : ℝ)|^4305 ≤ (42885388559463/100000000000000 : ℝ)^3281
        have hw : |(5245287921/10000000000 : ℝ)|=(5245287921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216478531/400000000 : ℝ)|^4305 ≤ (44682235666169/100000000000000 : ℝ)^3281
        have hw : |(216478531/400000000 : ℝ)|=(216478531/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s6_5 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (212227717/400000000 : ℝ)*x 0 + (-1959636459/10000000000 : ℝ)*x 1 + (216478531/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212227717/400000000 : ℝ)^4305 ≤ (10883639315633/25000000000000 : ℝ)^3281 := by
    have hnat : (212227717 : ℕ)^4305*25000000000000^3281 ≤ 10883639315633^3281*400000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212227717 400000000 10883639315633 25000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1959636459/10000000000 : ℝ)^4305 ≤ (736450441339/6250000000000 : ℝ)^3281 := by
    have hnat : (1959636459 : ℕ)^4305*6250000000000^3281 ≤ 736450441339^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1959636459 10000000000 736450441339 6250000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216478531/400000000 : ℝ)^4305 ≤ (44682235666169/100000000000000 : ℝ)^3281 := by
    have hnat : (216478531 : ℕ)^4305*100000000000000^3281 ≤ 44682235666169^3281*400000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216478531 400000000 44682235666169 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212227717/400000000 : ℝ), (-1959636459/10000000000 : ℝ), (216478531/400000000 : ℝ)] ![(10883639315633/25000000000000 : ℝ), (736450441339/6250000000000 : ℝ), (44682235666169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212227717/400000000 : ℝ)|^4305 ≤ (10883639315633/25000000000000 : ℝ)^3281
        have hw : |(212227717/400000000 : ℝ)|=(212227717/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1959636459/10000000000 : ℝ)|^4305 ≤ (736450441339/6250000000000 : ℝ)^3281
        have hw : |(-1959636459/10000000000 : ℝ)|=(1959636459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216478531/400000000 : ℝ)|^4305 ≤ (44682235666169/100000000000000 : ℝ)^3281
        have hw : |(216478531/400000000 : ℝ)|=(216478531/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s6_6 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (212227717/400000000 : ℝ)*x 0 + (216478531/400000000 : ℝ)*x 1 + (-979818229/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212227717/400000000 : ℝ)^4305 ≤ (10883639315633/25000000000000 : ℝ)^3281 := by
    have hnat : (212227717 : ℕ)^4305*25000000000000^3281 ≤ 10883639315633^3281*400000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212227717 400000000 10883639315633 25000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216478531/400000000 : ℝ)^4305 ≤ (44682235666169/100000000000000 : ℝ)^3281 := by
    have hnat : (216478531 : ℕ)^4305*100000000000000^3281 ≤ 44682235666169^3281*400000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216478531 400000000 44682235666169 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (979818229/5000000000 : ℝ)^4305 ≤ (2356641410707/20000000000000 : ℝ)^3281 := by
    have hnat : (979818229 : ℕ)^4305*20000000000000^3281 ≤ 2356641410707^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      979818229 5000000000 2356641410707 20000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212227717/400000000 : ℝ), (216478531/400000000 : ℝ), (-979818229/5000000000 : ℝ)] ![(10883639315633/25000000000000 : ℝ), (44682235666169/100000000000000 : ℝ), (2356641410707/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212227717/400000000 : ℝ)|^4305 ≤ (10883639315633/25000000000000 : ℝ)^3281
        have hw : |(212227717/400000000 : ℝ)|=(212227717/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216478531/400000000 : ℝ)|^4305 ≤ (44682235666169/100000000000000 : ℝ)^3281
        have hw : |(216478531/400000000 : ℝ)|=(216478531/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-979818229/5000000000 : ℝ)|^4305 ≤ (2356641410707/20000000000000 : ℝ)^3281
        have hw : |(-979818229/5000000000 : ℝ)|=(979818229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s6_7 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2162929683/5000000000 : ℝ)*x 0 + (4503933359/10000000000 : ℝ)*x 1 + (2077212833/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2162929683/5000000000 : ℝ)^4305 ≤ (16651777787189/50000000000000 : ℝ)^3281 := by
    have hnat : (2162929683 : ℕ)^4305*50000000000000^3281 ≤ 16651777787189^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162929683 5000000000 16651777787189 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4503933359/10000000000 : ℝ)^4305 ≤ (35113814945509/100000000000000 : ℝ)^3281 := by
    have hnat : (4503933359 : ℕ)^4305*100000000000000^3281 ≤ 35113814945509^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503933359 10000000000 35113814945509 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2077212833/5000000000 : ℝ)^4305 ≤ (7895657366311/25000000000000 : ℝ)^3281 := by
    have hnat : (2077212833 : ℕ)^4305*25000000000000^3281 ≤ 7895657366311^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077212833 5000000000 7895657366311 25000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2162929683/5000000000 : ℝ), (4503933359/10000000000 : ℝ), (2077212833/5000000000 : ℝ)] ![(16651777787189/50000000000000 : ℝ), (35113814945509/100000000000000 : ℝ), (7895657366311/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2162929683/5000000000 : ℝ)|^4305 ≤ (16651777787189/50000000000000 : ℝ)^3281
        have hw : |(2162929683/5000000000 : ℝ)|=(2162929683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4503933359/10000000000 : ℝ)|^4305 ≤ (35113814945509/100000000000000 : ℝ)^3281
        have hw : |(4503933359/10000000000 : ℝ)|=(4503933359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2077212833/5000000000 : ℝ)|^4305 ≤ (7895657366311/25000000000000 : ℝ)^3281
        have hw : |(2077212833/5000000000 : ℝ)|=(2077212833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1345_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154846843/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14717/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2787/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2231/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1471/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14717/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2787/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14717/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2787/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14717/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2787/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14717/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2787/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14717/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2787/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14717/100000 : ℝ)*(X 0 2+X 1 2) := by
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
  have hpowlo : (2787/25000 : ℝ) ^ (269/64 : ℝ) ≤ (9891216837593219/100000000000000000000 : ℝ) := by
    have hpowers : (2787/25000 : ℝ)^269 ≤ (9891216837593219/100000000000000000000 : ℝ)^64 := by
      have hnat : (2787 : ℕ)^269*100000000000000000000^64 ≤ 9891216837593219^64*25000^269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2787 25000 9891216837593219 100000000000000000000 269 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2787/25000 : ℝ)) (X := (9891216837593219/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 269 64 (by norm_num) hpowers
    exact h
  have hpowhi : (14717/100000 : ℝ) ^ (269/64 : ℝ) ≤ (1986645921961847/6250000000000000000 : ℝ) := by
    have hpowers : (14717/100000 : ℝ)^269 ≤ (1986645921961847/6250000000000000000 : ℝ)^64 := by
      have hnat : (14717 : ℕ)^269*6250000000000000000^64 ≤ 1986645921961847^64*100000^269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14717 100000 1986645921961847 6250000000000000000 269 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14717/100000 : ℝ)) (X := (1986645921961847/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 269 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009891216837593219/50000000000000000000 : ℝ) ≤ (2000094124931641/2000000000000000 : ℝ) ^ (269/64 : ℝ) := by
    have hpowers : (50009891216837593219/50000000000000000000 : ℝ)^64 ≤ (2000094124931641/2000000000000000 : ℝ)^269 := by
      have hnat : (50009891216837593219 : ℕ)^64*2000000000000000^269 ≤ 2000094124931641^269*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009891216837593219 50000000000000000000 2000094124931641 2000000000000000 64 269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000094124931641/2000000000000000 : ℝ)) (X := (50009891216837593219/50000000000000000000 : ℝ)) (by norm_num) 269 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (100041677551588982771/100000000000000000000 : ℝ) ≤ (10000991427436937/10000000000000000 : ℝ) ^ (269/64 : ℝ) := by
    have hpowers : (100041677551588982771/100000000000000000000 : ℝ)^64 ≤ (10000991427436937/10000000000000000 : ℝ)^269 := by
      have hnat : (100041677551588982771 : ℕ)^64*10000000000000000^269 ≤ 10000991427436937^269*100000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100041677551588982771 100000000000000000000 10000991427436937 10000000000000000 64 269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000991427436937/10000000000000000 : ℝ)) (X := (100041677551588982771/100000000000000000000 : ℝ)) (by norm_num) 269 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (3126986645921961847/3125000000000000000 : ℝ) ≤ (10001512230215669/10000000000000000 : ℝ) ^ (269/64 : ℝ) := by
    have hpowers : (3126986645921961847/3125000000000000000 : ℝ)^64 ≤ (10001512230215669/10000000000000000 : ℝ)^269 := by
      have hnat : (3126986645921961847 : ℕ)^64*10000000000000000^269 ≤ 10001512230215669^269*3125000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126986645921961847 3125000000000000000 10001512230215669 10000000000000000 64 269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001512230215669/10000000000000000 : ℝ)) (X := (3126986645921961847/3125000000000000000 : ℝ)) (by norm_num) 269 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9891216837593219/100000000000000000000 : ℝ) ≤ ((35680067840650524973/35690000000000000000 : ℝ)+2*(130200694683/89225000000000 : ℝ)*(2787/25000 : ℝ))^(269/64 : ℝ) := by
    rw [show (35680067840650524973/35690000000000000000 : ℝ)+2*(130200694683/89225000000000 : ℝ)*(2787/25000 : ℝ)=(2000094124931641/2000000000000000 : ℝ) by norm_num, show 1+2*(9891216837593219/100000000000000000000 : ℝ)=(50009891216837593219/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1986645921961847/6250000000000000000 : ℝ)+(9891216837593219/100000000000000000000 : ℝ) ≤ ((35680067840650524973/35690000000000000000 : ℝ)+(130200694683/89225000000000 : ℝ)*((14717/100000 : ℝ)+(2787/25000 : ℝ)))^(269/64 : ℝ) := by
    rw [show (35680067840650524973/35690000000000000000 : ℝ)+(130200694683/89225000000000 : ℝ)*((14717/100000 : ℝ)+(2787/25000 : ℝ))=(10000991427436937/10000000000000000 : ℝ) by norm_num, show 1+(1986645921961847/6250000000000000000 : ℝ)+(9891216837593219/100000000000000000000 : ℝ)=(100041677551588982771/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1986645921961847/6250000000000000000 : ℝ) ≤ ((35680067840650524973/35690000000000000000 : ℝ)+2*(130200694683/89225000000000 : ℝ)*(14717/100000 : ℝ))^(269/64 : ℝ) := by
    rw [show (35680067840650524973/35690000000000000000 : ℝ)+2*(130200694683/89225000000000 : ℝ)*(14717/100000 : ℝ)=(10001512230215669/10000000000000000 : ℝ) by norm_num, show 1+2*(1986645921961847/6250000000000000000 : ℝ)=(3126986645921961847/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (35680067840650524973/35690000000000000000 : ℝ)*(X 1 0+X 2 0)+(130200694683/89225000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (269/64 : ℝ)) (lo := (2787/25000 : ℝ)) (hi := (14717/100000 : ℝ)) (c := (35680067840650524973/35690000000000000000 : ℝ)) (alpha := (130200694683/89225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (35680067840650524973/35690000000000000000 : ℝ)*(X 0 1+X 2 1)+(130200694683/89225000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (269/64 : ℝ)) (lo := (2787/25000 : ℝ)) (hi := (14717/100000 : ℝ)) (c := (35680067840650524973/35690000000000000000 : ℝ)) (alpha := (130200694683/89225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (35680067840650524973/35690000000000000000 : ℝ)*(X 0 2+X 1 2)+(130200694683/89225000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (269/64 : ℝ)) (lo := (2787/25000 : ℝ)) (hi := (14717/100000 : ℝ)) (c := (35680067840650524973/35690000000000000000 : ℝ)) (alpha := (130200694683/89225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-510344663/2500000000 : ℝ)*X 0 0+(5412567661/10000000000 : ℝ)*X 0 1+(1311171659/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337237553/2500000000 : ℝ)*X 1 0+(-1063456549/5000000000 : ℝ)*X 1 1+(1311171659/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337237553/2500000000 : ℝ)*X 2 0+(1311171659/2500000000 : ℝ)*X 2 1+(-2126913097/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((865166777/2000000000 : ℝ)*X 0 0+(2076579153/5000000000 : ℝ)*X 0 1+(563149277/1250000000 : ℝ)*X 0 2+(865166777/2000000000 : ℝ)*X 1 0+(2076579153/5000000000 : ℝ)*X 1 1+(563149277/1250000000 : ℝ)*X 1 2+(865166777/2000000000 : ℝ)*X 2 0+(2076579153/5000000000 : ℝ)*X 2 1+(563149277/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-510347701/2500000000 : ℝ)*X 0 0+(5245287921/10000000000 : ℝ)*X 0 1+(216478531/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((212227717/400000000 : ℝ)*X 1 0+(-1959636459/10000000000 : ℝ)*X 1 1+(216478531/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((212227717/400000000 : ℝ)*X 2 0+(216478531/400000000 : ℝ)*X 2 1+(-979818229/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2162929683/5000000000 : ℝ)*X 0 0+(4503933359/10000000000 : ℝ)*X 0 1+(2077212833/5000000000 : ℝ)*X 0 2+(2162929683/5000000000 : ℝ)*X 1 0+(4503933359/10000000000 : ℝ)*X 1 1+(2077212833/5000000000 : ℝ)*X 1 2+(2162929683/5000000000 : ℝ)*X 2 0+(4503933359/10000000000 : ℝ)*X 2 1+(2077212833/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (64240148710136001777923367/5576562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (2162918597/100000000000000 : ℝ)*(base19) + (403167131/20000000000000 : ℝ)*(base23) + (78673933/100000000000000 : ℝ)*(lower2) + (57839643/20000000000000 : ℝ)*(upper3) + (181486747/100000000000000 : ℝ)*(upper5) + (27491726878239/625000000000 : ℝ)*(major0) + (27491726878239/625000000000 : ℝ)*(major1) + (27491726878239/625000000000 : ℝ)*(major2) + (1489161363660489/25000000000000 : ℝ)*(sp0) + (744585936275693/12500000000000 : ℝ)*(sp1) + (2978343818644243/50000000000000 : ℝ)*(sp2) + (1420319877871939/50000000000000 : ℝ)*(sp3) + (8839696437/20000000000000 : ℝ)*(sp4) + (22808179521/100000000000000 : ℝ)*(sp7) + (2840662563923399/100000000000000 : ℝ)*(f.failure) + (297834482656207/5000000000000 : ℝ)*(f.sum) + (87133257331/44612500000000000000000000 : ℝ)*base66 + (88216192691112547/22306250000000000000000000000000 : ℝ)*base67 + (161434506140031297/22306250000000000000000000000000 : ℝ)*base69 + (33343686831837547/22306250000000000000000000000000 : ℝ)*base71 + (7630558360581/3569000000000000000000000000 : ℝ)*base73 + (78358887971949953/22306250000000000000000000000000 : ℝ)*base76 + (51252402790512453/22306250000000000000000000000000 : ℝ)*base78 + (246427714332643797/22306250000000000000000000000000 : ℝ)*base79 + (2167089743097/892250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (28979357/10000000000000000000000 : ℝ)*base89 + (28979357/10000000000000000000000 : ℝ)*base91 + (28979357/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1026594186445954560852734199/89225000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (400075323/20000000000000 : ℝ)*(base19) + (434615687/20000000000000 : ℝ)*(base23) + (46787671/20000000000000 : ℝ)*(upper3) + (39148693/50000000000000 : ℝ)*(lower4) + (118044313/50000000000000 : ℝ)*(upper5) + (221521323091293/5000000000000 : ℝ)*(major0) + (221521323091293/5000000000000 : ℝ)*(major1) + (221521323091293/5000000000000 : ℝ)*(major2) + (10220222421/25000000000000 : ℝ)*(sp1) + (10990780321/25000000000000 : ℝ)*(sp2) + (2999842870367507/50000000000000 : ℝ)*(sp4) + (1499910714867179/25000000000000 : ℝ)*(sp5) + (1199927920907059/20000000000000 : ℝ)*(sp6) + (2861166799394069/100000000000000 : ℝ)*(sp7) + (2861166799394069/100000000000000 : ℝ)*(f.failure) + (2999842870367507/50000000000000 : ℝ)*(f.sum) + (333245255979/1784500000000000000000000000 : ℝ)*base66 + (2121137412183710089/178450000000000000000000000000000 : ℝ)*base67 + (710191768979160089/178450000000000000000000000000000 : ℝ)*base69 + (2775935793264060089/178450000000000000000000000000000 : ℝ)*base71 + (6346772067151/3569000000000000000000000000 : ℝ)*base74 + (140247974123860089/178450000000000000000000000000000 : ℝ)*base75 + (1507628690565310089/178450000000000000000000000000000 : ℝ)*base77 + (2401788251358960089/178450000000000000000000000000000 : ℝ)*base79 + (31134936911/11153125000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (102425833/10000000000000000000000 : ℝ)*base90 + (102425833/10000000000000000000000 : ℝ)*base92 + (102425833/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1345_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154846843/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14717/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2787/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2231/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1471/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1345_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1345_s7_0 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-408276841/2000000000 : ℝ)*x 0 + (1353127521/2500000000 : ℝ)*x 1 + (2622370323/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (408276841/2000000000 : ℝ)^4305 ≤ (12432323023697/100000000000000 : ℝ)^3281 := by
    have hnat : (408276841 : ℕ)^4305*100000000000000^3281 ≤ 12432323023697^3281*2000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408276841 2000000000 12432323023697 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353127521/2500000000 : ℝ)^4305 ≤ (44688159317403/100000000000000 : ℝ)^3281 := by
    have hnat : (1353127521 : ℕ)^4305*100000000000000^3281 ≤ 44688159317403^3281*2500000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353127521 2500000000 44688159317403 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622370323/5000000000 : ℝ)^4305 ≤ (42879517648677/100000000000000 : ℝ)^3281 := by
    have hnat : (2622370323 : ℕ)^4305*100000000000000^3281 ≤ 42879517648677^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622370323 5000000000 42879517648677 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-408276841/2000000000 : ℝ), (1353127521/2500000000 : ℝ), (2622370323/5000000000 : ℝ)] ![(12432323023697/100000000000000 : ℝ), (44688159317403/100000000000000 : ℝ), (42879517648677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-408276841/2000000000 : ℝ)|^4305 ≤ (12432323023697/100000000000000 : ℝ)^3281
        have hw : |(-408276841/2000000000 : ℝ)|=(408276841/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353127521/2500000000 : ℝ)|^4305 ≤ (44688159317403/100000000000000 : ℝ)^3281
        have hw : |(1353127521/2500000000 : ℝ)|=(1353127521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622370323/5000000000 : ℝ)|^4305 ≤ (42879517648677/100000000000000 : ℝ)^3281
        have hw : |(2622370323/5000000000 : ℝ)|=(2622370323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s7_1 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674467833/5000000000 : ℝ)*x 0 + (-2126860961/10000000000 : ℝ)*x 1 + (5244740609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674467833/5000000000 : ℝ)^4305 ≤ (4400070452577/10000000000000 : ℝ)^3281 := by
    have hnat : (2674467833 : ℕ)^4305*10000000000000^3281 ≤ 4400070452577^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674467833 5000000000 4400070452577 10000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2126860961/10000000000 : ℝ)^4305 ≤ (102498267249/781250000000 : ℝ)^3281 := by
    have hnat : (2126860961 : ℕ)^4305*781250000000^3281 ≤ 102498267249^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126860961 10000000000 102498267249 781250000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244740609/10000000000 : ℝ)^4305 ≤ (8575903450353/20000000000000 : ℝ)^3281 := by
    have hnat : (5244740609 : ℕ)^4305*20000000000000^3281 ≤ 8575903450353^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244740609 10000000000 8575903450353 20000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674467833/5000000000 : ℝ), (-2126860961/10000000000 : ℝ), (5244740609/10000000000 : ℝ)] ![(4400070452577/10000000000000 : ℝ), (102498267249/781250000000 : ℝ), (8575903450353/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674467833/5000000000 : ℝ)|^4305 ≤ (4400070452577/10000000000000 : ℝ)^3281
        have hw : |(2674467833/5000000000 : ℝ)|=(2674467833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2126860961/10000000000 : ℝ)|^4305 ≤ (102498267249/781250000000 : ℝ)^3281
        have hw : |(-2126860961/10000000000 : ℝ)|=(2126860961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244740609/10000000000 : ℝ)|^4305 ≤ (8575903450353/20000000000000 : ℝ)^3281
        have hw : |(5244740609/10000000000 : ℝ)|=(5244740609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s7_2 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069787171/2000000000 : ℝ)*x 0 + (5244740571/10000000000 : ℝ)*x 1 + (-53171519/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069787171/2000000000 : ℝ)^4305 ≤ (44000706565727/100000000000000 : ℝ)^3281 := by
    have hnat : (1069787171 : ℕ)^4305*100000000000000^3281 ≤ 44000706565727^3281*2000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069787171 2000000000 44000706565727 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244740571/10000000000 : ℝ)^4305 ≤ (21439758422063/50000000000000 : ℝ)^3281 := by
    have hnat : (5244740571 : ℕ)^4305*50000000000000^3281 ≤ 21439758422063^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244740571 10000000000 21439758422063 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (53171519/250000000 : ℝ)^4305 ≤ (13119776581011/100000000000000 : ℝ)^3281 := by
    have hnat : (53171519 : ℕ)^4305*100000000000000^3281 ≤ 13119776581011^3281*250000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53171519 250000000 13119776581011 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069787171/2000000000 : ℝ), (5244740571/10000000000 : ℝ), (-53171519/250000000 : ℝ)] ![(44000706565727/100000000000000 : ℝ), (21439758422063/50000000000000 : ℝ), (13119776581011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069787171/2000000000 : ℝ)|^4305 ≤ (44000706565727/100000000000000 : ℝ)^3281
        have hw : |(1069787171/2000000000 : ℝ)|=(1069787171/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244740571/10000000000 : ℝ)|^4305 ≤ (21439758422063/50000000000000 : ℝ)^3281
        have hw : |(5244740571/10000000000 : ℝ)|=(5244740571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-53171519/250000000 : ℝ)|^4305 ≤ (13119776581011/100000000000000 : ℝ)^3281
        have hw : |(-53171519/250000000 : ℝ)|=(53171519/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s7_3 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4325837867/10000000000 : ℝ)*x 0 + (830654969/2000000000 : ℝ)*x 1 + (2252538333/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4325837867/10000000000 : ℝ)^4305 ≤ (16651669201383/50000000000000 : ℝ)^3281 := by
    have hnat : (4325837867 : ℕ)^4305*50000000000000^3281 ≤ 16651669201383^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4325837867 10000000000 16651669201383 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (830654969/2000000000 : ℝ)^4305 ≤ (15785575375811/50000000000000 : ℝ)^3281 := by
    have hnat : (830654969 : ℕ)^4305*50000000000000^3281 ≤ 15785575375811^3281*2000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      830654969 2000000000 15785575375811 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2252538333/5000000000 : ℝ)^4305 ≤ (8781377707363/25000000000000 : ℝ)^3281 := by
    have hnat : (2252538333 : ℕ)^4305*25000000000000^3281 ≤ 8781377707363^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252538333 5000000000 8781377707363 25000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4325837867/10000000000 : ℝ), (830654969/2000000000 : ℝ), (2252538333/5000000000 : ℝ)] ![(16651669201383/50000000000000 : ℝ), (15785575375811/50000000000000 : ℝ), (8781377707363/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4325837867/10000000000 : ℝ)|^4305 ≤ (16651669201383/50000000000000 : ℝ)^3281
        have hw : |(4325837867/10000000000 : ℝ)|=(4325837867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(830654969/2000000000 : ℝ)|^4305 ≤ (15785575375811/50000000000000 : ℝ)^3281
        have hw : |(830654969/2000000000 : ℝ)|=(830654969/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2252538333/5000000000 : ℝ)|^4305 ≤ (8781377707363/25000000000000 : ℝ)^3281
        have hw : |(2252538333/5000000000 : ℝ)|=(2252538333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s7_4 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2041396369/10000000000 : ℝ)*x 0 + (5245341113/10000000000 : ℝ)*x 1 + (1082381299/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2041396369/10000000000 : ℝ)^4305 ≤ (12432420224819/100000000000000 : ℝ)^3281 := by
    have hnat : (2041396369 : ℕ)^4305*100000000000000^3281 ≤ 12432420224819^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2041396369 10000000000 12432420224819 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245341113/10000000000 : ℝ)^4305 ≤ (335046556161/781250000000 : ℝ)^3281 := by
    have hnat : (5245341113 : ℕ)^4305*781250000000^3281 ≤ 335046556161^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245341113 10000000000 335046556161 781250000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082381299/2000000000 : ℝ)^4305 ≤ (22340810285967/50000000000000 : ℝ)^3281 := by
    have hnat : (1082381299 : ℕ)^4305*50000000000000^3281 ≤ 22340810285967^3281*2000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082381299 2000000000 22340810285967 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2041396369/10000000000 : ℝ), (5245341113/10000000000 : ℝ), (1082381299/2000000000 : ℝ)] ![(12432420224819/100000000000000 : ℝ), (335046556161/781250000000 : ℝ), (22340810285967/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2041396369/10000000000 : ℝ)|^4305 ≤ (12432420224819/100000000000000 : ℝ)^3281
        have hw : |(-2041396369/10000000000 : ℝ)|=(2041396369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245341113/10000000000 : ℝ)|^4305 ≤ (335046556161/781250000000 : ℝ)^3281
        have hw : |(5245341113/10000000000 : ℝ)|=(5245341113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082381299/2000000000 : ℝ)|^4305 ≤ (22340810285967/50000000000000 : ℝ)^3281
        have hw : |(1082381299/2000000000 : ℝ)|=(1082381299/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s7_5 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305707193/10000000000 : ℝ)*x 0 + (-489923721/2500000000 : ℝ)*x 1 + (338244159/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305707193/10000000000 : ℝ)^4305 ≤ (21767355436751/50000000000000 : ℝ)^3281 := by
    have hnat : (5305707193 : ℕ)^4305*50000000000000^3281 ≤ 21767355436751^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305707193 10000000000 21767355436751 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (489923721/2500000000 : ℝ)^4305 ≤ (1472958501673/12500000000000 : ℝ)^3281 := by
    have hnat : (489923721 : ℕ)^4305*12500000000000^3281 ≤ 1472958501673^3281*2500000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      489923721 2500000000 1472958501673 12500000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338244159/625000000 : ℝ)^4305 ≤ (11170405275687/25000000000000 : ℝ)^3281 := by
    have hnat : (338244159 : ℕ)^4305*25000000000000^3281 ≤ 11170405275687^3281*625000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338244159 625000000 11170405275687 25000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305707193/10000000000 : ℝ), (-489923721/2500000000 : ℝ), (338244159/625000000 : ℝ)] ![(21767355436751/50000000000000 : ℝ), (1472958501673/12500000000000 : ℝ), (11170405275687/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305707193/10000000000 : ℝ)|^4305 ≤ (21767355436751/50000000000000 : ℝ)^3281
        have hw : |(5305707193/10000000000 : ℝ)|=(5305707193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-489923721/2500000000 : ℝ)|^4305 ≤ (1472958501673/12500000000000 : ℝ)^3281
        have hw : |(-489923721/2500000000 : ℝ)|=(489923721/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338244159/625000000 : ℝ)|^4305 ≤ (11170405275687/25000000000000 : ℝ)^3281
        have hw : |(338244159/625000000 : ℝ)|=(338244159/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s7_6 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305707207/10000000000 : ℝ)*x 0 + (5411906519/10000000000 : ℝ)*x 1 + (-979847449/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305707207/10000000000 : ℝ)^4305 ≤ (43534711024227/100000000000000 : ℝ)^3281 := by
    have hnat : (5305707207 : ℕ)^4305*100000000000000^3281 ≤ 43534711024227^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305707207 10000000000 43534711024227 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5411906519/10000000000 : ℝ)^4305 ≤ (1787264833277/4000000000000 : ℝ)^3281 := by
    have hnat : (5411906519 : ℕ)^4305*4000000000000^3281 ≤ 1787264833277^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411906519 10000000000 1787264833277 4000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (979847449/5000000000 : ℝ)^4305 ≤ (11783668123839/100000000000000 : ℝ)^3281 := by
    have hnat : (979847449 : ℕ)^4305*100000000000000^3281 ≤ 11783668123839^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      979847449 5000000000 11783668123839 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305707207/10000000000 : ℝ), (5411906519/10000000000 : ℝ), (-979847449/5000000000 : ℝ)] ![(43534711024227/100000000000000 : ℝ), (1787264833277/4000000000000 : ℝ), (11783668123839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305707207/10000000000 : ℝ)|^4305 ≤ (43534711024227/100000000000000 : ℝ)^3281
        have hw : |(5305707207/10000000000 : ℝ)|=(5305707207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5411906519/10000000000 : ℝ)|^4305 ≤ (1787264833277/4000000000000 : ℝ)^3281
        have hw : |(5411906519/10000000000 : ℝ)|=(5411906519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-979847449/5000000000 : ℝ)|^4305 ≤ (11783668123839/100000000000000 : ℝ)^3281
        have hw : |(-979847449/5000000000 : ℝ)|=(979847449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s7_7 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4325863277/10000000000 : ℝ)*x 0 + (281488597/625000000 : ℝ)*x 1 + (1038635117/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4325863277/10000000000 : ℝ)^4305 ≤ (33303595081283/100000000000000 : ℝ)^3281 := by
    have hnat : (4325863277 : ℕ)^4305*100000000000000^3281 ≤ 33303595081283^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4325863277 10000000000 33303595081283 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (281488597/625000000 : ℝ)^4305 ≤ (274317424269/781250000000 : ℝ)^3281 := by
    have hnat : (281488597 : ℕ)^4305*781250000000^3281 ≤ 274317424269^3281*625000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281488597 625000000 274317424269 781250000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1038635117/2500000000 : ℝ)^4305 ≤ (7895943649307/25000000000000 : ℝ)^3281 := by
    have hnat : (1038635117 : ℕ)^4305*25000000000000^3281 ≤ 7895943649307^3281*2500000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038635117 2500000000 7895943649307 25000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4325863277/10000000000 : ℝ), (281488597/625000000 : ℝ), (1038635117/2500000000 : ℝ)] ![(33303595081283/100000000000000 : ℝ), (274317424269/781250000000 : ℝ), (7895943649307/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4325863277/10000000000 : ℝ)|^4305 ≤ (33303595081283/100000000000000 : ℝ)^3281
        have hw : |(4325863277/10000000000 : ℝ)|=(4325863277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(281488597/625000000 : ℝ)|^4305 ≤ (274317424269/781250000000 : ℝ)^3281
        have hw : |(281488597/625000000 : ℝ)|=(281488597/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1038635117/2500000000 : ℝ)|^4305 ≤ (7895943649307/25000000000000 : ℝ)^3281
        have hw : |(1038635117/2500000000 : ℝ)|=(1038635117/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1345_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154846843/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1471/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2231/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11157/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3677/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1471/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2231/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1471/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2231/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1471/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2231/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1471/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2231/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1471/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2231/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1471/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2231/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2231/20000 : ℝ) ^ (269/64 : ℝ) ≤ (4958674033323839/50000000000000000000 : ℝ) := by
    have hpowers : (2231/20000 : ℝ)^269 ≤ (4958674033323839/50000000000000000000 : ℝ)^64 := by
      have hnat : (2231 : ℕ)^269*50000000000000000000^64 ≤ 4958674033323839^64*20000^269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2231 20000 4958674033323839 50000000000000000000 269 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2231/20000 : ℝ)) (X := (4958674033323839/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 269 64 (by norm_num) hpowers
    exact h
  have hpowhi : (1471/10000 : ℝ) ^ (269/64 : ℝ) ≤ (3965354582585263/12500000000000000000 : ℝ) := by
    have hpowers : (1471/10000 : ℝ)^269 ≤ (3965354582585263/12500000000000000000 : ℝ)^64 := by
      have hnat : (1471 : ℕ)^269*12500000000000000000^64 ≤ 3965354582585263^64*10000^269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1471 10000 3965354582585263 12500000000000000000 269 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1471/10000 : ℝ)) (X := (3965354582585263/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 269 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004958674033323839/25000000000000000000 : ℝ) ≤ (2500117966972403/2500000000000000 : ℝ) ^ (269/64 : ℝ) := by
    have hpowers : (25004958674033323839/25000000000000000000 : ℝ)^64 ≤ (2500117966972403/2500000000000000 : ℝ)^269 := by
      have hnat : (25004958674033323839 : ℕ)^64*2500000000000000^269 ≤ 2500117966972403^269*25000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004958674033323839 25000000000000000000 2500117966972403 2500000000000000 64 269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500117966972403/2500000000000000 : ℝ)) (X := (25004958674033323839/25000000000000000000 : ℝ)) (by norm_num) 269 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020820092363664891/50000000000000000000 : ℝ) ≤ (10000990538693371/10000000000000000 : ℝ) ^ (269/64 : ℝ) := by
    have hpowers : (50020820092363664891/50000000000000000000 : ℝ)^64 ≤ (10000990538693371/10000000000000000 : ℝ)^269 := by
      have hnat : (50020820092363664891 : ℕ)^64*10000000000000000^269 ≤ 10000990538693371^269*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020820092363664891 50000000000000000000 10000990538693371 10000000000000000 64 269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000990538693371/10000000000000000 : ℝ)) (X := (50020820092363664891/50000000000000000000 : ℝ)) (by norm_num) 269 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253965354582585263/6250000000000000000 : ℝ) ≤ (1000150920949713/1000000000000000 : ℝ) ^ (269/64 : ℝ) := by
    have hpowers : (6253965354582585263/6250000000000000000 : ℝ)^64 ≤ (1000150920949713/1000000000000000 : ℝ)^269 := by
      have hnat : (6253965354582585263 : ℕ)^64*1000000000000000^269 ≤ 1000150920949713^269*6250000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253965354582585263 6250000000000000000 1000150920949713 1000000000000000 64 269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000150920949713/1000000000000000 : ℝ)) (X := (6253965354582585263/6250000000000000000 : ℝ)) (by norm_num) 269 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4958674033323839/50000000000000000000 : ℝ) ≤ ((3554010594471570737/3555000000000000000 : ℝ)+2*(518670803759/355500000000000 : ℝ)*(2231/20000 : ℝ))^(269/64 : ℝ) := by
    rw [show (3554010594471570737/3555000000000000000 : ℝ)+2*(518670803759/355500000000000 : ℝ)*(2231/20000 : ℝ)=(2500117966972403/2500000000000000 : ℝ) by norm_num, show 1+2*(4958674033323839/50000000000000000000 : ℝ)=(25004958674033323839/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3965354582585263/12500000000000000000 : ℝ)+(4958674033323839/50000000000000000000 : ℝ) ≤ ((3554010594471570737/3555000000000000000 : ℝ)+(518670803759/355500000000000 : ℝ)*((1471/10000 : ℝ)+(2231/20000 : ℝ)))^(269/64 : ℝ) := by
    rw [show (3554010594471570737/3555000000000000000 : ℝ)+(518670803759/355500000000000 : ℝ)*((1471/10000 : ℝ)+(2231/20000 : ℝ))=(10000990538693371/10000000000000000 : ℝ) by norm_num, show 1+(3965354582585263/12500000000000000000 : ℝ)+(4958674033323839/50000000000000000000 : ℝ)=(50020820092363664891/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3965354582585263/12500000000000000000 : ℝ) ≤ ((3554010594471570737/3555000000000000000 : ℝ)+2*(518670803759/355500000000000 : ℝ)*(1471/10000 : ℝ))^(269/64 : ℝ) := by
    rw [show (3554010594471570737/3555000000000000000 : ℝ)+2*(518670803759/355500000000000 : ℝ)*(1471/10000 : ℝ)=(1000150920949713/1000000000000000 : ℝ) by norm_num, show 1+2*(3965354582585263/12500000000000000000 : ℝ)=(6253965354582585263/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3554010594471570737/3555000000000000000 : ℝ)*(X 1 0+X 2 0)+(518670803759/355500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (269/64 : ℝ)) (lo := (2231/20000 : ℝ)) (hi := (1471/10000 : ℝ)) (c := (3554010594471570737/3555000000000000000 : ℝ)) (alpha := (518670803759/355500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3554010594471570737/3555000000000000000 : ℝ)*(X 0 1+X 2 1)+(518670803759/355500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (269/64 : ℝ)) (lo := (2231/20000 : ℝ)) (hi := (1471/10000 : ℝ)) (c := (3554010594471570737/3555000000000000000 : ℝ)) (alpha := (518670803759/355500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3554010594471570737/3555000000000000000 : ℝ)*(X 0 2+X 1 2)+(518670803759/355500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (269/64 : ℝ)) (lo := (2231/20000 : ℝ)) (hi := (1471/10000 : ℝ)) (c := (3554010594471570737/3555000000000000000 : ℝ)) (alpha := (518670803759/355500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-408276841/2000000000 : ℝ)*X 0 0+(1353127521/2500000000 : ℝ)*X 0 1+(2622370323/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674467833/5000000000 : ℝ)*X 1 0+(-2126860961/10000000000 : ℝ)*X 1 1+(5244740609/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069787171/2000000000 : ℝ)*X 2 0+(5244740571/10000000000 : ℝ)*X 2 1+(-53171519/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4325837867/10000000000 : ℝ)*X 0 0+(830654969/2000000000 : ℝ)*X 0 1+(2252538333/5000000000 : ℝ)*X 0 2+(4325837867/10000000000 : ℝ)*X 1 0+(830654969/2000000000 : ℝ)*X 1 1+(2252538333/5000000000 : ℝ)*X 1 2+(4325837867/10000000000 : ℝ)*X 2 0+(830654969/2000000000 : ℝ)*X 2 1+(2252538333/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2041396369/10000000000 : ℝ)*X 0 0+(5245341113/10000000000 : ℝ)*X 0 1+(1082381299/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305707193/10000000000 : ℝ)*X 1 0+(-489923721/2500000000 : ℝ)*X 1 1+(338244159/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305707207/10000000000 : ℝ)*X 2 0+(5411906519/10000000000 : ℝ)*X 2 1+(-979847449/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4325863277/10000000000 : ℝ)*X 0 0+(281488597/625000000 : ℝ)*X 0 1+(1038635117/2500000000 : ℝ)*X 0 2+(4325863277/10000000000 : ℝ)*X 1 0+(281488597/625000000 : ℝ)*X 1 1+(1038635117/2500000000 : ℝ)*X 1 2+(4325863277/10000000000 : ℝ)*X 2 0+(281488597/625000000 : ℝ)*X 2 1+(1038635117/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (70697834772385825954085271/19750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (460861641/100000000000000 : ℝ)*(base19) + (593462833/100000000000000 : ℝ)*(base23) + (25723561/50000000000000 : ℝ)*(lower2) + (871889/625000000000 : ℝ)*(upper5) + (4401549653491851/100000000000000 : ℝ)*(major0) + (4401549653491851/100000000000000 : ℝ)*(major1) + (4401549653491851/100000000000000 : ℝ)*(major2) + (2980283487549751/50000000000000 : ℝ)*(sp0) + (2980289152388063/50000000000000 : ℝ)*(sp1) + (2980290210309177/50000000000000 : ℝ)*(sp2) + (2842514209824027/100000000000000 : ℝ)*(sp3) + (2807796337/20000000000000 : ℝ)*(sp4) + (112422171/5000000000000 : ℝ)*(sp5) + (3963757239/100000000000000 : ℝ)*(sp7) + (1421259086790633/50000000000000 : ℝ)*(f.failure) + (5960581014081187/100000000000000 : ℝ)*(f.sum) + (20298481193789/2962500000000000000000000000 : ℝ)*base65 + (847765115453115271/118500000000000000000000000000000 : ℝ)*base68 + (1185250404674384729/118500000000000000000000000000000 : ℝ)*base69 + (1232452700814884729/118500000000000000000000000000000 : ℝ)*base71 + (3656010709711/2962500000000000000000000000 : ℝ)*base74 + (838479251304884729/118500000000000000000000000000000 : ℝ)*base75 + (56049556575884729/118500000000000000000000000000000 : ℝ)*base77 + (1756440482931615271/118500000000000000000000000000000 : ℝ)*base80 + (16508650584853/5925000000000000000000000000 : ℝ)*base81 + (27978381/5000000000000000000000 : ℝ)*base90 + (27978381/5000000000000000000000 : ℝ)*base92 + (27978381/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7251164842203859341761599/1975000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (615435187/100000000000000 : ℝ)*(base19) + (340550431/50000000000000 : ℝ)*(base23) + (3640479/1562500000000 : ℝ)*(lower1) + (78794573/100000000000000 : ℝ)*(upper3) + (12231633/50000000000000 : ℝ)*(lower4) + (8067329/10000000000000 : ℝ)*(upper5) + (443334193707619/10000000000000 : ℝ)*(major0) + (443334193707619/10000000000000 : ℝ)*(major1) + (443334193707619/10000000000000 : ℝ)*(major2) + (456166141/100000000000000 : ℝ)*(sp2) + (6003634140176393/100000000000000 : ℝ)*(sp4) + (3001816762370603/50000000000000 : ℝ)*(sp5) + (600363300290939/10000000000000 : ℝ)*(sp6) + (2863049611593431/100000000000000 : ℝ)*(sp7) + (2863049611593431/100000000000000 : ℝ)*(f.failure) + (6003634140176393/100000000000000 : ℝ)*(f.sum) + (1913432978927/888750000000000000000000000 : ℝ)*base66 + (1550042083341005203/35550000000000000000000000000000 : ℝ)*base67 + (113349239486094797/35550000000000000000000000000000 : ℝ)*base70 + (4610705759497805203/35550000000000000000000000000000 : ℝ)*base71 + (659731678601/1777500000000000000000000000 : ℝ)*base73 + (2128594463257955203/35550000000000000000000000000000 : ℝ)*base75 + (3156839437044797/35550000000000000000000000000000 : ℝ)*base78 + (794548609439405203/35550000000000000000000000000000 : ℝ)*base79 + (6745650791801/1777500000000000000000000000 : ℝ)*base81 + (10111667/10000000000000000000000 : ℝ)*base90 + (10111667/10000000000000000000000 : ℝ)*base92 + (10111667/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1345_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154846843/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1471/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2231/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11157/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3677/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1345_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1345_box_0 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-14994951/80000000 : ℝ)*x 0 + (2694907301/5000000000 : ℝ)*x 1 + (5389814491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (14994951/80000000 : ℝ)^4305 ≤ (11115094299019/100000000000000 : ℝ)^3281 := by
    have hnat : (14994951 : ℕ)^4305*100000000000000^3281 ≤ 11115094299019^3281*80000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14994951 80000000 11115094299019 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2694907301/5000000000 : ℝ)^4305 ≤ (11110613360673/25000000000000 : ℝ)^3281 := by
    have hnat : (2694907301 : ℕ)^4305*25000000000000^3281 ≤ 11110613360673^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2694907301 5000000000 11110613360673 25000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5389814491/10000000000 : ℝ)^4305 ≤ (11110613060443/25000000000000 : ℝ)^3281 := by
    have hnat : (5389814491 : ℕ)^4305*25000000000000^3281 ≤ 11110613060443^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389814491 10000000000 11110613060443 25000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-14994951/80000000 : ℝ), (2694907301/5000000000 : ℝ), (5389814491/10000000000 : ℝ)] ![(11115094299019/100000000000000 : ℝ), (11110613360673/25000000000000 : ℝ), (11110613060443/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-14994951/80000000 : ℝ)|^4305 ≤ (11115094299019/100000000000000 : ℝ)^3281
        have hw : |(-14994951/80000000 : ℝ)|=(14994951/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2694907301/5000000000 : ℝ)|^4305 ≤ (11110613360673/25000000000000 : ℝ)^3281
        have hw : |(2694907301/5000000000 : ℝ)|=(2694907301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5389814491/10000000000 : ℝ)|^4305 ≤ (11110613060443/25000000000000 : ℝ)^3281
        have hw : |(5389814491/10000000000 : ℝ)|=(5389814491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_box_1 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2642602917/5000000000 : ℝ)*x 0 + (-2017701979/10000000000 : ℝ)*x 1 + (5389814401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642602917/5000000000 : ℝ)^4305 ≤ (21657061971051/50000000000000 : ℝ)^3281 := by
    have hnat : (2642602917 : ℕ)^4305*50000000000000^3281 ≤ 21657061971051^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642602917 5000000000 21657061971051 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2017701979/10000000000 : ℝ)^4305 ≤ (12243424770877/100000000000000 : ℝ)^3281 := by
    have hnat : (2017701979 : ℕ)^4305*100000000000000^3281 ≤ 12243424770877^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2017701979 10000000000 12243424770877 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5389814401/10000000000 : ℝ)^4305 ≤ (44442451268053/100000000000000 : ℝ)^3281 := by
    have hnat : (5389814401 : ℕ)^4305*100000000000000^3281 ≤ 44442451268053^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389814401 10000000000 44442451268053 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642602917/5000000000 : ℝ), (-2017701979/10000000000 : ℝ), (5389814401/10000000000 : ℝ)] ![(21657061971051/50000000000000 : ℝ), (12243424770877/100000000000000 : ℝ), (44442451268053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642602917/5000000000 : ℝ)|^4305 ≤ (21657061971051/50000000000000 : ℝ)^3281
        have hw : |(2642602917/5000000000 : ℝ)|=(2642602917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2017701979/10000000000 : ℝ)|^4305 ≤ (12243424770877/100000000000000 : ℝ)^3281
        have hw : |(-2017701979/10000000000 : ℝ)|=(2017701979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5389814401/10000000000 : ℝ)|^4305 ≤ (44442451268053/100000000000000 : ℝ)^3281
        have hw : |(5389814401/10000000000 : ℝ)|=(5389814401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_box_2 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1057041149/2000000000 : ℝ)*x 0 + (5389814559/10000000000 : ℝ)*x 1 + (-403540377/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057041149/2000000000 : ℝ)^4305 ≤ (1732564919403/4000000000000 : ℝ)^3281 := by
    have hnat : (1057041149 : ℕ)^4305*4000000000000^3281 ≤ 1732564919403^3281*2000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057041149 2000000000 1732564919403 4000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5389814559/10000000000 : ℝ)^4305 ≤ (4444245297747/10000000000000 : ℝ)^3281 := by
    have hnat : (5389814559 : ℕ)^4305*10000000000000^3281 ≤ 4444245297747^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389814559 10000000000 4444245297747 10000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (403540377/2000000000 : ℝ)^4305 ≤ (2448684804493/20000000000000 : ℝ)^3281 := by
    have hnat : (403540377 : ℕ)^4305*20000000000000^3281 ≤ 2448684804493^3281*2000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403540377 2000000000 2448684804493 20000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057041149/2000000000 : ℝ), (5389814559/10000000000 : ℝ), (-403540377/2000000000 : ℝ)] ![(1732564919403/4000000000000 : ℝ), (4444245297747/10000000000000 : ℝ), (2448684804493/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057041149/2000000000 : ℝ)|^4305 ≤ (1732564919403/4000000000000 : ℝ)^3281
        have hw : |(1057041149/2000000000 : ℝ)|=(1057041149/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5389814559/10000000000 : ℝ)|^4305 ≤ (4444245297747/10000000000000 : ℝ)^3281
        have hw : |(5389814559/10000000000 : ℝ)|=(5389814559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-403540377/2000000000 : ℝ)|^4305 ≤ (2448684804493/20000000000000 : ℝ)^3281
        have hw : |(-403540377/2000000000 : ℝ)|=(403540377/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_box_3 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (69905571/156250000 : ℝ)*x 0 + (4255661559/10000000000 : ℝ)*x 1 + (4255661643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (69905571/156250000 : ℝ)^4305 ≤ (8701871774343/25000000000000 : ℝ)^3281 := by
    have hnat : (69905571 : ℕ)^4305*25000000000000^3281 ≤ 8701871774343^3281*156250000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69905571 156250000 8701871774343 25000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4255661559/10000000000 : ℝ)^4305 ≤ (32596256015379/100000000000000 : ℝ)^3281 := by
    have hnat : (4255661559 : ℕ)^4305*100000000000000^3281 ≤ 32596256015379^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4255661559 10000000000 32596256015379 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4255661643/10000000000 : ℝ)^4305 ≤ (16298128429791/50000000000000 : ℝ)^3281 := by
    have hnat : (4255661643 : ℕ)^4305*50000000000000^3281 ≤ 16298128429791^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4255661643 10000000000 16298128429791 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(69905571/156250000 : ℝ), (4255661559/10000000000 : ℝ), (4255661643/10000000000 : ℝ)] ![(8701871774343/25000000000000 : ℝ), (32596256015379/100000000000000 : ℝ), (16298128429791/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(69905571/156250000 : ℝ)|^4305 ≤ (8701871774343/25000000000000 : ℝ)^3281
        have hw : |(69905571/156250000 : ℝ)|=(69905571/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4255661559/10000000000 : ℝ)|^4305 ≤ (32596256015379/100000000000000 : ℝ)^3281
        have hw : |(4255661559/10000000000 : ℝ)|=(4255661559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4255661643/10000000000 : ℝ)|^4305 ≤ (16298128429791/50000000000000 : ℝ)^3281
        have hw : |(4255661643/10000000000 : ℝ)|=(4255661643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_box_4 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-552787917/2500000000 : ℝ)*x 0 + (164531029/312500000 : ℝ)*x 1 + (105299861/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (552787917/2500000000 : ℝ)^4305 ≤ (215721793811/1562500000000 : ℝ)^3281 := by
    have hnat : (552787917 : ℕ)^4305*1562500000000^3281 ≤ 215721793811^3281*2500000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552787917 2500000000 215721793811 1562500000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164531029/312500000 : ℝ)^4305 ≤ (2154845096861/5000000000000 : ℝ)^3281 := by
    have hnat : (164531029 : ℕ)^4305*5000000000000^3281 ≤ 2154845096861^3281*312500000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164531029 312500000 2154845096861 5000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105299861/200000000 : ℝ)^4305 ≤ (43096903247533/100000000000000 : ℝ)^3281 := by
    have hnat : (105299861 : ℕ)^4305*100000000000000^3281 ≤ 43096903247533^3281*200000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105299861 200000000 43096903247533 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-552787917/2500000000 : ℝ), (164531029/312500000 : ℝ), (105299861/200000000 : ℝ)] ![(215721793811/1562500000000 : ℝ), (2154845096861/5000000000000 : ℝ), (43096903247533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-552787917/2500000000 : ℝ)|^4305 ≤ (215721793811/1562500000000 : ℝ)^3281
        have hw : |(-552787917/2500000000 : ℝ)|=(552787917/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164531029/312500000 : ℝ)|^4305 ≤ (2154845096861/5000000000000 : ℝ)^3281
        have hw : |(164531029/312500000 : ℝ)|=(164531029/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(105299861/200000000 : ℝ)|^4305 ≤ (43096903247533/100000000000000 : ℝ)^3281
        have hw : |(105299861/200000000 : ℝ)|=(105299861/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_box_5 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2686433173/5000000000 : ℝ)*x 0 + (-258476257/1250000000 : ℝ)*x 1 + (1316248357/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686433173/5000000000 : ℝ)^4305 ≤ (22129589306163/50000000000000 : ℝ)^3281 := by
    have hnat : (2686433173 : ℕ)^4305*50000000000000^3281 ≤ 22129589306163^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686433173 5000000000 22129589306163 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (258476257/1250000000 : ℝ)^4305 ≤ (3160978516943/25000000000000 : ℝ)^3281 := by
    have hnat : (258476257 : ℕ)^4305*25000000000000^3281 ≤ 3160978516943^3281*1250000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258476257 1250000000 3160978516943 25000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316248357/2500000000 : ℝ)^4305 ≤ (8619381461471/20000000000000 : ℝ)^3281 := by
    have hnat : (1316248357 : ℕ)^4305*20000000000000^3281 ≤ 8619381461471^3281*2500000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316248357 2500000000 8619381461471 20000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686433173/5000000000 : ℝ), (-258476257/1250000000 : ℝ), (1316248357/2500000000 : ℝ)] ![(22129589306163/50000000000000 : ℝ), (3160978516943/25000000000000 : ℝ), (8619381461471/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686433173/5000000000 : ℝ)|^4305 ≤ (22129589306163/50000000000000 : ℝ)^3281
        have hw : |(2686433173/5000000000 : ℝ)|=(2686433173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-258476257/1250000000 : ℝ)|^4305 ≤ (3160978516943/25000000000000 : ℝ)^3281
        have hw : |(-258476257/1250000000 : ℝ)|=(258476257/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316248357/2500000000 : ℝ)|^4305 ≤ (8619381461471/20000000000000 : ℝ)^3281
        have hw : |(1316248357/2500000000 : ℝ)|=(1316248357/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_box_6 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2686433693/5000000000 : ℝ)*x 0 + (329062047/625000000 : ℝ)*x 1 + (-51695239/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686433693/5000000000 : ℝ)^4305 ≤ (8851837970627/20000000000000 : ℝ)^3281 := by
    have hnat : (2686433693 : ℕ)^4305*20000000000000^3281 ≤ 8851837970627^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686433693 5000000000 8851837970627 20000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329062047/625000000 : ℝ)^4305 ≤ (10774225011733/25000000000000 : ℝ)^3281 := by
    have hnat : (329062047 : ℕ)^4305*25000000000000^3281 ≤ 10774225011733^3281*625000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329062047 625000000 10774225011733 25000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (51695239/250000000 : ℝ)^4305 ≤ (2528782017671/20000000000000 : ℝ)^3281 := by
    have hnat : (51695239 : ℕ)^4305*20000000000000^3281 ≤ 2528782017671^3281*250000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51695239 250000000 2528782017671 20000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686433693/5000000000 : ℝ), (329062047/625000000 : ℝ), (-51695239/250000000 : ℝ)] ![(8851837970627/20000000000000 : ℝ), (10774225011733/25000000000000 : ℝ), (2528782017671/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686433693/5000000000 : ℝ)|^4305 ≤ (8851837970627/20000000000000 : ℝ)^3281
        have hw : |(2686433693/5000000000 : ℝ)|=(2686433693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329062047/625000000 : ℝ)|^4305 ≤ (10774225011733/25000000000000 : ℝ)^3281
        have hw : |(329062047/625000000 : ℝ)|=(329062047/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-51695239/250000000 : ℝ)|^4305 ≤ (2528782017671/20000000000000 : ℝ)^3281
        have hw : |(-51695239/250000000 : ℝ)|=(51695239/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_box_7 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2088395143/5000000000 : ℝ)*x 0 + (4404191551/10000000000 : ℝ)*x 1 + (4404190931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2088395143/5000000000 : ℝ)^4305 ≤ (7951474815353/25000000000000 : ℝ)^3281 := by
    have hnat : (2088395143 : ℕ)^4305*25000000000000^3281 ≤ 7951474815353^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2088395143 5000000000 7951474815353 25000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4404191551/10000000000 : ℝ)^4305 ≤ (6819410701743/20000000000000 : ℝ)^3281 := by
    have hnat : (4404191551 : ℕ)^4305*20000000000000^3281 ≤ 6819410701743^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4404191551 10000000000 6819410701743 20000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4404190931/10000000000 : ℝ)^4305 ≤ (1704852360531/5000000000000 : ℝ)^3281 := by
    have hnat : (4404190931 : ℕ)^4305*5000000000000^3281 ≤ 1704852360531^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4404190931 10000000000 1704852360531 5000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2088395143/5000000000 : ℝ), (4404191551/10000000000 : ℝ), (4404190931/10000000000 : ℝ)] ![(7951474815353/25000000000000 : ℝ), (6819410701743/20000000000000 : ℝ), (1704852360531/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2088395143/5000000000 : ℝ)|^4305 ≤ (7951474815353/25000000000000 : ℝ)^3281
        have hw : |(2088395143/5000000000 : ℝ)|=(2088395143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4404191551/10000000000 : ℝ)|^4305 ≤ (6819410701743/20000000000000 : ℝ)^3281
        have hw : |(4404191551/10000000000 : ℝ)|=(4404191551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4404190931/10000000000 : ℝ)|^4305 ≤ (1704852360531/5000000000000 : ℝ)^3281
        have hw : |(4404190931/10000000000 : ℝ)|=(4404190931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_box_8 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-13377613/62500000 : ℝ)*x 0 + (2589523891/5000000000 : ℝ)*x 1 + (1350958577/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13377613/62500000 : ℝ)^4305 ≤ (6614808136757/50000000000000 : ℝ)^3281 := by
    have hnat : (13377613 : ℕ)^4305*50000000000000^3281 ≤ 6614808136757^3281*62500000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13377613 62500000 6614808136757 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2589523891/5000000000 : ℝ)^4305 ≤ (42176188142653/100000000000000 : ℝ)^3281 := by
    have hnat : (2589523891 : ℕ)^4305*100000000000000^3281 ≤ 42176188142653^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589523891 5000000000 42176188142653 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1350958577/2500000000 : ℝ)^4305 ≤ (44594195572213/100000000000000 : ℝ)^3281 := by
    have hnat : (1350958577 : ℕ)^4305*100000000000000^3281 ≤ 44594195572213^3281*2500000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350958577 2500000000 44594195572213 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-13377613/62500000 : ℝ), (2589523891/5000000000 : ℝ), (1350958577/2500000000 : ℝ)] ![(6614808136757/50000000000000 : ℝ), (42176188142653/100000000000000 : ℝ), (44594195572213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-13377613/62500000 : ℝ)|^4305 ≤ (6614808136757/50000000000000 : ℝ)^3281
        have hw : |(-13377613/62500000 : ℝ)|=(13377613/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2589523891/5000000000 : ℝ)|^4305 ≤ (42176188142653/100000000000000 : ℝ)^3281
        have hw : |(2589523891/5000000000 : ℝ)|=(2589523891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1350958577/2500000000 : ℝ)|^4305 ≤ (44594195572213/100000000000000 : ℝ)^3281
        have hw : |(1350958577/2500000000 : ℝ)|=(1350958577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_box_9 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5275356387/10000000000 : ℝ)*x 0 + (-2011941707/10000000000 : ℝ)*x 1 + (1350958093/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275356387/10000000000 : ℝ)^4305 ≤ (675128788363/1562500000000 : ℝ)^3281 := by
    have hnat : (5275356387 : ℕ)^4305*1562500000000^3281 ≤ 675128788363^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275356387 10000000000 675128788363 1562500000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2011941707/10000000000 : ℝ)^4305 ≤ (12197582917817/100000000000000 : ℝ)^3281 := by
    have hnat : (2011941707 : ℕ)^4305*100000000000000^3281 ≤ 12197582917817^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011941707 10000000000 12197582917817 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1350958093/2500000000 : ℝ)^4305 ≤ (44594174609449/100000000000000 : ℝ)^3281 := by
    have hnat : (1350958093 : ℕ)^4305*100000000000000^3281 ≤ 44594174609449^3281*2500000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350958093 2500000000 44594174609449 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275356387/10000000000 : ℝ), (-2011941707/10000000000 : ℝ), (1350958093/2500000000 : ℝ)] ![(675128788363/1562500000000 : ℝ), (12197582917817/100000000000000 : ℝ), (44594174609449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275356387/10000000000 : ℝ)|^4305 ≤ (675128788363/1562500000000 : ℝ)^3281
        have hw : |(5275356387/10000000000 : ℝ)|=(5275356387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2011941707/10000000000 : ℝ)|^4305 ≤ (12197582917817/100000000000000 : ℝ)^3281
        have hw : |(-2011941707/10000000000 : ℝ)|=(2011941707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1350958093/2500000000 : ℝ)|^4305 ≤ (44594174609449/100000000000000 : ℝ)^3281
        have hw : |(1350958093/2500000000 : ℝ)|=(1350958093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_box_10 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5275354159/10000000000 : ℝ)*x 0 + (2701917113/5000000000 : ℝ)*x 1 + (-2011942193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275354159/10000000000 : ℝ)^4305 ≤ (21604109255611/50000000000000 : ℝ)^3281 := by
    have hnat : (5275354159 : ℕ)^4305*50000000000000^3281 ≤ 21604109255611^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275354159 10000000000 21604109255611 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2701917113/5000000000 : ℝ)^4305 ≤ (5574274335541/12500000000000 : ℝ)^3281 := by
    have hnat : (2701917113 : ℕ)^4305*12500000000000^3281 ≤ 5574274335541^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701917113 5000000000 5574274335541 12500000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2011942193/10000000000 : ℝ)^4305 ≤ (2439517356763/20000000000000 : ℝ)^3281 := by
    have hnat : (2011942193 : ℕ)^4305*20000000000000^3281 ≤ 2439517356763^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011942193 10000000000 2439517356763 20000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275354159/10000000000 : ℝ), (2701917113/5000000000 : ℝ), (-2011942193/10000000000 : ℝ)] ![(21604109255611/50000000000000 : ℝ), (5574274335541/12500000000000 : ℝ), (2439517356763/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275354159/10000000000 : ℝ)|^4305 ≤ (21604109255611/50000000000000 : ℝ)^3281
        have hw : |(5275354159/10000000000 : ℝ)|=(5275354159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2701917113/5000000000 : ℝ)|^4305 ≤ (5574274335541/12500000000000 : ℝ)^3281
        have hw : |(2701917113/5000000000 : ℝ)|=(2701917113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2011942193/10000000000 : ℝ)|^4305 ≤ (2439517356763/20000000000000 : ℝ)^3281
        have hw : |(-2011942193/10000000000 : ℝ)|=(2011942193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_box_11 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (901354343/2000000000 : ℝ)*x 0 + (211948347/500000000 : ℝ)*x 1 + (4238966211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (901354343/2000000000 : ℝ)^4305 ≤ (8785713167031/25000000000000 : ℝ)^3281 := by
    have hnat : (901354343 : ℕ)^4305*25000000000000^3281 ≤ 8785713167031^3281*2000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901354343 2000000000 8785713167031 25000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (211948347/500000000 : ℝ)^4305 ≤ (32428577318011/100000000000000 : ℝ)^3281 := by
    have hnat : (211948347 : ℕ)^4305*100000000000000^3281 ≤ 32428577318011^3281*500000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211948347 500000000 32428577318011 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4238966211/10000000000 : ℝ)^4305 ≤ (16214285000259/50000000000000 : ℝ)^3281 := by
    have hnat : (4238966211 : ℕ)^4305*50000000000000^3281 ≤ 16214285000259^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4238966211 10000000000 16214285000259 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(901354343/2000000000 : ℝ), (211948347/500000000 : ℝ), (4238966211/10000000000 : ℝ)] ![(8785713167031/25000000000000 : ℝ), (32428577318011/100000000000000 : ℝ), (16214285000259/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(901354343/2000000000 : ℝ)|^4305 ≤ (8785713167031/25000000000000 : ℝ)^3281
        have hw : |(901354343/2000000000 : ℝ)|=(901354343/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(211948347/500000000 : ℝ)|^4305 ≤ (32428577318011/100000000000000 : ℝ)^3281
        have hw : |(211948347/500000000 : ℝ)|=(211948347/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4238966211/10000000000 : ℝ)|^4305 ≤ (16214285000259/50000000000000 : ℝ)^3281
        have hw : |(4238966211/10000000000 : ℝ)|=(4238966211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_box_12 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-972716053/5000000000 : ℝ)*x 0 + (5473561171/10000000000 : ℝ)*x 1 + (525392119/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (972716053/5000000000 : ℝ)^4305 ≤ (11671267386253/100000000000000 : ℝ)^3281 := by
    have hnat : (972716053 : ℕ)^4305*100000000000000^3281 ≤ 11671267386253^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      972716053 5000000000 11671267386253 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5473561171/10000000000 : ℝ)^4305 ≤ (1417209533567/3125000000000 : ℝ)^3281 := by
    have hnat : (5473561171 : ℕ)^4305*3125000000000^3281 ≤ 1417209533567^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5473561171 10000000000 1417209533567 3125000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (525392119/1000000000 : ℝ)^4305 ≤ (42978027526797/100000000000000 : ℝ)^3281 := by
    have hnat : (525392119 : ℕ)^4305*100000000000000^3281 ≤ 42978027526797^3281*1000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525392119 1000000000 42978027526797 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-972716053/5000000000 : ℝ), (5473561171/10000000000 : ℝ), (525392119/1000000000 : ℝ)] ![(11671267386253/100000000000000 : ℝ), (1417209533567/3125000000000 : ℝ), (42978027526797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-972716053/5000000000 : ℝ)|^4305 ≤ (11671267386253/100000000000000 : ℝ)^3281
        have hw : |(-972716053/5000000000 : ℝ)|=(972716053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5473561171/10000000000 : ℝ)|^4305 ≤ (1417209533567/3125000000000 : ℝ)^3281
        have hw : |(5473561171/10000000000 : ℝ)|=(5473561171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(525392119/1000000000 : ℝ)|^4305 ≤ (42978027526797/100000000000000 : ℝ)^3281
        have hw : |(525392119/1000000000 : ℝ)|=(525392119/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_box_13 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5380640087/10000000000 : ℝ)*x 0 + (-2072150709/10000000000 : ℝ)*x 1 + (2626960689/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5380640087/10000000000 : ℝ)^4305 ≤ (44343219826239/100000000000000 : ℝ)^3281 := by
    have hnat : (5380640087 : ℕ)^4305*100000000000000^3281 ≤ 44343219826239^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5380640087 10000000000 44343219826239 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2072150709/10000000000 : ℝ)^4305 ≤ (2535750122267/20000000000000 : ℝ)^3281 := by
    have hnat : (2072150709 : ℕ)^4305*20000000000000^3281 ≤ 2535750122267^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072150709 10000000000 2535750122267 20000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2626960689/5000000000 : ℝ)^4305 ≤ (21489014772321/50000000000000 : ℝ)^3281 := by
    have hnat : (2626960689 : ℕ)^4305*50000000000000^3281 ≤ 21489014772321^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626960689 5000000000 21489014772321 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5380640087/10000000000 : ℝ), (-2072150709/10000000000 : ℝ), (2626960689/5000000000 : ℝ)] ![(44343219826239/100000000000000 : ℝ), (2535750122267/20000000000000 : ℝ), (21489014772321/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5380640087/10000000000 : ℝ)|^4305 ≤ (44343219826239/100000000000000 : ℝ)^3281
        have hw : |(5380640087/10000000000 : ℝ)|=(5380640087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2072150709/10000000000 : ℝ)|^4305 ≤ (2535750122267/20000000000000 : ℝ)^3281
        have hw : |(-2072150709/10000000000 : ℝ)|=(2072150709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2626960689/5000000000 : ℝ)|^4305 ≤ (21489014772321/50000000000000 : ℝ)^3281
        have hw : |(2626960689/5000000000 : ℝ)|=(2626960689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_box_14 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1345159969/2500000000 : ℝ)*x 0 + (2626960681/5000000000 : ℝ)*x 1 + (-414430203/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1345159969/2500000000 : ℝ)^4305 ≤ (44343217544623/100000000000000 : ℝ)^3281 := by
    have hnat : (1345159969 : ℕ)^4305*100000000000000^3281 ≤ 44343217544623^3281*2500000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345159969 2500000000 44343217544623 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2626960681/5000000000 : ℝ)^4305 ≤ (4297802937291/10000000000000 : ℝ)^3281 := by
    have hnat : (2626960681 : ℕ)^4305*10000000000000^3281 ≤ 4297802937291^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626960681 5000000000 4297802937291 10000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (414430203/2000000000 : ℝ)^4305 ≤ (6339376533993/50000000000000 : ℝ)^3281 := by
    have hnat : (414430203 : ℕ)^4305*50000000000000^3281 ≤ 6339376533993^3281*2000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414430203 2000000000 6339376533993 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1345159969/2500000000 : ℝ), (2626960681/5000000000 : ℝ), (-414430203/2000000000 : ℝ)] ![(44343217544623/100000000000000 : ℝ), (4297802937291/10000000000000 : ℝ), (6339376533993/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1345159969/2500000000 : ℝ)|^4305 ≤ (44343217544623/100000000000000 : ℝ)^3281
        have hw : |(1345159969/2500000000 : ℝ)|=(1345159969/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2626960681/5000000000 : ℝ)|^4305 ≤ (4297802937291/10000000000000 : ℝ)^3281
        have hw : |(2626960681/5000000000 : ℝ)|=(2626960681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-414430203/2000000000 : ℝ)|^4305 ≤ (6339376533993/50000000000000 : ℝ)^3281
        have hw : |(-414430203/2000000000 : ℝ)|=(414430203/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_box_15 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1037495751/2500000000 : ℝ)*x 0 + (88347113/200000000 : ℝ)*x 1 + (4417355503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1037495751/2500000000 : ℝ)^4305 ≤ (6307664439013/20000000000000 : ℝ)^3281 := by
    have hnat : (1037495751 : ℕ)^4305*20000000000000^3281 ≤ 6307664439013^3281*2500000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037495751 2500000000 6307664439013 20000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (88347113/200000000 : ℝ)^4305 ≤ (34230839641431/100000000000000 : ℝ)^3281 := by
    have hnat : (88347113 : ℕ)^4305*100000000000000^3281 ≤ 34230839641431^3281*200000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88347113 200000000 34230839641431 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4417355503/10000000000 : ℝ)^4305 ≤ (17115419073391/50000000000000 : ℝ)^3281 := by
    have hnat : (4417355503 : ℕ)^4305*50000000000000^3281 ≤ 17115419073391^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4417355503 10000000000 17115419073391 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1037495751/2500000000 : ℝ), (88347113/200000000 : ℝ), (4417355503/10000000000 : ℝ)] ![(6307664439013/20000000000000 : ℝ), (34230839641431/100000000000000 : ℝ), (17115419073391/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1037495751/2500000000 : ℝ)|^4305 ≤ (6307664439013/20000000000000 : ℝ)^3281
        have hw : |(1037495751/2500000000 : ℝ)|=(1037495751/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(88347113/200000000 : ℝ)|^4305 ≤ (34230839641431/100000000000000 : ℝ)^3281
        have hw : |(88347113/200000000 : ℝ)|=(88347113/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4417355503/10000000000 : ℝ)|^4305 ≤ (17115419073391/50000000000000 : ℝ)^3281
        have hw : |(4417355503/10000000000 : ℝ)|=(4417355503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1345_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154846843/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3677/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11157/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(7857/12500 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58947/100000 : ℝ) ∧ (19993/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (21091/25000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3677/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11157/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3677/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11157/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3677/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11157/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3677/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11157/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3677/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11157/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3677/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11157/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11157/100000 : ℝ) ^ (269/64 : ℝ) ≤ (1984964757195533/20000000000000000000 : ℝ) := by
    have hpowers : (11157/100000 : ℝ)^269 ≤ (1984964757195533/20000000000000000000 : ℝ)^64 := by
      have hnat : (11157 : ℕ)^269*20000000000000000000^64 ≤ 1984964757195533^64*100000^269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11157 100000 1984964757195533 20000000000000000000 269 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11157/100000 : ℝ)) (X := (1984964757195533/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 269 64 (by norm_num) hpowers
    exact h
  have hpowhi : (3677/25000 : ℝ) ^ (269/64 : ℝ) ≤ (317047121172657/1000000000000000000 : ℝ) := by
    have hpowers : (3677/25000 : ℝ)^269 ≤ (317047121172657/1000000000000000000 : ℝ)^64 := by
      have hnat : (3677 : ℕ)^269*1000000000000000000^64 ≤ 317047121172657^64*25000^269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3677 25000 317047121172657 1000000000000000000 269 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3677/25000 : ℝ)) (X := (317047121172657/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 269 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001984964757195533/10000000000000000000 : ℝ) ≤ (312514756986181/312500000000000 : ℝ) ^ (269/64 : ℝ) := by
    have hpowers : (10001984964757195533/10000000000000000000 : ℝ)^64 ≤ (312514756986181/312500000000000 : ℝ)^269 := by
      have hnat : (10001984964757195533 : ℕ)^64*312500000000000^269 ≤ 312514756986181^269*10000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001984964757195533 10000000000000000000 312514756986181 312500000000000 64 269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312514756986181/312500000000000 : ℝ)) (X := (10001984964757195533/10000000000000000000 : ℝ)) (by norm_num) 269 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (20008325907180648673/20000000000000000000 : ℝ) ≤ (10000990285418807/10000000000000000 : ℝ) ^ (269/64 : ℝ) := by
    have hpowers : (20008325907180648673/20000000000000000000 : ℝ)^64 ≤ (10000990285418807/10000000000000000 : ℝ)^269 := by
      have hnat : (20008325907180648673 : ℕ)^64*10000000000000000^269 ≤ 10000990285418807^269*20000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20008325907180648673 20000000000000000000 10000990285418807 10000000000000000 64 269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000990285418807/10000000000000000 : ℝ)) (X := (20008325907180648673/20000000000000000000 : ℝ)) (by norm_num) 269 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (500317047121172657/500000000000000000 : ℝ) ≤ (5000754173639911/5000000000000000 : ℝ) ^ (269/64 : ℝ) := by
    have hpowers : (500317047121172657/500000000000000000 : ℝ)^64 ≤ (5000754173639911/5000000000000000 : ℝ)^269 := by
      have hnat : (500317047121172657 : ℕ)^64*5000000000000000^269 ≤ 5000754173639911^269*500000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500317047121172657 500000000000000000 5000754173639911 5000000000000000 64 269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000754173639911/5000000000000000 : ℝ)) (X := (500317047121172657/500000000000000000 : ℝ)) (by norm_num) 269 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1984964757195533/20000000000000000000 : ℝ) ≤ ((17750058416743515341/17755000000000000000 : ℝ)+2*(103612372203/71020000000000 : ℝ)*(11157/100000 : ℝ))^(269/64 : ℝ) := by
    rw [show (17750058416743515341/17755000000000000000 : ℝ)+2*(103612372203/71020000000000 : ℝ)*(11157/100000 : ℝ)=(312514756986181/312500000000000 : ℝ) by norm_num, show 1+2*(1984964757195533/20000000000000000000 : ℝ)=(10001984964757195533/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(317047121172657/1000000000000000000 : ℝ)+(1984964757195533/20000000000000000000 : ℝ) ≤ ((17750058416743515341/17755000000000000000 : ℝ)+(103612372203/71020000000000 : ℝ)*((3677/25000 : ℝ)+(11157/100000 : ℝ)))^(269/64 : ℝ) := by
    rw [show (17750058416743515341/17755000000000000000 : ℝ)+(103612372203/71020000000000 : ℝ)*((3677/25000 : ℝ)+(11157/100000 : ℝ))=(10000990285418807/10000000000000000 : ℝ) by norm_num, show 1+(317047121172657/1000000000000000000 : ℝ)+(1984964757195533/20000000000000000000 : ℝ)=(20008325907180648673/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(317047121172657/1000000000000000000 : ℝ) ≤ ((17750058416743515341/17755000000000000000 : ℝ)+2*(103612372203/71020000000000 : ℝ)*(3677/25000 : ℝ))^(269/64 : ℝ) := by
    rw [show (17750058416743515341/17755000000000000000 : ℝ)+2*(103612372203/71020000000000 : ℝ)*(3677/25000 : ℝ)=(5000754173639911/5000000000000000 : ℝ) by norm_num, show 1+2*(317047121172657/1000000000000000000 : ℝ)=(500317047121172657/500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17750058416743515341/17755000000000000000 : ℝ)*(X 1 0+X 2 0)+(103612372203/71020000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (269/64 : ℝ)) (lo := (11157/100000 : ℝ)) (hi := (3677/25000 : ℝ)) (c := (17750058416743515341/17755000000000000000 : ℝ)) (alpha := (103612372203/71020000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17750058416743515341/17755000000000000000 : ℝ)*(X 0 1+X 2 1)+(103612372203/71020000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (269/64 : ℝ)) (lo := (11157/100000 : ℝ)) (hi := (3677/25000 : ℝ)) (c := (17750058416743515341/17755000000000000000 : ℝ)) (alpha := (103612372203/71020000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17750058416743515341/17755000000000000000 : ℝ)*(X 0 2+X 1 2)+(103612372203/71020000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (269/64 : ℝ)) (lo := (11157/100000 : ℝ)) (hi := (3677/25000 : ℝ)) (c := (17750058416743515341/17755000000000000000 : ℝ)) (alpha := (103612372203/71020000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-14994951/80000000 : ℝ)*X 0 0+(2694907301/5000000000 : ℝ)*X 0 1+(5389814491/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2642602917/5000000000 : ℝ)*X 1 0+(-2017701979/10000000000 : ℝ)*X 1 1+(5389814401/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1057041149/2000000000 : ℝ)*X 2 0+(5389814559/10000000000 : ℝ)*X 2 1+(-403540377/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((69905571/156250000 : ℝ)*X 0 0+(4255661559/10000000000 : ℝ)*X 0 1+(4255661643/10000000000 : ℝ)*X 0 2+(69905571/156250000 : ℝ)*X 1 0+(4255661559/10000000000 : ℝ)*X 1 1+(4255661643/10000000000 : ℝ)*X 1 2+(69905571/156250000 : ℝ)*X 2 0+(4255661559/10000000000 : ℝ)*X 2 1+(4255661643/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-552787917/2500000000 : ℝ)*X 0 0+(164531029/312500000 : ℝ)*X 0 1+(105299861/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2686433173/5000000000 : ℝ)*X 1 0+(-258476257/1250000000 : ℝ)*X 1 1+(1316248357/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2686433693/5000000000 : ℝ)*X 2 0+(329062047/625000000 : ℝ)*X 2 1+(-51695239/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2088395143/5000000000 : ℝ)*X 0 0+(4404191551/10000000000 : ℝ)*X 0 1+(4404190931/10000000000 : ℝ)*X 0 2+(2088395143/5000000000 : ℝ)*X 1 0+(4404191551/10000000000 : ℝ)*X 1 1+(4404190931/10000000000 : ℝ)*X 1 2+(2088395143/5000000000 : ℝ)*X 2 0+(4404191551/10000000000 : ℝ)*X 2 1+(4404190931/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-13377613/62500000 : ℝ)*X 0 0+(2589523891/5000000000 : ℝ)*X 0 1+(1350958577/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5275356387/10000000000 : ℝ)*X 1 0+(-2011941707/10000000000 : ℝ)*X 1 1+(1350958093/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5275354159/10000000000 : ℝ)*X 2 0+(2701917113/5000000000 : ℝ)*X 2 1+(-2011942193/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((901354343/2000000000 : ℝ)*X 0 0+(211948347/500000000 : ℝ)*X 0 1+(4238966211/10000000000 : ℝ)*X 0 2+(901354343/2000000000 : ℝ)*X 1 0+(211948347/500000000 : ℝ)*X 1 1+(4238966211/10000000000 : ℝ)*X 1 2+(901354343/2000000000 : ℝ)*X 2 0+(211948347/500000000 : ℝ)*X 2 1+(4238966211/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-972716053/5000000000 : ℝ)*X 0 0+(5473561171/10000000000 : ℝ)*X 0 1+(525392119/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5380640087/10000000000 : ℝ)*X 1 0+(-2072150709/10000000000 : ℝ)*X 1 1+(2626960689/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1345159969/2500000000 : ℝ)*X 2 0+(2626960681/5000000000 : ℝ)*X 2 1+(-414430203/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1037495751/2500000000 : ℝ)*X 0 0+(88347113/200000000 : ℝ)*X 0 1+(4417355503/10000000000 : ℝ)*X 0 2+(1037495751/2500000000 : ℝ)*X 1 0+(88347113/200000000 : ℝ)*X 1 1+(4417355503/10000000000 : ℝ)*X 1 2+(1037495751/2500000000 : ℝ)*X 2 0+(88347113/200000000 : ℝ)*X 2 1+(4417355503/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-7857/12500 : ℝ) ≤ (-1115972364487675353939419109/1775500000000000000000000000 : ℝ) := by norm_num
    linear_combination (3074691/4000000000000 : ℝ)*(upper0) + (196794641/50000000000000 : ℝ)*(lower2) + (14880109/100000000000000 : ℝ)*(upper5) + (584800287999599/20000000000000 : ℝ)*(major0) + (584800287999599/20000000000000 : ℝ)*(major1) + (584800287999599/20000000000000 : ℝ)*(major2) + (1027898741/50000000000000 : ℝ)*(sp3) + (995157509341069/25000000000000 : ℝ)*(sp4) + (1990286068714671/50000000000000 : ℝ)*(sp5) + (1990299184766531/50000000000000 : ℝ)*(sp6) + (1888316351829333/100000000000000 : ℝ)*(sp7) + (5760725111/100000000000000 : ℝ)*(sp8) + (15915165011/25000000000000 : ℝ)*(sp13) + (1497142253/4000000000000 : ℝ)*(sp14) + (29504975119169/1562500000000 : ℝ)*(f.failure) + (3980635798089387/100000000000000 : ℝ)*(f.sum) + (11779118532113/3551000000000000000000000000 : ℝ)*base66 + (8980090571782501741/355100000000000000000000000000000 : ℝ)*base68 + (2450827677878898259/355100000000000000000000000000000 : ℝ)*base69 + (3950969761616998259/355100000000000000000000000000000 : ℝ)*base71 + (14106330688369/1775500000000000000000000000 : ℝ)*base74 + (4592366526276898259/355100000000000000000000000000000 : ℝ)*base75 + (333391093290201741/355100000000000000000000000000000 : ℝ)*base78 + (477571677636901741/355100000000000000000000000000000 : ℝ)*base80 + (6092328856931/3551000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1245967/156250000000000000000 : ℝ)*base89 + (1245967/156250000000000000000 : ℝ)*base91 + (1245967/156250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (58947/100000 : ℝ) ≤ (16353883930465847566948261351461/27742187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (8132807/100000000000000 : ℝ)*(upper0) + (7930853/50000000000000 : ℝ)*(lower1) + (15975793/100000000000000 : ℝ)*(upper4) + (187050187680357/6250000000000 : ℝ)*(major0) + (187050187680357/6250000000000 : ℝ)*(major1) + (187050187680357/6250000000000 : ℝ)*(major2) + (504150547298781/12500000000000 : ℝ)*(sp0) + (4033167168431977/100000000000000 : ℝ)*(sp1) + (63018815160229/1562500000000 : ℝ)*(sp2) + (1932747918394203/100000000000000 : ℝ)*(sp3) + (39550823/2500000000000 : ℝ)*(sp6) + (624504833/25000000000000 : ℝ)*(sp7) + (85868583/6250000000000 : ℝ)*(sp8) + (19291927799/50000000000000 : ℝ)*(sp9) + (386550083282707/20000000000000 : ℝ)*(f.failure) + (504150719035947/12500000000000 : ℝ)*(f.sum) + (583313771887/221937500000000000000000000 : ℝ)*base65 + (598572045115612013/110968750000000000000000000000000 : ℝ)*base68 + (761608687765987013/110968750000000000000000000000000 : ℝ)*base70 + (464737898655518263/110968750000000000000000000000000 : ℝ)*base72 + (11774420482901/887750000000000000000000000 : ℝ)*base74 + (387633618140705763/110968750000000000000000000000000 : ℝ)*base76 + (1128662553449143263/110968750000000000000000000000000 : ℝ)*base78 + (991298902560887987/110968750000000000000000000000000 : ℝ)*base79 + (110388097879/28408000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (15444001/2000000000000000000000 : ℝ)*base89 + (15444001/2000000000000000000000 : ℝ)*base91 + (15444001/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (19993/25000 : ℝ) ≤ (177493241289244173316988751/221937500000000000000000000 : ℝ) := by norm_num
    linear_combination (17897997/10000000000000 : ℝ)*(upper1) + (259192449/50000000000000 : ℝ)*(upper2) + (29322993/6250000000000 : ℝ)*(lower5) + (413101245669729/12500000000000 : ℝ)*(major0) + (413101245669729/12500000000000 : ℝ)*(major1) + (413101245669729/12500000000000 : ℝ)*(major2) + (225527306431/100000000000000 : ℝ)*(sp1) + (352695128061/50000000000000 : ℝ)*(sp2) + (238874376579/100000000000000 : ℝ)*(sp3) + (71911999873/100000000000000 : ℝ)*(sp4) + (2224322773890699/50000000000000 : ℝ)*(sp8) + (111212298311871/2500000000000 : ℝ)*(sp9) + (1112003017381287/25000000000000 : ℝ)*(sp10) + (1067002727310031/50000000000000 : ℝ)*(sp11) + (1067122164498321/50000000000000 : ℝ)*(f.failure) + (444871745978127/10000000000000 : ℝ)*(f.sum) + (3986950953247/1775500000000000000000000000 : ℝ)*base65 + (753563114039374911/221937500000000000000000000000000 : ℝ)*base68 + (3056705159157624911/221937500000000000000000000000000 : ℝ)*base70 + (761778467724937411/221937500000000000000000000000000 : ℝ)*base72 + (451529981477/443875000000000000000000000 : ℝ)*base74 + (434649564503187589/221937500000000000000000000000000 : ℝ)*base75 + (495499714007062589/221937500000000000000000000000000 : ℝ)*base77 + (265143712050250089/221937500000000000000000000000000 : ℝ)*base79 + (39673680699/3551000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (85650603/5000000000000000000000 : ℝ)*base89 + (85650603/5000000000000000000000 : ℝ)*base91 + (85650603/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-21091/25000 : ℝ) ≤ (-187229226429682420824664281657093/221937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13977171/20000000000000 : ℝ)*(lower0) + (1090833/50000000000000 : ℝ)*(lower1) + (18908727/25000000000000 : ℝ)*(upper3) + (36415039/25000000000000 : ℝ)*(lower4) + (835324653634409/25000000000000 : ℝ)*(major0) + (835324653634409/25000000000000 : ℝ)*(major1) + (835324653634409/25000000000000 : ℝ)*(major2) + (143092303/25000000000000 : ℝ)*(sp0) + (3190340311/5000000000000 : ℝ)*(sp6) + (1148466389/3125000000000 : ℝ)*(sp7) + (569113549100739/12500000000000 : ℝ)*(sp12) + (1138227241293781/25000000000000 : ℝ)*(sp13) + (4552845158368903/100000000000000 : ℝ)*(sp14) + (215777192621961/10000000000000 : ℝ)*(sp15) + (1078904338572029/50000000000000 : ℝ)*(f.failure) + (1138227241293781/25000000000000 : ℝ)*(f.sum) + (249914526341/110968750000000000000000000 : ℝ)*base65 + (5307027358511781531/443875000000000000000000000000000 : ℝ)*base68 + (1161647634154968469/443875000000000000000000000000000 : ℝ)*base69 + (5086423450765781531/443875000000000000000000000000000 : ℝ)*base72 + (1640541781519/887750000000000000000000000 : ℝ)*base73 + (544374609532531531/443875000000000000000000000000000 : ℝ)*base76 + (4949053530660781531/443875000000000000000000000000000 : ℝ)*base78 + (515970465331968469/443875000000000000000000000000000 : ℝ)*base79 + (38314582984557/710200000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (18754447/5000000000000000000000 : ℝ)*base89 + (18754447/5000000000000000000000 : ℝ)*base91 + (18754447/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1345_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154846843/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3677/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11157/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7857/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(58947/100000 : ℝ) else (19993/25000 : ℝ) ≤ X j i ∧ X j i ≤ (21091/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1345_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1345_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154846843/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14717/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2787/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7857/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(58947/100000 : ℝ) else (19993/25000 : ℝ) ≤ X j i ∧ X j i ≤ (21091/25000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1345_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1345_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1345_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154846843/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14717/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2787/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7857/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(58947/100000 : ℝ) else (19993/25000 : ℝ) ≤ X j i ∧ X j i ≤ (21091/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1345_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
