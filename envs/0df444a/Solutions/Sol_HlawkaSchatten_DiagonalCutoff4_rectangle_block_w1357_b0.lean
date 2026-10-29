-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1357_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:09:52.145982+00:00
-- url     : https://prove2.me/submissions/5c4e2923-b673-4093-89ff-47f62c26d8e3

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
theorem support_rectangle_w1357_s0_0 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-180031183/1000000000 : ℝ)*x 0 + (1497615837/2500000000 : ℝ)*x 1 + (75226177/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (180031183/1000000000 : ℝ)^4317 ≤ (1056303442531/10000000000000 : ℝ)^3293 := by
    have hnat : (180031183 : ℕ)^4317*10000000000000^3293 ≤ 1056303442531^3293*1000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180031183 1000000000 1056303442531 10000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1497615837/2500000000 : ℝ)^4317 ≤ (10216188850581/20000000000000 : ℝ)^3293 := by
    have hnat : (1497615837 : ℕ)^4317*20000000000000^3293 ≤ 10216188850581^3293*2500000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1497615837 2500000000 10216188850581 20000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (75226177/156250000 : ℝ)^4317 ≤ (19178010651753/50000000000000 : ℝ)^3293 := by
    have hnat : (75226177 : ℕ)^4317*50000000000000^3293 ≤ 19178010651753^3293*156250000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75226177 156250000 19178010651753 50000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-180031183/1000000000 : ℝ), (1497615837/2500000000 : ℝ), (75226177/156250000 : ℝ)] ![(1056303442531/10000000000000 : ℝ), (10216188850581/20000000000000 : ℝ), (19178010651753/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-180031183/1000000000 : ℝ)|^4317 ≤ (1056303442531/10000000000000 : ℝ)^3293
        have hw : |(-180031183/1000000000 : ℝ)|=(180031183/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1497615837/2500000000 : ℝ)|^4317 ≤ (10216188850581/20000000000000 : ℝ)^3293
        have hw : |(1497615837/2500000000 : ℝ)|=(1497615837/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(75226177/156250000 : ℝ)|^4317 ≤ (19178010651753/50000000000000 : ℝ)^3293
        have hw : |(75226177/156250000 : ℝ)|=(75226177/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s0_1 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1375033377/2500000000 : ℝ)*x 0 + (-2468012643/10000000000 : ℝ)*x 1 + (4814475809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1375033377/2500000000 : ℝ)^4317 ≤ (5708855061051/12500000000000 : ℝ)^3293 := by
    have hnat : (1375033377 : ℕ)^4317*12500000000000^3293 ≤ 5708855061051^3293*2500000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1375033377 2500000000 5708855061051 12500000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2468012643/10000000000 : ℝ)^4317 ≤ (1996641645999/12500000000000 : ℝ)^3293 := by
    have hnat : (2468012643 : ℕ)^4317*12500000000000^3293 ≤ 1996641645999^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2468012643 10000000000 1996641645999 12500000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4814475809/10000000000 : ℝ)^4317 ≤ (38356026327163/100000000000000 : ℝ)^3293 := by
    have hnat : (4814475809 : ℕ)^4317*100000000000000^3293 ≤ 38356026327163^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4814475809 10000000000 38356026327163 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1375033377/2500000000 : ℝ), (-2468012643/10000000000 : ℝ), (4814475809/10000000000 : ℝ)] ![(5708855061051/12500000000000 : ℝ), (1996641645999/12500000000000 : ℝ), (38356026327163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1375033377/2500000000 : ℝ)|^4317 ≤ (5708855061051/12500000000000 : ℝ)^3293
        have hw : |(1375033377/2500000000 : ℝ)|=(1375033377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2468012643/10000000000 : ℝ)|^4317 ≤ (1996641645999/12500000000000 : ℝ)^3293
        have hw : |(-2468012643/10000000000 : ℝ)|=(2468012643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4814475809/10000000000 : ℝ)|^4317 ≤ (38356026327163/100000000000000 : ℝ)^3293
        have hw : |(4814475809/10000000000 : ℝ)|=(4814475809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s0_2 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1100026671/2000000000 : ℝ)*x 0 + (4814475359/10000000000 : ℝ)*x 1 + (-1234006697/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1100026671/2000000000 : ℝ)^4317 ≤ (45670838822897/100000000000000 : ℝ)^3293 := by
    have hnat : (1100026671 : ℕ)^4317*100000000000000^3293 ≤ 45670838822897^3293*2000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100026671 2000000000 45670838822897 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4814475359/10000000000 : ℝ)^4317 ≤ (9589005406819/25000000000000 : ℝ)^3293 := by
    have hnat : (4814475359 : ℕ)^4317*25000000000000^3293 ≤ 9589005406819^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4814475359 10000000000 9589005406819 25000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1234006697/5000000000 : ℝ)^4317 ≤ (998321221247/6250000000000 : ℝ)^3293 := by
    have hnat : (1234006697 : ℕ)^4317*6250000000000^3293 ≤ 998321221247^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1234006697 5000000000 998321221247 6250000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1100026671/2000000000 : ℝ), (4814475359/10000000000 : ℝ), (-1234006697/5000000000 : ℝ)] ![(45670838822897/100000000000000 : ℝ), (9589005406819/25000000000000 : ℝ), (998321221247/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1100026671/2000000000 : ℝ)|^4317 ≤ (45670838822897/100000000000000 : ℝ)^3293
        have hw : |(1100026671/2000000000 : ℝ)|=(1100026671/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4814475359/10000000000 : ℝ)|^4317 ≤ (9589005406819/25000000000000 : ℝ)^3293
        have hw : |(4814475359/10000000000 : ℝ)|=(4814475359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1234006697/5000000000 : ℝ)|^4317 ≤ (998321221247/6250000000000 : ℝ)^3293
        have hw : |(-1234006697/5000000000 : ℝ)|=(1234006697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s0_3 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (835301989/2000000000 : ℝ)*x 0 + (1552927649/5000000000 : ℝ)*x 1 + (5582955129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (835301989/2000000000 : ℝ)^4317 ≤ (31834694600971/100000000000000 : ℝ)^3293 := by
    have hnat : (835301989 : ℕ)^4317*100000000000000^3293 ≤ 31834694600971^3293*2000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      835301989 2000000000 31834694600971 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1552927649/5000000000 : ℝ)^4317 ≤ (5397697643901/25000000000000 : ℝ)^3293 := by
    have hnat : (1552927649 : ℕ)^4317*25000000000000^3293 ≤ 5397697643901^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1552927649 5000000000 5397697643901 25000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5582955129/10000000000 : ℝ)^4317 ≤ (46574514798639/100000000000000 : ℝ)^3293 := by
    have hnat : (5582955129 : ℕ)^4317*100000000000000^3293 ≤ 46574514798639^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5582955129 10000000000 46574514798639 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(835301989/2000000000 : ℝ), (1552927649/5000000000 : ℝ), (5582955129/10000000000 : ℝ)] ![(31834694600971/100000000000000 : ℝ), (5397697643901/25000000000000 : ℝ), (46574514798639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(835301989/2000000000 : ℝ)|^4317 ≤ (31834694600971/100000000000000 : ℝ)^3293
        have hw : |(835301989/2000000000 : ℝ)|=(835301989/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1552927649/5000000000 : ℝ)|^4317 ≤ (5397697643901/25000000000000 : ℝ)^3293
        have hw : |(1552927649/5000000000 : ℝ)|=(1552927649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5582955129/10000000000 : ℝ)|^4317 ≤ (46574514798639/100000000000000 : ℝ)^3293
        have hw : |(5582955129/10000000000 : ℝ)|=(5582955129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s0_4 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1804690363/10000000000 : ℝ)*x 0 + (4844714831/10000000000 : ℝ)*x 1 + (5959143613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1804690363/10000000000 : ℝ)^4317 ≤ (10596726209407/100000000000000 : ℝ)^3293 := by
    have hnat : (1804690363 : ℕ)^4317*100000000000000^3293 ≤ 10596726209407^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1804690363 10000000000 10596726209407 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4844714831/10000000000 : ℝ)^4317 ≤ (19336078251987/50000000000000 : ℝ)^3293 := by
    have hnat : (4844714831 : ℕ)^4317*50000000000000^3293 ≤ 19336078251987^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4844714831 10000000000 19336078251987 50000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5959143613/10000000000 : ℝ)^4317 ≤ (6341389659967/12500000000000 : ℝ)^3293 := by
    have hnat : (5959143613 : ℕ)^4317*12500000000000^3293 ≤ 6341389659967^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5959143613 10000000000 6341389659967 12500000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1804690363/10000000000 : ℝ), (4844714831/10000000000 : ℝ), (5959143613/10000000000 : ℝ)] ![(10596726209407/100000000000000 : ℝ), (19336078251987/50000000000000 : ℝ), (6341389659967/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1804690363/10000000000 : ℝ)|^4317 ≤ (10596726209407/100000000000000 : ℝ)^3293
        have hw : |(-1804690363/10000000000 : ℝ)|=(1804690363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4844714831/10000000000 : ℝ)|^4317 ≤ (19336078251987/50000000000000 : ℝ)^3293
        have hw : |(4844714831/10000000000 : ℝ)|=(4844714831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5959143613/10000000000 : ℝ)|^4317 ≤ (6341389659967/12500000000000 : ℝ)^3293
        have hw : |(5959143613/10000000000 : ℝ)|=(5959143613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s0_5 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1035909119/2000000000 : ℝ)*x 0 + (-165418299/1250000000 : ℝ)*x 1 + (5959143069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1035909119/2000000000 : ℝ)^4317 ≤ (42213079789309/100000000000000 : ℝ)^3293 := by
    have hnat : (1035909119 : ℕ)^4317*100000000000000^3293 ≤ 42213079789309^3293*2000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035909119 2000000000 42213079789309 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (165418299/1250000000 : ℝ)^4317 ≤ (7055808985191/100000000000000 : ℝ)^3293 := by
    have hnat : (165418299 : ℕ)^4317*100000000000000^3293 ≤ 7055808985191^3293*1250000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165418299 1250000000 7055808985191 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5959143069/10000000000 : ℝ)^4317 ≤ (50731111208463/100000000000000 : ℝ)^3293 := by
    have hnat : (5959143069 : ℕ)^4317*100000000000000^3293 ≤ 50731111208463^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5959143069 10000000000 50731111208463 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1035909119/2000000000 : ℝ), (-165418299/1250000000 : ℝ), (5959143069/10000000000 : ℝ)] ![(42213079789309/100000000000000 : ℝ), (7055808985191/100000000000000 : ℝ), (50731111208463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1035909119/2000000000 : ℝ)|^4317 ≤ (42213079789309/100000000000000 : ℝ)^3293
        have hw : |(1035909119/2000000000 : ℝ)|=(1035909119/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-165418299/1250000000 : ℝ)|^4317 ≤ (7055808985191/100000000000000 : ℝ)^3293
        have hw : |(-165418299/1250000000 : ℝ)|=(165418299/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5959143069/10000000000 : ℝ)|^4317 ≤ (50731111208463/100000000000000 : ℝ)^3293
        have hw : |(5959143069/10000000000 : ℝ)|=(5959143069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s0_6 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1035909089/2000000000 : ℝ)*x 0 + (1489785939/2500000000 : ℝ)*x 1 + (-52933821/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1035909089/2000000000 : ℝ)^4317 ≤ (21106539093333/50000000000000 : ℝ)^3293 := by
    have hnat : (1035909089 : ℕ)^4317*50000000000000^3293 ≤ 21106539093333^3293*2000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035909089 2000000000 21106539093333 50000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1489785939/2500000000 : ℝ)^4317 ≤ (25365559437839/50000000000000 : ℝ)^3293 := by
    have hnat : (1489785939 : ℕ)^4317*50000000000000^3293 ≤ 25365559437839^3293*2500000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1489785939 2500000000 25365559437839 50000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52933821/400000000 : ℝ)^4317 ≤ (7055802925051/100000000000000 : ℝ)^3293 := by
    have hnat : (52933821 : ℕ)^4317*100000000000000^3293 ≤ 7055802925051^3293*400000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52933821 400000000 7055802925051 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1035909089/2000000000 : ℝ), (1489785939/2500000000 : ℝ), (-52933821/400000000 : ℝ)] ![(21106539093333/50000000000000 : ℝ), (25365559437839/50000000000000 : ℝ), (7055802925051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1035909089/2000000000 : ℝ)|^4317 ≤ (21106539093333/50000000000000 : ℝ)^3293
        have hw : |(1035909089/2000000000 : ℝ)|=(1035909089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1489785939/2500000000 : ℝ)|^4317 ≤ (25365559437839/50000000000000 : ℝ)^3293
        have hw : |(1489785939/2500000000 : ℝ)|=(1489785939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-52933821/400000000 : ℝ)|^4317 ≤ (7055802925051/100000000000000 : ℝ)^3293
        have hw : |(-52933821/400000000 : ℝ)|=(52933821/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s0_7 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (837145857/2000000000 : ℝ)*x 0 + (344953757/625000000 : ℝ)*x 1 + (3171827031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (837145857/2000000000 : ℝ)^4317 ≤ (31926851164623/100000000000000 : ℝ)^3293 := by
    have hnat : (837145857 : ℕ)^4317*100000000000000^3293 ≤ 31926851164623^3293*2000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      837145857 2000000000 31926851164623 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (344953757/625000000 : ℝ)^4317 ≤ (45879159315599/100000000000000 : ℝ)^3293 := by
    have hnat : (344953757 : ℕ)^4317*100000000000000^3293 ≤ 45879159315599^3293*625000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344953757 625000000 45879159315599 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3171827031/10000000000 : ℝ)^4317 ≤ (4438797900157/20000000000000 : ℝ)^3293 := by
    have hnat : (3171827031 : ℕ)^4317*20000000000000^3293 ≤ 4438797900157^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3171827031 10000000000 4438797900157 20000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(837145857/2000000000 : ℝ), (344953757/625000000 : ℝ), (3171827031/10000000000 : ℝ)] ![(31926851164623/100000000000000 : ℝ), (45879159315599/100000000000000 : ℝ), (4438797900157/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(837145857/2000000000 : ℝ)|^4317 ≤ (31926851164623/100000000000000 : ℝ)^3293
        have hw : |(837145857/2000000000 : ℝ)|=(837145857/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(344953757/625000000 : ℝ)|^4317 ≤ (45879159315599/100000000000000 : ℝ)^3293
        have hw : |(344953757/625000000 : ℝ)|=(344953757/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3171827031/10000000000 : ℝ)|^4317 ≤ (4438797900157/20000000000000 : ℝ)^3293
        have hw : |(3171827031/10000000000 : ℝ)|=(3171827031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1357_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155319977/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (763/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6691/25000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (1079/256 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^1079 ≤ (0 : ℝ)^256 := by
      have hnat : (0 : ℕ)^1079*1^256 ≤ 0^256*1^1079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 1079 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (1079/256 : ℝ) ≤ (420508750149564669/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^1079 ≤ (420508750149564669/20000000000000000000 : ℝ)^256 := by
      have hnat : (2 : ℕ)^1079*20000000000000000000^256 ≤ 420508750149564669^256*5^1079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 420508750149564669 20000000000000000000 1079 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (420508750149564669/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (1079/256 : ℝ) := by
    have hpowers : (1 : ℝ)^256 ≤ (1 : ℝ)^1079 := by
      have hnat : (1 : ℕ)^256*1^1079 ≤ 1^1079*1^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 256 1079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (20420508750149564669/20000000000000000000 : ℝ) ≤ (10049489136961237/10000000000000000 : ℝ) ^ (1079/256 : ℝ) := by
    have hpowers : (20420508750149564669/20000000000000000000 : ℝ)^256 ≤ (10049489136961237/10000000000000000 : ℝ)^1079 := by
      have hnat : (20420508750149564669 : ℕ)^256*10000000000000000^1079 ≤ 10049489136961237^1079*20000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20420508750149564669 20000000000000000000 10049489136961237 10000000000000000 256 1079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10049489136961237/10000000000000000 : ℝ)) (X := (20420508750149564669/20000000000000000000 : ℝ)) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (10420508750149564669/10000000000000000000 : ℝ) ≤ (5049489136961237/5000000000000000 : ℝ) ^ (1079/256 : ℝ) := by
    have hpowers : (10420508750149564669/10000000000000000000 : ℝ)^256 ≤ (5049489136961237/5000000000000000 : ℝ)^1079 := by
      have hnat : (10420508750149564669 : ℕ)^256*5000000000000000^1079 ≤ 5049489136961237^1079*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10420508750149564669 10000000000000000000 5049489136961237 5000000000000000 256 1079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5049489136961237/5000000000000000 : ℝ)) (X := (10420508750149564669/10000000000000000000 : ℝ)) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(49489136961237/4000000000000000 : ℝ)*(0 : ℝ))^(1079/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(49489136961237/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(420508750149564669/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(49489136961237/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(1079/256 : ℝ) := by
    rw [show (1 : ℝ)+(49489136961237/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10049489136961237/10000000000000000 : ℝ) by norm_num, show 1+(420508750149564669/20000000000000000000 : ℝ)+(0 : ℝ)=(20420508750149564669/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(420508750149564669/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(49489136961237/4000000000000000 : ℝ)*(2/5 : ℝ))^(1079/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(49489136961237/4000000000000000 : ℝ)*(2/5 : ℝ)=(5049489136961237/5000000000000000 : ℝ) by norm_num, show 1+2*(420508750149564669/20000000000000000000 : ℝ)=(10420508750149564669/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(49489136961237/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1079/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (49489136961237/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(49489136961237/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1079/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (49489136961237/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(49489136961237/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1079/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (49489136961237/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-180031183/1000000000 : ℝ)*X 0 0+(1497615837/2500000000 : ℝ)*X 0 1+(75226177/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1375033377/2500000000 : ℝ)*X 1 0+(-2468012643/10000000000 : ℝ)*X 1 1+(4814475809/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1100026671/2000000000 : ℝ)*X 2 0+(4814475359/10000000000 : ℝ)*X 2 1+(-1234006697/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((835301989/2000000000 : ℝ)*X 0 0+(1552927649/5000000000 : ℝ)*X 0 1+(5582955129/10000000000 : ℝ)*X 0 2+(835301989/2000000000 : ℝ)*X 1 0+(1552927649/5000000000 : ℝ)*X 1 1+(5582955129/10000000000 : ℝ)*X 1 2+(835301989/2000000000 : ℝ)*X 2 0+(1552927649/5000000000 : ℝ)*X 2 1+(5582955129/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1804690363/10000000000 : ℝ)*X 0 0+(4844714831/10000000000 : ℝ)*X 0 1+(5959143613/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1035909119/2000000000 : ℝ)*X 1 0+(-165418299/1250000000 : ℝ)*X 1 1+(5959143069/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1035909089/2000000000 : ℝ)*X 2 0+(1489785939/2500000000 : ℝ)*X 2 1+(-52933821/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((837145857/2000000000 : ℝ)*X 0 0+(344953757/625000000 : ℝ)*X 0 1+(3171827031/10000000000 : ℝ)*X 0 2+(837145857/2000000000 : ℝ)*X 1 0+(344953757/625000000 : ℝ)*X 1 1+(3171827031/10000000000 : ℝ)*X 1 2+(837145857/2000000000 : ℝ)*X 2 0+(344953757/625000000 : ℝ)*X 2 1+(3171827031/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (316195847181663518868261/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (38905411/25000000000000 : ℝ)*(base1) + (147418539/10000000000000 : ℝ)*(base19) + (145053059/10000000000000 : ℝ)*(base23) + (126135843/50000000000000 : ℝ)*(upper3) + (2075393/4000000000000 : ℝ)*(upper5) + (627030264040949/100000000000000 : ℝ)*(major0) + (627030264040949/100000000000000 : ℝ)*(major1) + (627030264040949/100000000000000 : ℝ)*(major2) + (425177015715839/50000000000000 : ℝ)*(sp0) + (850356578811049/100000000000000 : ℝ)*(sp1) + (850356602465849/100000000000000 : ℝ)*(sp2) + (20184983846193/5000000000000 : ℝ)*(sp3) + (835437281/20000000000000 : ℝ)*(sp4) + (1899799/78125000000 : ℝ)*(sp7) + (12615695759007/3125000000000 : ℝ)*(f.failure) + (850358052996439/100000000000000 : ℝ)*(f.sum) + (386730564693913/200000000000000000000000000000 : ℝ)*base65 + (226063826093913/400000000000000000000000000000 : ℝ)*base67 + (1213440430093913/400000000000000000000000000000 : ℝ)*base69 + (232603123106087/400000000000000000000000000000 : ℝ)*base72 + (879365511093913/200000000000000000000000000000 : ℝ)*base73 + (622403633293913/400000000000000000000000000000 : ℝ)*base75 + (596291475693913/400000000000000000000000000000 : ℝ)*base77 + (1161657890706087/400000000000000000000000000000 : ℝ)*base80 + (1103873842893913/200000000000000000000000000000 : ℝ)*base81 + (842161/312500000000000000000 : ℝ)*base90 + (842161/312500000000000000000 : ℝ)*base92 + (842161/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (966953614760088953277969/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (899453067/50000000000000 : ℝ)*(base19) + (993696683/50000000000000 : ℝ)*(base23) + (97278969/50000000000000 : ℝ)*(base39) + (51993311/25000000000000 : ℝ)*(upper3) + (279516687/100000000000000 : ℝ)*(upper5) + (661658525763121/100000000000000 : ℝ)*(major0) + (661658525763121/100000000000000 : ℝ)*(major1) + (661658331205183/100000000000000 : ℝ)*(major2) + (82141741/2000000000000 : ℝ)*(sp1) + (4503937427/100000000000000 : ℝ)*(sp2) + (897319480991887/100000000000000 : ℝ)*(sp4) + (897313574998703/100000000000000 : ℝ)*(sp5) + (897313184219031/100000000000000 : ℝ)*(sp6) + (425997053658539/100000000000000 : ℝ)*(sp7) + (425997053658539/100000000000000 : ℝ)*(f.failure) + (7010309965233/781250000000 : ℝ)*(f.sum) + (56060945752003/25000000000000000000000000000 : ℝ)*base65 + (2989484421508629/400000000000000000000000000000 : ℝ)*base68 + (549268245140677/400000000000000000000000000000 : ℝ)*base69 + (288764844491371/400000000000000000000000000000 : ℝ)*base71 + (61865654447997/25000000000000000000000000000 : ℝ)*base74 + (261829845259323/400000000000000000000000000000 : ℝ)*base76 + (432660023140677/400000000000000000000000000000 : ℝ)*base77 + (1631171182340677/400000000000000000000000000000 : ℝ)*base79 + (1139965581940677/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (56666397/10000000000000000000000 : ℝ)*base90 + (56666397/10000000000000000000000 : ℝ)*base92 + (56666397/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1357_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155319977/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (763/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6691/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1357_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1357_s1_0 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-198296147/1000000000 : ℝ)*x 0 + (2817739717/5000000000 : ℝ)*x 1 + (5052472667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (198296147/1000000000 : ℝ)^4317 ≤ (2397923135327/20000000000000 : ℝ)^3293 := by
    have hnat : (198296147 : ℕ)^4317*20000000000000^3293 ≤ 2397923135327^3293*1000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198296147 1000000000 2397923135327 20000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2817739717/5000000000 : ℝ)^4317 ≤ (23574890113727/50000000000000 : ℝ)^3293 := by
    have hnat : (2817739717 : ℕ)^4317*50000000000000^3293 ≤ 23574890113727^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2817739717 5000000000 23574890113727 50000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5052472667/10000000000 : ℝ)^4317 ≤ (2553787755261/6250000000000 : ℝ)^3293 := by
    have hnat : (5052472667 : ℕ)^4317*6250000000000^3293 ≤ 2553787755261^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5052472667 10000000000 2553787755261 6250000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-198296147/1000000000 : ℝ), (2817739717/5000000000 : ℝ), (5052472667/10000000000 : ℝ)] ![(2397923135327/20000000000000 : ℝ), (23574890113727/50000000000000 : ℝ), (2553787755261/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-198296147/1000000000 : ℝ)|^4317 ≤ (2397923135327/20000000000000 : ℝ)^3293
        have hw : |(-198296147/1000000000 : ℝ)|=(198296147/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2817739717/5000000000 : ℝ)|^4317 ≤ (23574890113727/50000000000000 : ℝ)^3293
        have hw : |(2817739717/5000000000 : ℝ)|=(2817739717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5052472667/10000000000 : ℝ)|^4317 ≤ (2553787755261/6250000000000 : ℝ)^3293
        have hw : |(5052472667/10000000000 : ℝ)|=(5052472667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s1_1 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5404159983/10000000000 : ℝ)*x 0 + (-1146836287/5000000000 : ℝ)*x 1 + (252623671/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5404159983/10000000000 : ℝ)^4317 ≤ (11157237000397/25000000000000 : ℝ)^3293 := by
    have hnat : (5404159983 : ℕ)^4317*25000000000000^3293 ≤ 11157237000397^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404159983 10000000000 11157237000397 25000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1146836287/5000000000 : ℝ)^4317 ≤ (2902087982893/20000000000000 : ℝ)^3293 := by
    have hnat : (1146836287 : ℕ)^4317*20000000000000^3293 ≤ 2902087982893^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1146836287 5000000000 2902087982893 20000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (252623671/500000000 : ℝ)^4317 ≤ (40860612067543/100000000000000 : ℝ)^3293 := by
    have hnat : (252623671 : ℕ)^4317*100000000000000^3293 ≤ 40860612067543^3293*500000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252623671 500000000 40860612067543 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5404159983/10000000000 : ℝ), (-1146836287/5000000000 : ℝ), (252623671/500000000 : ℝ)] ![(11157237000397/25000000000000 : ℝ), (2902087982893/20000000000000 : ℝ), (40860612067543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5404159983/10000000000 : ℝ)|^4317 ≤ (11157237000397/25000000000000 : ℝ)^3293
        have hw : |(5404159983/10000000000 : ℝ)|=(5404159983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1146836287/5000000000 : ℝ)|^4317 ≤ (2902087982893/20000000000000 : ℝ)^3293
        have hw : |(-1146836287/5000000000 : ℝ)|=(1146836287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(252623671/500000000 : ℝ)|^4317 ≤ (40860612067543/100000000000000 : ℝ)^3293
        have hw : |(252623671/500000000 : ℝ)|=(252623671/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s1_2 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5404160071/10000000000 : ℝ)*x 0 + (1010494563/2000000000 : ℝ)*x 1 + (-2293673233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5404160071/10000000000 : ℝ)^4317 ≤ (446289489543/1000000000000 : ℝ)^3293 := by
    have hnat : (5404160071 : ℕ)^4317*1000000000000^3293 ≤ 446289489543^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404160071 10000000000 446289489543 1000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1010494563/2000000000 : ℝ)^4317 ≤ (10215151413321/25000000000000 : ℝ)^3293 := by
    have hnat : (1010494563 : ℕ)^4317*25000000000000^3293 ≤ 10215151413321^3293*2000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1010494563 2000000000 10215151413321 25000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2293673233/10000000000 : ℝ)^4317 ≤ (7255222689951/50000000000000 : ℝ)^3293 := by
    have hnat : (2293673233 : ℕ)^4317*50000000000000^3293 ≤ 7255222689951^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2293673233 10000000000 7255222689951 50000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5404160071/10000000000 : ℝ), (1010494563/2000000000 : ℝ), (-2293673233/10000000000 : ℝ)] ![(446289489543/1000000000000 : ℝ), (10215151413321/25000000000000 : ℝ), (7255222689951/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5404160071/10000000000 : ℝ)|^4317 ≤ (446289489543/1000000000000 : ℝ)^3293
        have hw : |(5404160071/10000000000 : ℝ)|=(5404160071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1010494563/2000000000 : ℝ)|^4317 ≤ (10215151413321/25000000000000 : ℝ)^3293
        have hw : |(1010494563/2000000000 : ℝ)|=(1010494563/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2293673233/10000000000 : ℝ)|^4317 ≤ (7255222689951/50000000000000 : ℝ)^3293
        have hw : |(-2293673233/10000000000 : ℝ)|=(2293673233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s1_3 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (268101707/625000000 : ℝ)*x 0 + (3716068269/10000000000 : ℝ)*x 1 + (2472054919/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268101707/625000000 : ℝ)^4317 ≤ (6593951842247/20000000000000 : ℝ)^3293 := by
    have hnat : (268101707 : ℕ)^4317*20000000000000^3293 ≤ 6593951842247^3293*625000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268101707 625000000 6593951842247 20000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3716068269/10000000000 : ℝ)^4317 ≤ (27314658042827/100000000000000 : ℝ)^3293 := by
    have hnat : (3716068269 : ℕ)^4317*100000000000000^3293 ≤ 27314658042827^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3716068269 10000000000 27314658042827 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2472054919/5000000000 : ℝ)^4317 ≤ (39715582734413/100000000000000 : ℝ)^3293 := by
    have hnat : (2472054919 : ℕ)^4317*100000000000000^3293 ≤ 39715582734413^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2472054919 5000000000 39715582734413 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268101707/625000000 : ℝ), (3716068269/10000000000 : ℝ), (2472054919/5000000000 : ℝ)] ![(6593951842247/20000000000000 : ℝ), (27314658042827/100000000000000 : ℝ), (39715582734413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268101707/625000000 : ℝ)|^4317 ≤ (6593951842247/20000000000000 : ℝ)^3293
        have hw : |(268101707/625000000 : ℝ)|=(268101707/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3716068269/10000000000 : ℝ)|^4317 ≤ (27314658042827/100000000000000 : ℝ)^3293
        have hw : |(3716068269/10000000000 : ℝ)|=(3716068269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2472054919/5000000000 : ℝ)|^4317 ≤ (39715582734413/100000000000000 : ℝ)^3293
        have hw : |(2472054919/5000000000 : ℝ)|=(2472054919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s1_4 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-247933911/1250000000 : ℝ)*x 0 + (316231533/625000000 : ℝ)*x 1 + (175878673/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (247933911/1250000000 : ℝ)^4317 ≤ (46850222301/390625000000 : ℝ)^3293 := by
    have hnat : (247933911 : ℕ)^4317*390625000000^3293 ≤ 46850222301^3293*1250000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      247933911 1250000000 46850222301 390625000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (316231533/625000000 : ℝ)^4317 ≤ (40937293919881/100000000000000 : ℝ)^3293 := by
    have hnat : (316231533 : ℕ)^4317*100000000000000^3293 ≤ 40937293919881^3293*625000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      316231533 625000000 40937293919881 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (175878673/312500000 : ℝ)^4317 ≤ (47069049164399/100000000000000 : ℝ)^3293 := by
    have hnat : (175878673 : ℕ)^4317*100000000000000^3293 ≤ 47069049164399^3293*312500000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175878673 312500000 47069049164399 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-247933911/1250000000 : ℝ), (316231533/625000000 : ℝ), (175878673/312500000 : ℝ)] ![(46850222301/390625000000 : ℝ), (40937293919881/100000000000000 : ℝ), (47069049164399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-247933911/1250000000 : ℝ)|^4317 ≤ (46850222301/390625000000 : ℝ)^3293
        have hw : |(-247933911/1250000000 : ℝ)|=(247933911/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(316231533/625000000 : ℝ)|^4317 ≤ (40937293919881/100000000000000 : ℝ)^3293
        have hw : |(316231533/625000000 : ℝ)|=(316231533/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(175878673/312500000 : ℝ)|^4317 ≤ (47069049164399/100000000000000 : ℝ)^3293
        have hw : |(175878673/312500000 : ℝ)|=(175878673/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s1_5 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2626344867/5000000000 : ℝ)*x 0 + (-171802827/1000000000 : ℝ)*x 1 + (5628117597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2626344867/5000000000 : ℝ)^4317 ≤ (42996283398771/100000000000000 : ℝ)^3293 := by
    have hnat : (2626344867 : ℕ)^4317*100000000000000^3293 ≤ 42996283398771^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626344867 5000000000 42996283398771 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (171802827/1000000000 : ℝ)^4317 ≤ (9934666759411/100000000000000 : ℝ)^3293 := by
    have hnat : (171802827 : ℕ)^4317*100000000000000^3293 ≤ 9934666759411^3293*1000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171802827 1000000000 9934666759411 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5628117597/10000000000 : ℝ)^4317 ≤ (47069049833193/100000000000000 : ℝ)^3293 := by
    have hnat : (5628117597 : ℕ)^4317*100000000000000^3293 ≤ 47069049833193^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5628117597 10000000000 47069049833193 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2626344867/5000000000 : ℝ), (-171802827/1000000000 : ℝ), (5628117597/10000000000 : ℝ)] ![(42996283398771/100000000000000 : ℝ), (9934666759411/100000000000000 : ℝ), (47069049833193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2626344867/5000000000 : ℝ)|^4317 ≤ (42996283398771/100000000000000 : ℝ)^3293
        have hw : |(2626344867/5000000000 : ℝ)|=(2626344867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-171802827/1000000000 : ℝ)|^4317 ≤ (9934666759411/100000000000000 : ℝ)^3293
        have hw : |(-171802827/1000000000 : ℝ)|=(171802827/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5628117597/10000000000 : ℝ)|^4317 ≤ (47069049833193/100000000000000 : ℝ)^3293
        have hw : |(5628117597/10000000000 : ℝ)|=(5628117597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s1_6 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1313172407/2500000000 : ℝ)*x 0 + (2814058839/5000000000 : ℝ)*x 1 + (-859014151/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1313172407/2500000000 : ℝ)^4317 ≤ (21498141130643/50000000000000 : ℝ)^3293 := by
    have hnat : (1313172407 : ℕ)^4317*50000000000000^3293 ≤ 21498141130643^3293*2500000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313172407 2500000000 21498141130643 50000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2814058839/5000000000 : ℝ)^4317 ≤ (2941815670079/6250000000000 : ℝ)^3293 := by
    have hnat : (2814058839 : ℕ)^4317*6250000000000^3293 ≤ 2941815670079^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2814058839 5000000000 2941815670079 6250000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (859014151/5000000000 : ℝ)^4317 ≤ (2483666750499/25000000000000 : ℝ)^3293 := by
    have hnat : (859014151 : ℕ)^4317*25000000000000^3293 ≤ 2483666750499^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      859014151 5000000000 2483666750499 25000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1313172407/2500000000 : ℝ), (2814058839/5000000000 : ℝ), (-859014151/5000000000 : ℝ)] ![(21498141130643/50000000000000 : ℝ), (2941815670079/6250000000000 : ℝ), (2483666750499/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1313172407/2500000000 : ℝ)|^4317 ≤ (21498141130643/50000000000000 : ℝ)^3293
        have hw : |(1313172407/2500000000 : ℝ)|=(1313172407/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2814058839/5000000000 : ℝ)|^4317 ≤ (2941815670079/6250000000000 : ℝ)^3293
        have hw : |(2814058839/5000000000 : ℝ)|=(2814058839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-859014151/5000000000 : ℝ)|^4317 ≤ (2483666750499/25000000000000 : ℝ)^3293
        have hw : |(-859014151/5000000000 : ℝ)|=(859014151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s1_7 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2145350881/5000000000 : ℝ)*x 0 + (2464438969/5000000000 : ℝ)*x 1 + (3731572893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2145350881/5000000000 : ℝ)^4317 ≤ (32980585750461/100000000000000 : ℝ)^3293 := by
    have hnat : (2145350881 : ℕ)^4317*100000000000000^3293 ≤ 32980585750461^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145350881 5000000000 32980585750461 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2464438969/5000000000 : ℝ)^4317 ≤ (9888813718399/25000000000000 : ℝ)^3293 := by
    have hnat : (2464438969 : ℕ)^4317*25000000000000^3293 ≤ 9888813718399^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2464438969 5000000000 9888813718399 25000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3731572893/10000000000 : ℝ)^4317 ≤ (1098566374337/4000000000000 : ℝ)^3293 := by
    have hnat : (3731572893 : ℕ)^4317*4000000000000^3293 ≤ 1098566374337^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3731572893 10000000000 1098566374337 4000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2145350881/5000000000 : ℝ), (2464438969/5000000000 : ℝ), (3731572893/10000000000 : ℝ)] ![(32980585750461/100000000000000 : ℝ), (9888813718399/25000000000000 : ℝ), (1098566374337/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2145350881/5000000000 : ℝ)|^4317 ≤ (32980585750461/100000000000000 : ℝ)^3293
        have hw : |(2145350881/5000000000 : ℝ)|=(2145350881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2464438969/5000000000 : ℝ)|^4317 ≤ (9888813718399/25000000000000 : ℝ)^3293
        have hw : |(2464438969/5000000000 : ℝ)|=(2464438969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3731572893/10000000000 : ℝ)|^4317 ≤ (1098566374337/4000000000000 : ℝ)^3293
        have hw : |(3731572893/10000000000 : ℝ)|=(3731572893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1357_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155319977/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6691/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (763/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1757/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (387/2000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6691/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (763/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6691/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (763/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6691/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (763/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6691/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (763/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6691/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (763/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6691/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (763/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (763/50000 : ℝ) ^ (1079/256 : ℝ) ≤ (441566557751/20000000000000000000 : ℝ) := by
    have hpowers : (763/50000 : ℝ)^1079 ≤ (441566557751/20000000000000000000 : ℝ)^256 := by
      have hnat : (763 : ℕ)^1079*20000000000000000000^256 ≤ 441566557751^256*50000^1079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        763 50000 441566557751 20000000000000000000 1079 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (763/50000 : ℝ)) (X := (441566557751/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have hpowhi : (6691/25000 : ℝ) ^ (1079/256 : ℝ) ≤ (77312015476319593/20000000000000000000 : ℝ) := by
    have hpowers : (6691/25000 : ℝ)^1079 ≤ (77312015476319593/20000000000000000000 : ℝ)^256 := by
      have hnat : (6691 : ℕ)^1079*20000000000000000000^256 ≤ 77312015476319593^256*25000^1079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6691 25000 77312015476319593 20000000000000000000 1079 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6691/25000 : ℝ)) (X := (77312015476319593/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000000441566557751/10000000000000000000 : ℝ) ≤ (1250000013095579/1250000000000000 : ℝ) ^ (1079/256 : ℝ) := by
    have hpowers : (10000000441566557751/10000000000000000000 : ℝ)^256 ≤ (1250000013095579/1250000000000000 : ℝ)^1079 := by
      have hnat : (10000000441566557751 : ℕ)^256*1250000000000000^1079 ≤ 1250000013095579^1079*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000000441566557751 10000000000000000000 1250000013095579 1250000000000000 256 1079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250000013095579/1250000000000000 : ℝ)) (X := (10000000441566557751/10000000000000000000 : ℝ)) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (627416014282589917/625000000000000000 : ℝ) ≤ (5004578979837837/5000000000000000 : ℝ) ^ (1079/256 : ℝ) := by
    have hpowers : (627416014282589917/625000000000000000 : ℝ)^256 ≤ (5004578979837837/5000000000000000 : ℝ)^1079 := by
      have hnat : (627416014282589917 : ℕ)^256*5000000000000000^1079 ≤ 5004578979837837^1079*625000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        627416014282589917 625000000000000000 5004578979837837 5000000000000000 256 1079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5004578979837837/5000000000000000 : ℝ)) (X := (627416014282589917/625000000000000000 : ℝ)) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (10077312015476319593/10000000000000000000 : ℝ) ≤ (2504578953646679/2500000000000000 : ℝ) ^ (1079/256 : ℝ) := by
    have hpowers : (10077312015476319593/10000000000000000000 : ℝ)^256 ≤ (2504578953646679/2500000000000000 : ℝ)^1079 := by
      have hnat : (10077312015476319593 : ℕ)^256*2500000000000000^1079 ≤ 2504578953646679^1079*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10077312015476319593 10000000000000000000 2504578953646679 2500000000000000 256 1079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2504578953646679/2500000000000000 : ℝ)) (X := (10077312015476319593/10000000000000000000 : ℝ)) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(441566557751/20000000000000000000 : ℝ) ≤ ((31544006608857660279/31547500000000000000 : ℝ)+2*(4578927455521/1261900000000000 : ℝ)*(763/50000 : ℝ))^(1079/256 : ℝ) := by
    rw [show (31544006608857660279/31547500000000000000 : ℝ)+2*(4578927455521/1261900000000000 : ℝ)*(763/50000 : ℝ)=(1250000013095579/1250000000000000 : ℝ) by norm_num, show 1+2*(441566557751/20000000000000000000 : ℝ)=(10000000441566557751/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(77312015476319593/20000000000000000000 : ℝ)+(441566557751/20000000000000000000 : ℝ) ≤ ((31544006608857660279/31547500000000000000 : ℝ)+(4578927455521/1261900000000000 : ℝ)*((6691/25000 : ℝ)+(763/50000 : ℝ)))^(1079/256 : ℝ) := by
    rw [show (31544006608857660279/31547500000000000000 : ℝ)+(4578927455521/1261900000000000 : ℝ)*((6691/25000 : ℝ)+(763/50000 : ℝ))=(5004578979837837/5000000000000000 : ℝ) by norm_num, show 1+(77312015476319593/20000000000000000000 : ℝ)+(441566557751/20000000000000000000 : ℝ)=(627416014282589917/625000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(77312015476319593/20000000000000000000 : ℝ) ≤ ((31544006608857660279/31547500000000000000 : ℝ)+2*(4578927455521/1261900000000000 : ℝ)*(6691/25000 : ℝ))^(1079/256 : ℝ) := by
    rw [show (31544006608857660279/31547500000000000000 : ℝ)+2*(4578927455521/1261900000000000 : ℝ)*(6691/25000 : ℝ)=(2504578953646679/2500000000000000 : ℝ) by norm_num, show 1+2*(77312015476319593/20000000000000000000 : ℝ)=(10077312015476319593/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (31544006608857660279/31547500000000000000 : ℝ)*(X 1 0+X 2 0)+(4578927455521/1261900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1079/256 : ℝ)) (lo := (763/50000 : ℝ)) (hi := (6691/25000 : ℝ)) (c := (31544006608857660279/31547500000000000000 : ℝ)) (alpha := (4578927455521/1261900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (31544006608857660279/31547500000000000000 : ℝ)*(X 0 1+X 2 1)+(4578927455521/1261900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1079/256 : ℝ)) (lo := (763/50000 : ℝ)) (hi := (6691/25000 : ℝ)) (c := (31544006608857660279/31547500000000000000 : ℝ)) (alpha := (4578927455521/1261900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (31544006608857660279/31547500000000000000 : ℝ)*(X 0 2+X 1 2)+(4578927455521/1261900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1079/256 : ℝ)) (lo := (763/50000 : ℝ)) (hi := (6691/25000 : ℝ)) (c := (31544006608857660279/31547500000000000000 : ℝ)) (alpha := (4578927455521/1261900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-198296147/1000000000 : ℝ)*X 0 0+(2817739717/5000000000 : ℝ)*X 0 1+(5052472667/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5404159983/10000000000 : ℝ)*X 1 0+(-1146836287/5000000000 : ℝ)*X 1 1+(252623671/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5404160071/10000000000 : ℝ)*X 2 0+(1010494563/2000000000 : ℝ)*X 2 1+(-2293673233/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((268101707/625000000 : ℝ)*X 0 0+(3716068269/10000000000 : ℝ)*X 0 1+(2472054919/5000000000 : ℝ)*X 0 2+(268101707/625000000 : ℝ)*X 1 0+(3716068269/10000000000 : ℝ)*X 1 1+(2472054919/5000000000 : ℝ)*X 1 2+(268101707/625000000 : ℝ)*X 2 0+(3716068269/10000000000 : ℝ)*X 2 1+(2472054919/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-247933911/1250000000 : ℝ)*X 0 0+(316231533/625000000 : ℝ)*X 0 1+(175878673/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2626344867/5000000000 : ℝ)*X 1 0+(-171802827/1000000000 : ℝ)*X 1 1+(5628117597/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1313172407/2500000000 : ℝ)*X 2 0+(2814058839/5000000000 : ℝ)*X 2 1+(-859014151/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2145350881/5000000000 : ℝ)*X 0 0+(2464438969/5000000000 : ℝ)*X 0 1+(3731572893/10000000000 : ℝ)*X 0 2+(2145350881/5000000000 : ℝ)*X 1 0+(2464438969/5000000000 : ℝ)*X 1 1+(3731572893/10000000000 : ℝ)*X 1 2+(2145350881/5000000000 : ℝ)*X 2 0+(2464438969/5000000000 : ℝ)*X 2 1+(3731572893/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1530436333982160051245901321/394343750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (64799919/100000000000000 : ℝ)*(base16) + (14377789/4000000000000 : ℝ)*(base19) + (489095913/100000000000000 : ℝ)*(base23) + (19952431/100000000000000 : ℝ)*(upper2) + (62248351/100000000000000 : ℝ)*(upper3) + (632390139812633/50000000000000 : ℝ)*(major0) + (632390139812633/50000000000000 : ℝ)*(major1) + (632390139812633/50000000000000 : ℝ)*(major2) + (171525049732131/10000000000000 : ℝ)*(sp0) + (428813439004099/25000000000000 : ℝ)*(sp1) + (1715253691165127/100000000000000 : ℝ)*(sp2) + (814305337048013/100000000000000 : ℝ)*(sp3) + (3682939731/100000000000000 : ℝ)*(sp4) + (456287899/50000000000000 : ℝ)*(sp7) + (203576562405953/25000000000000 : ℝ)*(f.failure) + (21440677253263/1250000000000 : ℝ)*(f.sum) + (602607570353/31547500000000000000000000000 : ℝ)*base65 + (13695293433185045393/1577375000000000000000000000000000 : ℝ)*base68 + (19128510458526920393/1577375000000000000000000000000000 : ℝ)*base70 + (6623422654203670393/1577375000000000000000000000000000 : ℝ)*base72 + (309752206654471/63095000000000000000000000000 : ℝ)*base73 + (2465220558304829607/1577375000000000000000000000000000 : ℝ)*base75 + (9850673145407545393/1577375000000000000000000000000000 : ℝ)*base78 + (1008122435702920393/1577375000000000000000000000000000 : ℝ)*base80 + (92760349780471/63095000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (34623081/2500000000000000000000 : ℝ)*base89 + (34623081/2500000000000000000000 : ℝ)*base91 + (34623081/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7394103431216815833335194071/1577375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (25407381/50000000000000 : ℝ)*(base1) + (30005537/3125000000000 : ℝ)*(base19) + (461452483/50000000000000 : ℝ)*(base23) + (55368951/50000000000000 : ℝ)*(upper3) + (20232491/20000000000000 : ℝ)*(upper5) + (1297246585304117/100000000000000 : ℝ)*(major0) + (1297246585304117/100000000000000 : ℝ)*(major1) + (1297246585304117/100000000000000 : ℝ)*(major2) + (5058207303/100000000000000 : ℝ)*(sp1) + (2498416543/50000000000000 : ℝ)*(sp2) + (219910495382057/12500000000000 : ℝ)*(sp4) + (1759277893857207/100000000000000 : ℝ)*(sp5) + (1759277992503641/100000000000000 : ℝ)*(sp6) + (83520905129843/10000000000000 : ℝ)*(sp7) + (104401137764149/12500000000000 : ℝ)*(f.failure) + (1759283912241693/100000000000000 : ℝ)*(f.sum) + (89634449922417/63095000000000000000000000000 : ℝ)*base65 + (8310159831071993643/3154750000000000000000000000000000 : ℝ)*base67 + (2226706109043506357/3154750000000000000000000000000000 : ℝ)*base70 + (4084270184611743643/3154750000000000000000000000000000 : ℝ)*base71 + (239523613600797/63095000000000000000000000000 : ℝ)*base73 + (2251140982252756357/3154750000000000000000000000000000 : ℝ)*base76 + (16122556843193493643/3154750000000000000000000000000000 : ℝ)*base77 + (19805469680951993643/3154750000000000000000000000000000 : ℝ)*base79 + (36090453149807/63095000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (8395427/1250000000000000000000 : ℝ)*base90 + (8395427/1250000000000000000000 : ℝ)*base92 + (8395427/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1357_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155319977/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6691/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (763/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1757/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (387/2000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1357_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1357_s2_0 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2021829841/10000000000 : ℝ)*x 0 + (1095142533/2000000000 : ℝ)*x 1 + (5187320933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2021829841/10000000000 : ℝ)^4317 ≤ (6149320226951/50000000000000 : ℝ)^3293 := by
    have hnat : (2021829841 : ℕ)^4317*50000000000000^3293 ≤ 6149320226951^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2021829841 10000000000 6149320226951 50000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1095142533/2000000000 : ℝ)^4317 ≤ (11351296597661/25000000000000 : ℝ)^3293 := by
    have hnat : (1095142533 : ℕ)^4317*25000000000000^3293 ≤ 11351296597661^3293*2000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095142533 2000000000 11351296597661 25000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5187320933/10000000000 : ℝ)^4317 ≤ (42296173143847/100000000000000 : ℝ)^3293 := by
    have hnat : (5187320933 : ℕ)^4317*100000000000000^3293 ≤ 42296173143847^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5187320933 10000000000 42296173143847 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2021829841/10000000000 : ℝ), (1095142533/2000000000 : ℝ), (5187320933/10000000000 : ℝ)] ![(6149320226951/50000000000000 : ℝ), (11351296597661/25000000000000 : ℝ), (42296173143847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2021829841/10000000000 : ℝ)|^4317 ≤ (6149320226951/50000000000000 : ℝ)^3293
        have hw : |(-2021829841/10000000000 : ℝ)|=(2021829841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1095142533/2000000000 : ℝ)|^4317 ≤ (11351296597661/25000000000000 : ℝ)^3293
        have hw : |(1095142533/2000000000 : ℝ)|=(1095142533/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5187320933/10000000000 : ℝ)|^4317 ≤ (42296173143847/100000000000000 : ℝ)^3293
        have hw : |(5187320933/10000000000 : ℝ)|=(5187320933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s2_1 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5364906599/10000000000 : ℝ)*x 0 + (-217072331/1000000000 : ℝ)*x 1 + (5187321297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364906599/10000000000 : ℝ)^4317 ≤ (5525557636059/12500000000000 : ℝ)^3293 := by
    have hnat : (5364906599 : ℕ)^4317*12500000000000^3293 ≤ 5525557636059^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364906599 10000000000 5525557636059 12500000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (217072331/1000000000 : ℝ)^4317 ≤ (1687420232779/12500000000000 : ℝ)^3293 := by
    have hnat : (217072331 : ℕ)^4317*12500000000000^3293 ≤ 1687420232779^3293*1000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217072331 1000000000 1687420232779 12500000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5187321297/10000000000 : ℝ)^4317 ≤ (42296177034743/100000000000000 : ℝ)^3293 := by
    have hnat : (5187321297 : ℕ)^4317*100000000000000^3293 ≤ 42296177034743^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5187321297 10000000000 42296177034743 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364906599/10000000000 : ℝ), (-217072331/1000000000 : ℝ), (5187321297/10000000000 : ℝ)] ![(5525557636059/12500000000000 : ℝ), (1687420232779/12500000000000 : ℝ), (42296177034743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364906599/10000000000 : ℝ)|^4317 ≤ (5525557636059/12500000000000 : ℝ)^3293
        have hw : |(5364906599/10000000000 : ℝ)|=(5364906599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-217072331/1000000000 : ℝ)|^4317 ≤ (1687420232779/12500000000000 : ℝ)^3293
        have hw : |(-217072331/1000000000 : ℝ)|=(217072331/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5187321297/10000000000 : ℝ)|^4317 ≤ (42296177034743/100000000000000 : ℝ)^3293
        have hw : |(5187321297/10000000000 : ℝ)|=(5187321297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s2_2 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (268245333/500000000 : ℝ)*x 0 + (648415153/1250000000 : ℝ)*x 1 + (-86828933/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268245333/500000000 : ℝ)^4317 ≤ (44204461747379/100000000000000 : ℝ)^3293 := by
    have hnat : (268245333 : ℕ)^4317*100000000000000^3293 ≤ 44204461747379^3293*500000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268245333 500000000 44204461747379 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (648415153/1250000000 : ℝ)^4317 ≤ (21148088127213/50000000000000 : ℝ)^3293 := by
    have hnat : (648415153 : ℕ)^4317*50000000000000^3293 ≤ 21148088127213^3293*1250000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      648415153 1250000000 21148088127213 50000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (86828933/400000000 : ℝ)^4317 ≤ (13499361984521/100000000000000 : ℝ)^3293 := by
    have hnat : (86828933 : ℕ)^4317*100000000000000^3293 ≤ 13499361984521^3293*400000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86828933 400000000 13499361984521 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268245333/500000000 : ℝ), (648415153/1250000000 : ℝ), (-86828933/400000000 : ℝ)] ![(44204461747379/100000000000000 : ℝ), (21148088127213/50000000000000 : ℝ), (13499361984521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268245333/500000000 : ℝ)|^4317 ≤ (44204461747379/100000000000000 : ℝ)^3293
        have hw : |(268245333/500000000 : ℝ)|=(268245333/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(648415153/1250000000 : ℝ)|^4317 ≤ (21148088127213/50000000000000 : ℝ)^3293
        have hw : |(648415153/1250000000 : ℝ)|=(648415153/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-86828933/400000000 : ℝ)|^4317 ≤ (13499361984521/100000000000000 : ℝ)^3293
        have hw : |(-86828933/400000000 : ℝ)|=(86828933/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s2_3 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4316854189/10000000000 : ℝ)*x 0 + (804603247/2000000000 : ℝ)*x 1 + (289405229/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4316854189/10000000000 : ℝ)^4317 ≤ (519443227111/1562500000000 : ℝ)^3293 := by
    have hnat : (4316854189 : ℕ)^4317*1562500000000^3293 ≤ 519443227111^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4316854189 10000000000 519443227111 1562500000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (804603247/2000000000 : ℝ)^4317 ≤ (30309736522911/100000000000000 : ℝ)^3293 := by
    have hnat : (804603247 : ℕ)^4317*100000000000000^3293 ≤ 30309736522911^3293*2000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      804603247 2000000000 30309736522911 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (289405229/625000000 : ℝ)^4317 ≤ (36445896937221/100000000000000 : ℝ)^3293 := by
    have hnat : (289405229 : ℕ)^4317*100000000000000^3293 ≤ 36445896937221^3293*625000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      289405229 625000000 36445896937221 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4316854189/10000000000 : ℝ), (804603247/2000000000 : ℝ), (289405229/625000000 : ℝ)] ![(519443227111/1562500000000 : ℝ), (30309736522911/100000000000000 : ℝ), (36445896937221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4316854189/10000000000 : ℝ)|^4317 ≤ (519443227111/1562500000000 : ℝ)^3293
        have hw : |(4316854189/10000000000 : ℝ)|=(4316854189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(804603247/2000000000 : ℝ)|^4317 ≤ (30309736522911/100000000000000 : ℝ)^3293
        have hw : |(804603247/2000000000 : ℝ)|=(804603247/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(289405229/625000000 : ℝ)|^4317 ≤ (36445896937221/100000000000000 : ℝ)^3293
        have hw : |(289405229/625000000 : ℝ)|=(289405229/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s2_4 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-80875663/400000000 : ℝ)*x 0 + (1037820083/2000000000 : ℝ)*x 1 + (5473917399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (80875663/400000000 : ℝ)^4317 ≤ (2459826550659/20000000000000 : ℝ)^3293 := by
    have hnat : (80875663 : ℕ)^4317*20000000000000^3293 ≤ 2459826550659^3293*400000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80875663 400000000 2459826550659 20000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1037820083/2000000000 : ℝ)^4317 ≤ (42315195531857/100000000000000 : ℝ)^3293 := by
    have hnat : (1037820083 : ℕ)^4317*100000000000000^3293 ≤ 42315195531857^3293*2000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037820083 2000000000 42315195531857 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5473917399/10000000000 : ℝ)^4317 ≤ (45385671694421/100000000000000 : ℝ)^3293 := by
    have hnat : (5473917399 : ℕ)^4317*100000000000000^3293 ≤ 45385671694421^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5473917399 10000000000 45385671694421 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-80875663/400000000 : ℝ), (1037820083/2000000000 : ℝ), (5473917399/10000000000 : ℝ)] ![(2459826550659/20000000000000 : ℝ), (42315195531857/100000000000000 : ℝ), (45385671694421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-80875663/400000000 : ℝ)|^4317 ≤ (2459826550659/20000000000000 : ℝ)^3293
        have hw : |(-80875663/400000000 : ℝ)|=(80875663/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1037820083/2000000000 : ℝ)|^4317 ≤ (42315195531857/100000000000000 : ℝ)^3293
        have hw : |(1037820083/2000000000 : ℝ)|=(1037820083/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5473917399/10000000000 : ℝ)|^4317 ≤ (45385671694421/100000000000000 : ℝ)^3293
        have hw : |(5473917399/10000000000 : ℝ)|=(5473917399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s2_5 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5290453949/10000000000 : ℝ)*x 0 + (-942063459/5000000000 : ℝ)*x 1 + (68423967/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5290453949/10000000000 : ℝ)^4317 ≤ (10850495695351/25000000000000 : ℝ)^3293 := by
    have hnat : (5290453949 : ℕ)^4317*25000000000000^3293 ≤ 10850495695351^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290453949 10000000000 10850495695351 25000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (942063459/5000000000 : ℝ)^4317 ≤ (280308648173/2500000000000 : ℝ)^3293 := by
    have hnat : (942063459 : ℕ)^4317*2500000000000^3293 ≤ 280308648173^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      942063459 5000000000 280308648173 2500000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (68423967/125000000 : ℝ)^4317 ≤ (45385671270509/100000000000000 : ℝ)^3293 := by
    have hnat : (68423967 : ℕ)^4317*100000000000000^3293 ≤ 45385671270509^3293*125000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68423967 125000000 45385671270509 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5290453949/10000000000 : ℝ), (-942063459/5000000000 : ℝ), (68423967/125000000 : ℝ)] ![(10850495695351/25000000000000 : ℝ), (280308648173/2500000000000 : ℝ), (45385671270509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5290453949/10000000000 : ℝ)|^4317 ≤ (10850495695351/25000000000000 : ℝ)^3293
        have hw : |(5290453949/10000000000 : ℝ)|=(5290453949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-942063459/5000000000 : ℝ)|^4317 ≤ (280308648173/2500000000000 : ℝ)^3293
        have hw : |(-942063459/5000000000 : ℝ)|=(942063459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(68423967/125000000 : ℝ)|^4317 ≤ (45385671270509/100000000000000 : ℝ)^3293
        have hw : |(68423967/125000000 : ℝ)|=(68423967/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s2_6 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1322613481/2500000000 : ℝ)*x 0 + (1368479351/2500000000 : ℝ)*x 1 + (-471031723/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322613481/2500000000 : ℝ)^4317 ≤ (43401982512531/100000000000000 : ℝ)^3293 := by
    have hnat : (1322613481 : ℕ)^4317*100000000000000^3293 ≤ 43401982512531^3293*2500000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322613481 2500000000 43401982512531 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1368479351/2500000000 : ℝ)^4317 ≤ (45385671748769/100000000000000 : ℝ)^3293 := by
    have hnat : (1368479351 : ℕ)^4317*100000000000000^3293 ≤ 45385671748769^3293*2500000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368479351 2500000000 45385671748769 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (471031723/2500000000 : ℝ)^4317 ≤ (5606172862041/50000000000000 : ℝ)^3293 := by
    have hnat : (471031723 : ℕ)^4317*50000000000000^3293 ≤ 5606172862041^3293*2500000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      471031723 2500000000 5606172862041 50000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322613481/2500000000 : ℝ), (1368479351/2500000000 : ℝ), (-471031723/2500000000 : ℝ)] ![(43401982512531/100000000000000 : ℝ), (45385671748769/100000000000000 : ℝ), (5606172862041/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322613481/2500000000 : ℝ)|^4317 ≤ (43401982512531/100000000000000 : ℝ)^3293
        have hw : |(1322613481/2500000000 : ℝ)|=(1322613481/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1368479351/2500000000 : ℝ)|^4317 ≤ (45385671748769/100000000000000 : ℝ)^3293
        have hw : |(1368479351/2500000000 : ℝ)|=(1368479351/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-471031723/2500000000 : ℝ)|^4317 ≤ (5606172862041/50000000000000 : ℝ)^3293
        have hw : |(-471031723/2500000000 : ℝ)|=(471031723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s2_7 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1079246133/2500000000 : ℝ)*x 0 + (2313367973/5000000000 : ℝ)*x 1 + (10066993/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079246133/2500000000 : ℝ)^4317 ≤ (6649136491787/20000000000000 : ℝ)^3293 := by
    have hnat : (1079246133 : ℕ)^4317*20000000000000^3293 ≤ 6649136491787^3293*2500000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079246133 2500000000 6649136491787 20000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2313367973/5000000000 : ℝ)^4317 ≤ (36407231329219/100000000000000 : ℝ)^3293 := by
    have hnat : (2313367973 : ℕ)^4317*100000000000000^3293 ≤ 36407231329219^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2313367973 5000000000 36407231329219 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10066993/25000000 : ℝ)^4317 ≤ (379338577439/1250000000000 : ℝ)^3293 := by
    have hnat : (10066993 : ℕ)^4317*1250000000000^3293 ≤ 379338577439^3293*25000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10066993 25000000 379338577439 1250000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079246133/2500000000 : ℝ), (2313367973/5000000000 : ℝ), (10066993/25000000 : ℝ)] ![(6649136491787/20000000000000 : ℝ), (36407231329219/100000000000000 : ℝ), (379338577439/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079246133/2500000000 : ℝ)|^4317 ≤ (6649136491787/20000000000000 : ℝ)^3293
        have hw : |(1079246133/2500000000 : ℝ)|=(1079246133/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2313367973/5000000000 : ℝ)|^4317 ≤ (36407231329219/100000000000000 : ℝ)^3293
        have hw : |(2313367973/5000000000 : ℝ)|=(2313367973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(10066993/25000000 : ℝ)|^4317 ≤ (379338577439/1250000000000 : ℝ)^3293
        have hw : |(10066993/25000000 : ℝ)|=(10066993/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1357_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155319977/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (387/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1757/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2487/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8023/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (387/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1757/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (387/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1757/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (387/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1757/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (387/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1757/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (387/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1757/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (387/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1757/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1757/25000 : ℝ) ^ (1079/256 : ℝ) ≤ (27580746483927/2000000000000000000 : ℝ) := by
    have hpowers : (1757/25000 : ℝ)^1079 ≤ (27580746483927/2000000000000000000 : ℝ)^256 := by
      have hnat : (1757 : ℕ)^1079*2000000000000000000^256 ≤ 27580746483927^256*25000^1079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1757 25000 27580746483927 2000000000000000000 1079 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1757/25000 : ℝ)) (X := (27580746483927/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have hpowhi : (387/2000 : ℝ) ^ (1079/256 : ℝ) ≤ (12313506810817541/12500000000000000000 : ℝ) := by
    have hpowers : (387/2000 : ℝ)^1079 ≤ (12313506810817541/12500000000000000000 : ℝ)^256 := by
      have hnat : (387 : ℕ)^1079*12500000000000000000^256 ≤ 12313506810817541^256*2000^1079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        387 2000 12313506810817541 12500000000000000000 1079 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (387/2000 : ℝ)) (X := (12313506810817541/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1000027580746483927/1000000000000000000 : ℝ) ≤ (1250008179560743/1250000000000000 : ℝ) ^ (1079/256 : ℝ) := by
    have hpowers : (1000027580746483927/1000000000000000000 : ℝ)^256 ≤ (1250008179560743/1250000000000000 : ℝ)^1079 := by
      have hnat : (1000027580746483927 : ℕ)^256*1250000000000000^1079 ≤ 1250008179560743^1079*1000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000027580746483927 1000000000000000000 1250008179560743 1250000000000000 256 1079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250008179560743/1250000000000000 : ℝ)) (X := (1000027580746483927/1000000000000000000 : ℝ)) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50049943545905368339/50000000000000000000 : ℝ) ≤ (2000473797222189/2000000000000000 : ℝ) ^ (1079/256 : ℝ) := by
    have hpowers : (50049943545905368339/50000000000000000000 : ℝ)^256 ≤ (2000473797222189/2000000000000000 : ℝ)^1079 := by
      have hnat : (50049943545905368339 : ℕ)^256*2000000000000000^1079 ≤ 2000473797222189^1079*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50049943545905368339 50000000000000000000 2000473797222189 2000000000000000 256 1079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000473797222189/2000000000000000 : ℝ)) (X := (50049943545905368339/50000000000000000000 : ℝ)) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (6262313506810817541/6250000000000000000 : ℝ) ≤ (5002336267867973/5000000000000000 : ℝ) ^ (1079/256 : ℝ) := by
    have hpowers : (6262313506810817541/6250000000000000000 : ℝ)^256 ≤ (5002336267867973/5000000000000000 : ℝ)^1079 := by
      have hnat : (6262313506810817541 : ℕ)^256*5000000000000000^1079 ≤ 5002336267867973^1079*6250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6262313506810817541 6250000000000000000 5002336267867973 5000000000000000 256 1079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002336267867973/5000000000000000 : ℝ)) (X := (6262313506810817541/6250000000000000000 : ℝ)) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(27580746483927/2000000000000000000 : ℝ) ≤ ((15398553451856348489/15402500000000000000 : ℝ)+2*(2303549625001/1232200000000000 : ℝ)*(1757/25000 : ℝ))^(1079/256 : ℝ) := by
    rw [show (15398553451856348489/15402500000000000000 : ℝ)+2*(2303549625001/1232200000000000 : ℝ)*(1757/25000 : ℝ)=(1250008179560743/1250000000000000 : ℝ) by norm_num, show 1+2*(27580746483927/2000000000000000000 : ℝ)=(1000027580746483927/1000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(12313506810817541/12500000000000000000 : ℝ)+(27580746483927/2000000000000000000 : ℝ) ≤ ((15398553451856348489/15402500000000000000 : ℝ)+(2303549625001/1232200000000000 : ℝ)*((387/2000 : ℝ)+(1757/25000 : ℝ)))^(1079/256 : ℝ) := by
    rw [show (15398553451856348489/15402500000000000000 : ℝ)+(2303549625001/1232200000000000 : ℝ)*((387/2000 : ℝ)+(1757/25000 : ℝ))=(2000473797222189/2000000000000000 : ℝ) by norm_num, show 1+(12313506810817541/12500000000000000000 : ℝ)+(27580746483927/2000000000000000000 : ℝ)=(50049943545905368339/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(12313506810817541/12500000000000000000 : ℝ) ≤ ((15398553451856348489/15402500000000000000 : ℝ)+2*(2303549625001/1232200000000000 : ℝ)*(387/2000 : ℝ))^(1079/256 : ℝ) := by
    rw [show (15398553451856348489/15402500000000000000 : ℝ)+2*(2303549625001/1232200000000000 : ℝ)*(387/2000 : ℝ)=(5002336267867973/5000000000000000 : ℝ) by norm_num, show 1+2*(12313506810817541/12500000000000000000 : ℝ)=(6262313506810817541/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15398553451856348489/15402500000000000000 : ℝ)*(X 1 0+X 2 0)+(2303549625001/1232200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1079/256 : ℝ)) (lo := (1757/25000 : ℝ)) (hi := (387/2000 : ℝ)) (c := (15398553451856348489/15402500000000000000 : ℝ)) (alpha := (2303549625001/1232200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15398553451856348489/15402500000000000000 : ℝ)*(X 0 1+X 2 1)+(2303549625001/1232200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1079/256 : ℝ)) (lo := (1757/25000 : ℝ)) (hi := (387/2000 : ℝ)) (c := (15398553451856348489/15402500000000000000 : ℝ)) (alpha := (2303549625001/1232200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15398553451856348489/15402500000000000000 : ℝ)*(X 0 2+X 1 2)+(2303549625001/1232200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1079/256 : ℝ)) (lo := (1757/25000 : ℝ)) (hi := (387/2000 : ℝ)) (c := (15398553451856348489/15402500000000000000 : ℝ)) (alpha := (2303549625001/1232200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2021829841/10000000000 : ℝ)*X 0 0+(1095142533/2000000000 : ℝ)*X 0 1+(5187320933/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5364906599/10000000000 : ℝ)*X 1 0+(-217072331/1000000000 : ℝ)*X 1 1+(5187321297/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((268245333/500000000 : ℝ)*X 2 0+(648415153/1250000000 : ℝ)*X 2 1+(-86828933/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4316854189/10000000000 : ℝ)*X 0 0+(804603247/2000000000 : ℝ)*X 0 1+(289405229/625000000 : ℝ)*X 0 2+(4316854189/10000000000 : ℝ)*X 1 0+(804603247/2000000000 : ℝ)*X 1 1+(289405229/625000000 : ℝ)*X 1 2+(4316854189/10000000000 : ℝ)*X 2 0+(804603247/2000000000 : ℝ)*X 2 1+(289405229/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-80875663/400000000 : ℝ)*X 0 0+(1037820083/2000000000 : ℝ)*X 0 1+(5473917399/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5290453949/10000000000 : ℝ)*X 1 0+(-942063459/5000000000 : ℝ)*X 1 1+(68423967/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1322613481/2500000000 : ℝ)*X 2 0+(1368479351/2500000000 : ℝ)*X 2 1+(-471031723/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1079246133/2500000000 : ℝ)*X 0 0+(2313367973/5000000000 : ℝ)*X 0 1+(10066993/25000000 : ℝ)*X 0 2+(1079246133/2500000000 : ℝ)*X 1 0+(2313367973/5000000000 : ℝ)*X 1 1+(10066993/25000000 : ℝ)*X 1 2+(1079246133/2500000000 : ℝ)*X 2 0+(2313367973/5000000000 : ℝ)*X 2 1+(10066993/25000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3685367243525079051073784487/385062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (834311791/50000000000000 : ℝ)*(base19) + (1643192039/100000000000000 : ℝ)*(base23) + (1739793/5000000000000 : ℝ)*(lower2) + (56883467/25000000000000 : ℝ)*(upper3) + (85354729/50000000000000 : ℝ)*(upper5) + (1278438922366939/50000000000000 : ℝ)*(major0) + (1278438922366939/50000000000000 : ℝ)*(major1) + (1278438922366939/50000000000000 : ℝ)*(major2) + (34675306383203/1000000000000 : ℝ)*(sp0) + (3467553454997113/100000000000000 : ℝ)*(sp1) + (216722092526791/6250000000000 : ℝ)*(sp2) + (1646189071971397/100000000000000 : ℝ)*(sp3) + (6121325099/25000000000000 : ℝ)*(sp4) + (1117484803/10000000000000 : ℝ)*(sp7) + (411550061704857/25000000000000 : ℝ)*(f.failure) + (433444390452587/12500000000000 : ℝ)*(f.sum) + (12296308858787/15402500000000000000000000000 : ℝ)*base65 + (2207194989426067671/770125000000000000000000000000000 : ℝ)*base67 + (731081403763557329/770125000000000000000000000000000 : ℝ)*base70 + (7270634275855442671/770125000000000000000000000000000 : ℝ)*base71 + (43294692606357/15402500000000000000000000000 : ℝ)*base73 + (4056334692139317671/770125000000000000000000000000000 : ℝ)*base75 + (4411854134388682329/770125000000000000000000000000000 : ℝ)*base78 + (3310991197958067671/770125000000000000000000000000000 : ℝ)*base79 + (48620350908499/30805000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (20028289/2500000000000000000000 : ℝ)*base89 + (20028289/2500000000000000000000 : ℝ)*base91 + (20028289/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (206254555884483052054282347/24066406250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1745815879/100000000000000 : ℝ)*(base19) + (1921445419/100000000000000 : ℝ)*(base23) + (40565451/20000000000000 : ℝ)*(upper3) + (15756199/20000000000000 : ℝ)*(lower4) + (18413807/12500000000000 : ℝ)*(upper5) + (323616354273187/12500000000000 : ℝ)*(major0) + (323616354273187/12500000000000 : ℝ)*(major1) + (323616354273187/12500000000000 : ℝ)*(major2) + (1250999489/6250000000000 : ℝ)*(sp1) + (1443339531/6250000000000 : ℝ)*(sp2) + (1755512194838593/50000000000000 : ℝ)*(sp4) + (3511002627869483/100000000000000 : ℝ)*(sp5) + (3510999374799271/100000000000000 : ℝ)*(sp6) + (66673479720783/4000000000000 : ℝ)*(sp7) + (66673479720783/4000000000000 : ℝ)*(f.failure) + (1755512194838593/50000000000000 : ℝ)*(f.sum) + (71202876098501/15402500000000000000000000000 : ℝ)*base66 + (1657019338809876943/192531250000000000000000000000000 : ℝ)*base67 + (1344700136625064443/192531250000000000000000000000000 : ℝ)*base69 + (645840650241658193/192531250000000000000000000000000 : ℝ)*base71 + (1596427123829/3850625000000000000000000000 : ℝ)*base74 + (3735506723236501943/192531250000000000000000000000000 : ℝ)*base75 + (1777245184454751943/192531250000000000000000000000000 : ℝ)*base77 + (3109306547338689443/192531250000000000000000000000000 : ℝ)*base79 + (7508010320437/1925312500000000000000000000 : ℝ)*base82 + (2018009/400000000000000000000 : ℝ)*base90 + (2018009/400000000000000000000 : ℝ)*base92 + (2018009/400000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1357_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155319977/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (387/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1757/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2487/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8023/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1357_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1357_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155319977/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2487/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8023/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1357_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1357_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1357_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155319977/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2487/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8023/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1357_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
