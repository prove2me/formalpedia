-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1400_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:44:49.464982+00:00
-- url     : https://prove2.me/submissions/0330e801-bff1-4301-86e6-e8a251b408c9

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
theorem support_rectangle_w1400_s0_0 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1775350417/10000000000 : ℝ)*x 0 + (5972240451/10000000000 : ℝ)*x 1 + (2412278723/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1775350417/10000000000 : ℝ)^545 ≤ (10443558560687/100000000000000 : ℝ)^417 := by
    have hnat : (1775350417 : ℕ)^545*100000000000000^417 ≤ 10443558560687^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1775350417 10000000000 10443558560687 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5972240451/10000000000 : ℝ)^545 ≤ (50982559072493/100000000000000 : ℝ)^417 := by
    have hnat : (5972240451 : ℕ)^545*100000000000000^417 ≤ 50982559072493^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5972240451 10000000000 50982559072493 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2412278723/5000000000 : ℝ)^545 ≤ (19286941179797/50000000000000 : ℝ)^417 := by
    have hnat : (2412278723 : ℕ)^545*50000000000000^417 ≤ 19286941179797^417*5000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2412278723 5000000000 19286941179797 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1775350417/10000000000 : ℝ), (5972240451/10000000000 : ℝ), (2412278723/5000000000 : ℝ)] ![(10443558560687/100000000000000 : ℝ), (50982559072493/100000000000000 : ℝ), (19286941179797/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1775350417/10000000000 : ℝ)|^545 ≤ (10443558560687/100000000000000 : ℝ)^417
        have hw : |(-1775350417/10000000000 : ℝ)|=(1775350417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5972240451/10000000000 : ℝ)|^545 ≤ (50982559072493/100000000000000 : ℝ)^417
        have hw : |(5972240451/10000000000 : ℝ)|=(5972240451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2412278723/5000000000 : ℝ)|^545 ≤ (19286941179797/50000000000000 : ℝ)^417
        have hw : |(2412278723/5000000000 : ℝ)|=(2412278723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s0_1 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5495329319/10000000000 : ℝ)*x 0 + (-242498737/1000000000 : ℝ)*x 1 + (2412278841/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5495329319/10000000000 : ℝ)^545 ≤ (2286407561917/5000000000000 : ℝ)^417 := by
    have hnat : (5495329319 : ℕ)^545*5000000000000^417 ≤ 2286407561917^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5495329319 10000000000 2286407561917 5000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (242498737/1000000000 : ℝ)^545 ≤ (15697963917849/100000000000000 : ℝ)^417 := by
    have hnat : (242498737 : ℕ)^545*100000000000000^417 ≤ 15697963917849^417*1000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      242498737 1000000000 15697963917849 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2412278841/5000000000 : ℝ)^545 ≤ (482173560321/1250000000000 : ℝ)^417 := by
    have hnat : (2412278841 : ℕ)^545*1250000000000^417 ≤ 482173560321^417*5000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2412278841 5000000000 482173560321 1250000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5495329319/10000000000 : ℝ), (-242498737/1000000000 : ℝ), (2412278841/5000000000 : ℝ)] ![(2286407561917/5000000000000 : ℝ), (15697963917849/100000000000000 : ℝ), (482173560321/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5495329319/10000000000 : ℝ)|^545 ≤ (2286407561917/5000000000000 : ℝ)^417
        have hw : |(5495329319/10000000000 : ℝ)|=(5495329319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-242498737/1000000000 : ℝ)|^545 ≤ (15697963917849/100000000000000 : ℝ)^417
        have hw : |(-242498737/1000000000 : ℝ)|=(242498737/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2412278841/5000000000 : ℝ)|^545 ≤ (482173560321/1250000000000 : ℝ)^417
        have hw : |(2412278841/5000000000 : ℝ)|=(2412278841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s0_2 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5495329483/10000000000 : ℝ)*x 0 + (603069699/1250000000 : ℝ)*x 1 + (-2424987271/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5495329483/10000000000 : ℝ)^545 ≤ (45728153021927/100000000000000 : ℝ)^417 := by
    have hnat : (5495329483 : ℕ)^545*100000000000000^417 ≤ 45728153021927^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5495329483 10000000000 45728153021927 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (603069699/1250000000 : ℝ)^545 ≤ (4821735485653/12500000000000 : ℝ)^417 := by
    have hnat : (603069699 : ℕ)^545*12500000000000^417 ≤ 4821735485653^417*1250000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      603069699 1250000000 4821735485653 12500000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2424987271/10000000000 : ℝ)^545 ≤ (15697963080263/100000000000000 : ℝ)^417 := by
    have hnat : (2424987271 : ℕ)^545*100000000000000^417 ≤ 15697963080263^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2424987271 10000000000 15697963080263 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5495329483/10000000000 : ℝ), (603069699/1250000000 : ℝ), (-2424987271/10000000000 : ℝ)] ![(45728153021927/100000000000000 : ℝ), (4821735485653/12500000000000 : ℝ), (15697963080263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5495329483/10000000000 : ℝ)|^545 ≤ (45728153021927/100000000000000 : ℝ)^417
        have hw : |(5495329483/10000000000 : ℝ)|=(5495329483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(603069699/1250000000 : ℝ)|^545 ≤ (4821735485653/12500000000000 : ℝ)^417
        have hw : |(603069699/1250000000 : ℝ)|=(603069699/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2424987271/10000000000 : ℝ)|^545 ≤ (15697963080263/100000000000000 : ℝ)^417
        have hw : |(-2424987271/10000000000 : ℝ)|=(2424987271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s0_3 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (26063683/62500000 : ℝ)*x 0 + (1552093571/5000000000 : ℝ)*x 1 + (5560653651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26063683/62500000 : ℝ)^545 ≤ (6376625196361/20000000000000 : ℝ)^417 := by
    have hnat : (26063683 : ℕ)^545*20000000000000^417 ≤ 6376625196361^417*62500000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26063683 62500000 6376625196361 20000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1552093571/5000000000 : ℝ)^545 ≤ (21676993545623/100000000000000 : ℝ)^417 := by
    have hnat : (1552093571 : ℕ)^545*100000000000000^417 ≤ 21676993545623^417*5000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1552093571 5000000000 21676993545623 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5560653651/10000000000 : ℝ)^545 ≤ (23219940230571/50000000000000 : ℝ)^417 := by
    have hnat : (5560653651 : ℕ)^545*50000000000000^417 ≤ 23219940230571^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5560653651 10000000000 23219940230571 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26063683/62500000 : ℝ), (1552093571/5000000000 : ℝ), (5560653651/10000000000 : ℝ)] ![(6376625196361/20000000000000 : ℝ), (21676993545623/100000000000000 : ℝ), (23219940230571/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26063683/62500000 : ℝ)|^545 ≤ (6376625196361/20000000000000 : ℝ)^417
        have hw : |(26063683/62500000 : ℝ)|=(26063683/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1552093571/5000000000 : ℝ)|^545 ≤ (21676993545623/100000000000000 : ℝ)^417
        have hw : |(1552093571/5000000000 : ℝ)|=(1552093571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5560653651/10000000000 : ℝ)|^545 ≤ (23219940230571/50000000000000 : ℝ)^417
        have hw : |(5560653651/10000000000 : ℝ)|=(5560653651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s0_4 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-444877631/2500000000 : ℝ)*x 0 + (303374049/625000000 : ℝ)*x 1 + (148544039/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (444877631/2500000000 : ℝ)^545 ≤ (10475553805977/100000000000000 : ℝ)^417 := by
    have hnat : (444877631 : ℕ)^545*100000000000000^417 ≤ 10475553805977^417*2500000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      444877631 2500000000 10475553805977 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (303374049/625000000 : ℝ)^545 ≤ (19440835678453/50000000000000 : ℝ)^417 := by
    have hnat : (303374049 : ℕ)^545*50000000000000^417 ≤ 19440835678453^417*625000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      303374049 625000000 19440835678453 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (148544039/250000000 : ℝ)^545 ≤ (50642774815127/100000000000000 : ℝ)^417 := by
    have hnat : (148544039 : ℕ)^545*100000000000000^417 ≤ 50642774815127^417*250000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      148544039 250000000 50642774815127 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-444877631/2500000000 : ℝ), (303374049/625000000 : ℝ), (148544039/250000000 : ℝ)] ![(10475553805977/100000000000000 : ℝ), (19440835678453/50000000000000 : ℝ), (50642774815127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-444877631/2500000000 : ℝ)|^545 ≤ (10475553805977/100000000000000 : ℝ)^417
        have hw : |(-444877631/2500000000 : ℝ)|=(444877631/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(303374049/625000000 : ℝ)|^545 ≤ (19440835678453/50000000000000 : ℝ)^417
        have hw : |(303374049/625000000 : ℝ)|=(303374049/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(148544039/250000000 : ℝ)|^545 ≤ (50642774815127/100000000000000 : ℝ)^417
        have hw : |(148544039/250000000 : ℝ)|=(148544039/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s0_5 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2591111869/5000000000 : ℝ)*x 0 + (-163472767/1250000000 : ℝ)*x 1 + (2970880281/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2591111869/5000000000 : ℝ)^545 ≤ (42353141374669/100000000000000 : ℝ)^417 := by
    have hnat : (2591111869 : ℕ)^545*100000000000000^417 ≤ 42353141374669^417*5000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591111869 5000000000 42353141374669 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163472767/1250000000 : ℝ)^545 ≤ (7004094911347/100000000000000 : ℝ)^417 := by
    have hnat : (163472767 : ℕ)^545*100000000000000^417 ≤ 7004094911347^417*1250000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163472767 1250000000 7004094911347 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2970880281/5000000000 : ℝ)^545 ≤ (25321381848991/50000000000000 : ℝ)^417 := by
    have hnat : (2970880281 : ℕ)^545*50000000000000^417 ≤ 25321381848991^417*5000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2970880281 5000000000 25321381848991 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2591111869/5000000000 : ℝ), (-163472767/1250000000 : ℝ), (2970880281/5000000000 : ℝ)] ![(42353141374669/100000000000000 : ℝ), (7004094911347/100000000000000 : ℝ), (25321381848991/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2591111869/5000000000 : ℝ)|^545 ≤ (42353141374669/100000000000000 : ℝ)^417
        have hw : |(2591111869/5000000000 : ℝ)|=(2591111869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-163472767/1250000000 : ℝ)|^545 ≤ (7004094911347/100000000000000 : ℝ)^417
        have hw : |(-163472767/1250000000 : ℝ)|=(163472767/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2970880281/5000000000 : ℝ)|^545 ≤ (25321381848991/50000000000000 : ℝ)^417
        have hw : |(2970880281/5000000000 : ℝ)|=(2970880281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s0_6 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5182220369/10000000000 : ℝ)*x 0 + (5941763843/10000000000 : ℝ)*x 1 + (-163472757/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5182220369/10000000000 : ℝ)^545 ≤ (10588276347223/25000000000000 : ℝ)^417 := by
    have hnat : (5182220369 : ℕ)^545*25000000000000^417 ≤ 10588276347223^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182220369 10000000000 10588276347223 25000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5941763843/10000000000 : ℝ)^545 ≤ (1582587507701/3125000000000 : ℝ)^417 := by
    have hnat : (5941763843 : ℕ)^545*3125000000000^417 ≤ 1582587507701^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5941763843 10000000000 1582587507701 3125000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163472757/1250000000 : ℝ)^545 ≤ (3502047175687/50000000000000 : ℝ)^417 := by
    have hnat : (163472757 : ℕ)^545*50000000000000^417 ≤ 3502047175687^417*1250000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163472757 1250000000 3502047175687 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5182220369/10000000000 : ℝ), (5941763843/10000000000 : ℝ), (-163472757/1250000000 : ℝ)] ![(10588276347223/25000000000000 : ℝ), (1582587507701/3125000000000 : ℝ), (3502047175687/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5182220369/10000000000 : ℝ)|^545 ≤ (10588276347223/25000000000000 : ℝ)^417
        have hw : |(5182220369/10000000000 : ℝ)|=(5182220369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5941763843/10000000000 : ℝ)|^545 ≤ (1582587507701/3125000000000 : ℝ)^417
        have hw : |(5941763843/10000000000 : ℝ)|=(5941763843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-163472757/1250000000 : ℝ)|^545 ≤ (3502047175687/50000000000000 : ℝ)^417
        have hw : |(-163472757/1250000000 : ℝ)|=(163472757/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s0_7 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (261193119/625000000 : ℝ)*x 0 + (219906751/400000000 : ℝ)*x 1 + (1584712679/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (261193119/625000000 : ℝ)^545 ≤ (799302320723/2500000000000 : ℝ)^417 := by
    have hnat : (261193119 : ℕ)^545*2500000000000^417 ≤ 799302320723^417*625000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261193119 625000000 799302320723 2500000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (219906751/400000000 : ℝ)^545 ≤ (45753595720749/100000000000000 : ℝ)^417 := by
    have hnat : (219906751 : ℕ)^545*100000000000000^417 ≤ 45753595720749^417*400000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219906751 400000000 45753595720749 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1584712679/5000000000 : ℝ)^545 ≤ (22274311435987/100000000000000 : ℝ)^417 := by
    have hnat : (1584712679 : ℕ)^545*100000000000000^417 ≤ 22274311435987^417*5000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1584712679 5000000000 22274311435987 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(261193119/625000000 : ℝ), (219906751/400000000 : ℝ), (1584712679/5000000000 : ℝ)] ![(799302320723/2500000000000 : ℝ), (45753595720749/100000000000000 : ℝ), (22274311435987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(261193119/625000000 : ℝ)|^545 ≤ (799302320723/2500000000000 : ℝ)^417
        have hw : |(261193119/625000000 : ℝ)|=(261193119/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(219906751/400000000 : ℝ)|^545 ≤ (45753595720749/100000000000000 : ℝ)^417
        have hw : |(219906751/400000000 : ℝ)|=(219906751/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1584712679/5000000000 : ℝ)|^545 ≤ (22274311435987/100000000000000 : ℝ)^417
        have hw : |(1584712679/5000000000 : ℝ)|=(1584712679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1400_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157018501/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1841/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1323/5000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4359/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4359 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4359*1^1024 ≤ 0^1024*1^4359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4359 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4359 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4359/1024 : ℝ) ≤ (2023180684549994651/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4359 ≤ (2023180684549994651/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4359*100000000000000000000^1024 ≤ 2023180684549994651^1024*5^4359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2023180684549994651 100000000000000000000 4359 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2023180684549994651/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4359 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4359/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4359 := by
      have hnat : (1 : ℕ)^1024*1^4359 ≤ 1^4359*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4359 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102023180684549994651/100000000000000000000 : ℝ) ≤ (10047164281279503/10000000000000000 : ℝ) ^ (4359/1024 : ℝ) := by
    have hpowers : (102023180684549994651/100000000000000000000 : ℝ)^1024 ≤ (10047164281279503/10000000000000000 : ℝ)^4359 := by
      have hnat : (102023180684549994651 : ℕ)^1024*10000000000000000^4359 ≤ 10047164281279503^4359*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102023180684549994651 100000000000000000000 10047164281279503 10000000000000000 1024 4359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10047164281279503/10000000000000000 : ℝ)) (X := (102023180684549994651/100000000000000000000 : ℝ)) (by norm_num) 4359 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52023180684549994651/50000000000000000000 : ℝ) ≤ (5047164281279503/5000000000000000 : ℝ) ^ (4359/1024 : ℝ) := by
    have hpowers : (52023180684549994651/50000000000000000000 : ℝ)^1024 ≤ (5047164281279503/5000000000000000 : ℝ)^4359 := by
      have hnat : (52023180684549994651 : ℕ)^1024*5000000000000000^4359 ≤ 5047164281279503^4359*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52023180684549994651 50000000000000000000 5047164281279503 5000000000000000 1024 4359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5047164281279503/5000000000000000 : ℝ)) (X := (52023180684549994651/50000000000000000000 : ℝ)) (by norm_num) 4359 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(47164281279503/4000000000000000 : ℝ)*(0 : ℝ))^(4359/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(47164281279503/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2023180684549994651/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(47164281279503/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4359/1024 : ℝ) := by
    rw [show (1 : ℝ)+(47164281279503/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10047164281279503/10000000000000000 : ℝ) by norm_num, show 1+(2023180684549994651/100000000000000000000 : ℝ)+(0 : ℝ)=(102023180684549994651/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2023180684549994651/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(47164281279503/4000000000000000 : ℝ)*(2/5 : ℝ))^(4359/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(47164281279503/4000000000000000 : ℝ)*(2/5 : ℝ)=(5047164281279503/5000000000000000 : ℝ) by norm_num, show 1+2*(2023180684549994651/100000000000000000000 : ℝ)=(52023180684549994651/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(47164281279503/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4359/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (47164281279503/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(47164281279503/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4359/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (47164281279503/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(47164281279503/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4359/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (47164281279503/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1775350417/10000000000 : ℝ)*X 0 0+(5972240451/10000000000 : ℝ)*X 0 1+(2412278723/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5495329319/10000000000 : ℝ)*X 1 0+(-242498737/1000000000 : ℝ)*X 1 1+(2412278841/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5495329483/10000000000 : ℝ)*X 2 0+(603069699/1250000000 : ℝ)*X 2 1+(-2424987271/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((26063683/62500000 : ℝ)*X 0 0+(1552093571/5000000000 : ℝ)*X 0 1+(5560653651/10000000000 : ℝ)*X 0 2+(26063683/62500000 : ℝ)*X 1 0+(1552093571/5000000000 : ℝ)*X 1 1+(5560653651/10000000000 : ℝ)*X 1 2+(26063683/62500000 : ℝ)*X 2 0+(1552093571/5000000000 : ℝ)*X 2 1+(5560653651/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-444877631/2500000000 : ℝ)*X 0 0+(303374049/625000000 : ℝ)*X 0 1+(148544039/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2591111869/5000000000 : ℝ)*X 1 0+(-163472767/1250000000 : ℝ)*X 1 1+(2970880281/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5182220369/10000000000 : ℝ)*X 2 0+(5941763843/10000000000 : ℝ)*X 2 1+(-163472757/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((261193119/625000000 : ℝ)*X 0 0+(219906751/400000000 : ℝ)*X 0 1+(1584712679/5000000000 : ℝ)*X 0 2+(261193119/625000000 : ℝ)*X 1 0+(219906751/400000000 : ℝ)*X 1 1+(1584712679/5000000000 : ℝ)*X 1 2+(261193119/625000000 : ℝ)*X 2 0+(219906751/400000000 : ℝ)*X 2 1+(1584712679/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (85071598136528831091747/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (166306431/20000000000000 : ℝ)*(base19) + (20937437/2500000000000 : ℝ)*(base23) + (101480353/100000000000000 : ℝ)*(upper3) + (11011601/100000000000000 : ℝ)*(upper4) + (117684913/100000000000000 : ℝ)*(upper5) + (319604601624583/50000000000000 : ℝ)*(major0) + (319604601624583/50000000000000 : ℝ)*(major1) + (319604601624583/50000000000000 : ℝ)*(major2) + (217830879342439/25000000000000 : ℝ)*(sp0) + (217831453406097/25000000000000 : ℝ)*(sp1) + (108915725957383/12500000000000 : ℝ)*(sp2) + (407090197903797/100000000000000 : ℝ)*(sp3) + (3127786787/100000000000000 : ℝ)*(sp4) + (362502297/25000000000000 : ℝ)*(sp7) + (81418329582597/20000000000000 : ℝ)*(f.failure) + (13614478830571/1562500000000 : ℝ)*(f.sum) + (30542248377751/100000000000000000000000000000 : ℝ)*base66 + (147581331222249/200000000000000000000000000000 : ℝ)*base67 + (792414910577751/200000000000000000000000000000 : ℝ)*base70 + (671625477977751/200000000000000000000000000000 : ℝ)*base72 + (16622632577751/100000000000000000000000000000 : ℝ)*base74 + (33497545422249/200000000000000000000000000000 : ℝ)*base75 + (1187935905977751/200000000000000000000000000000 : ℝ)*base78 + (1725891653577751/200000000000000000000000000000 : ℝ)*base80 + (326635081877751/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (16627097/2000000000000000000000 : ℝ)*base89 + (16627097/2000000000000000000000 : ℝ)*base91 + (16627097/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (58461934458516007399797/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (930727657/50000000000000 : ℝ)*(base19) + (1837528381/100000000000000 : ℝ)*(base23) + (170756419/25000000000000 : ℝ)*(base39) + (2743377/50000000000000 : ℝ)*(upper3) + (14148021/3125000000000 : ℝ)*(upper5) + (33720255273877/5000000000000 : ℝ)*(major0) + (33720255273877/5000000000000 : ℝ)*(major1) + (84300552806483/12500000000000 : ℝ)*(major2) + (5891409793/100000000000000 : ℝ)*(sp1) + (173576391/4000000000000 : ℝ)*(sp2) + (459651218757791/50000000000000 : ℝ)*(sp4) + (36771787386019/4000000000000 : ℝ)*(sp5) + (919296943603103/100000000000000 : ℝ)*(sp6) + (429506778616833/100000000000000 : ℝ)*(sp7) + (429506778616833/100000000000000 : ℝ)*(f.failure) + (459651560270629/50000000000000 : ℝ)*(f.sum) + (87798937651553/100000000000000000000000000000 : ℝ)*base65 + (47025100267949/50000000000000000000000000000 : ℝ)*base67 + (145207668763131/20000000000000000000000000000 : ℝ)*base69 + (8222734032051/50000000000000000000000000000 : ℝ)*base72 + (382449787551553/100000000000000000000000000000 : ℝ)*base73 + (11025291643131/20000000000000000000000000000 : ℝ)*base75 + (18079855836869/20000000000000000000000000000 : ℝ)*base78 + (156637872636869/20000000000000000000000000000 : ℝ)*base80 + (53711677233131/10000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (28972667/10000000000000000000000 : ℝ)*base90 + (28972667/10000000000000000000000 : ℝ)*base92 + (28972667/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1400_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157018501/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1841/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1323/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1400_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1400_s1_0 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-243978777/1250000000 : ℝ)*x 0 + (1404268593/2500000000 : ℝ)*x 1 + (5066632867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (243978777/1250000000 : ℝ)^545 ≤ (2364122998899/20000000000000 : ℝ)^417 := by
    have hnat : (243978777 : ℕ)^545*20000000000000^417 ≤ 2364122998899^417*1250000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      243978777 1250000000 2364122998899 20000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1404268593/2500000000 : ℝ)^545 ≤ (4705667216989/10000000000000 : ℝ)^417 := by
    have hnat : (1404268593 : ℕ)^545*10000000000000^417 ≤ 4705667216989^417*2500000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1404268593 2500000000 4705667216989 10000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5066632867/10000000000 : ℝ)^545 ≤ (20561356413699/50000000000000 : ℝ)^417 := by
    have hnat : (5066632867 : ℕ)^545*50000000000000^417 ≤ 20561356413699^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5066632867 10000000000 20561356413699 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-243978777/1250000000 : ℝ), (1404268593/2500000000 : ℝ), (5066632867/10000000000 : ℝ)] ![(2364122998899/20000000000000 : ℝ), (4705667216989/10000000000000 : ℝ), (20561356413699/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-243978777/1250000000 : ℝ)|^545 ≤ (2364122998899/20000000000000 : ℝ)^417
        have hw : |(-243978777/1250000000 : ℝ)|=(243978777/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1404268593/2500000000 : ℝ)|^545 ≤ (4705667216989/10000000000000 : ℝ)^417
        have hw : |(1404268593/2500000000 : ℝ)|=(1404268593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5066632867/10000000000 : ℝ)|^545 ≤ (20561356413699/50000000000000 : ℝ)^417
        have hw : |(5066632867/10000000000 : ℝ)|=(5066632867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s1_1 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (84370971/156250000 : ℝ)*x 0 + (-2244159497/10000000000 : ℝ)*x 1 + (5066634207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84370971/156250000 : ℝ)^545 ≤ (5586422083879/12500000000000 : ℝ)^417 := by
    have hnat : (84370971 : ℕ)^545*12500000000000^417 ≤ 5586422083879^417*156250000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84370971 156250000 5586422083879 12500000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2244159497/10000000000 : ℝ)^545 ≤ (14185896279659/100000000000000 : ℝ)^417 := by
    have hnat : (2244159497 : ℕ)^545*100000000000000^417 ≤ 14185896279659^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244159497 10000000000 14185896279659 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5066634207/10000000000 : ℝ)^545 ≤ (41122727041767/100000000000000 : ℝ)^417 := by
    have hnat : (5066634207 : ℕ)^545*100000000000000^417 ≤ 41122727041767^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5066634207 10000000000 41122727041767 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(84370971/156250000 : ℝ), (-2244159497/10000000000 : ℝ), (5066634207/10000000000 : ℝ)] ![(5586422083879/12500000000000 : ℝ), (14185896279659/100000000000000 : ℝ), (41122727041767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(84370971/156250000 : ℝ)|^545 ≤ (5586422083879/12500000000000 : ℝ)^417
        have hw : |(84370971/156250000 : ℝ)|=(84370971/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2244159497/10000000000 : ℝ)|^545 ≤ (14185896279659/100000000000000 : ℝ)^417
        have hw : |(-2244159497/10000000000 : ℝ)|=(2244159497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5066634207/10000000000 : ℝ)|^545 ≤ (41122727041767/100000000000000 : ℝ)^417
        have hw : |(5066634207/10000000000 : ℝ)|=(5066634207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s1_2 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5399743071/10000000000 : ℝ)*x 0 + (5066633051/10000000000 : ℝ)*x 1 + (-280519971/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5399743071/10000000000 : ℝ)^545 ≤ (44691386698491/100000000000000 : ℝ)^417 := by
    have hnat : (5399743071 : ℕ)^545*100000000000000^417 ≤ 44691386698491^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399743071 10000000000 44691386698491 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5066633051/10000000000 : ℝ)^545 ≤ (20561357389611/50000000000000 : ℝ)^417 := by
    have hnat : (5066633051 : ℕ)^545*50000000000000^417 ≤ 20561357389611^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5066633051 10000000000 20561357389611 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (280519971/1250000000 : ℝ)^545 ≤ (14185898518549/100000000000000 : ℝ)^417 := by
    have hnat : (280519971 : ℕ)^545*100000000000000^417 ≤ 14185898518549^417*1250000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280519971 1250000000 14185898518549 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5399743071/10000000000 : ℝ), (5066633051/10000000000 : ℝ), (-280519971/1250000000 : ℝ)] ![(44691386698491/100000000000000 : ℝ), (20561357389611/50000000000000 : ℝ), (14185898518549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5399743071/10000000000 : ℝ)|^545 ≤ (44691386698491/100000000000000 : ℝ)^417
        have hw : |(5399743071/10000000000 : ℝ)|=(5399743071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5066633051/10000000000 : ℝ)|^545 ≤ (20561357389611/50000000000000 : ℝ)^417
        have hw : |(5066633051/10000000000 : ℝ)|=(5066633051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-280519971/1250000000 : ℝ)|^545 ≤ (14185898518549/100000000000000 : ℝ)^417
        have hw : |(-280519971/1250000000 : ℝ)|=(280519971/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s1_3 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4281894149/10000000000 : ℝ)*x 0 + (1864721687/5000000000 : ℝ)*x 1 + (4907588507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4281894149/10000000000 : ℝ)^545 ≤ (33003875537337/100000000000000 : ℝ)^417 := by
    have hnat : (4281894149 : ℕ)^545*100000000000000^417 ≤ 33003875537337^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4281894149 10000000000 33003875537337 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1864721687/5000000000 : ℝ)^545 ≤ (13776162359473/50000000000000 : ℝ)^417 := by
    have hnat : (1864721687 : ℕ)^545*50000000000000^417 ≤ 13776162359473^417*5000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1864721687 5000000000 13776162359473 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4907588507/10000000000 : ℝ)^545 ≤ (39443799730061/100000000000000 : ℝ)^417 := by
    have hnat : (4907588507 : ℕ)^545*100000000000000^417 ≤ 39443799730061^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4907588507 10000000000 39443799730061 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4281894149/10000000000 : ℝ), (1864721687/5000000000 : ℝ), (4907588507/10000000000 : ℝ)] ![(33003875537337/100000000000000 : ℝ), (13776162359473/50000000000000 : ℝ), (39443799730061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4281894149/10000000000 : ℝ)|^545 ≤ (33003875537337/100000000000000 : ℝ)^417
        have hw : |(4281894149/10000000000 : ℝ)|=(4281894149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1864721687/5000000000 : ℝ)|^545 ≤ (13776162359473/50000000000000 : ℝ)^417
        have hw : |(1864721687/5000000000 : ℝ)|=(1864721687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4907588507/10000000000 : ℝ)|^545 ≤ (39443799730061/100000000000000 : ℝ)^417
        have hw : |(4907588507/10000000000 : ℝ)|=(4907588507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s1_4 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-976135013/5000000000 : ℝ)*x 0 + (5073236159/10000000000 : ℝ)*x 1 + (280517819/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (976135013/5000000000 : ℝ)^545 ≤ (5912048135827/50000000000000 : ℝ)^417 := by
    have hnat : (976135013 : ℕ)^545*50000000000000^417 ≤ 5912048135827^417*5000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      976135013 5000000000 5912048135827 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5073236159/10000000000 : ℝ)^545 ≤ (20596386411493/50000000000000 : ℝ)^417 := by
    have hnat : (5073236159 : ℕ)^545*50000000000000^417 ≤ 20596386411493^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5073236159 10000000000 20596386411493 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (280517819/500000000 : ℝ)^545 ≤ (23491565442053/50000000000000 : ℝ)^417 := by
    have hnat : (280517819 : ℕ)^545*50000000000000^417 ≤ 23491565442053^417*500000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280517819 500000000 23491565442053 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-976135013/5000000000 : ℝ), (5073236159/10000000000 : ℝ), (280517819/500000000 : ℝ)] ![(5912048135827/50000000000000 : ℝ), (20596386411493/50000000000000 : ℝ), (23491565442053/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-976135013/5000000000 : ℝ)|^545 ≤ (5912048135827/50000000000000 : ℝ)^417
        have hw : |(-976135013/5000000000 : ℝ)|=(976135013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5073236159/10000000000 : ℝ)|^545 ≤ (20596386411493/50000000000000 : ℝ)^417
        have hw : |(5073236159/10000000000 : ℝ)|=(5073236159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(280517819/500000000 : ℝ)|^545 ≤ (23491565442053/50000000000000 : ℝ)^417
        have hw : |(280517819/500000000 : ℝ)|=(280517819/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s1_5 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2628121043/5000000000 : ℝ)*x 0 + (-212554661/1250000000 : ℝ)*x 1 + (5610356323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628121043/5000000000 : ℝ)^545 ≤ (43145491585793/100000000000000 : ℝ)^417 := by
    have hnat : (2628121043 : ℕ)^545*100000000000000^417 ≤ 43145491585793^417*5000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628121043 5000000000 43145491585793 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (212554661/1250000000 : ℝ)^545 ≤ (9871378137047/100000000000000 : ℝ)^417 := by
    have hnat : (212554661 : ℕ)^545*100000000000000^417 ≤ 9871378137047^417*1250000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212554661 1250000000 9871378137047 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5610356323/10000000000 : ℝ)^545 ≤ (46983130260247/100000000000000 : ℝ)^417 := by
    have hnat : (5610356323 : ℕ)^545*100000000000000^417 ≤ 46983130260247^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5610356323 10000000000 46983130260247 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628121043/5000000000 : ℝ), (-212554661/1250000000 : ℝ), (5610356323/10000000000 : ℝ)] ![(43145491585793/100000000000000 : ℝ), (9871378137047/100000000000000 : ℝ), (46983130260247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628121043/5000000000 : ℝ)|^545 ≤ (43145491585793/100000000000000 : ℝ)^417
        have hw : |(2628121043/5000000000 : ℝ)|=(2628121043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-212554661/1250000000 : ℝ)|^545 ≤ (9871378137047/100000000000000 : ℝ)^417
        have hw : |(-212554661/1250000000 : ℝ)|=(212554661/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5610356323/10000000000 : ℝ)|^545 ≤ (46983130260247/100000000000000 : ℝ)^417
        have hw : |(5610356323/10000000000 : ℝ)|=(5610356323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s1_6 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1314060653/2500000000 : ℝ)*x 0 + (1402589189/2500000000 : ℝ)*x 1 + (-1700435919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314060653/2500000000 : ℝ)^545 ≤ (5393187153593/12500000000000 : ℝ)^417 := by
    have hnat : (1314060653 : ℕ)^545*12500000000000^417 ≤ 5393187153593^417*2500000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314060653 2500000000 5393187153593 12500000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1402589189/2500000000 : ℝ)^545 ≤ (4698313499939/10000000000000 : ℝ)^417 := by
    have hnat : (1402589189 : ℕ)^545*10000000000000^417 ≤ 4698313499939^417*2500000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1402589189 2500000000 4698313499939 10000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1700435919/10000000000 : ℝ)^545 ≤ (1974273550053/20000000000000 : ℝ)^417 := by
    have hnat : (1700435919 : ℕ)^545*20000000000000^417 ≤ 1974273550053^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1700435919 10000000000 1974273550053 20000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314060653/2500000000 : ℝ), (1402589189/2500000000 : ℝ), (-1700435919/10000000000 : ℝ)] ![(5393187153593/12500000000000 : ℝ), (4698313499939/10000000000000 : ℝ), (1974273550053/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314060653/2500000000 : ℝ)|^545 ≤ (5393187153593/12500000000000 : ℝ)^417
        have hw : |(1314060653/2500000000 : ℝ)|=(1314060653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1402589189/2500000000 : ℝ)|^545 ≤ (4698313499939/10000000000000 : ℝ)^417
        have hw : |(1402589189/2500000000 : ℝ)|=(1402589189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1700435919/10000000000 : ℝ)|^545 ≤ (1974273550053/20000000000000 : ℝ)^417
        have hw : |(-1700435919/10000000000 : ℝ)|=(1700435919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s1_7 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4282837103/10000000000 : ℝ)*x 0 + (4893454961/10000000000 : ℝ)*x 1 + (3743820391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4282837103/10000000000 : ℝ)^545 ≤ (33013374903877/100000000000000 : ℝ)^417 := by
    have hnat : (4282837103 : ℕ)^545*100000000000000^417 ≤ 33013374903877^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4282837103 10000000000 33013374903877 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4893454961/10000000000 : ℝ)^545 ≤ (39295401043271/100000000000000 : ℝ)^417 := by
    have hnat : (4893454961 : ℕ)^545*100000000000000^417 ≤ 39295401043271^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4893454961 10000000000 39295401043271 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3743820391/10000000000 : ℝ)^545 ≤ (5538244807343/20000000000000 : ℝ)^417 := by
    have hnat : (3743820391 : ℕ)^545*20000000000000^417 ≤ 5538244807343^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3743820391 10000000000 5538244807343 20000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4282837103/10000000000 : ℝ), (4893454961/10000000000 : ℝ), (3743820391/10000000000 : ℝ)] ![(33013374903877/100000000000000 : ℝ), (39295401043271/100000000000000 : ℝ), (5538244807343/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4282837103/10000000000 : ℝ)|^545 ≤ (33013374903877/100000000000000 : ℝ)^417
        have hw : |(4282837103/10000000000 : ℝ)|=(4282837103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4893454961/10000000000 : ℝ)|^545 ≤ (39295401043271/100000000000000 : ℝ)^417
        have hw : |(4893454961/10000000000 : ℝ)|=(4893454961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3743820391/10000000000 : ℝ)|^545 ≤ (5538244807343/20000000000000 : ℝ)^417
        have hw : |(3743820391/10000000000 : ℝ)|=(3743820391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1400_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157018501/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1323/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1841/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (463/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19043/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1323/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1841/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1323/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1841/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1323/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1841/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1323/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1841/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1323/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1841/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1323/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1841/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1841/100000 : ℝ) ^ (4359/1024 : ℝ) ≤ (4117357878471/100000000000000000000 : ℝ) := by
    have hpowers : (1841/100000 : ℝ)^4359 ≤ (4117357878471/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1841 : ℕ)^4359*100000000000000000000^1024 ≤ 4117357878471^1024*100000^4359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1841 100000 4117357878471 100000000000000000000 4359 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1841/100000 : ℝ)) (X := (4117357878471/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4359 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1323/5000 : ℝ) ^ (4359/1024 : ℝ) ≤ (348385185920100161/100000000000000000000 : ℝ) := by
    have hpowers : (1323/5000 : ℝ)^4359 ≤ (348385185920100161/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1323 : ℕ)^4359*100000000000000000000^1024 ≤ 348385185920100161^1024*5000^4359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1323 5000 348385185920100161 100000000000000000000 4359 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1323/5000 : ℝ)) (X := (348385185920100161/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4359 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000004117357878471/50000000000000000000 : ℝ) ≤ (10000000193446861/10000000000000000 : ℝ) ^ (4359/1024 : ℝ) := by
    have hpowers : (50000004117357878471/50000000000000000000 : ℝ)^1024 ≤ (10000000193446861/10000000000000000 : ℝ)^4359 := by
      have hnat : (50000004117357878471 : ℕ)^1024*10000000000000000^4359 ≤ 10000000193446861^4359*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000004117357878471 50000000000000000000 10000000193446861 10000000000000000 1024 4359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000193446861/10000000000000000 : ℝ)) (X := (50000004117357878471/50000000000000000000 : ℝ)) (by norm_num) 4359 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12543548662909747329/12500000000000000000 : ℝ) ≤ (1251021668286137/1250000000000000 : ℝ) ^ (4359/1024 : ℝ) := by
    have hpowers : (12543548662909747329/12500000000000000000 : ℝ)^1024 ≤ (1251021668286137/1250000000000000 : ℝ)^4359 := by
      have hnat : (12543548662909747329 : ℕ)^1024*1250000000000000^4359 ≤ 1251021668286137^4359*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12543548662909747329 12500000000000000000 1251021668286137 1250000000000000 1024 4359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1251021668286137/1250000000000000 : ℝ)) (X := (12543548662909747329/12500000000000000000 : ℝ)) (by norm_num) 4359 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50348385185920100161/50000000000000000000 : ℝ) ≤ (10016346499131331/10000000000000000 : ℝ) ^ (4359/1024 : ℝ) := by
    have hpowers : (50348385185920100161/50000000000000000000 : ℝ)^1024 ≤ (10016346499131331/10000000000000000 : ℝ)^4359 := by
      have hnat : (50348385185920100161 : ℕ)^1024*10000000000000000^4359 ≤ 10016346499131331^4359*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50348385185920100161 50000000000000000000 10016346499131331 10000000000000000 1024 4359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10016346499131331/10000000000000000 : ℝ)) (X := (50348385185920100161/50000000000000000000 : ℝ)) (by norm_num) 4359 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4117357878471/100000000000000000000 : ℝ) ≤ ((35165701601957594527/35170000000000000000 : ℝ)+2*(1634630568447/492380000000000 : ℝ)*(1841/100000 : ℝ))^(4359/1024 : ℝ) := by
    rw [show (35165701601957594527/35170000000000000000 : ℝ)+2*(1634630568447/492380000000000 : ℝ)*(1841/100000 : ℝ)=(10000000193446861/10000000000000000 : ℝ) by norm_num, show 1+2*(4117357878471/100000000000000000000 : ℝ)=(50000004117357878471/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(348385185920100161/100000000000000000000 : ℝ)+(4117357878471/100000000000000000000 : ℝ) ≤ ((35165701601957594527/35170000000000000000 : ℝ)+(1634630568447/492380000000000 : ℝ)*((1323/5000 : ℝ)+(1841/100000 : ℝ)))^(4359/1024 : ℝ) := by
    rw [show (35165701601957594527/35170000000000000000 : ℝ)+(1634630568447/492380000000000 : ℝ)*((1323/5000 : ℝ)+(1841/100000 : ℝ))=(1251021668286137/1250000000000000 : ℝ) by norm_num, show 1+(348385185920100161/100000000000000000000 : ℝ)+(4117357878471/100000000000000000000 : ℝ)=(12543548662909747329/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(348385185920100161/100000000000000000000 : ℝ) ≤ ((35165701601957594527/35170000000000000000 : ℝ)+2*(1634630568447/492380000000000 : ℝ)*(1323/5000 : ℝ))^(4359/1024 : ℝ) := by
    rw [show (35165701601957594527/35170000000000000000 : ℝ)+2*(1634630568447/492380000000000 : ℝ)*(1323/5000 : ℝ)=(10016346499131331/10000000000000000 : ℝ) by norm_num, show 1+2*(348385185920100161/100000000000000000000 : ℝ)=(50348385185920100161/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (35165701601957594527/35170000000000000000 : ℝ)*(X 1 0+X 2 0)+(1634630568447/492380000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4359/1024 : ℝ)) (lo := (1841/100000 : ℝ)) (hi := (1323/5000 : ℝ)) (c := (35165701601957594527/35170000000000000000 : ℝ)) (alpha := (1634630568447/492380000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (35165701601957594527/35170000000000000000 : ℝ)*(X 0 1+X 2 1)+(1634630568447/492380000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4359/1024 : ℝ)) (lo := (1841/100000 : ℝ)) (hi := (1323/5000 : ℝ)) (c := (35165701601957594527/35170000000000000000 : ℝ)) (alpha := (1634630568447/492380000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (35165701601957594527/35170000000000000000 : ℝ)*(X 0 2+X 1 2)+(1634630568447/492380000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4359/1024 : ℝ)) (lo := (1841/100000 : ℝ)) (hi := (1323/5000 : ℝ)) (c := (35165701601957594527/35170000000000000000 : ℝ)) (alpha := (1634630568447/492380000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-243978777/1250000000 : ℝ)*X 0 0+(1404268593/2500000000 : ℝ)*X 0 1+(5066632867/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((84370971/156250000 : ℝ)*X 1 0+(-2244159497/10000000000 : ℝ)*X 1 1+(5066634207/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5399743071/10000000000 : ℝ)*X 2 0+(5066633051/10000000000 : ℝ)*X 2 1+(-280519971/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4281894149/10000000000 : ℝ)*X 0 0+(1864721687/5000000000 : ℝ)*X 0 1+(4907588507/10000000000 : ℝ)*X 0 2+(4281894149/10000000000 : ℝ)*X 1 0+(1864721687/5000000000 : ℝ)*X 1 1+(4907588507/10000000000 : ℝ)*X 1 2+(4281894149/10000000000 : ℝ)*X 2 0+(1864721687/5000000000 : ℝ)*X 2 1+(4907588507/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-976135013/5000000000 : ℝ)*X 0 0+(5073236159/10000000000 : ℝ)*X 0 1+(280517819/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2628121043/5000000000 : ℝ)*X 1 0+(-212554661/1250000000 : ℝ)*X 1 1+(5610356323/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1314060653/2500000000 : ℝ)*X 2 0+(1402589189/2500000000 : ℝ)*X 2 1+(-1700435919/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4282837103/10000000000 : ℝ)*X 0 0+(4893454961/10000000000 : ℝ)*X 0 1+(3743820391/10000000000 : ℝ)*X 0 2+(4282837103/10000000000 : ℝ)*X 1 0+(4893454961/10000000000 : ℝ)*X 1 1+(3743820391/10000000000 : ℝ)*X 1 2+(4282837103/10000000000 : ℝ)*X 2 0+(4893454961/10000000000 : ℝ)*X 2 1+(3743820391/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (50901065391377057848081977483/12309500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (678686759/100000000000000 : ℝ)*(base19) + (12052613/1250000000000 : ℝ)*(base23) + (97079953/100000000000000 : ℝ)*(upper3) + (1779641/12500000000000 : ℝ)*(upper4) + (28345507/100000000000000 : ℝ)*(upper5) + (1332769376392351/100000000000000 : ℝ)*(major0) + (1332769376392351/100000000000000 : ℝ)*(major1) + (1332769376392351/100000000000000 : ℝ)*(major2) + (908366048073053/50000000000000 : ℝ)*(sp0) + (454185066814389/25000000000000 : ℝ)*(sp1) + (908369990867637/50000000000000 : ℝ)*(sp2) + (424397185204011/50000000000000 : ℝ)*(sp3) + (8849798209/100000000000000 : ℝ)*(sp4) + (65971911/2000000000000 : ℝ)*(sp7) + (212199417250893/25000000000000 : ℝ)*(f.failure) + (908370472972157/50000000000000 : ℝ)*(f.sum) + (5354368676253/4923800000000000000000000000 : ℝ)*base66 + (25496033126725340839/24619000000000000000000000000000000 : ℝ)*base67 + (35829905522110340839/24619000000000000000000000000000000 : ℝ)*base69 + (171751162248343659161/24619000000000000000000000000000000 : ℝ)*base72 + (113371128528823/24619000000000000000000000000 : ℝ)*base73 + (137473791366519659161/24619000000000000000000000000000000 : ℝ)*base76 + (224561895776246340839/24619000000000000000000000000000000 : ℝ)*base77 + (29225656256216340839/24619000000000000000000000000000000 : ℝ)*base79 + (130101060429029/24619000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (15228607/2500000000000000000000 : ℝ)*base90 + (15228607/2500000000000000000000 : ℝ)*base92 + (15228607/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4643422450862703339456109413/1758500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (182982987/100000000000000 : ℝ)*(base1) + (21895069/2500000000000 : ℝ)*(base19) + (1168956423/100000000000000 : ℝ)*(base23) + (28691301/50000000000000 : ℝ)*(upper3) + (44415321/25000000000000 : ℝ)*(upper5) + (1365812177468073/100000000000000 : ℝ)*(major0) + (1365812177468073/100000000000000 : ℝ)*(major1) + (1365812177468073/100000000000000 : ℝ)*(major2) + (393199871/10000000000000 : ℝ)*(sp1) + (3922745561/50000000000000 : ℝ)*(sp2) + (1861782890613123/100000000000000 : ℝ)*(sp4) + (930888949914333/50000000000000 : ℝ)*(sp5) + (1861773693182591/100000000000000 : ℝ)*(sp6) + (217460344076099/25000000000000 : ℝ)*(sp7) + (434920779643691/50000000000000 : ℝ)*(f.failure) + (232722838453767/12500000000000 : ℝ)*(f.sum) + (895207960421/24619000000000000000000000000 : ℝ)*base65 + (51441721605677244703/24619000000000000000000000000000000 : ℝ)*base68 + (405824606114274244703/24619000000000000000000000000000000 : ℝ)*base70 + (39007174885093755297/24619000000000000000000000000000000 : ℝ)*base71 + (17618690618149/24619000000000000000000000000 : ℝ)*base73 + (64626274688686244703/24619000000000000000000000000000000 : ℝ)*base76 + (19172737354628244703/24619000000000000000000000000000000 : ℝ)*base78 + (112836102577963755297/24619000000000000000000000000000000 : ℝ)*base79 + (88139182782589/12309500000000000000000000000 : ℝ)*base82 + (24927191/5000000000000000000000 : ℝ)*base89 + (24927191/5000000000000000000000 : ℝ)*base91 + (24927191/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1400_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157018501/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1323/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1841/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (463/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19043/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1400_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1400_s2_0 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1987185771/10000000000 : ℝ)*x 0 + (1366222083/2500000000 : ℝ)*x 1 + (2598048791/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1987185771/10000000000 : ℝ)^545 ≤ (12101233847989/100000000000000 : ℝ)^417 := by
    have hnat : (1987185771 : ℕ)^545*100000000000000^417 ≤ 12101233847989^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1987185771 10000000000 12101233847989 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1366222083/2500000000 : ℝ)^545 ≤ (5674671405161/12500000000000 : ℝ)^417 := by
    have hnat : (1366222083 : ℕ)^545*12500000000000^417 ≤ 5674671405161^417*2500000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366222083 2500000000 5674671405161 12500000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2598048791/5000000000 : ℝ)^545 ≤ (42501394897783/100000000000000 : ℝ)^417 := by
    have hnat : (2598048791 : ℕ)^545*100000000000000^417 ≤ 42501394897783^417*5000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598048791 5000000000 42501394897783 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1987185771/10000000000 : ℝ), (1366222083/2500000000 : ℝ), (2598048791/5000000000 : ℝ)] ![(12101233847989/100000000000000 : ℝ), (5674671405161/12500000000000 : ℝ), (42501394897783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1987185771/10000000000 : ℝ)|^545 ≤ (12101233847989/100000000000000 : ℝ)^417
        have hw : |(-1987185771/10000000000 : ℝ)|=(1987185771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1366222083/2500000000 : ℝ)|^545 ≤ (5674671405161/12500000000000 : ℝ)^417
        have hw : |(1366222083/2500000000 : ℝ)|=(1366222083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2598048791/5000000000 : ℝ)|^545 ≤ (42501394897783/100000000000000 : ℝ)^417
        have hw : |(2598048791/5000000000 : ℝ)|=(2598048791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s2_1 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5362010083/10000000000 : ℝ)*x 0 + (-85026433/400000000 : ℝ)*x 1 + (2598048783/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362010083/10000000000 : ℝ)^545 ≤ (44283663334133/100000000000000 : ℝ)^417 := by
    have hnat : (5362010083 : ℕ)^545*100000000000000^417 ≤ 44283663334133^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362010083 10000000000 44283663334133 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (85026433/400000000 : ℝ)^545 ≤ (6607470962881/50000000000000 : ℝ)^417 := by
    have hnat : (85026433 : ℕ)^545*50000000000000^417 ≤ 6607470962881^417*400000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85026433 400000000 6607470962881 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2598048783/5000000000 : ℝ)^545 ≤ (2125069736337/5000000000000 : ℝ)^417 := by
    have hnat : (2598048783 : ℕ)^545*5000000000000^417 ≤ 2125069736337^417*5000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598048783 5000000000 2125069736337 5000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362010083/10000000000 : ℝ), (-85026433/400000000 : ℝ), (2598048783/5000000000 : ℝ)] ![(44283663334133/100000000000000 : ℝ), (6607470962881/50000000000000 : ℝ), (2125069736337/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362010083/10000000000 : ℝ)|^545 ≤ (44283663334133/100000000000000 : ℝ)^417
        have hw : |(5362010083/10000000000 : ℝ)|=(5362010083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-85026433/400000000 : ℝ)|^545 ≤ (6607470962881/50000000000000 : ℝ)^417
        have hw : |(-85026433/400000000 : ℝ)|=(85026433/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2598048783/5000000000 : ℝ)|^545 ≤ (2125069736337/5000000000000 : ℝ)^417
        have hw : |(2598048783/5000000000 : ℝ)|=(2598048783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s2_2 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5362009893/10000000000 : ℝ)*x 0 + (5196097779/10000000000 : ℝ)*x 1 + (-531415199/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362009893/10000000000 : ℝ)^545 ≤ (22141830641651/50000000000000 : ℝ)^417 := by
    have hnat : (5362009893 : ℕ)^545*50000000000000^417 ≤ 22141830641651^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362009893 10000000000 22141830641651 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5196097779/10000000000 : ℝ)^545 ≤ (8500279400751/20000000000000 : ℝ)^417 := by
    have hnat : (5196097779 : ℕ)^545*20000000000000^417 ≤ 8500279400751^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196097779 10000000000 8500279400751 20000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (531415199/2500000000 : ℝ)^545 ≤ (3303735422533/25000000000000 : ℝ)^417 := by
    have hnat : (531415199 : ℕ)^545*25000000000000^417 ≤ 3303735422533^417*2500000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531415199 2500000000 3303735422533 25000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362009893/10000000000 : ℝ), (5196097779/10000000000 : ℝ), (-531415199/2500000000 : ℝ)] ![(22141830641651/50000000000000 : ℝ), (8500279400751/20000000000000 : ℝ), (3303735422533/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362009893/10000000000 : ℝ)|^545 ≤ (22141830641651/50000000000000 : ℝ)^417
        have hw : |(5362009893/10000000000 : ℝ)|=(5362009893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5196097779/10000000000 : ℝ)|^545 ≤ (8500279400751/20000000000000 : ℝ)^417
        have hw : |(5196097779/10000000000 : ℝ)|=(5196097779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-531415199/2500000000 : ℝ)|^545 ≤ (3303735422533/25000000000000 : ℝ)^417
        have hw : |(-531415199/2500000000 : ℝ)|=(531415199/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s2_3 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1076694017/2500000000 : ℝ)*x 0 + (251740731/625000000 : ℝ)*x 1 + (1150790881/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076694017/2500000000 : ℝ)^545 ≤ (33254752028917/100000000000000 : ℝ)^417 := by
    have hnat : (1076694017 : ℕ)^545*100000000000000^417 ≤ 33254752028917^417*2500000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076694017 2500000000 33254752028917 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (251740731/625000000 : ℝ)^545 ≤ (15234178010417/50000000000000 : ℝ)^417 := by
    have hnat : (251740731 : ℕ)^545*50000000000000^417 ≤ 15234178010417^417*625000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251740731 625000000 15234178010417 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1150790881/2500000000 : ℝ)^545 ≤ (290215135467/800000000000 : ℝ)^417 := by
    have hnat : (1150790881 : ℕ)^545*800000000000^417 ≤ 290215135467^417*2500000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1150790881 2500000000 290215135467 800000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1076694017/2500000000 : ℝ), (251740731/625000000 : ℝ), (1150790881/2500000000 : ℝ)] ![(33254752028917/100000000000000 : ℝ), (15234178010417/50000000000000 : ℝ), (290215135467/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1076694017/2500000000 : ℝ)|^545 ≤ (33254752028917/100000000000000 : ℝ)^417
        have hw : |(1076694017/2500000000 : ℝ)|=(1076694017/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(251740731/625000000 : ℝ)|^545 ≤ (15234178010417/50000000000000 : ℝ)^417
        have hw : |(251740731/625000000 : ℝ)|=(251740731/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1150790881/2500000000 : ℝ)|^545 ≤ (290215135467/800000000000 : ℝ)^417
        have hw : |(1150790881/2500000000 : ℝ)|=(1150790881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s2_4 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-993618379/5000000000 : ℝ)*x 0 + (1039536337/2000000000 : ℝ)*x 1 + (5463291043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (993618379/5000000000 : ℝ)^545 ≤ (6050819824349/50000000000000 : ℝ)^417 := by
    have hnat : (993618379 : ℕ)^545*50000000000000^417 ≤ 6050819824349^417*5000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      993618379 5000000000 6050819824349 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1039536337/2000000000 : ℝ)^545 ≤ (42518330087559/100000000000000 : ℝ)^417 := by
    have hnat : (1039536337 : ℕ)^545*100000000000000^417 ≤ 42518330087559^417*2000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039536337 2000000000 42518330087559 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5463291043/10000000000 : ℝ)^545 ≤ (22690015125841/50000000000000 : ℝ)^417 := by
    have hnat : (5463291043 : ℕ)^545*50000000000000^417 ≤ 22690015125841^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5463291043 10000000000 22690015125841 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-993618379/5000000000 : ℝ), (1039536337/2000000000 : ℝ), (5463291043/10000000000 : ℝ)] ![(6050819824349/50000000000000 : ℝ), (42518330087559/100000000000000 : ℝ), (22690015125841/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-993618379/5000000000 : ℝ)|^545 ≤ (6050819824349/50000000000000 : ℝ)^417
        have hw : |(-993618379/5000000000 : ℝ)|=(993618379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1039536337/2000000000 : ℝ)|^545 ≤ (42518330087559/100000000000000 : ℝ)^417
        have hw : |(1039536337/2000000000 : ℝ)|=(1039536337/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5463291043/10000000000 : ℝ)|^545 ≤ (22690015125841/50000000000000 : ℝ)^417
        have hw : |(5463291043/10000000000 : ℝ)|=(5463291043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s2_5 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5292310959/10000000000 : ℝ)*x 0 + (-1858467957/10000000000 : ℝ)*x 1 + (1092658149/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5292310959/10000000000 : ℝ)^545 ≤ (8706569378139/20000000000000 : ℝ)^417 := by
    have hnat : (5292310959 : ℕ)^545*20000000000000^417 ≤ 8706569378139^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5292310959 10000000000 8706569378139 20000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1858467957/10000000000 : ℝ)^545 ≤ (2217425216049/20000000000000 : ℝ)^417 := by
    have hnat : (1858467957 : ℕ)^545*20000000000000^417 ≤ 2217425216049^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1858467957 10000000000 2217425216049 20000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1092658149/2000000000 : ℝ)^545 ≤ (22690013508293/50000000000000 : ℝ)^417 := by
    have hnat : (1092658149 : ℕ)^545*50000000000000^417 ≤ 22690013508293^417*2000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092658149 2000000000 22690013508293 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5292310959/10000000000 : ℝ), (-1858467957/10000000000 : ℝ), (1092658149/2000000000 : ℝ)] ![(8706569378139/20000000000000 : ℝ), (2217425216049/20000000000000 : ℝ), (22690013508293/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5292310959/10000000000 : ℝ)|^545 ≤ (8706569378139/20000000000000 : ℝ)^417
        have hw : |(5292310959/10000000000 : ℝ)|=(5292310959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1858467957/10000000000 : ℝ)|^545 ≤ (2217425216049/20000000000000 : ℝ)^417
        have hw : |(-1858467957/10000000000 : ℝ)|=(1858467957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1092658149/2000000000 : ℝ)|^545 ≤ (22690013508293/50000000000000 : ℝ)^417
        have hw : |(1092658149/2000000000 : ℝ)|=(1092658149/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s2_6 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1323078093/2500000000 : ℝ)*x 0 + (5463290727/10000000000 : ℝ)*x 1 + (-1858466033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323078093/2500000000 : ℝ)^545 ≤ (1741314483251/4000000000000 : ℝ)^417 := by
    have hnat : (1323078093 : ℕ)^545*4000000000000^417 ≤ 1741314483251^417*2500000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323078093 2500000000 1741314483251 4000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5463290727/10000000000 : ℝ)^545 ≤ (22690013410589/50000000000000 : ℝ)^417 := by
    have hnat : (5463290727 : ℕ)^545*50000000000000^417 ≤ 22690013410589^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5463290727 10000000000 22690013410589 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1858466033/10000000000 : ℝ)^545 ≤ (11087111078929/100000000000000 : ℝ)^417 := by
    have hnat : (1858466033 : ℕ)^545*100000000000000^417 ≤ 11087111078929^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1858466033 10000000000 11087111078929 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323078093/2500000000 : ℝ), (5463290727/10000000000 : ℝ), (-1858466033/10000000000 : ℝ)] ![(1741314483251/4000000000000 : ℝ), (22690013410589/50000000000000 : ℝ), (11087111078929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323078093/2500000000 : ℝ)|^545 ≤ (1741314483251/4000000000000 : ℝ)^417
        have hw : |(1323078093/2500000000 : ℝ)|=(1323078093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5463290727/10000000000 : ℝ)|^545 ≤ (22690013410589/50000000000000 : ℝ)^417
        have hw : |(5463290727/10000000000 : ℝ)|=(5463290727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1858466033/10000000000 : ℝ)|^545 ≤ (11087111078929/100000000000000 : ℝ)^417
        have hw : |(-1858466033/10000000000 : ℝ)|=(1858466033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s2_7 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4306886499/10000000000 : ℝ)*x 0 + (2299886733/5000000000 : ℝ)*x 1 + (4031270001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4306886499/10000000000 : ℝ)^545 ≤ (8313966615877/25000000000000 : ℝ)^417 := by
    have hnat : (4306886499 : ℕ)^545*25000000000000^417 ≤ 8313966615877^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4306886499 10000000000 8313966615877 25000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2299886733/5000000000 : ℝ)^545 ≤ (36241978533351/100000000000000 : ℝ)^417 := by
    have hnat : (2299886733 : ℕ)^545*100000000000000^417 ≤ 36241978533351^417*5000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2299886733 5000000000 36241978533351 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4031270001/10000000000 : ℝ)^545 ≤ (30502154982623/100000000000000 : ℝ)^417 := by
    have hnat : (4031270001 : ℕ)^545*100000000000000^417 ≤ 30502154982623^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4031270001 10000000000 30502154982623 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4306886499/10000000000 : ℝ), (2299886733/5000000000 : ℝ), (4031270001/10000000000 : ℝ)] ![(8313966615877/25000000000000 : ℝ), (36241978533351/100000000000000 : ℝ), (30502154982623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4306886499/10000000000 : ℝ)|^545 ≤ (8313966615877/25000000000000 : ℝ)^417
        have hw : |(4306886499/10000000000 : ℝ)|=(4306886499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2299886733/5000000000 : ℝ)|^545 ≤ (36241978533351/100000000000000 : ℝ)^417
        have hw : |(2299886733/5000000000 : ℝ)|=(2299886733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4031270001/10000000000 : ℝ)|^545 ≤ (30502154982623/100000000000000 : ℝ)^417
        have hw : |(4031270001/10000000000 : ℝ)|=(4031270001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1400_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157018501/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19043/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (463/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (10207/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3973/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19043/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (463/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19043/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (463/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19043/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (463/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19043/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (463/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19043/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (463/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19043/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (463/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (463/6250 : ℝ) ^ (4359/1024 : ℝ) ≤ (1543485253631627/100000000000000000000 : ℝ) := by
    have hpowers : (463/6250 : ℝ)^4359 ≤ (1543485253631627/100000000000000000000 : ℝ)^1024 := by
      have hnat : (463 : ℕ)^4359*100000000000000000000^1024 ≤ 1543485253631627^1024*6250^4359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        463 6250 1543485253631627 100000000000000000000 4359 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (463/6250 : ℝ)) (X := (1543485253631627/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4359 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (19043/100000 : ℝ) ^ (4359/1024 : ℝ) ≤ (85891784832955679/100000000000000000000 : ℝ) := by
    have hpowers : (19043/100000 : ℝ)^4359 ≤ (85891784832955679/100000000000000000000 : ℝ)^1024 := by
      have hnat : (19043 : ℕ)^4359*100000000000000000000^1024 ≤ 85891784832955679^1024*100000^4359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19043 100000 85891784832955679 100000000000000000000 4359 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19043/100000 : ℝ)) (X := (85891784832955679/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4359 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001543485253631627/50000000000000000000 : ℝ) ≤ (10000072517101889/10000000000000000 : ℝ) ^ (4359/1024 : ℝ) := by
    have hpowers : (50001543485253631627/50000000000000000000 : ℝ)^1024 ≤ (10000072517101889/10000000000000000 : ℝ)^4359 := by
      have hnat : (50001543485253631627 : ℕ)^1024*10000000000000000^4359 ≤ 10000072517101889^4359*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001543485253631627 50000000000000000000 10000072517101889 10000000000000000 1024 4359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000072517101889/10000000000000000 : ℝ)) (X := (50001543485253631627/50000000000000000000 : ℝ)) (by norm_num) 4359 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50043717635043293653/50000000000000000000 : ℝ) ≤ (5001026655024543/5000000000000000 : ℝ) ^ (4359/1024 : ℝ) := by
    have hpowers : (50043717635043293653/50000000000000000000 : ℝ)^1024 ≤ (5001026655024543/5000000000000000 : ℝ)^4359 := by
      have hnat : (50043717635043293653 : ℕ)^1024*5000000000000000^4359 ≤ 5001026655024543^4359*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50043717635043293653 50000000000000000000 5001026655024543 5000000000000000 1024 4359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001026655024543/5000000000000000 : ℝ)) (X := (50043717635043293653/50000000000000000000 : ℝ)) (by norm_num) 4359 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50085891784832955679/50000000000000000000 : ℝ) ≤ (10004034102996283/10000000000000000 : ℝ) ^ (4359/1024 : ℝ) := by
    have hpowers : (50085891784832955679/50000000000000000000 : ℝ)^1024 ≤ (10004034102996283/10000000000000000 : ℝ)^4359 := by
      have hnat : (50085891784832955679 : ℕ)^1024*10000000000000000^4359 ≤ 10004034102996283^4359*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50085891784832955679 50000000000000000000 10004034102996283 10000000000000000 1024 4359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004034102996283/10000000000000000 : ℝ)) (X := (50085891784832955679/50000000000000000000 : ℝ)) (by norm_num) 4359 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1543485253631627/100000000000000000000 : ℝ) ≤ ((116321496308174807763/116350000000000000000 : ℝ)+2*(1980792947197/1163500000000000 : ℝ)*(463/6250 : ℝ))^(4359/1024 : ℝ) := by
    rw [show (116321496308174807763/116350000000000000000 : ℝ)+2*(1980792947197/1163500000000000 : ℝ)*(463/6250 : ℝ)=(10000072517101889/10000000000000000 : ℝ) by norm_num, show 1+2*(1543485253631627/100000000000000000000 : ℝ)=(50001543485253631627/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(85891784832955679/100000000000000000000 : ℝ)+(1543485253631627/100000000000000000000 : ℝ) ≤ ((116321496308174807763/116350000000000000000 : ℝ)+(1980792947197/1163500000000000 : ℝ)*((19043/100000 : ℝ)+(463/6250 : ℝ)))^(4359/1024 : ℝ) := by
    rw [show (116321496308174807763/116350000000000000000 : ℝ)+(1980792947197/1163500000000000 : ℝ)*((19043/100000 : ℝ)+(463/6250 : ℝ))=(5001026655024543/5000000000000000 : ℝ) by norm_num, show 1+(85891784832955679/100000000000000000000 : ℝ)+(1543485253631627/100000000000000000000 : ℝ)=(50043717635043293653/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(85891784832955679/100000000000000000000 : ℝ) ≤ ((116321496308174807763/116350000000000000000 : ℝ)+2*(1980792947197/1163500000000000 : ℝ)*(19043/100000 : ℝ))^(4359/1024 : ℝ) := by
    rw [show (116321496308174807763/116350000000000000000 : ℝ)+2*(1980792947197/1163500000000000 : ℝ)*(19043/100000 : ℝ)=(10004034102996283/10000000000000000 : ℝ) by norm_num, show 1+2*(85891784832955679/100000000000000000000 : ℝ)=(50085891784832955679/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (116321496308174807763/116350000000000000000 : ℝ)*(X 1 0+X 2 0)+(1980792947197/1163500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4359/1024 : ℝ)) (lo := (463/6250 : ℝ)) (hi := (19043/100000 : ℝ)) (c := (116321496308174807763/116350000000000000000 : ℝ)) (alpha := (1980792947197/1163500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (116321496308174807763/116350000000000000000 : ℝ)*(X 0 1+X 2 1)+(1980792947197/1163500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4359/1024 : ℝ)) (lo := (463/6250 : ℝ)) (hi := (19043/100000 : ℝ)) (c := (116321496308174807763/116350000000000000000 : ℝ)) (alpha := (1980792947197/1163500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (116321496308174807763/116350000000000000000 : ℝ)*(X 0 2+X 1 2)+(1980792947197/1163500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4359/1024 : ℝ)) (lo := (463/6250 : ℝ)) (hi := (19043/100000 : ℝ)) (c := (116321496308174807763/116350000000000000000 : ℝ)) (alpha := (1980792947197/1163500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1987185771/10000000000 : ℝ)*X 0 0+(1366222083/2500000000 : ℝ)*X 0 1+(2598048791/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5362010083/10000000000 : ℝ)*X 1 0+(-85026433/400000000 : ℝ)*X 1 1+(2598048783/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5362009893/10000000000 : ℝ)*X 2 0+(5196097779/10000000000 : ℝ)*X 2 1+(-531415199/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1076694017/2500000000 : ℝ)*X 0 0+(251740731/625000000 : ℝ)*X 0 1+(1150790881/2500000000 : ℝ)*X 0 2+(1076694017/2500000000 : ℝ)*X 1 0+(251740731/625000000 : ℝ)*X 1 1+(1150790881/2500000000 : ℝ)*X 1 2+(1076694017/2500000000 : ℝ)*X 2 0+(251740731/625000000 : ℝ)*X 2 1+(1150790881/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-993618379/5000000000 : ℝ)*X 0 0+(1039536337/2000000000 : ℝ)*X 0 1+(5463291043/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5292310959/10000000000 : ℝ)*X 1 0+(-1858467957/10000000000 : ℝ)*X 1 1+(1092658149/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1323078093/2500000000 : ℝ)*X 2 0+(5463290727/10000000000 : ℝ)*X 2 1+(-1858466033/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4306886499/10000000000 : ℝ)*X 0 0+(2299886733/5000000000 : ℝ)*X 0 1+(4031270001/10000000000 : ℝ)*X 0 2+(4306886499/10000000000 : ℝ)*X 1 0+(2299886733/5000000000 : ℝ)*X 1 1+(4031270001/10000000000 : ℝ)*X 1 2+(4306886499/10000000000 : ℝ)*X 2 0+(2299886733/5000000000 : ℝ)*X 2 1+(4031270001/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (973711693518395791451120853/116350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1422424127/100000000000000 : ℝ)*(base19) + (561808981/50000000000000 : ℝ)*(base23) + (89532577/100000000000000 : ℝ)*(lower2) + (249747077/100000000000000 : ℝ)*(upper3) + (113386563/100000000000000 : ℝ)*(upper5) + (54586054463841/2000000000000 : ℝ)*(major0) + (54586054463841/2000000000000 : ℝ)*(major1) + (54586054463841/2000000000000 : ℝ)*(major2) + (465048077106439/12500000000000 : ℝ)*(sp0) + (930099799630607/25000000000000 : ℝ)*(sp1) + (3720399497328593/100000000000000 : ℝ)*(sp2) + (1738195391670431/100000000000000 : ℝ)*(sp3) + (4001023761/25000000000000 : ℝ)*(sp4) + (9154806579/100000000000000 : ℝ)*(sp7) + (173820454647701/10000000000000 : ℝ)*(f.failure) + (930100155236639/25000000000000 : ℝ)*(f.sum) + (4499626423479/2327000000000000000000000000 : ℝ)*base65 + (2081982463889497683/232700000000000000000000000000000 : ℝ)*base67 + (3642661947999997683/232700000000000000000000000000000 : ℝ)*base69 + (2960098523254197683/232700000000000000000000000000000 : ℝ)*base71 + (111212137931/581750000000000000000000000 : ℝ)*base73 + (4628128908935597683/232700000000000000000000000000000 : ℝ)*base75 + (4100298499136697683/232700000000000000000000000000000 : ℝ)*base77 + (3288050781477397683/232700000000000000000000000000000 : ℝ)*base79 + (9102673803189/2327000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (5883799/1000000000000000000000 : ℝ)*base90 + (5883799/1000000000000000000000 : ℝ)*base92 + (5883799/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3271455204217907285490024339/2908750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (149450797/50000000000000 : ℝ)*(base19) + (1474202181/100000000000000 : ℝ)*(base23) + (46958967/25000000000000 : ℝ)*(lower2) + (11703949/50000000000000 : ℝ)*(upper3) + (82746133/100000000000000 : ℝ)*(lower4) + (1380986600970183/50000000000000 : ℝ)*(major0) + (1380986600970183/50000000000000 : ℝ)*(major1) + (1380986600970183/50000000000000 : ℝ)*(major2) + (27993856183/100000000000000 : ℝ)*(sp2) + (322827281/20000000000000 : ℝ)*(sp3) + (941233762416729/25000000000000 : ℝ)*(sp4) + (1882467375382661/50000000000000 : ℝ)*(sp5) + (3764905581608553/100000000000000 : ℝ)*(sp6) + (879504851293791/50000000000000 : ℝ)*(sp7) + (879505658361993/50000000000000 : ℝ)*(f.failure) + (941233762416729/25000000000000 : ℝ)*(f.sum) + (134943506599037/14543750000000000000000000000 : ℝ)*base66 + (59200495079265030629/5817500000000000000000000000000000 : ℝ)*base67 + (70166909362700030629/5817500000000000000000000000000000 : ℝ)*base69 + (24852525334995030629/5817500000000000000000000000000000 : ℝ)*base71 + (466223279129/113623046875000000000000000 : ℝ)*base74 + (52520619699815030629/5817500000000000000000000000000000 : ℝ)*base75 + (25373934264497530629/5817500000000000000000000000000000 : ℝ)*base77 + (42696991474625030629/5817500000000000000000000000000000 : ℝ)*base79 + (4777467569227/58175000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (43767507/5000000000000000000000 : ℝ)*base90 + (43767507/5000000000000000000000 : ℝ)*base92 + (43767507/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1400_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157018501/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19043/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (463/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10207/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3973/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1400_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1400_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157018501/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10207/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3973/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1400_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1400_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1400_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157018501/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10207/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3973/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1400_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
