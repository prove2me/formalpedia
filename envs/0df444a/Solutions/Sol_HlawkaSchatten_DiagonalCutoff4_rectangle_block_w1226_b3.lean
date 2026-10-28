-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1226_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:13:13.922982+00:00
-- url     : https://prove2.me/submissions/6c1f17ce-c858-4d07-8cb7-42c6830902fc

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
theorem support_rectangle_w1226_box_0 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2003167923/10000000000 : ℝ)*x 0 + (5375079453/10000000000 : ℝ)*x 1 + (1343770149/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2003167923/10000000000 : ℝ)^8419 ≤ (11946750471907/100000000000000 : ℝ)^6371 := by
    have hnat : (2003167923 : ℕ)^8419*100000000000000^6371 ≤ 11946750471907^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2003167923 10000000000 11946750471907 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5375079453/10000000000 : ℝ)^8419 ≤ (44026618568087/100000000000000 : ℝ)^6371 := by
    have hnat : (5375079453 : ℕ)^8419*100000000000000^6371 ≤ 44026618568087^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375079453 10000000000 44026618568087 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1343770149/2500000000 : ℝ)^8419 ≤ (44026630939793/100000000000000 : ℝ)^6371 := by
    have hnat : (1343770149 : ℕ)^8419*100000000000000^6371 ≤ 44026630939793^6371*2500000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343770149 2500000000 44026630939793 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2003167923/10000000000 : ℝ), (5375079453/10000000000 : ℝ), (1343770149/2500000000 : ℝ)] ![(11946750471907/100000000000000 : ℝ), (44026618568087/100000000000000 : ℝ), (44026630939793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2003167923/10000000000 : ℝ)|^8419 ≤ (11946750471907/100000000000000 : ℝ)^6371
        have hw : |(-2003167923/10000000000 : ℝ)|=(2003167923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5375079453/10000000000 : ℝ)|^8419 ≤ (44026618568087/100000000000000 : ℝ)^6371
        have hw : |(5375079453/10000000000 : ℝ)|=(5375079453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1343770149/2500000000 : ℝ)|^8419 ≤ (44026630939793/100000000000000 : ℝ)^6371
        have hw : |(1343770149/2500000000 : ℝ)|=(1343770149/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_box_1 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5296682313/10000000000 : ℝ)*x 0 + (-2109685949/10000000000 : ℝ)*x 1 + (5375080547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296682313/10000000000 : ℝ)^8419 ≤ (2698753278399/6250000000000 : ℝ)^6371 := by
    have hnat : (5296682313 : ℕ)^8419*6250000000000^6371 ≤ 2698753278399^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296682313 10000000000 2698753278399 6250000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2109685949/10000000000 : ℝ)^8419 ≤ (19989557997/156250000000 : ℝ)^6371 := by
    have hnat : (2109685949 : ℕ)^8419*156250000000^6371 ≤ 19989557997^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109685949 10000000000 19989557997 156250000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5375080547/10000000000 : ℝ)^8419 ≤ (22013315204711/50000000000000 : ℝ)^6371 := by
    have hnat : (5375080547 : ℕ)^8419*50000000000000^6371 ≤ 22013315204711^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375080547 10000000000 22013315204711 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296682313/10000000000 : ℝ), (-2109685949/10000000000 : ℝ), (5375080547/10000000000 : ℝ)] ![(2698753278399/6250000000000 : ℝ), (19989557997/156250000000 : ℝ), (22013315204711/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296682313/10000000000 : ℝ)|^8419 ≤ (2698753278399/6250000000000 : ℝ)^6371
        have hw : |(5296682313/10000000000 : ℝ)|=(5296682313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2109685949/10000000000 : ℝ)|^8419 ≤ (19989557997/156250000000 : ℝ)^6371
        have hw : |(-2109685949/10000000000 : ℝ)|=(2109685949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5375080547/10000000000 : ℝ)|^8419 ≤ (22013315204711/50000000000000 : ℝ)^6371
        have hw : |(5375080547/10000000000 : ℝ)|=(5375080547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_box_2 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5296682893/10000000000 : ℝ)*x 0 + (215003193/400000000 : ℝ)*x 1 + (-421937229/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296682893/10000000000 : ℝ)^8419 ≤ (43180058702659/100000000000000 : ℝ)^6371 := by
    have hnat : (5296682893 : ℕ)^8419*100000000000000^6371 ≤ 43180058702659^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296682893 10000000000 43180058702659 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215003193/400000000 : ℝ)^8419 ≤ (22013311297287/50000000000000 : ℝ)^6371 := by
    have hnat : (215003193 : ℕ)^8419*50000000000000^6371 ≤ 22013311297287^6371*400000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215003193 400000000 22013311297287 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (421937229/2000000000 : ℝ)^8419 ≤ (1599164836089/12500000000000 : ℝ)^6371 := by
    have hnat : (421937229 : ℕ)^8419*12500000000000^6371 ≤ 1599164836089^6371*2000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421937229 2000000000 1599164836089 12500000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296682893/10000000000 : ℝ), (215003193/400000000 : ℝ), (-421937229/2000000000 : ℝ)] ![(43180058702659/100000000000000 : ℝ), (22013311297287/50000000000000 : ℝ), (1599164836089/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296682893/10000000000 : ℝ)|^8419 ≤ (43180058702659/100000000000000 : ℝ)^6371
        have hw : |(5296682893/10000000000 : ℝ)|=(5296682893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(215003193/400000000 : ℝ)|^8419 ≤ (22013311297287/50000000000000 : ℝ)^6371
        have hw : |(215003193/400000000 : ℝ)|=(215003193/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-421937229/2000000000 : ℝ)|^8419 ≤ (1599164836089/12500000000000 : ℝ)^6371
        have hw : |(-421937229/2000000000 : ℝ)|=(421937229/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_box_3 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (557456613/1250000000 : ℝ)*x 0 + (4301687051/10000000000 : ℝ)*x 1 + (2150843463/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (557456613/1250000000 : ℝ)^8419 ≤ (17200321862529/50000000000000 : ℝ)^6371 := by
    have hnat : (557456613 : ℕ)^8419*50000000000000^6371 ≤ 17200321862529^6371*1250000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      557456613 1250000000 17200321862529 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4301687051/10000000000 : ℝ)^8419 ≤ (4099959844973/12500000000000 : ℝ)^6371 := by
    have hnat : (4301687051 : ℕ)^8419*12500000000000^6371 ≤ 4099959844973^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4301687051 10000000000 4099959844973 12500000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2150843463/5000000000 : ℝ)^8419 ≤ (32799677500297/100000000000000 : ℝ)^6371 := by
    have hnat : (2150843463 : ℕ)^8419*100000000000000^6371 ≤ 32799677500297^6371*5000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150843463 5000000000 32799677500297 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(557456613/1250000000 : ℝ), (4301687051/10000000000 : ℝ), (2150843463/5000000000 : ℝ)] ![(17200321862529/50000000000000 : ℝ), (4099959844973/12500000000000 : ℝ), (32799677500297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(557456613/1250000000 : ℝ)|^8419 ≤ (17200321862529/50000000000000 : ℝ)^6371
        have hw : |(557456613/1250000000 : ℝ)|=(557456613/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4301687051/10000000000 : ℝ)|^8419 ≤ (4099959844973/12500000000000 : ℝ)^6371
        have hw : |(4301687051/10000000000 : ℝ)|=(4301687051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2150843463/5000000000 : ℝ)|^8419 ≤ (32799677500297/100000000000000 : ℝ)^6371
        have hw : |(2150843463/5000000000 : ℝ)|=(2150843463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_box_4 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-563230833/2500000000 : ℝ)*x 0 + (660265251/1250000000 : ℝ)*x 1 + (1320530301/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (563230833/2500000000 : ℝ)^8419 ≤ (558139124007/4000000000000 : ℝ)^6371 := by
    have hnat : (563230833 : ℕ)^8419*4000000000000^6371 ≤ 558139124007^6371*2500000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563230833 2500000000 558139124007 4000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (660265251/1250000000 : ℝ)^8419 ≤ (4302326526707/10000000000000 : ℝ)^6371 := by
    have hnat : (660265251 : ℕ)^8419*10000000000000^6371 ≤ 4302326526707^6371*1250000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660265251 1250000000 4302326526707 10000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1320530301/2500000000 : ℝ)^8419 ≤ (43023256613329/100000000000000 : ℝ)^6371 := by
    have hnat : (1320530301 : ℕ)^8419*100000000000000^6371 ≤ 43023256613329^6371*2500000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320530301 2500000000 43023256613329 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-563230833/2500000000 : ℝ), (660265251/1250000000 : ℝ), (1320530301/2500000000 : ℝ)] ![(558139124007/4000000000000 : ℝ), (4302326526707/10000000000000 : ℝ), (43023256613329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-563230833/2500000000 : ℝ)|^8419 ≤ (558139124007/4000000000000 : ℝ)^6371
        have hw : |(-563230833/2500000000 : ℝ)|=(563230833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(660265251/1250000000 : ℝ)|^8419 ≤ (4302326526707/10000000000000 : ℝ)^6371
        have hw : |(660265251/1250000000 : ℝ)|=(660265251/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1320530301/2500000000 : ℝ)|^8419 ≤ (43023256613329/100000000000000 : ℝ)^6371
        have hw : |(1320530301/2500000000 : ℝ)|=(1320530301/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_box_5 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2681117237/5000000000 : ℝ)*x 0 + (-2146493171/10000000000 : ℝ)*x 1 + (5282122231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681117237/5000000000 : ℝ)^8419 ≤ (43887639366527/100000000000000 : ℝ)^6371 := by
    have hnat : (2681117237 : ℕ)^8419*100000000000000^6371 ≤ 43887639366527^6371*5000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681117237 5000000000 43887639366527 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2146493171/10000000000 : ℝ)^8419 ≤ (261781858973/2000000000000 : ℝ)^6371 := by
    have hnat : (2146493171 : ℕ)^8419*2000000000000^6371 ≤ 261781858973^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2146493171 10000000000 261781858973 2000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5282122231/10000000000 : ℝ)^8419 ≤ (43023267667299/100000000000000 : ℝ)^6371 := by
    have hnat : (5282122231 : ℕ)^8419*100000000000000^6371 ≤ 43023267667299^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282122231 10000000000 43023267667299 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681117237/5000000000 : ℝ), (-2146493171/10000000000 : ℝ), (5282122231/10000000000 : ℝ)] ![(43887639366527/100000000000000 : ℝ), (261781858973/2000000000000 : ℝ), (43023267667299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681117237/5000000000 : ℝ)|^8419 ≤ (43887639366527/100000000000000 : ℝ)^6371
        have hw : |(2681117237/5000000000 : ℝ)|=(2681117237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2146493171/10000000000 : ℝ)|^8419 ≤ (261781858973/2000000000000 : ℝ)^6371
        have hw : |(-2146493171/10000000000 : ℝ)|=(2146493171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5282122231/10000000000 : ℝ)|^8419 ≤ (43023267667299/100000000000000 : ℝ)^6371
        have hw : |(5282122231/10000000000 : ℝ)|=(5282122231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_box_6 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (10724473/20000000 : ℝ)*x 0 + (5282121203/10000000000 : ℝ)*x 1 + (-1073245913/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10724473/20000000 : ℝ)^8419 ≤ (43887661278869/100000000000000 : ℝ)^6371 := by
    have hnat : (10724473 : ℕ)^8419*100000000000000^6371 ≤ 43887661278869^6371*20000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10724473 20000000 43887661278869 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5282121203/10000000000 : ℝ)^8419 ≤ (21511628301283/50000000000000 : ℝ)^6371 := by
    have hnat : (5282121203 : ℕ)^8419*50000000000000^6371 ≤ 21511628301283^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282121203 10000000000 21511628301283 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1073245913/5000000000 : ℝ)^8419 ≤ (13089082110499/100000000000000 : ℝ)^6371 := by
    have hnat : (1073245913 : ℕ)^8419*100000000000000^6371 ≤ 13089082110499^6371*5000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073245913 5000000000 13089082110499 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10724473/20000000 : ℝ), (5282121203/10000000000 : ℝ), (-1073245913/5000000000 : ℝ)] ![(43887661278869/100000000000000 : ℝ), (21511628301283/50000000000000 : ℝ), (13089082110499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10724473/20000000 : ℝ)|^8419 ≤ (43887661278869/100000000000000 : ℝ)^6371
        have hw : |(10724473/20000000 : ℝ)|=(10724473/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5282121203/10000000000 : ℝ)|^8419 ≤ (21511628301283/50000000000000 : ℝ)^6371
        have hw : |(5282121203/10000000000 : ℝ)|=(5282121203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1073245913/5000000000 : ℝ)|^8419 ≤ (13089082110499/100000000000000 : ℝ)^6371
        have hw : |(-1073245913/5000000000 : ℝ)|=(1073245913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_box_7 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4245900771/10000000000 : ℝ)*x 0 + (4408542821/10000000000 : ℝ)*x 1 + (2204271439/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4245900771/10000000000 : ℝ)^8419 ≤ (32238757085743/100000000000000 : ℝ)^6371 := by
    have hnat : (4245900771 : ℕ)^8419*100000000000000^6371 ≤ 32238757085743^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4245900771 10000000000 32238757085743 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4408542821/10000000000 : ℝ)^8419 ≤ (3388062115851/10000000000000 : ℝ)^6371 := by
    have hnat : (4408542821 : ℕ)^8419*10000000000000^6371 ≤ 3388062115851^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4408542821 10000000000 3388062115851 10000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2204271439/5000000000 : ℝ)^8419 ≤ (4235077717173/12500000000000 : ℝ)^6371 := by
    have hnat : (2204271439 : ℕ)^8419*12500000000000^6371 ≤ 4235077717173^6371*5000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2204271439 5000000000 4235077717173 12500000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4245900771/10000000000 : ℝ), (4408542821/10000000000 : ℝ), (2204271439/5000000000 : ℝ)] ![(32238757085743/100000000000000 : ℝ), (3388062115851/10000000000000 : ℝ), (4235077717173/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4245900771/10000000000 : ℝ)|^8419 ≤ (32238757085743/100000000000000 : ℝ)^6371
        have hw : |(4245900771/10000000000 : ℝ)|=(4245900771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4408542821/10000000000 : ℝ)|^8419 ≤ (3388062115851/10000000000000 : ℝ)^6371
        have hw : |(4408542821/10000000000 : ℝ)|=(4408542821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2204271439/5000000000 : ℝ)|^8419 ≤ (4235077717173/12500000000000 : ℝ)^6371
        have hw : |(2204271439/5000000000 : ℝ)|=(2204271439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_box_8 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-440120771/2000000000 : ℝ)*x 0 + (5218743881/10000000000 : ℝ)*x 1 + (673086549/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (440120771/2000000000 : ℝ)^8419 ≤ (422714977277/3125000000000 : ℝ)^6371 := by
    have hnat : (440120771 : ℕ)^8419*3125000000000^6371 ≤ 422714977277^6371*2000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440120771 2000000000 422714977277 3125000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218743881/10000000000 : ℝ)^8419 ≤ (5292802856591/12500000000000 : ℝ)^6371 := by
    have hnat : (5218743881 : ℕ)^8419*12500000000000^6371 ≤ 5292802856591^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218743881 10000000000 5292802856591 12500000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673086549/1250000000 : ℝ)^8419 ≤ (44130697853947/100000000000000 : ℝ)^6371 := by
    have hnat : (673086549 : ℕ)^8419*100000000000000^6371 ≤ 44130697853947^6371*1250000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673086549 1250000000 44130697853947 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-440120771/2000000000 : ℝ), (5218743881/10000000000 : ℝ), (673086549/1250000000 : ℝ)] ![(422714977277/3125000000000 : ℝ), (5292802856591/12500000000000 : ℝ), (44130697853947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-440120771/2000000000 : ℝ)|^8419 ≤ (422714977277/3125000000000 : ℝ)^6371
        have hw : |(-440120771/2000000000 : ℝ)|=(440120771/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218743881/10000000000 : ℝ)|^8419 ≤ (5292802856591/12500000000000 : ℝ)^6371
        have hw : |(5218743881/10000000000 : ℝ)|=(5218743881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673086549/1250000000 : ℝ)|^8419 ≤ (44130697853947/100000000000000 : ℝ)^6371
        have hw : |(673086549/1250000000 : ℝ)|=(673086549/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_box_9 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1322475283/2500000000 : ℝ)*x 0 + (-2105812589/10000000000 : ℝ)*x 1 + (2692346203/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322475283/2500000000 : ℝ)^8419 ≤ (134709420587/312500000000 : ℝ)^6371 := by
    have hnat : (1322475283 : ℕ)^8419*312500000000^6371 ≤ 134709420587^6371*2500000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322475283 2500000000 134709420587 312500000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2105812589/10000000000 : ℝ)^8419 ≤ (12762287395551/100000000000000 : ℝ)^6371 := by
    have hnat : (2105812589 : ℕ)^8419*100000000000000^6371 ≤ 12762287395551^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105812589 10000000000 12762287395551 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2692346203/5000000000 : ℝ)^8419 ≤ (44130698005569/100000000000000 : ℝ)^6371 := by
    have hnat : (2692346203 : ℕ)^8419*100000000000000^6371 ≤ 44130698005569^6371*5000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692346203 5000000000 44130698005569 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322475283/2500000000 : ℝ), (-2105812589/10000000000 : ℝ), (2692346203/5000000000 : ℝ)] ![(134709420587/312500000000 : ℝ), (12762287395551/100000000000000 : ℝ), (44130698005569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322475283/2500000000 : ℝ)|^8419 ≤ (134709420587/312500000000 : ℝ)^6371
        have hw : |(1322475283/2500000000 : ℝ)|=(1322475283/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2105812589/10000000000 : ℝ)|^8419 ≤ (12762287395551/100000000000000 : ℝ)^6371
        have hw : |(-2105812589/10000000000 : ℝ)|=(2105812589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2692346203/5000000000 : ℝ)|^8419 ≤ (44130698005569/100000000000000 : ℝ)^6371
        have hw : |(2692346203/5000000000 : ℝ)|=(2692346203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_box_10 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2644950567/5000000000 : ℝ)*x 0 + (5384692391/10000000000 : ℝ)*x 1 + (-1052906303/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644950567/5000000000 : ℝ)^8419 ≤ (43107014609377/100000000000000 : ℝ)^6371 := by
    have hnat : (2644950567 : ℕ)^8419*100000000000000^6371 ≤ 43107014609377^6371*5000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644950567 5000000000 43107014609377 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5384692391/10000000000 : ℝ)^8419 ≤ (44130697843117/100000000000000 : ℝ)^6371 := by
    have hnat : (5384692391 : ℕ)^8419*100000000000000^6371 ≤ 44130697843117^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384692391 10000000000 44130697843117 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052906303/5000000000 : ℝ)^8419 ≤ (12762287531699/100000000000000 : ℝ)^6371 := by
    have hnat : (1052906303 : ℕ)^8419*100000000000000^6371 ≤ 12762287531699^6371*5000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052906303 5000000000 12762287531699 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644950567/5000000000 : ℝ), (5384692391/10000000000 : ℝ), (-1052906303/5000000000 : ℝ)] ![(43107014609377/100000000000000 : ℝ), (44130697843117/100000000000000 : ℝ), (12762287531699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644950567/5000000000 : ℝ)|^8419 ≤ (43107014609377/100000000000000 : ℝ)^6371
        have hw : |(2644950567/5000000000 : ℝ)|=(2644950567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5384692391/10000000000 : ℝ)|^8419 ≤ (44130697843117/100000000000000 : ℝ)^6371
        have hw : |(5384692391/10000000000 : ℝ)|=(5384692391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1052906303/5000000000 : ℝ)|^8419 ≤ (12762287531699/100000000000000 : ℝ)^6371
        have hw : |(-1052906303/5000000000 : ℝ)|=(1052906303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_box_11 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1120370757/2500000000 : ℝ)*x 0 + (2145315707/5000000000 : ℝ)*x 1 + (4290631397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1120370757/2500000000 : ℝ)^8419 ≤ (346233414579/1000000000000 : ℝ)^6371 := by
    have hnat : (1120370757 : ℕ)^8419*1000000000000^6371 ≤ 346233414579^6371*2500000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120370757 2500000000 346233414579 1000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2145315707/5000000000 : ℝ)^8419 ≤ (16344164675939/50000000000000 : ℝ)^6371 := by
    have hnat : (2145315707 : ℕ)^8419*50000000000000^6371 ≤ 16344164675939^6371*5000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145315707 5000000000 16344164675939 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4290631397/10000000000 : ℝ)^8419 ≤ (32688329180729/100000000000000 : ℝ)^6371 := by
    have hnat : (4290631397 : ℕ)^8419*100000000000000^6371 ≤ 32688329180729^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4290631397 10000000000 32688329180729 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1120370757/2500000000 : ℝ), (2145315707/5000000000 : ℝ), (4290631397/10000000000 : ℝ)] ![(346233414579/1000000000000 : ℝ), (16344164675939/50000000000000 : ℝ), (32688329180729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1120370757/2500000000 : ℝ)|^8419 ≤ (346233414579/1000000000000 : ℝ)^6371
        have hw : |(1120370757/2500000000 : ℝ)|=(1120370757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2145315707/5000000000 : ℝ)|^8419 ≤ (16344164675939/50000000000000 : ℝ)^6371
        have hw : |(2145315707/5000000000 : ℝ)|=(2145315707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4290631397/10000000000 : ℝ)|^8419 ≤ (32688329180729/100000000000000 : ℝ)^6371
        have hw : |(4290631397/10000000000 : ℝ)|=(4290631397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_box_12 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2055755859/10000000000 : ℝ)*x 0 + (5437239111/10000000000 : ℝ)*x 1 + (5274048311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2055755859/10000000000 : ℝ)^8419 ≤ (193170911301/1562500000000 : ℝ)^6371 := by
    have hnat : (2055755859 : ℕ)^8419*1562500000000^6371 ≤ 193170911301^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2055755859 10000000000 193170911301 1562500000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5437239111/10000000000 : ℝ)^8419 ≤ (4470067514829/10000000000000 : ℝ)^6371 := by
    have hnat : (5437239111 : ℕ)^8419*10000000000000^6371 ≤ 4470067514829^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437239111 10000000000 4470067514829 10000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5274048311/10000000000 : ℝ)^8419 ≤ (21468193260241/50000000000000 : ℝ)^6371 := by
    have hnat : (5274048311 : ℕ)^8419*50000000000000^6371 ≤ 21468193260241^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274048311 10000000000 21468193260241 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2055755859/10000000000 : ℝ), (5437239111/10000000000 : ℝ), (5274048311/10000000000 : ℝ)] ![(193170911301/1562500000000 : ℝ), (4470067514829/10000000000000 : ℝ), (21468193260241/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2055755859/10000000000 : ℝ)|^8419 ≤ (193170911301/1562500000000 : ℝ)^6371
        have hw : |(-2055755859/10000000000 : ℝ)|=(2055755859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5437239111/10000000000 : ℝ)|^8419 ≤ (4470067514829/10000000000000 : ℝ)^6371
        have hw : |(5437239111/10000000000 : ℝ)|=(5437239111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5274048311/10000000000 : ℝ)|^8419 ≤ (21468193260241/50000000000000 : ℝ)^6371
        have hw : |(5274048311/10000000000 : ℝ)|=(5274048311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_box_13 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2683962553/5000000000 : ℝ)*x 0 + (-2149633981/10000000000 : ℝ)*x 1 + (1318512271/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2683962553/5000000000 : ℝ)^8419 ≤ (43949197278687/100000000000000 : ℝ)^6371 := by
    have hnat : (2683962553 : ℕ)^8419*100000000000000^6371 ≤ 43949197278687^6371*5000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2683962553 5000000000 43949197278687 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2149633981/10000000000 : ℝ)^8419 ≤ (6557203938503/50000000000000 : ℝ)^6371 := by
    have hnat : (2149633981 : ℕ)^8419*50000000000000^6371 ≤ 6557203938503^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149633981 10000000000 6557203938503 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1318512271/2500000000 : ℝ)^8419 ≤ (10734098709117/25000000000000 : ℝ)^6371 := by
    have hnat : (1318512271 : ℕ)^8419*25000000000000^6371 ≤ 10734098709117^6371*2500000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318512271 2500000000 10734098709117 25000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2683962553/5000000000 : ℝ), (-2149633981/10000000000 : ℝ), (1318512271/2500000000 : ℝ)] ![(43949197278687/100000000000000 : ℝ), (6557203938503/50000000000000 : ℝ), (10734098709117/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2683962553/5000000000 : ℝ)|^8419 ≤ (43949197278687/100000000000000 : ℝ)^6371
        have hw : |(2683962553/5000000000 : ℝ)|=(2683962553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2149633981/10000000000 : ℝ)|^8419 ≤ (6557203938503/50000000000000 : ℝ)^6371
        have hw : |(-2149633981/10000000000 : ℝ)|=(2149633981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1318512271/2500000000 : ℝ)|^8419 ≤ (10734098709117/25000000000000 : ℝ)^6371
        have hw : |(1318512271/2500000000 : ℝ)|=(1318512271/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_box_14 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (670990721/1250000000 : ℝ)*x 0 + (5274048747/10000000000 : ℝ)*x 1 + (-2149633541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (670990721/1250000000 : ℝ)^8419 ≤ (21974602220517/50000000000000 : ℝ)^6371 := by
    have hnat : (670990721 : ℕ)^8419*50000000000000^6371 ≤ 21974602220517^6371*1250000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      670990721 1250000000 21974602220517 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5274048747/10000000000 : ℝ)^8419 ≤ (42936391210999/100000000000000 : ℝ)^6371 := by
    have hnat : (5274048747 : ℕ)^8419*100000000000000^6371 ≤ 42936391210999^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274048747 10000000000 42936391210999 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2149633541/10000000000 : ℝ)^8419 ≤ (13114404329773/100000000000000 : ℝ)^6371 := by
    have hnat : (2149633541 : ℕ)^8419*100000000000000^6371 ≤ 13114404329773^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149633541 10000000000 13114404329773 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(670990721/1250000000 : ℝ), (5274048747/10000000000 : ℝ), (-2149633541/10000000000 : ℝ)] ![(21974602220517/50000000000000 : ℝ), (42936391210999/100000000000000 : ℝ), (13114404329773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(670990721/1250000000 : ℝ)|^8419 ≤ (21974602220517/50000000000000 : ℝ)^6371
        have hw : |(670990721/1250000000 : ℝ)|=(670990721/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5274048747/10000000000 : ℝ)|^8419 ≤ (42936391210999/100000000000000 : ℝ)^6371
        have hw : |(5274048747/10000000000 : ℝ)|=(5274048747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2149633541/10000000000 : ℝ)|^8419 ≤ (13114404329773/100000000000000 : ℝ)^6371
        have hw : |(-2149633541/10000000000 : ℝ)|=(2149633541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_box_15 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2113552283/5000000000 : ℝ)*x 0 + (441781897/1000000000 : ℝ)*x 1 + (2208908839/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2113552283/5000000000 : ℝ)^8419 ≤ (8012573956071/25000000000000 : ℝ)^6371 := by
    have hnat : (2113552283 : ℕ)^8419*25000000000000^6371 ≤ 8012573956071^6371*5000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113552283 5000000000 8012573956071 25000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (441781897/1000000000 : ℝ)^8419 ≤ (16987429323327/50000000000000 : ℝ)^6371 := by
    have hnat : (441781897 : ℕ)^8419*50000000000000^6371 ≤ 16987429323327^6371*1000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441781897 1000000000 16987429323327 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2208908839/5000000000 : ℝ)^8419 ≤ (16987422758321/50000000000000 : ℝ)^6371 := by
    have hnat : (2208908839 : ℕ)^8419*50000000000000^6371 ≤ 16987422758321^6371*5000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2208908839 5000000000 16987422758321 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2113552283/5000000000 : ℝ), (441781897/1000000000 : ℝ), (2208908839/5000000000 : ℝ)] ![(8012573956071/25000000000000 : ℝ), (16987429323327/50000000000000 : ℝ), (16987422758321/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2113552283/5000000000 : ℝ)|^8419 ≤ (8012573956071/25000000000000 : ℝ)^6371
        have hw : |(2113552283/5000000000 : ℝ)|=(2113552283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(441781897/1000000000 : ℝ)|^8419 ≤ (16987429323327/50000000000000 : ℝ)^6371
        have hw : |(441781897/1000000000 : ℝ)|=(441781897/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2208908839/5000000000 : ℝ)|^8419 ≤ (16987422758321/50000000000000 : ℝ)^6371
        have hw : |(2208908839/5000000000 : ℝ)|=(2208908839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1226_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30223053/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (573/5000 : ℝ)*pair X i i ≤ pair X i h) :
    -(15561/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11873/20000 : ℝ) ∧ (40031/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (83311/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2819/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (573/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2819/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (573/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2819/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (573/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2819/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (573/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2819/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (573/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2819/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (573/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (573/5000 : ℝ) ^ (4209/1024 : ℝ) ≤ (13580570770498857/100000000000000000000 : ℝ) := by
    have hpowers : (573/5000 : ℝ)^4209 ≤ (13580570770498857/100000000000000000000 : ℝ)^1024 := by
      have hnat : (573 : ℕ)^4209*100000000000000000000^1024 ≤ 13580570770498857^1024*5000^4209 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        573 5000 13580570770498857 100000000000000000000 4209 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (573/5000 : ℝ)) (X := (13580570770498857/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4209 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2819/20000 : ℝ) ^ (4209/1024 : ℝ) ≤ (31794962920705497/100000000000000000000 : ℝ) := by
    have hpowers : (2819/20000 : ℝ)^4209 ≤ (31794962920705497/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2819 : ℕ)^4209*100000000000000000000^1024 ≤ 31794962920705497^1024*20000^4209 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2819 20000 31794962920705497 100000000000000000000 4209 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2819/20000 : ℝ)) (X := (31794962920705497/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4209 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013580570770498857/50000000000000000000 : ℝ) ≤ (5000330365302529/5000000000000000 : ℝ) ^ (4209/1024 : ℝ) := by
    have hpowers : (50013580570770498857/50000000000000000000 : ℝ)^1024 ≤ (5000330365302529/5000000000000000 : ℝ)^4209 := by
      have hnat : (50013580570770498857 : ℕ)^1024*5000000000000000^4209 ≤ 5000330365302529^4209*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013580570770498857 50000000000000000000 5000330365302529 5000000000000000 1024 4209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000330365302529/5000000000000000 : ℝ)) (X := (50013580570770498857/50000000000000000000 : ℝ)) (by norm_num) 4209 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022687766845602177/50000000000000000000 : ℝ) ≤ (10001103743681121/10000000000000000 : ℝ) ^ (4209/1024 : ℝ) := by
    have hpowers : (50022687766845602177/50000000000000000000 : ℝ)^1024 ≤ (10001103743681121/10000000000000000 : ℝ)^4209 := by
      have hnat : (50022687766845602177 : ℕ)^1024*10000000000000000^4209 ≤ 10001103743681121^4209*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022687766845602177 50000000000000000000 10001103743681121 10000000000000000 1024 4209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001103743681121/10000000000000000 : ℝ)) (X := (50022687766845602177/50000000000000000000 : ℝ)) (by norm_num) 4209 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031794962920705497/50000000000000000000 : ℝ) ≤ (156274168074331/156250000000000 : ℝ) ^ (4209/1024 : ℝ) := by
    have hpowers : (50031794962920705497/50000000000000000000 : ℝ)^1024 ≤ (156274168074331/156250000000000 : ℝ)^4209 := by
      have hnat : (50031794962920705497 : ℕ)^1024*156250000000000^4209 ≤ 156274168074331^4209*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031794962920705497 50000000000000000000 156274168074331 156250000000000 1024 4209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156274168074331/156250000000000 : ℝ)) (X := (50031794962920705497/50000000000000000000 : ℝ)) (by norm_num) 4209 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13580570770498857/100000000000000000000 : ℝ) ≤ ((2634158716544096387/2635000000000000000 : ℝ)+2*(443013076063/263500000000000 : ℝ)*(573/5000 : ℝ))^(4209/1024 : ℝ) := by
    rw [show (2634158716544096387/2635000000000000000 : ℝ)+2*(443013076063/263500000000000 : ℝ)*(573/5000 : ℝ)=(5000330365302529/5000000000000000 : ℝ) by norm_num, show 1+2*(13580570770498857/100000000000000000000 : ℝ)=(50013580570770498857/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31794962920705497/100000000000000000000 : ℝ)+(13580570770498857/100000000000000000000 : ℝ) ≤ ((2634158716544096387/2635000000000000000 : ℝ)+(443013076063/263500000000000 : ℝ)*((2819/20000 : ℝ)+(573/5000 : ℝ)))^(4209/1024 : ℝ) := by
    rw [show (2634158716544096387/2635000000000000000 : ℝ)+(443013076063/263500000000000 : ℝ)*((2819/20000 : ℝ)+(573/5000 : ℝ))=(10001103743681121/10000000000000000 : ℝ) by norm_num, show 1+(31794962920705497/100000000000000000000 : ℝ)+(13580570770498857/100000000000000000000 : ℝ)=(50022687766845602177/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31794962920705497/100000000000000000000 : ℝ) ≤ ((2634158716544096387/2635000000000000000 : ℝ)+2*(443013076063/263500000000000 : ℝ)*(2819/20000 : ℝ))^(4209/1024 : ℝ) := by
    rw [show (2634158716544096387/2635000000000000000 : ℝ)+2*(443013076063/263500000000000 : ℝ)*(2819/20000 : ℝ)=(156274168074331/156250000000000 : ℝ) by norm_num, show 1+2*(31794962920705497/100000000000000000000 : ℝ)=(50031794962920705497/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2634158716544096387/2635000000000000000 : ℝ)*(X 1 0+X 2 0)+(443013076063/263500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4209/1024 : ℝ)) (lo := (573/5000 : ℝ)) (hi := (2819/20000 : ℝ)) (c := (2634158716544096387/2635000000000000000 : ℝ)) (alpha := (443013076063/263500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2634158716544096387/2635000000000000000 : ℝ)*(X 0 1+X 2 1)+(443013076063/263500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4209/1024 : ℝ)) (lo := (573/5000 : ℝ)) (hi := (2819/20000 : ℝ)) (c := (2634158716544096387/2635000000000000000 : ℝ)) (alpha := (443013076063/263500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2634158716544096387/2635000000000000000 : ℝ)*(X 0 2+X 1 2)+(443013076063/263500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4209/1024 : ℝ)) (lo := (573/5000 : ℝ)) (hi := (2819/20000 : ℝ)) (c := (2634158716544096387/2635000000000000000 : ℝ)) (alpha := (443013076063/263500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2003167923/10000000000 : ℝ)*X 0 0+(5375079453/10000000000 : ℝ)*X 0 1+(1343770149/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5296682313/10000000000 : ℝ)*X 1 0+(-2109685949/10000000000 : ℝ)*X 1 1+(5375080547/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5296682893/10000000000 : ℝ)*X 2 0+(215003193/400000000 : ℝ)*X 2 1+(-421937229/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((557456613/1250000000 : ℝ)*X 0 0+(4301687051/10000000000 : ℝ)*X 0 1+(2150843463/5000000000 : ℝ)*X 0 2+(557456613/1250000000 : ℝ)*X 1 0+(4301687051/10000000000 : ℝ)*X 1 1+(2150843463/5000000000 : ℝ)*X 1 2+(557456613/1250000000 : ℝ)*X 2 0+(4301687051/10000000000 : ℝ)*X 2 1+(2150843463/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-563230833/2500000000 : ℝ)*X 0 0+(660265251/1250000000 : ℝ)*X 0 1+(1320530301/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2681117237/5000000000 : ℝ)*X 1 0+(-2146493171/10000000000 : ℝ)*X 1 1+(5282122231/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((10724473/20000000 : ℝ)*X 2 0+(5282121203/10000000000 : ℝ)*X 2 1+(-1073245913/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4245900771/10000000000 : ℝ)*X 0 0+(4408542821/10000000000 : ℝ)*X 0 1+(2204271439/5000000000 : ℝ)*X 0 2+(4245900771/10000000000 : ℝ)*X 1 0+(4408542821/10000000000 : ℝ)*X 1 1+(2204271439/5000000000 : ℝ)*X 1 2+(4245900771/10000000000 : ℝ)*X 2 0+(4408542821/10000000000 : ℝ)*X 2 1+(2204271439/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-440120771/2000000000 : ℝ)*X 0 0+(5218743881/10000000000 : ℝ)*X 0 1+(673086549/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1322475283/2500000000 : ℝ)*X 1 0+(-2105812589/10000000000 : ℝ)*X 1 1+(2692346203/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2644950567/5000000000 : ℝ)*X 2 0+(5384692391/10000000000 : ℝ)*X 2 1+(-1052906303/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1120370757/2500000000 : ℝ)*X 0 0+(2145315707/5000000000 : ℝ)*X 0 1+(4290631397/10000000000 : ℝ)*X 0 2+(1120370757/2500000000 : ℝ)*X 1 0+(2145315707/5000000000 : ℝ)*X 1 1+(4290631397/10000000000 : ℝ)*X 1 2+(1120370757/2500000000 : ℝ)*X 2 0+(2145315707/5000000000 : ℝ)*X 2 1+(4290631397/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2055755859/10000000000 : ℝ)*X 0 0+(5437239111/10000000000 : ℝ)*X 0 1+(5274048311/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2683962553/5000000000 : ℝ)*X 1 0+(-2149633981/10000000000 : ℝ)*X 1 1+(1318512271/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((670990721/1250000000 : ℝ)*X 2 0+(5274048747/10000000000 : ℝ)*X 2 1+(-2149633541/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2113552283/5000000000 : ℝ)*X 0 0+(441781897/1000000000 : ℝ)*X 0 1+(2208908839/5000000000 : ℝ)*X 0 2+(2113552283/5000000000 : ℝ)*X 1 0+(441781897/1000000000 : ℝ)*X 1 1+(2208908839/5000000000 : ℝ)*X 1 2+(2113552283/5000000000 : ℝ)*X 2 0+(441781897/1000000000 : ℝ)*X 2 1+(2208908839/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-15561/25000 : ℝ) ≤ (-41001333111435035507336504203749/65875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1491969/25000000000000 : ℝ)*(upper0) + (193154737/50000000000000 : ℝ)*(lower1) + (215752973/20000000000000 : ℝ)*(lower2) + (21742493/6250000000000 : ℝ)*(lower3) + (1995101841783309/50000000000000 : ℝ)*(major0) + (1995101841783309/50000000000000 : ℝ)*(major1) + (1995101841783309/50000000000000 : ℝ)*(major2) + (65679829/1000000000000 : ℝ)*(sp1) + (192047313/2500000000000 : ℝ)*(sp2) + (2680297571385701/50000000000000 : ℝ)*(sp4) + (2680322227215763/50000000000000 : ℝ)*(sp5) + (2680321670260953/50000000000000 : ℝ)*(sp6) + (330062922793291/12500000000000 : ℝ)*(sp7) + (3492477689/6250000000000 : ℝ)*(sp8) + (330062922793291/12500000000000 : ℝ)*(f.failure) + (2680325511207213/50000000000000 : ℝ)*(f.sum) + (433707258089867/6587500000000000000000000000 : ℝ)*base65 + (757087157485525417/131750000000000000000000000000000 : ℝ)*base68 + (1072673870938474583/131750000000000000000000000000000 : ℝ)*base69 + (669418673482474583/131750000000000000000000000000000 : ℝ)*base71 + (43714639465823/1646875000000000000000000000 : ℝ)*base73 + (1081524916305974583/131750000000000000000000000000000 : ℝ)*base75 + (3368106760285525417/131750000000000000000000000000000 : ℝ)*base78 + (6850496366497974583/131750000000000000000000000000000 : ℝ)*base79 + (50907854930517/6587500000000000000000000000 : ℝ)*base81 + (3062577/250000000000000000000 : ℝ)*base90 + (3062577/250000000000000000000 : ℝ)*base92 + (3062577/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (11873/20000 : ℝ) ≤ (460094782653734410677581631/775000000000000000000000000 : ℝ) := by norm_num
    linear_combination (35090503/100000000000000 : ℝ)*(lower0) + (23178577/50000000000000 : ℝ)*(lower3) + (45490121/100000000000000 : ℝ)*(upper4) + (2027895494637991/50000000000000 : ℝ)*(major0) + (2027895494637991/50000000000000 : ℝ)*(major1) + (2027895494637991/50000000000000 : ℝ)*(major2) + (675981892526247/12500000000000 : ℝ)*(sp0) + (5407850201779213/100000000000000 : ℝ)*(sp1) + (5407851556343449/100000000000000 : ℝ)*(sp2) + (2683894950088717/100000000000000 : ℝ)*(sp3) + (37200525207/100000000000000 : ℝ)*(sp5) + (10603248983/100000000000000 : ℝ)*(sp7) + (35845960971/100000000000000 : ℝ)*(sp10) + (6452418889/20000000000000 : ℝ)*(sp12) + (26839055533377/1000000000000 : ℝ)*(f.failure) + (270394370115221/5000000000000 : ℝ)*(f.sum) + (66028129953/48437500000000000000000000 : ℝ)*base65 + (59985705773669499/7750000000000000000000000000000 : ℝ)*base68 + (18875822822169499/7750000000000000000000000000000 : ℝ)*base70 + (2492561064919499/7750000000000000000000000000000 : ℝ)*base72 + (4375473018899/387500000000000000000000000 : ℝ)*base73 + (19735543341080501/7750000000000000000000000000000 : ℝ)*base75 + (18788835984080501/7750000000000000000000000000000 : ℝ)*base77 + (41659988363080501/7750000000000000000000000000000 : ℝ)*base79 + (856517704177/775000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (60019/20000000000000000000 : ℝ)*base90 + (60019/20000000000000000000 : ℝ)*base92 + (60019/20000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (40031/50000 : ℝ) ≤ (105484366802422107615089123080173/131750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4118971/50000000000000 : ℝ)*(upper0) + (10086451/100000000000000 : ℝ)*(upper1) + (3443199/50000000000000 : ℝ)*(upper2) + (10314027/100000000000000 : ℝ)*(upper3) + (635623/25000000000000 : ℝ)*(upper4) + (4522800148496293/100000000000000 : ℝ)*(major0) + (4522800148496293/100000000000000 : ℝ)*(major1) + (4522800148496293/100000000000000 : ℝ)*(major2) + (1067532391/12500000000000 : ℝ)*(sp1) + (178564091/50000000000000 : ℝ)*(sp2) + (1205193009631121/20000000000000 : ℝ)*(sp8) + (6025956507896477/100000000000000 : ℝ)*(sp9) + (6025964691027423/100000000000000 : ℝ)*(sp10) + (1496473618497871/50000000000000 : ℝ)*(sp11) + (1496473618497871/50000000000000 : ℝ)*(f.failure) + (1205193009631121/20000000000000 : ℝ)*(f.sum) + (6490736916269/205859375000000000000000000 : ℝ)*base66 + (4021137858006716609/263500000000000000000000000000000 : ℝ)*base68 + (1249282951560216609/263500000000000000000000000000000 : ℝ)*base70 + (15452226245505216609/263500000000000000000000000000000 : ℝ)*base72 + (24208774753467/6587500000000000000000000000 : ℝ)*base73 + (2937105045446783391/263500000000000000000000000000000 : ℝ)*base75 + (9731819671564783391/263500000000000000000000000000000 : ℝ)*base77 + (4726781250269716609/263500000000000000000000000000000 : ℝ)*base80 + (57541486238409/13175000000000000000000000000 : ℝ)*base81 + (5620163/1000000000000000000000 : ℝ)*base89 + (5620163/1000000000000000000000 : ℝ)*base91 + (5620163/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-83311/100000 : ℝ) ≤ (-885149132217031336826199523173/1062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (61910771/25000000000000 : ℝ)*(lower0) + (101414537/25000000000000 : ℝ)*(lower2) + (22348113/5000000000000 : ℝ)*(upper3) + (574550199/100000000000000 : ℝ)*(upper5) + (2279088846804417/50000000000000 : ℝ)*(major0) + (2279088846804417/50000000000000 : ℝ)*(major1) + (2279088846804417/50000000000000 : ℝ)*(major2) + (135676989/12500000000000 : ℝ)*(sp4) + (27135801057/10000000000000 : ℝ)*(sp7) + (2335222189/100000000000000 : ℝ)*(sp8) + (6127763146931107/100000000000000 : ℝ)*(sp12) + (765970820946151/12500000000000 : ℝ)*(sp13) + (765970820946151/12500000000000 : ℝ)*(sp14) + (377010855772253/12500000000000 : ℝ)*(sp15) + (3016358204188593/100000000000000 : ℝ)*(f.failure) + (765970820946151/12500000000000 : ℝ)*(f.sum) + (42602384369/3320312500000000000000000 : ℝ)*base65 + (12829372937191891/4250000000000000000000000000000 : ℝ)*base68 + (21602211092441891/4250000000000000000000000000000 : ℝ)*base70 + (28807320909691891/4250000000000000000000000000000 : ℝ)*base72 + (275348823471/53125000000000000000000000 : ℝ)*base74 + (9618108093191891/4250000000000000000000000000000 : ℝ)*base76 + (23336712382308109/4250000000000000000000000000000 : ℝ)*base77 + (19023704136691891/4250000000000000000000000000000 : ℝ)*base80 + (1499842781809/212500000000000000000000000 : ℝ)*base82 + (11765571/2000000000000000000000 : ℝ)*base90 + (11765571/2000000000000000000000 : ℝ)*base92 + (11765571/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1226_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30223053/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (573/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15561/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(11873/20000 : ℝ) else (40031/50000 : ℝ) ≤ X j i ∧ X j i ≤ (83311/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1226_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1226_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30223053/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (573/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15561/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(11873/20000 : ℝ) else (40031/50000 : ℝ) ≤ X j i ∧ X j i ≤ (83311/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1226_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30223053/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (573/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15561/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(11873/20000 : ℝ) else (40031/50000 : ℝ) ≤ X j i ∧ X j i ≤ (83311/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1226_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
