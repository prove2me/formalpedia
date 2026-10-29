-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1409_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:48:07.321988+00:00
-- url     : https://prove2.me/submissions/fecd3cfc-38f9-47c0-8522-a2a71bebc869

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
theorem support_rectangle_w1409_s0_0 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1770192911/10000000000 : ℝ)*x 0 + (5968478219/10000000000 : ℝ)*x 1 + (15083253/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1770192911/10000000000 : ℝ)^4369 ≤ (1041881275309/10000000000000 : ℝ)^3345 := by
    have hnat : (1770192911 : ℕ)^4369*10000000000000^3345 ≤ 1041881275309^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1770192911 10000000000 1041881275309 10000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5968478219/10000000000 : ℝ)^4369 ≤ (6370288177007/12500000000000 : ℝ)^3345 := by
    have hnat : (5968478219 : ℕ)^4369*12500000000000^3345 ≤ 6370288177007^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5968478219 10000000000 6370288177007 12500000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (15083253/31250000 : ℝ)^4369 ≤ (2413680113019/6250000000000 : ℝ)^3345 := by
    have hnat : (15083253 : ℕ)^4369*6250000000000^3345 ≤ 2413680113019^3345*31250000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15083253 31250000 2413680113019 6250000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1770192911/10000000000 : ℝ), (5968478219/10000000000 : ℝ), (15083253/31250000 : ℝ)] ![(1041881275309/10000000000000 : ℝ), (6370288177007/12500000000000 : ℝ), (2413680113019/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1770192911/10000000000 : ℝ)|^4369 ≤ (1041881275309/10000000000000 : ℝ)^3345
        have hw : |(-1770192911/10000000000 : ℝ)|=(1770192911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5968478219/10000000000 : ℝ)|^4369 ≤ (6370288177007/12500000000000 : ℝ)^3345
        have hw : |(5968478219/10000000000 : ℝ)|=(5968478219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(15083253/31250000 : ℝ)|^4369 ≤ (2413680113019/6250000000000 : ℝ)^3345
        have hw : |(15083253/31250000 : ℝ)|=(15083253/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s0_1 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2747162979/5000000000 : ℝ)*x 0 + (-2416112451/10000000000 : ℝ)*x 1 + (4826641259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2747162979/5000000000 : ℝ)^4369 ≤ (45739856706219/100000000000000 : ℝ)^3345 := by
    have hnat : (2747162979 : ℕ)^4369*100000000000000^3345 ≤ 45739856706219^3345*5000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2747162979 5000000000 45739856706219 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2416112451/10000000000 : ℝ)^4369 ≤ (7820629166569/50000000000000 : ℝ)^3345 := by
    have hnat : (2416112451 : ℕ)^4369*50000000000000^3345 ≤ 7820629166569^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2416112451 10000000000 7820629166569 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4826641259/10000000000 : ℝ)^4369 ≤ (38618884933029/100000000000000 : ℝ)^3345 := by
    have hnat : (4826641259 : ℕ)^4369*100000000000000^3345 ≤ 38618884933029^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4826641259 10000000000 38618884933029 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2747162979/5000000000 : ℝ), (-2416112451/10000000000 : ℝ), (4826641259/10000000000 : ℝ)] ![(45739856706219/100000000000000 : ℝ), (7820629166569/50000000000000 : ℝ), (38618884933029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2747162979/5000000000 : ℝ)|^4369 ≤ (45739856706219/100000000000000 : ℝ)^3345
        have hw : |(2747162979/5000000000 : ℝ)|=(2747162979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2416112451/10000000000 : ℝ)|^4369 ≤ (7820629166569/50000000000000 : ℝ)^3345
        have hw : |(-2416112451/10000000000 : ℝ)|=(2416112451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4826641259/10000000000 : ℝ)|^4369 ≤ (38618884933029/100000000000000 : ℝ)^3345
        have hw : |(4826641259/10000000000 : ℝ)|=(4826641259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s0_2 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5494326183/10000000000 : ℝ)*x 0 + (965328227/2000000000 : ℝ)*x 1 + (-604028079/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5494326183/10000000000 : ℝ)^4369 ≤ (2286992957637/5000000000000 : ℝ)^3345 := by
    have hnat : (5494326183 : ℕ)^4369*5000000000000^3345 ≤ 2286992957637^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5494326183 10000000000 2286992957637 5000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (965328227/2000000000 : ℝ)^4369 ≤ (9654720909289/25000000000000 : ℝ)^3345 := by
    have hnat : (965328227 : ℕ)^4369*25000000000000^3345 ≤ 9654720909289^3345*2000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      965328227 2000000000 9654720909289 25000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (604028079/2500000000 : ℝ)^4369 ≤ (7820628595821/50000000000000 : ℝ)^3345 := by
    have hnat : (604028079 : ℕ)^4369*50000000000000^3345 ≤ 7820628595821^3345*2500000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      604028079 2500000000 7820628595821 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5494326183/10000000000 : ℝ), (965328227/2000000000 : ℝ), (-604028079/2500000000 : ℝ)] ![(2286992957637/5000000000000 : ℝ), (9654720909289/25000000000000 : ℝ), (7820628595821/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5494326183/10000000000 : ℝ)|^4369 ≤ (2286992957637/5000000000000 : ℝ)^3345
        have hw : |(5494326183/10000000000 : ℝ)|=(5494326183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(965328227/2000000000 : ℝ)|^4369 ≤ (9654720909289/25000000000000 : ℝ)^3345
        have hw : |(965328227/2000000000 : ℝ)|=(965328227/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-604028079/2500000000 : ℝ)|^4369 ≤ (7820628595821/50000000000000 : ℝ)^3345
        have hw : |(-604028079/2500000000 : ℝ)|=(604028079/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s0_3 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (521110391/1250000000 : ℝ)*x 0 + (620780899/2000000000 : ℝ)*x 1 + (5555991469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (521110391/1250000000 : ℝ)^4369 ≤ (31893112733893/100000000000000 : ℝ)^3345 := by
    have hnat : (521110391 : ℕ)^4369*100000000000000^3345 ≤ 31893112733893^3345*1250000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521110391 1250000000 31893112733893 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (620780899/2000000000 : ℝ)^4369 ≤ (1355960401933/6250000000000 : ℝ)^3345 := by
    have hnat : (620780899 : ℕ)^4369*6250000000000^3345 ≤ 1355960401933^3345*2000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      620780899 2000000000 1355960401933 6250000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5555991469/10000000000 : ℝ)^4369 ≤ (4641152083197/10000000000000 : ℝ)^3345 := by
    have hnat : (5555991469 : ℕ)^4369*10000000000000^3345 ≤ 4641152083197^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5555991469 10000000000 4641152083197 10000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(521110391/1250000000 : ℝ), (620780899/2000000000 : ℝ), (5555991469/10000000000 : ℝ)] ![(31893112733893/100000000000000 : ℝ), (1355960401933/6250000000000 : ℝ), (4641152083197/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(521110391/1250000000 : ℝ)|^4369 ≤ (31893112733893/100000000000000 : ℝ)^3345
        have hw : |(521110391/1250000000 : ℝ)|=(521110391/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(620780899/2000000000 : ℝ)|^4369 ≤ (1355960401933/6250000000000 : ℝ)^3345
        have hw : |(620780899/2000000000 : ℝ)|=(620780899/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5555991469/10000000000 : ℝ)|^4369 ≤ (4641152083197/10000000000000 : ℝ)^3345
        have hw : |(5555991469/10000000000 : ℝ)|=(5555991469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s0_4 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-887153809/5000000000 : ℝ)*x 0 + (2427949751/5000000000 : ℝ)*x 1 + (5938174811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (887153809/5000000000 : ℝ)^4369 ≤ (5225227848463/50000000000000 : ℝ)^3345 := by
    have hnat : (887153809 : ℕ)^4369*50000000000000^3345 ≤ 5225227848463^3345*5000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      887153809 5000000000 5225227848463 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2427949751/5000000000 : ℝ)^4369 ≤ (62279894427/160000000000 : ℝ)^3345 := by
    have hnat : (2427949751 : ℕ)^4369*160000000000^3345 ≤ 62279894427^3345*5000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2427949751 5000000000 62279894427 160000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5938174811/10000000000 : ℝ)^4369 ≤ (12656152569017/25000000000000 : ℝ)^3345 := by
    have hnat : (5938174811 : ℕ)^4369*25000000000000^3345 ≤ 12656152569017^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5938174811 10000000000 12656152569017 25000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-887153809/5000000000 : ℝ), (2427949751/5000000000 : ℝ), (5938174811/10000000000 : ℝ)] ![(5225227848463/50000000000000 : ℝ), (62279894427/160000000000 : ℝ), (12656152569017/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-887153809/5000000000 : ℝ)|^4369 ≤ (5225227848463/50000000000000 : ℝ)^3345
        have hw : |(-887153809/5000000000 : ℝ)|=(887153809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2427949751/5000000000 : ℝ)|^4369 ≤ (62279894427/160000000000 : ℝ)^3345
        have hw : |(2427949751/5000000000 : ℝ)|=(2427949751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5938174811/10000000000 : ℝ)|^4369 ≤ (12656152569017/25000000000000 : ℝ)^3345
        have hw : |(5938174811/10000000000 : ℝ)|=(5938174811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s0_5 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (51827681/100000000 : ℝ)*x 0 + (-326144797/2500000000 : ℝ)*x 1 + (5938174549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (51827681/100000000 : ℝ)^4369 ≤ (8476391032237/20000000000000 : ℝ)^3345 := by
    have hnat : (51827681 : ℕ)^4369*20000000000000^3345 ≤ 8476391032237^3345*100000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51827681 100000000 8476391032237 20000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (326144797/2500000000 : ℝ)^4369 ≤ (6993437468967/100000000000000 : ℝ)^3345 := by
    have hnat : (326144797 : ℕ)^4369*100000000000000^3345 ≤ 6993437468967^3345*2500000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326144797 2500000000 6993437468967 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5938174549/10000000000 : ℝ)^4369 ≤ (12656151839667/25000000000000 : ℝ)^3345 := by
    have hnat : (5938174549 : ℕ)^4369*25000000000000^3345 ≤ 12656151839667^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5938174549 10000000000 12656151839667 25000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(51827681/100000000 : ℝ), (-326144797/2500000000 : ℝ), (5938174549/10000000000 : ℝ)] ![(8476391032237/20000000000000 : ℝ), (6993437468967/100000000000000 : ℝ), (12656151839667/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(51827681/100000000 : ℝ)|^4369 ≤ (8476391032237/20000000000000 : ℝ)^3345
        have hw : |(51827681/100000000 : ℝ)|=(51827681/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-326144797/2500000000 : ℝ)|^4369 ≤ (6993437468967/100000000000000 : ℝ)^3345
        have hw : |(-326144797/2500000000 : ℝ)|=(326144797/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5938174549/10000000000 : ℝ)|^4369 ≤ (12656151839667/25000000000000 : ℝ)^3345
        have hw : |(5938174549/10000000000 : ℝ)|=(5938174549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s0_6 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2591384081/5000000000 : ℝ)*x 0 + (5938174947/10000000000 : ℝ)*x 1 + (-1304578461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2591384081/5000000000 : ℝ)^4369 ≤ (42381955823397/100000000000000 : ℝ)^3345 := by
    have hnat : (2591384081 : ℕ)^4369*100000000000000^3345 ≤ 42381955823397^3345*5000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591384081 5000000000 42381955823397 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5938174947/10000000000 : ℝ)^4369 ≤ (50624611790443/100000000000000 : ℝ)^3345 := by
    have hnat : (5938174947 : ℕ)^4369*100000000000000^3345 ≤ 50624611790443^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5938174947 10000000000 50624611790443 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304578461/10000000000 : ℝ)^4369 ≤ (69934323787/1000000000000 : ℝ)^3345 := by
    have hnat : (1304578461 : ℕ)^4369*1000000000000^3345 ≤ 69934323787^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304578461 10000000000 69934323787 1000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2591384081/5000000000 : ℝ), (5938174947/10000000000 : ℝ), (-1304578461/10000000000 : ℝ)] ![(42381955823397/100000000000000 : ℝ), (50624611790443/100000000000000 : ℝ), (69934323787/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2591384081/5000000000 : ℝ)|^4369 ≤ (42381955823397/100000000000000 : ℝ)^3345
        have hw : |(2591384081/5000000000 : ℝ)|=(2591384081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5938174947/10000000000 : ℝ)|^4369 ≤ (50624611790443/100000000000000 : ℝ)^3345
        have hw : |(5938174947/10000000000 : ℝ)|=(5938174947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1304578461/10000000000 : ℝ)|^4369 ≤ (69934323787/1000000000000 : ℝ)^3345
        have hw : |(-1304578461/10000000000 : ℝ)|=(1304578461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s0_7 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (261107579/625000000 : ℝ)*x 0 + (5493158583/10000000000 : ℝ)*x 1 + (3168981603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (261107579/625000000 : ℝ)^4369 ≤ (639629084101/2000000000000 : ℝ)^3345 := by
    have hnat : (261107579 : ℕ)^4369*2000000000000^3345 ≤ 639629084101^3345*625000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261107579 625000000 639629084101 2000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5493158583/10000000000 : ℝ)^4369 ≤ (9145432751269/20000000000000 : ℝ)^3345 := by
    have hnat : (5493158583 : ℕ)^4369*20000000000000^3345 ≤ 9145432751269^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5493158583 10000000000 9145432751269 20000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3168981603/10000000000 : ℝ)^4369 ≤ (22291382029341/100000000000000 : ℝ)^3345 := by
    have hnat : (3168981603 : ℕ)^4369*100000000000000^3345 ≤ 22291382029341^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3168981603 10000000000 22291382029341 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(261107579/625000000 : ℝ), (5493158583/10000000000 : ℝ), (3168981603/10000000000 : ℝ)] ![(639629084101/2000000000000 : ℝ), (9145432751269/20000000000000 : ℝ), (22291382029341/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(261107579/625000000 : ℝ)|^4369 ≤ (639629084101/2000000000000 : ℝ)^3345
        have hw : |(261107579/625000000 : ℝ)|=(261107579/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5493158583/10000000000 : ℝ)|^4369 ≤ (9145432751269/20000000000000 : ℝ)^3345
        have hw : |(5493158583/10000000000 : ℝ)|=(5493158583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3168981603/10000000000 : ℝ)|^4369 ≤ (22291382029341/100000000000000 : ℝ)^3345
        have hw : |(3168981603/10000000000 : ℝ)|=(3168981603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1409_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31474923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (381/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26397/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (273/64 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^273 ≤ (0 : ℝ)^64 := by
      have hnat : (0 : ℕ)^273*1^64 ≤ 0^64*1^273 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 273 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 273 64 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (273/64 : ℝ) ≤ (2006952761843481419/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^273 ≤ (2006952761843481419/100000000000000000000 : ℝ)^64 := by
      have hnat : (2 : ℕ)^273*100000000000000000000^64 ≤ 2006952761843481419^64*5^273 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2006952761843481419 100000000000000000000 273 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2006952761843481419/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 273 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (273/64 : ℝ) := by
    have hpowers : (1 : ℝ)^64 ≤ (1 : ℝ)^273 := by
      have hnat : (1 : ℕ)^64*1^273 ≤ 1^273*1^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 64 273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 273 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (102006952761843481419/100000000000000000000 : ℝ) ≤ (2009338441066133/2000000000000000 : ℝ) ^ (273/64 : ℝ) := by
    have hpowers : (102006952761843481419/100000000000000000000 : ℝ)^64 ≤ (2009338441066133/2000000000000000 : ℝ)^273 := by
      have hnat : (102006952761843481419 : ℕ)^64*2000000000000000^273 ≤ 2009338441066133^273*100000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102006952761843481419 100000000000000000000 2009338441066133 2000000000000000 64 273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2009338441066133/2000000000000000 : ℝ)) (X := (102006952761843481419/100000000000000000000 : ℝ)) (by norm_num) 273 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (52006952761843481419/50000000000000000000 : ℝ) ≤ (1009338441066133/1000000000000000 : ℝ) ^ (273/64 : ℝ) := by
    have hpowers : (52006952761843481419/50000000000000000000 : ℝ)^64 ≤ (1009338441066133/1000000000000000 : ℝ)^273 := by
      have hnat : (52006952761843481419 : ℕ)^64*1000000000000000^273 ≤ 1009338441066133^273*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52006952761843481419 50000000000000000000 1009338441066133 1000000000000000 64 273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1009338441066133/1000000000000000 : ℝ)) (X := (52006952761843481419/50000000000000000000 : ℝ)) (by norm_num) 273 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(9338441066133/800000000000000 : ℝ)*(0 : ℝ))^(273/64 : ℝ) := by
    rw [show (1 : ℝ)+2*(9338441066133/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2006952761843481419/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(9338441066133/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(273/64 : ℝ) := by
    rw [show (1 : ℝ)+(9338441066133/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2009338441066133/2000000000000000 : ℝ) by norm_num, show 1+(2006952761843481419/100000000000000000000 : ℝ)+(0 : ℝ)=(102006952761843481419/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2006952761843481419/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(9338441066133/800000000000000 : ℝ)*(2/5 : ℝ))^(273/64 : ℝ) := by
    rw [show (1 : ℝ)+2*(9338441066133/800000000000000 : ℝ)*(2/5 : ℝ)=(1009338441066133/1000000000000000 : ℝ) by norm_num, show 1+2*(2006952761843481419/100000000000000000000 : ℝ)=(52006952761843481419/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(9338441066133/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (273/64 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9338441066133/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(9338441066133/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (273/64 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9338441066133/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(9338441066133/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (273/64 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9338441066133/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1770192911/10000000000 : ℝ)*X 0 0+(5968478219/10000000000 : ℝ)*X 0 1+(15083253/31250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2747162979/5000000000 : ℝ)*X 1 0+(-2416112451/10000000000 : ℝ)*X 1 1+(4826641259/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5494326183/10000000000 : ℝ)*X 2 0+(965328227/2000000000 : ℝ)*X 2 1+(-604028079/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((521110391/1250000000 : ℝ)*X 0 0+(620780899/2000000000 : ℝ)*X 0 1+(5555991469/10000000000 : ℝ)*X 0 2+(521110391/1250000000 : ℝ)*X 1 0+(620780899/2000000000 : ℝ)*X 1 1+(5555991469/10000000000 : ℝ)*X 1 2+(521110391/1250000000 : ℝ)*X 2 0+(620780899/2000000000 : ℝ)*X 2 1+(5555991469/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-887153809/5000000000 : ℝ)*X 0 0+(2427949751/5000000000 : ℝ)*X 0 1+(5938174811/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((51827681/100000000 : ℝ)*X 1 0+(-326144797/2500000000 : ℝ)*X 1 1+(5938174549/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2591384081/5000000000 : ℝ)*X 2 0+(5938174947/10000000000 : ℝ)*X 2 1+(-1304578461/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((261107579/625000000 : ℝ)*X 0 0+(5493158583/10000000000 : ℝ)*X 0 1+(3168981603/10000000000 : ℝ)*X 0 2+(261107579/625000000 : ℝ)*X 1 0+(5493158583/10000000000 : ℝ)*X 1 1+(3168981603/10000000000 : ℝ)*X 1 2+(261107579/625000000 : ℝ)*X 2 0+(5493158583/10000000000 : ℝ)*X 2 1+(3168981603/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (791589536205357909/100000000000000000000000 : ℝ) := by norm_num
    linear_combination (803993/5000000000000 : ℝ)*(base1) + (462477687/25000000000000 : ℝ)*(base19) + (471443907/25000000000000 : ℝ)*(base23) + (3357627/1562500000000 : ℝ)*(upper3) + (13092983/5000000000000 : ℝ)*(upper5) + (128361685839757/20000000000000 : ℝ)*(major0) + (128361685839757/20000000000000 : ℝ)*(major1) + (320904214599393/50000000000000 : ℝ)*(major2) + (218946921894389/25000000000000 : ℝ)*(sp0) + (437896332021493/50000000000000 : ℝ)*(sp1) + (437896314089053/50000000000000 : ℝ)*(sp2) + (101954735847841/25000000000000 : ℝ)*(sp3) + (3421228019/50000000000000 : ℝ)*(sp4) + (195069339/6250000000000 : ℝ)*(sp7) + (407822080580649/100000000000000 : ℝ)*(f.failure) + (175158902790747/20000000000000 : ℝ)*(f.sum) + (29127575322943/80000000000000000000000000000 : ℝ)*base65 + (71313886177269/40000000000000000000000000000 : ℝ)*base67 + (159793230193681/16000000000000000000000000000 : ℝ)*base69 + (15558749982731/40000000000000000000000000000 : ℝ)*base72 + (112396677317057/80000000000000000000000000000 : ℝ)*base74 + (211242721457681/16000000000000000000000000000 : ℝ)*base75 + (10899489166319/16000000000000000000000000000 : ℝ)*base78 + (38087554737681/16000000000000000000000000000 : ℝ)*base79 + (9391897486319/8000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (22565027/2000000000000000000000 : ℝ)*base89 + (22565027/2000000000000000000000 : ℝ)*base91 + (2565027/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20619678385808634409821/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (435266551/25000000000000 : ℝ)*(base19) + (1807645471/100000000000000 : ℝ)*(base23) + (52998097/25000000000000 : ℝ)*(base32) + (67203503/25000000000000 : ℝ)*(upper3) + (159376269/100000000000000 : ℝ)*(upper5) + (84639901729593/12500000000000 : ℝ)*(major0) + (84639901729593/12500000000000 : ℝ)*(major1) + (84639901729593/12500000000000 : ℝ)*(major2) + (3726100269/100000000000000 : ℝ)*(sp1) + (4649773259/100000000000000 : ℝ)*(sp2) + (461989332024077/50000000000000 : ℝ)*(sp4) + (461986598440841/50000000000000 : ℝ)*(sp5) + (36958888265177/4000000000000 : ℝ)*(sp6) + (86051855340779/20000000000000 : ℝ)*(sp7) + (430259488696283/100000000000000 : ℝ)*(f.failure) + (461989332024077/50000000000000 : ℝ)*(f.sum) + (5254834366131/5000000000000000000000000000 : ℝ)*base66 + (18008404756131/10000000000000000000000000000 : ℝ)*base68 + (38267329616131/10000000000000000000000000000 : ℝ)*base70 + (37139905646131/10000000000000000000000000000 : ℝ)*base72 + (8833390076131/5000000000000000000000000000 : ℝ)*base74 + (81959941566131/10000000000000000000000000000 : ℝ)*base76 + (38518709096131/10000000000000000000000000000 : ℝ)*base78 + (46486456076131/10000000000000000000000000000 : ℝ)*base80 + (21155758406131/5000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (2188791/2000000000000000000000 : ℝ)*base90 + (2188791/2000000000000000000000 : ℝ)*base92 + (2188791/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1409_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31474923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (381/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26397/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1409_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1409_s1_0 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1945390737/10000000000 : ℝ)*x 0 + (1122670369/2000000000 : ℝ)*x 1 + (2534742147/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1945390737/10000000000 : ℝ)^4369 ≤ (589279786163/5000000000000 : ℝ)^3345 := by
    have hnat : (1945390737 : ℕ)^4369*5000000000000^3345 ≤ 589279786163^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1945390737 10000000000 589279786163 5000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1122670369/2000000000 : ℝ)^4369 ≤ (47038345764119/100000000000000 : ℝ)^3345 := by
    have hnat : (1122670369 : ℕ)^4369*100000000000000^3345 ≤ 47038345764119^3345*2000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122670369 2000000000 47038345764119 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2534742147/5000000000 : ℝ)^4369 ≤ (41176058495943/100000000000000 : ℝ)^3345 := by
    have hnat : (2534742147 : ℕ)^4369*100000000000000^3345 ≤ 41176058495943^3345*5000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2534742147 5000000000 41176058495943 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1945390737/10000000000 : ℝ), (1122670369/2000000000 : ℝ), (2534742147/5000000000 : ℝ)] ![(589279786163/5000000000000 : ℝ), (47038345764119/100000000000000 : ℝ), (41176058495943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1945390737/10000000000 : ℝ)|^4369 ≤ (589279786163/5000000000000 : ℝ)^3345
        have hw : |(-1945390737/10000000000 : ℝ)|=(1945390737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1122670369/2000000000 : ℝ)|^4369 ≤ (47038345764119/100000000000000 : ℝ)^3345
        have hw : |(1122670369/2000000000 : ℝ)|=(1122670369/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2534742147/5000000000 : ℝ)|^4369 ≤ (41176058495943/100000000000000 : ℝ)^3345
        have hw : |(2534742147/5000000000 : ℝ)|=(2534742147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s1_1 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5398827941/10000000000 : ℝ)*x 0 + (-111701261/500000000 : ℝ)*x 1 + (5069484801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5398827941/10000000000 : ℝ)^4369 ≤ (2794015005889/6250000000000 : ℝ)^3345 := by
    have hnat : (5398827941 : ℕ)^4369*6250000000000^3345 ≤ 2794015005889^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398827941 10000000000 2794015005889 6250000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (111701261/500000000 : ℝ)^4369 ≤ (14119696010869/100000000000000 : ℝ)^3345 := by
    have hnat : (111701261 : ℕ)^4369*100000000000000^3345 ≤ 14119696010869^3345*500000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111701261 500000000 14119696010869 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5069484801/10000000000 : ℝ)^4369 ≤ (41176063874613/100000000000000 : ℝ)^3345 := by
    have hnat : (5069484801 : ℕ)^4369*100000000000000^3345 ≤ 41176063874613^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5069484801 10000000000 41176063874613 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5398827941/10000000000 : ℝ), (-111701261/500000000 : ℝ), (5069484801/10000000000 : ℝ)] ![(2794015005889/6250000000000 : ℝ), (14119696010869/100000000000000 : ℝ), (41176063874613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5398827941/10000000000 : ℝ)|^4369 ≤ (2794015005889/6250000000000 : ℝ)^3345
        have hw : |(5398827941/10000000000 : ℝ)|=(5398827941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-111701261/500000000 : ℝ)|^4369 ≤ (14119696010869/100000000000000 : ℝ)^3345
        have hw : |(-111701261/500000000 : ℝ)|=(111701261/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5069484801/10000000000 : ℝ)|^4369 ≤ (41176063874613/100000000000000 : ℝ)^3345
        have hw : |(5069484801/10000000000 : ℝ)|=(5069484801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s1_2 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1349707101/2500000000 : ℝ)*x 0 + (5069484513/10000000000 : ℝ)*x 1 + (-446804997/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1349707101/2500000000 : ℝ)^4369 ≤ (44704245101669/100000000000000 : ℝ)^3345 := by
    have hnat : (1349707101 : ℕ)^4369*100000000000000^3345 ≤ 44704245101669^3345*2500000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349707101 2500000000 44704245101669 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5069484513/10000000000 : ℝ)^4369 ≤ (20588030409637/50000000000000 : ℝ)^3345 := by
    have hnat : (5069484513 : ℕ)^4369*50000000000000^3345 ≤ 20588030409637^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5069484513 10000000000 20588030409637 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (446804997/2000000000 : ℝ)^4369 ≤ (3529923517729/25000000000000 : ℝ)^3345 := by
    have hnat : (446804997 : ℕ)^4369*25000000000000^3345 ≤ 3529923517729^3345*2000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      446804997 2000000000 3529923517729 25000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1349707101/2500000000 : ℝ), (5069484513/10000000000 : ℝ), (-446804997/2000000000 : ℝ)] ![(44704245101669/100000000000000 : ℝ), (20588030409637/50000000000000 : ℝ), (3529923517729/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1349707101/2500000000 : ℝ)|^4369 ≤ (44704245101669/100000000000000 : ℝ)^3345
        have hw : |(1349707101/2500000000 : ℝ)|=(1349707101/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5069484513/10000000000 : ℝ)|^4369 ≤ (20588030409637/50000000000000 : ℝ)^3345
        have hw : |(5069484513/10000000000 : ℝ)|=(5069484513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-446804997/2000000000 : ℝ)|^4369 ≤ (3529923517729/25000000000000 : ℝ)^3345
        have hw : |(-446804997/2000000000 : ℝ)|=(446804997/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s1_3 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4280265979/10000000000 : ℝ)*x 0 + (3732155887/10000000000 : ℝ)*x 1 + (245005327/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4280265979/10000000000 : ℝ)^4369 ≤ (33010601244099/100000000000000 : ℝ)^3345 := by
    have hnat : (4280265979 : ℕ)^4369*100000000000000^3345 ≤ 33010601244099^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4280265979 10000000000 33010601244099 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3732155887/10000000000 : ℝ)^4369 ≤ (6900244040201/25000000000000 : ℝ)^3345 := by
    have hnat : (3732155887 : ℕ)^4369*25000000000000^3345 ≤ 6900244040201^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3732155887 10000000000 6900244040201 25000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (245005327/500000000 : ℝ)^4369 ≤ (7877684515371/20000000000000 : ℝ)^3345 := by
    have hnat : (245005327 : ℕ)^4369*20000000000000^3345 ≤ 7877684515371^3345*500000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      245005327 500000000 7877684515371 20000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4280265979/10000000000 : ℝ), (3732155887/10000000000 : ℝ), (245005327/500000000 : ℝ)] ![(33010601244099/100000000000000 : ℝ), (6900244040201/25000000000000 : ℝ), (7877684515371/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4280265979/10000000000 : ℝ)|^4369 ≤ (33010601244099/100000000000000 : ℝ)^3345
        have hw : |(4280265979/10000000000 : ℝ)|=(4280265979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3732155887/10000000000 : ℝ)|^4369 ≤ (6900244040201/25000000000000 : ℝ)^3345
        have hw : |(3732155887/10000000000 : ℝ)|=(3732155887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(245005327/500000000 : ℝ)|^4369 ≤ (7877684515371/20000000000000 : ℝ)^3345
        have hw : |(245005327/500000000 : ℝ)|=(245005327/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s1_4 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1945817013/10000000000 : ℝ)*x 0 + (2537981213/5000000000 : ℝ)*x 1 + (5606762089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1945817013/10000000000 : ℝ)^4369 ≤ (2357793775291/20000000000000 : ℝ)^3345 := by
    have hnat : (1945817013 : ℕ)^4369*20000000000000^3345 ≤ 2357793775291^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1945817013 10000000000 2357793775291 20000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2537981213/5000000000 : ℝ)^4369 ≤ (20622398622063/50000000000000 : ℝ)^3345 := by
    have hnat : (2537981213 : ℕ)^4369*50000000000000^3345 ≤ 20622398622063^3345*5000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2537981213 5000000000 20622398622063 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5606762089/10000000000 : ℝ)^4369 ≤ (46966233859509/100000000000000 : ℝ)^3345 := by
    have hnat : (5606762089 : ℕ)^4369*100000000000000^3345 ≤ 46966233859509^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5606762089 10000000000 46966233859509 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1945817013/10000000000 : ℝ), (2537981213/5000000000 : ℝ), (5606762089/10000000000 : ℝ)] ![(2357793775291/20000000000000 : ℝ), (20622398622063/50000000000000 : ℝ), (46966233859509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1945817013/10000000000 : ℝ)|^4369 ≤ (2357793775291/20000000000000 : ℝ)^3345
        have hw : |(-1945817013/10000000000 : ℝ)|=(1945817013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2537981213/5000000000 : ℝ)|^4369 ≤ (20622398622063/50000000000000 : ℝ)^3345
        have hw : |(2537981213/5000000000 : ℝ)|=(2537981213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5606762089/10000000000 : ℝ)|^4369 ≤ (46966233859509/100000000000000 : ℝ)^3345
        have hw : |(5606762089/10000000000 : ℝ)|=(5606762089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s1_5 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628471737/5000000000 : ℝ)*x 0 + (-1696748051/10000000000 : ℝ)*x 1 + (1401690483/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628471737/5000000000 : ℝ)^4369 ≤ (5396992474617/12500000000000 : ℝ)^3345 := by
    have hnat : (2628471737 : ℕ)^4369*12500000000000^3345 ≤ 5396992474617^3345*5000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628471737 5000000000 5396992474617 12500000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1696748051/10000000000 : ℝ)^4369 ≤ (985782804143/10000000000000 : ℝ)^3345 := by
    have hnat : (1696748051 : ℕ)^4369*10000000000000^3345 ≤ 985782804143^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1696748051 10000000000 985782804143 10000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1401690483/2500000000 : ℝ)^4369 ≤ (23483116070881/50000000000000 : ℝ)^3345 := by
    have hnat : (1401690483 : ℕ)^4369*50000000000000^3345 ≤ 23483116070881^3345*2500000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1401690483 2500000000 23483116070881 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628471737/5000000000 : ℝ), (-1696748051/10000000000 : ℝ), (1401690483/2500000000 : ℝ)] ![(5396992474617/12500000000000 : ℝ), (985782804143/10000000000000 : ℝ), (23483116070881/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628471737/5000000000 : ℝ)|^4369 ≤ (5396992474617/12500000000000 : ℝ)^3345
        have hw : |(2628471737/5000000000 : ℝ)|=(2628471737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1696748051/10000000000 : ℝ)|^4369 ≤ (985782804143/10000000000000 : ℝ)^3345
        have hw : |(-1696748051/10000000000 : ℝ)|=(1696748051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1401690483/2500000000 : ℝ)|^4369 ≤ (23483116070881/50000000000000 : ℝ)^3345
        have hw : |(1401690483/2500000000 : ℝ)|=(1401690483/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s1_6 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256944103/10000000000 : ℝ)*x 0 + (1401690607/2500000000 : ℝ)*x 1 + (-106046653/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256944103/10000000000 : ℝ)^4369 ≤ (4317594654447/10000000000000 : ℝ)^3345 := by
    have hnat : (5256944103 : ℕ)^4369*10000000000000^3345 ≤ 4317594654447^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256944103 10000000000 4317594654447 10000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1401690607/2500000000 : ℝ)^4369 ≤ (4696623756853/10000000000000 : ℝ)^3345 := by
    have hnat : (1401690607 : ℕ)^4369*10000000000000^3345 ≤ 4696623756853^3345*2500000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1401690607 2500000000 4696623756853 10000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (106046653/625000000 : ℝ)^4369 ≤ (4928907938619/50000000000000 : ℝ)^3345 := by
    have hnat : (106046653 : ℕ)^4369*50000000000000^3345 ≤ 4928907938619^3345*625000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106046653 625000000 4928907938619 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256944103/10000000000 : ℝ), (1401690607/2500000000 : ℝ), (-106046653/625000000 : ℝ)] ![(4317594654447/10000000000000 : ℝ), (4696623756853/10000000000000 : ℝ), (4928907938619/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256944103/10000000000 : ℝ)|^4369 ≤ (4317594654447/10000000000000 : ℝ)^3345
        have hw : |(5256944103/10000000000 : ℝ)|=(5256944103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1401690607/2500000000 : ℝ)|^4369 ≤ (4696623756853/10000000000000 : ℝ)^3345
        have hw : |(1401690607/2500000000 : ℝ)|=(1401690607/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-106046653/625000000 : ℝ)|^4369 ≤ (4928907938619/50000000000000 : ℝ)^3345
        have hw : |(-106046653/625000000 : ℝ)|=(106046653/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s1_7 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4281182893/10000000000 : ℝ)*x 0 + (2443096731/5000000000 : ℝ)*x 1 + (3746307309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4281182893/10000000000 : ℝ)^4369 ≤ (33019837829349/100000000000000 : ℝ)^3345 := by
    have hnat : (4281182893 : ℕ)^4369*100000000000000^3345 ≤ 33019837829349^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4281182893 10000000000 33019837829349 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2443096731/5000000000 : ℝ)^4369 ≤ (3924241234251/10000000000000 : ℝ)^3345 := by
    have hnat : (2443096731 : ℕ)^4369*10000000000000^3345 ≤ 3924241234251^3345*5000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2443096731 5000000000 3924241234251 10000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3746307309/10000000000 : ℝ)^4369 ≤ (27737749810019/100000000000000 : ℝ)^3345 := by
    have hnat : (3746307309 : ℕ)^4369*100000000000000^3345 ≤ 27737749810019^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3746307309 10000000000 27737749810019 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4281182893/10000000000 : ℝ), (2443096731/5000000000 : ℝ), (3746307309/10000000000 : ℝ)] ![(33019837829349/100000000000000 : ℝ), (3924241234251/10000000000000 : ℝ), (27737749810019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4281182893/10000000000 : ℝ)|^4369 ≤ (33019837829349/100000000000000 : ℝ)^3345
        have hw : |(4281182893/10000000000 : ℝ)|=(4281182893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2443096731/5000000000 : ℝ)|^4369 ≤ (3924241234251/10000000000000 : ℝ)^3345
        have hw : |(2443096731/5000000000 : ℝ)|=(2443096731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3746307309/10000000000 : ℝ)|^4369 ≤ (27737749810019/100000000000000 : ℝ)^3345
        have hw : |(3746307309/10000000000 : ℝ)|=(3746307309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1409_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31474923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26397/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (381/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (1871/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18981/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26397/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (381/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26397/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (381/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26397/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (381/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26397/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (381/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26397/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (381/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26397/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (381/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (381/20000 : ℝ) ^ (273/64 : ℝ) ≤ (4599144174621/100000000000000000000 : ℝ) := by
    have hpowers : (381/20000 : ℝ)^273 ≤ (4599144174621/100000000000000000000 : ℝ)^64 := by
      have hnat : (381 : ℕ)^273*100000000000000000000^64 ≤ 4599144174621^64*20000^273 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        381 20000 4599144174621 100000000000000000000 273 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (381/20000 : ℝ)) (X := (4599144174621/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 273 64 (by norm_num) hpowers
    exact h
  have hpowhi : (26397/100000 : ℝ) ^ (273/64 : ℝ) ≤ (340854257483236633/100000000000000000000 : ℝ) := by
    have hpowers : (26397/100000 : ℝ)^273 ≤ (340854257483236633/100000000000000000000 : ℝ)^64 := by
      have hnat : (26397 : ℕ)^273*100000000000000000000^64 ≤ 340854257483236633^64*100000^273 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26397 100000 340854257483236633 100000000000000000000 273 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26397/100000 : ℝ)) (X := (340854257483236633/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 273 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000004599144174621/50000000000000000000 : ℝ) ≤ (5000000107818761/5000000000000000 : ℝ) ^ (273/64 : ℝ) := by
    have hpowers : (50000004599144174621/50000000000000000000 : ℝ)^64 ≤ (5000000107818761/5000000000000000 : ℝ)^273 := by
      have hnat : (50000004599144174621 : ℕ)^64*5000000000000000^273 ≤ 5000000107818761^273*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000004599144174621 50000000000000000000 5000000107818761 5000000000000000 64 273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000107818761/5000000000000000 : ℝ)) (X := (50000004599144174621/50000000000000000000 : ℝ)) (by norm_num) 273 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (50170429428313705627/50000000000000000000 : ℝ) ≤ (5003990212573183/5000000000000000 : ℝ) ^ (273/64 : ℝ) := by
    have hpowers : (50170429428313705627/50000000000000000000 : ℝ)^64 ≤ (5003990212573183/5000000000000000 : ℝ)^273 := by
      have hnat : (50170429428313705627 : ℕ)^64*5000000000000000^273 ≤ 5003990212573183^273*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50170429428313705627 50000000000000000000 5003990212573183 5000000000000000 64 273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003990212573183/5000000000000000 : ℝ)) (X := (50170429428313705627/50000000000000000000 : ℝ)) (by norm_num) 273 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (50340854257483236633/50000000000000000000 : ℝ) ≤ (1001596063465521/1000000000000000 : ℝ) ^ (273/64 : ℝ) := by
    have hpowers : (50340854257483236633/50000000000000000000 : ℝ)^64 ≤ (1001596063465521/1000000000000000 : ℝ)^273 := by
      have hnat : (50340854257483236633 : ℕ)^64*1000000000000000^273 ≤ 1001596063465521^273*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50340854257483236633 50000000000000000000 1001596063465521 1000000000000000 64 273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1001596063465521/1000000000000000 : ℝ)) (X := (50340854257483236633/50000000000000000000 : ℝ)) (by norm_num) 273 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4599144174621/100000000000000000000 : ℝ) ≤ ((1275466670224820277/1275625000000000000 : ℝ)+2*(1995052377211/612300000000000 : ℝ)*(381/20000 : ℝ))^(273/64 : ℝ) := by
    rw [show (1275466670224820277/1275625000000000000 : ℝ)+2*(1995052377211/612300000000000 : ℝ)*(381/20000 : ℝ)=(5000000107818761/5000000000000000 : ℝ) by norm_num, show 1+2*(4599144174621/100000000000000000000 : ℝ)=(50000004599144174621/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(340854257483236633/100000000000000000000 : ℝ)+(4599144174621/100000000000000000000 : ℝ) ≤ ((1275466670224820277/1275625000000000000 : ℝ)+(1995052377211/612300000000000 : ℝ)*((26397/100000 : ℝ)+(381/20000 : ℝ)))^(273/64 : ℝ) := by
    rw [show (1275466670224820277/1275625000000000000 : ℝ)+(1995052377211/612300000000000 : ℝ)*((26397/100000 : ℝ)+(381/20000 : ℝ))=(5003990212573183/5000000000000000 : ℝ) by norm_num, show 1+(340854257483236633/100000000000000000000 : ℝ)+(4599144174621/100000000000000000000 : ℝ)=(50170429428313705627/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(340854257483236633/100000000000000000000 : ℝ) ≤ ((1275466670224820277/1275625000000000000 : ℝ)+2*(1995052377211/612300000000000 : ℝ)*(26397/100000 : ℝ))^(273/64 : ℝ) := by
    rw [show (1275466670224820277/1275625000000000000 : ℝ)+2*(1995052377211/612300000000000 : ℝ)*(26397/100000 : ℝ)=(1001596063465521/1000000000000000 : ℝ) by norm_num, show 1+2*(340854257483236633/100000000000000000000 : ℝ)=(50340854257483236633/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1275466670224820277/1275625000000000000 : ℝ)*(X 1 0+X 2 0)+(1995052377211/612300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (273/64 : ℝ)) (lo := (381/20000 : ℝ)) (hi := (26397/100000 : ℝ)) (c := (1275466670224820277/1275625000000000000 : ℝ)) (alpha := (1995052377211/612300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1275466670224820277/1275625000000000000 : ℝ)*(X 0 1+X 2 1)+(1995052377211/612300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (273/64 : ℝ)) (lo := (381/20000 : ℝ)) (hi := (26397/100000 : ℝ)) (c := (1275466670224820277/1275625000000000000 : ℝ)) (alpha := (1995052377211/612300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1275466670224820277/1275625000000000000 : ℝ)*(X 0 2+X 1 2)+(1995052377211/612300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (273/64 : ℝ)) (lo := (381/20000 : ℝ)) (hi := (26397/100000 : ℝ)) (c := (1275466670224820277/1275625000000000000 : ℝ)) (alpha := (1995052377211/612300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1945390737/10000000000 : ℝ)*X 0 0+(1122670369/2000000000 : ℝ)*X 0 1+(2534742147/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5398827941/10000000000 : ℝ)*X 1 0+(-111701261/500000000 : ℝ)*X 1 1+(5069484801/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1349707101/2500000000 : ℝ)*X 2 0+(5069484513/10000000000 : ℝ)*X 2 1+(-446804997/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4280265979/10000000000 : ℝ)*X 0 0+(3732155887/10000000000 : ℝ)*X 0 1+(245005327/500000000 : ℝ)*X 0 2+(4280265979/10000000000 : ℝ)*X 1 0+(3732155887/10000000000 : ℝ)*X 1 1+(245005327/500000000 : ℝ)*X 1 2+(4280265979/10000000000 : ℝ)*X 2 0+(3732155887/10000000000 : ℝ)*X 2 1+(245005327/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1945817013/10000000000 : ℝ)*X 0 0+(2537981213/5000000000 : ℝ)*X 0 1+(5606762089/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2628471737/5000000000 : ℝ)*X 1 0+(-1696748051/10000000000 : ℝ)*X 1 1+(1401690483/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5256944103/10000000000 : ℝ)*X 2 0+(1401690607/2500000000 : ℝ)*X 2 1+(-106046653/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4281182893/10000000000 : ℝ)*X 0 0+(2443096731/5000000000 : ℝ)*X 0 1+(3746307309/10000000000 : ℝ)*X 0 2+(4281182893/10000000000 : ℝ)*X 1 0+(2443096731/5000000000 : ℝ)*X 1 1+(3746307309/10000000000 : ℝ)*X 1 2+(4281182893/10000000000 : ℝ)*X 2 0+(2443096731/5000000000 : ℝ)*X 2 1+(3746307309/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5826682302363734690896387/613281250000000000000000000000 : ℝ) := by norm_num
    linear_combination (78381621/100000000000000 : ℝ)*(base1) + (362201971/20000000000000 : ℝ)*(base19) + (246087033/12500000000000 : ℝ)*(base23) + (153102721/100000000000000 : ℝ)*(upper3) + (293355039/100000000000000 : ℝ)*(upper5) + (168432686755433/12500000000000 : ℝ)*(major0) + (168432686755433/12500000000000 : ℝ)*(major1) + (168432686755433/12500000000000 : ℝ)*(major2) + (1838695250286571/100000000000000 : ℝ)*(sp0) + (1838708126172973/100000000000000 : ℝ)*(sp1) + (459676992121641/25000000000000 : ℝ)*(sp2) + (856206800851737/100000000000000 : ℝ)*(sp3) + (7382638939/50000000000000 : ℝ)*(sp4) + (2927488163/50000000000000 : ℝ)*(sp7) + (214053183552421/25000000000000 : ℝ)*(f.failure) + (459677484295707/25000000000000 : ℝ)*(f.sum) + (89328535247/956718750000000000000000000 : ℝ)*base65 + (11118309535313153/2989746093750000000000000000000 : ℝ)*base67 + (195708685834270849/23917968750000000000000000000000 : ℝ)*base69 + (157179815869458349/23917968750000000000000000000000 : ℝ)*base71 + (57416662302761/30615000000000000000000000000 : ℝ)*base74 + (178561579494724021/95671875000000000000000000000000 : ℝ)*base75 + (764178654331755271/95671875000000000000000000000000 : ℝ)*base77 + (358847614747099021/95671875000000000000000000000000 : ℝ)*base79 + (60278790698447/15307500000000000000000000000 : ℝ)*base81 + (2561417/500000000000000000000 : ℝ)*base90 + (2561417/500000000000000000000 : ℝ)*base92 + (2561417/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (55356586747365351221845899/31890625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (41401571/20000000000000 : ℝ)*(base1) + (3317433/500000000000 : ℝ)*(base19) + (505292897/50000000000000 : ℝ)*(base23) + (7974033/50000000000000 : ℝ)*(upper3) + (182201531/100000000000000 : ℝ)*(upper5) + (345154156020699/25000000000000 : ℝ)*(major0) + (345154156020699/25000000000000 : ℝ)*(major1) + (345154156020699/25000000000000 : ℝ)*(major2) + (604413189/25000000000000 : ℝ)*(sp1) + (6926083663/100000000000000 : ℝ)*(sp2) + (1883953015033123/100000000000000 : ℝ)*(sp4) + (235493715860739/12500000000000 : ℝ)*(sp5) + (1883944871355811/100000000000000 : ℝ)*(sp6) + (877280175271583/100000000000000 : ℝ)*(sp7) + (877280382279439/100000000000000 : ℝ)*(f.failure) + (470988202006317/25000000000000 : ℝ)*(f.sum) + (2138994647069/1275625000000000000000000000 : ℝ)*base65 + (234753033947557373/31890625000000000000000000000000 : ℝ)*base67 + (120404498926463623/31890625000000000000000000000000 : ℝ)*base69 + (80290964029098999/15945312500000000000000000000000 : ℝ)*base71 + (1957306777359/5102500000000000000000000000 : ℝ)*base74 + (64662137718901001/15945312500000000000000000000000 : ℝ)*base76 + (21009332546619873/31890625000000000000000000000000 : ℝ)*base77 + (11957185776669281/3986328125000000000000000000000 : ℝ)*base79 + (1848790007873/637812500000000000000000000 : ℝ)*base82 + (12991803/2000000000000000000000 : ℝ)*base90 + (12991803/2000000000000000000000 : ℝ)*base92 + (12991803/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1409_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31474923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26397/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (381/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1871/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18981/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1409_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1409_s2_0 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-396008727/2000000000 : ℝ)*x 0 + (5462758999/10000000000 : ℝ)*x 1 + (5197796289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (396008727/2000000000 : ℝ)^4369 ≤ (12060542001551/100000000000000 : ℝ)^3345 := by
    have hnat : (396008727 : ℕ)^4369*100000000000000^3345 ≤ 12060542001551^3345*2000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396008727 2000000000 12060542001551 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5462758999/10000000000 : ℝ)^4369 ≤ (2269845902303/5000000000000 : ℝ)^3345 := by
    have hnat : (5462758999 : ℕ)^4369*5000000000000^3345 ≤ 2269845902303^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462758999 10000000000 2269845902303 5000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5197796289/10000000000 : ℝ)^4369 ≤ (42542539934707/100000000000000 : ℝ)^3345 := by
    have hnat : (5197796289 : ℕ)^4369*100000000000000^3345 ≤ 42542539934707^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5197796289 10000000000 42542539934707 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-396008727/2000000000 : ℝ), (5462758999/10000000000 : ℝ), (5197796289/10000000000 : ℝ)] ![(12060542001551/100000000000000 : ℝ), (2269845902303/5000000000000 : ℝ), (42542539934707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-396008727/2000000000 : ℝ)|^4369 ≤ (12060542001551/100000000000000 : ℝ)^3345
        have hw : |(-396008727/2000000000 : ℝ)|=(396008727/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5462758999/10000000000 : ℝ)|^4369 ≤ (2269845902303/5000000000000 : ℝ)^3345
        have hw : |(5462758999/10000000000 : ℝ)|=(5462758999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5197796289/10000000000 : ℝ)|^4369 ≤ (42542539934707/100000000000000 : ℝ)^3345
        have hw : |(5197796289/10000000000 : ℝ)|=(5197796289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s2_1 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5361423049/10000000000 : ℝ)*x 0 + (-1058244543/5000000000 : ℝ)*x 1 + (1299449067/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5361423049/10000000000 : ℝ)^4369 ≤ (11075031961997/25000000000000 : ℝ)^3345 := by
    have hnat : (5361423049 : ℕ)^4369*25000000000000^3345 ≤ 11075031961997^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5361423049 10000000000 11075031961997 25000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1058244543/5000000000 : ℝ)^4369 ≤ (13157332423467/100000000000000 : ℝ)^3345 := by
    have hnat : (1058244543 : ℕ)^4369*100000000000000^3345 ≤ 13157332423467^3345*5000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058244543 5000000000 13157332423467 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1299449067/2500000000 : ℝ)^4369 ≤ (42542539710211/100000000000000 : ℝ)^3345 := by
    have hnat : (1299449067 : ℕ)^4369*100000000000000^3345 ≤ 42542539710211^3345*2500000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299449067 2500000000 42542539710211 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5361423049/10000000000 : ℝ), (-1058244543/5000000000 : ℝ), (1299449067/2500000000 : ℝ)] ![(11075031961997/25000000000000 : ℝ), (13157332423467/100000000000000 : ℝ), (42542539710211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5361423049/10000000000 : ℝ)|^4369 ≤ (11075031961997/25000000000000 : ℝ)^3345
        have hw : |(5361423049/10000000000 : ℝ)|=(5361423049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1058244543/5000000000 : ℝ)|^4369 ≤ (13157332423467/100000000000000 : ℝ)^3345
        have hw : |(-1058244543/5000000000 : ℝ)|=(1058244543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1299449067/2500000000 : ℝ)|^4369 ≤ (42542539710211/100000000000000 : ℝ)^3345
        have hw : |(1299449067/2500000000 : ℝ)|=(1299449067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s2_2 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1340355701/2500000000 : ℝ)*x 0 + (1039559309/2000000000 : ℝ)*x 1 + (-2116489047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1340355701/2500000000 : ℝ)^4369 ≤ (22150062601947/50000000000000 : ℝ)^3345 := by
    have hnat : (1340355701 : ℕ)^4369*50000000000000^3345 ≤ 22150062601947^3345*2500000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1340355701 2500000000 22150062601947 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1039559309/2000000000 : ℝ)^4369 ≤ (1701701706857/4000000000000 : ℝ)^3345 := by
    have hnat : (1039559309 : ℕ)^4369*4000000000000^3345 ≤ 1701701706857^3345*2000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039559309 2000000000 1701701706857 4000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2116489047/10000000000 : ℝ)^4369 ≤ (32893330267/250000000000 : ℝ)^3345 := by
    have hnat : (2116489047 : ℕ)^4369*250000000000^3345 ≤ 32893330267^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116489047 10000000000 32893330267 250000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1340355701/2500000000 : ℝ), (1039559309/2000000000 : ℝ), (-2116489047/10000000000 : ℝ)] ![(22150062601947/50000000000000 : ℝ), (1701701706857/4000000000000 : ℝ), (32893330267/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1340355701/2500000000 : ℝ)|^4369 ≤ (22150062601947/50000000000000 : ℝ)^3345
        have hw : |(1340355701/2500000000 : ℝ)|=(1340355701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1039559309/2000000000 : ℝ)|^4369 ≤ (1701701706857/4000000000000 : ℝ)^3345
        have hw : |(1039559309/2000000000 : ℝ)|=(1039559309/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2116489047/10000000000 : ℝ)|^4369 ≤ (32893330267/250000000000 : ℝ)^3345
        have hw : |(-2116489047/10000000000 : ℝ)|=(2116489047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s2_3 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4304676571/10000000000 : ℝ)*x 0 + (4028686183/10000000000 : ℝ)*x 1 + (4597691529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4304676571/10000000000 : ℝ)^4369 ≤ (16628354516443/50000000000000 : ℝ)^3345 := by
    have hnat : (4304676571 : ℕ)^4369*50000000000000^3345 ≤ 16628354516443^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4304676571 10000000000 16628354516443 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4028686183/10000000000 : ℝ)^4369 ≤ (30499498275751/100000000000000 : ℝ)^3345 := by
    have hnat : (4028686183 : ℕ)^4369*100000000000000^3345 ≤ 30499498275751^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4028686183 10000000000 30499498275751 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4597691529/10000000000 : ℝ)^4369 ≤ (18121896335997/50000000000000 : ℝ)^3345 := by
    have hnat : (4597691529 : ℕ)^4369*50000000000000^3345 ≤ 18121896335997^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4597691529 10000000000 18121896335997 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4304676571/10000000000 : ℝ), (4028686183/10000000000 : ℝ), (4597691529/10000000000 : ℝ)] ![(16628354516443/50000000000000 : ℝ), (30499498275751/100000000000000 : ℝ), (18121896335997/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4304676571/10000000000 : ℝ)|^4369 ≤ (16628354516443/50000000000000 : ℝ)^3345
        have hw : |(4304676571/10000000000 : ℝ)|=(4304676571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4028686183/10000000000 : ℝ)|^4369 ≤ (30499498275751/100000000000000 : ℝ)^3345
        have hw : |(4028686183/10000000000 : ℝ)|=(4028686183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4597691529/10000000000 : ℝ)|^4369 ≤ (18121896335997/50000000000000 : ℝ)^3345
        have hw : |(4597691529/10000000000 : ℝ)|=(4597691529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s2_4 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-61877899/312500000 : ℝ)*x 0 + (5199343373/10000000000 : ℝ)*x 1 + (2730599567/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (61877899/312500000 : ℝ)^4369 ≤ (6030466445037/50000000000000 : ℝ)^3345 := by
    have hnat : (61877899 : ℕ)^4369*50000000000000^3345 ≤ 6030466445037^3345*312500000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61877899 312500000 6030466445037 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5199343373/10000000000 : ℝ)^4369 ≤ (8511815897493/20000000000000 : ℝ)^3345 := by
    have hnat : (5199343373 : ℕ)^4369*20000000000000^3345 ≤ 8511815897493^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5199343373 10000000000 8511815897493 20000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2730599567/5000000000 : ℝ)^4369 ≤ (45379987604627/100000000000000 : ℝ)^3345 := by
    have hnat : (2730599567 : ℕ)^4369*100000000000000^3345 ≤ 45379987604627^3345*5000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2730599567 5000000000 45379987604627 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-61877899/312500000 : ℝ), (5199343373/10000000000 : ℝ), (2730599567/5000000000 : ℝ)] ![(6030466445037/50000000000000 : ℝ), (8511815897493/20000000000000 : ℝ), (45379987604627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-61877899/312500000 : ℝ)|^4369 ≤ (6030466445037/50000000000000 : ℝ)^3345
        have hw : |(-61877899/312500000 : ℝ)|=(61877899/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5199343373/10000000000 : ℝ)|^4369 ≤ (8511815897493/20000000000000 : ℝ)^3345
        have hw : |(5199343373/10000000000 : ℝ)|=(5199343373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2730599567/5000000000 : ℝ)|^4369 ≤ (45379987604627/100000000000000 : ℝ)^3345
        have hw : |(2730599567/5000000000 : ℝ)|=(2730599567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s2_5 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5292655889/10000000000 : ℝ)*x 0 + (-1853086839/10000000000 : ℝ)*x 1 + (2730599429/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5292655889/10000000000 : ℝ)^4369 ≤ (43559438838501/100000000000000 : ℝ)^3345 := by
    have hnat : (5292655889 : ℕ)^4369*100000000000000^3345 ≤ 43559438838501^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5292655889 10000000000 43559438838501 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1853086839/10000000000 : ℝ)^4369 ≤ (1106057654591/10000000000000 : ℝ)^3345 := by
    have hnat : (1853086839 : ℕ)^4369*10000000000000^3345 ≤ 1106057654591^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1853086839 10000000000 1106057654591 10000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2730599429/5000000000 : ℝ)^4369 ≤ (45379984609113/100000000000000 : ℝ)^3345 := by
    have hnat : (2730599429 : ℕ)^4369*100000000000000^3345 ≤ 45379984609113^3345*5000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2730599429 5000000000 45379984609113 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5292655889/10000000000 : ℝ), (-1853086839/10000000000 : ℝ), (2730599429/5000000000 : ℝ)] ![(43559438838501/100000000000000 : ℝ), (1106057654591/10000000000000 : ℝ), (45379984609113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5292655889/10000000000 : ℝ)|^4369 ≤ (43559438838501/100000000000000 : ℝ)^3345
        have hw : |(5292655889/10000000000 : ℝ)|=(5292655889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1853086839/10000000000 : ℝ)|^4369 ≤ (1106057654591/10000000000000 : ℝ)^3345
        have hw : |(-1853086839/10000000000 : ℝ)|=(1853086839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2730599429/5000000000 : ℝ)|^4369 ≤ (45379984609113/100000000000000 : ℝ)^3345
        have hw : |(2730599429/5000000000 : ℝ)|=(2730599429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s2_6 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (132316433/250000000 : ℝ)*x 0 + (2730599417/5000000000 : ℝ)*x 1 + (-926542449/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132316433/250000000 : ℝ)^4369 ≤ (21779727110629/50000000000000 : ℝ)^3345 := by
    have hnat : (132316433 : ℕ)^4369*50000000000000^3345 ≤ 21779727110629^3345*250000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132316433 250000000 21779727110629 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2730599417/5000000000 : ℝ)^4369 ≤ (45379984348633/100000000000000 : ℝ)^3345 := by
    have hnat : (2730599417 : ℕ)^4369*100000000000000^3345 ≤ 45379984348633^3345*5000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2730599417 5000000000 45379984348633 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (926542449/5000000000 : ℝ)^4369 ≤ (11060561414013/100000000000000 : ℝ)^3345 := by
    have hnat : (926542449 : ℕ)^4369*100000000000000^3345 ≤ 11060561414013^3345*5000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      926542449 5000000000 11060561414013 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132316433/250000000 : ℝ), (2730599417/5000000000 : ℝ), (-926542449/5000000000 : ℝ)] ![(21779727110629/50000000000000 : ℝ), (45379984348633/100000000000000 : ℝ), (11060561414013/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132316433/250000000 : ℝ)|^4369 ≤ (21779727110629/50000000000000 : ℝ)^3345
        have hw : |(132316433/250000000 : ℝ)|=(132316433/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2730599417/5000000000 : ℝ)|^4369 ≤ (45379984348633/100000000000000 : ℝ)^3345
        have hw : |(2730599417/5000000000 : ℝ)|=(2730599417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-926542449/5000000000 : ℝ)|^4369 ≤ (11060561414013/100000000000000 : ℝ)^3345
        have hw : |(-926542449/5000000000 : ℝ)|=(926542449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s2_7 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (215239163/500000000 : ℝ)*x 0 + (4594369619/10000000000 : ℝ)*x 1 + (2016017757/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215239163/500000000 : ℝ)^4369 ≤ (16628892806011/50000000000000 : ℝ)^3345 := by
    have hnat : (215239163 : ℕ)^4369*50000000000000^3345 ≤ 16628892806011^3345*500000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215239163 500000000 16628892806011 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4594369619/10000000000 : ℝ)^4369 ≤ (18104796594053/50000000000000 : ℝ)^3345 := by
    have hnat : (4594369619 : ℕ)^4369*50000000000000^3345 ≤ 18104796594053^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4594369619 10000000000 18104796594053 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2016017757/5000000000 : ℝ)^4369 ≤ (30532621186853/100000000000000 : ℝ)^3345 := by
    have hnat : (2016017757 : ℕ)^4369*100000000000000^3345 ≤ 30532621186853^3345*5000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016017757 5000000000 30532621186853 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215239163/500000000 : ℝ), (4594369619/10000000000 : ℝ), (2016017757/5000000000 : ℝ)] ![(16628892806011/50000000000000 : ℝ), (18104796594053/50000000000000 : ℝ), (30532621186853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215239163/500000000 : ℝ)|^4369 ≤ (16628892806011/50000000000000 : ℝ)^3345
        have hw : |(215239163/500000000 : ℝ)|=(215239163/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4594369619/10000000000 : ℝ)|^4369 ≤ (18104796594053/50000000000000 : ℝ)^3345
        have hw : |(4594369619/10000000000 : ℝ)|=(4594369619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2016017757/5000000000 : ℝ)|^4369 ≤ (30532621186853/100000000000000 : ℝ)^3345
        have hw : |(2016017757/5000000000 : ℝ)|=(2016017757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1409_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31474923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18981/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1871/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5129/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15863/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18981/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1871/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18981/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1871/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18981/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1871/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18981/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1871/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18981/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1871/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18981/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1871/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1871/25000 : ℝ) ^ (273/64 : ℝ) ≤ (393928052491619/25000000000000000000 : ℝ) := by
    have hpowers : (1871/25000 : ℝ)^273 ≤ (393928052491619/25000000000000000000 : ℝ)^64 := by
      have hnat : (1871 : ℕ)^273*25000000000000000000^64 ≤ 393928052491619^64*25000^273 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1871 25000 393928052491619 25000000000000000000 273 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1871/25000 : ℝ)) (X := (393928052491619/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 273 64 (by norm_num) hpowers
    exact h
  have hpowhi : (18981/100000 : ℝ) ^ (273/64 : ℝ) ≤ (10434938114656147/12500000000000000000 : ℝ) := by
    have hpowers : (18981/100000 : ℝ)^273 ≤ (10434938114656147/12500000000000000000 : ℝ)^64 := by
      have hnat : (18981 : ℕ)^273*12500000000000000000^64 ≤ 10434938114656147^64*100000^273 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18981 100000 10434938114656147 12500000000000000000 273 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18981/100000 : ℝ)) (X := (10434938114656147/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 273 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500393928052491619/12500000000000000000 : ℝ) ≤ (5000036939327819/5000000000000000 : ℝ) ^ (273/64 : ℝ) := by
    have hpowers : (12500393928052491619/12500000000000000000 : ℝ)^64 ≤ (5000036939327819/5000000000000000 : ℝ)^273 := by
      have hnat : (12500393928052491619 : ℕ)^64*5000000000000000^273 ≤ 5000036939327819^273*12500000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500393928052491619 12500000000000000000 5000036939327819 5000000000000000 64 273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000036939327819/5000000000000000 : ℝ)) (X := (12500393928052491619/12500000000000000000 : ℝ)) (by norm_num) 273 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (25021263804281803913/25000000000000000000 : ℝ) ≤ (10001993319593309/10000000000000000 : ℝ) ^ (273/64 : ℝ) := by
    have hpowers : (25021263804281803913/25000000000000000000 : ℝ)^64 ≤ (10001993319593309/10000000000000000 : ℝ)^273 := by
      have hnat : (25021263804281803913 : ℕ)^64*10000000000000000^273 ≤ 10001993319593309^273*25000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25021263804281803913 25000000000000000000 10001993319593309 10000000000000000 64 273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001993319593309/10000000000000000 : ℝ)) (X := (25021263804281803913/25000000000000000000 : ℝ)) (by norm_num) 273 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (6260434938114656147/6250000000000000000 : ℝ) ≤ (500195638026549/500000000000000 : ℝ) ^ (273/64 : ℝ) := by
    have hpowers : (6260434938114656147/6250000000000000000 : ℝ)^64 ≤ (500195638026549/500000000000000 : ℝ)^273 := by
      have hnat : (6260434938114656147 : ℕ)^64*500000000000000^273 ≤ 500195638026549^273*6250000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6260434938114656147 6250000000000000000 500195638026549 500000000000000 64 273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500195638026549/500000000000000 : ℝ)) (X := (6260434938114656147/6250000000000000000 : ℝ)) (by norm_num) 273 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(393928052491619/25000000000000000000 : ℝ) ≤ ((57471059595474405279/57485000000000000000 : ℝ)+2*(1919440937671/1149700000000000 : ℝ)*(1871/25000 : ℝ))^(273/64 : ℝ) := by
    rw [show (57471059595474405279/57485000000000000000 : ℝ)+2*(1919440937671/1149700000000000 : ℝ)*(1871/25000 : ℝ)=(5000036939327819/5000000000000000 : ℝ) by norm_num, show 1+2*(393928052491619/25000000000000000000 : ℝ)=(12500393928052491619/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10434938114656147/12500000000000000000 : ℝ)+(393928052491619/25000000000000000000 : ℝ) ≤ ((57471059595474405279/57485000000000000000 : ℝ)+(1919440937671/1149700000000000 : ℝ)*((18981/100000 : ℝ)+(1871/25000 : ℝ)))^(273/64 : ℝ) := by
    rw [show (57471059595474405279/57485000000000000000 : ℝ)+(1919440937671/1149700000000000 : ℝ)*((18981/100000 : ℝ)+(1871/25000 : ℝ))=(10001993319593309/10000000000000000 : ℝ) by norm_num, show 1+(10434938114656147/12500000000000000000 : ℝ)+(393928052491619/25000000000000000000 : ℝ)=(25021263804281803913/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10434938114656147/12500000000000000000 : ℝ) ≤ ((57471059595474405279/57485000000000000000 : ℝ)+2*(1919440937671/1149700000000000 : ℝ)*(18981/100000 : ℝ))^(273/64 : ℝ) := by
    rw [show (57471059595474405279/57485000000000000000 : ℝ)+2*(1919440937671/1149700000000000 : ℝ)*(18981/100000 : ℝ)=(500195638026549/500000000000000 : ℝ) by norm_num, show 1+2*(10434938114656147/12500000000000000000 : ℝ)=(6260434938114656147/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (57471059595474405279/57485000000000000000 : ℝ)*(X 1 0+X 2 0)+(1919440937671/1149700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (273/64 : ℝ)) (lo := (1871/25000 : ℝ)) (hi := (18981/100000 : ℝ)) (c := (57471059595474405279/57485000000000000000 : ℝ)) (alpha := (1919440937671/1149700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (57471059595474405279/57485000000000000000 : ℝ)*(X 0 1+X 2 1)+(1919440937671/1149700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (273/64 : ℝ)) (lo := (1871/25000 : ℝ)) (hi := (18981/100000 : ℝ)) (c := (57471059595474405279/57485000000000000000 : ℝ)) (alpha := (1919440937671/1149700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (57471059595474405279/57485000000000000000 : ℝ)*(X 0 2+X 1 2)+(1919440937671/1149700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (273/64 : ℝ)) (lo := (1871/25000 : ℝ)) (hi := (18981/100000 : ℝ)) (c := (57471059595474405279/57485000000000000000 : ℝ)) (alpha := (1919440937671/1149700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-396008727/2000000000 : ℝ)*X 0 0+(5462758999/10000000000 : ℝ)*X 0 1+(5197796289/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5361423049/10000000000 : ℝ)*X 1 0+(-1058244543/5000000000 : ℝ)*X 1 1+(1299449067/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1340355701/2500000000 : ℝ)*X 2 0+(1039559309/2000000000 : ℝ)*X 2 1+(-2116489047/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4304676571/10000000000 : ℝ)*X 0 0+(4028686183/10000000000 : ℝ)*X 0 1+(4597691529/10000000000 : ℝ)*X 0 2+(4304676571/10000000000 : ℝ)*X 1 0+(4028686183/10000000000 : ℝ)*X 1 1+(4597691529/10000000000 : ℝ)*X 1 2+(4304676571/10000000000 : ℝ)*X 2 0+(4028686183/10000000000 : ℝ)*X 2 1+(4597691529/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-61877899/312500000 : ℝ)*X 0 0+(5199343373/10000000000 : ℝ)*X 0 1+(2730599567/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5292655889/10000000000 : ℝ)*X 1 0+(-1853086839/10000000000 : ℝ)*X 1 1+(2730599429/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((132316433/250000000 : ℝ)*X 2 0+(2730599417/5000000000 : ℝ)*X 2 1+(-926542449/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((215239163/500000000 : ℝ)*X 0 0+(4594369619/10000000000 : ℝ)*X 0 1+(2016017757/5000000000 : ℝ)*X 0 2+(215239163/500000000 : ℝ)*X 1 0+(4594369619/10000000000 : ℝ)*X 1 1+(2016017757/5000000000 : ℝ)*X 1 2+(215239163/500000000 : ℝ)*X 2 0+(4594369619/10000000000 : ℝ)*X 2 1+(2016017757/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10536440861620157547958034223/1437125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (275877437/25000000000000 : ℝ)*(base19) + (753027893/100000000000000 : ℝ)*(base23) + (95441691/100000000000000 : ℝ)*(lower2) + (13627839/6250000000000 : ℝ)*(upper3) + (2336501/3125000000000 : ℝ)*(upper5) + (2765803500536379/100000000000000 : ℝ)*(major0) + (2765803500536379/100000000000000 : ℝ)*(major1) + (138290175026819/5000000000000 : ℝ)*(major2) + (943532598266763/25000000000000 : ℝ)*(sp0) + (943535207293051/25000000000000 : ℝ)*(sp1) + (3774141179654059/100000000000000 : ℝ)*(sp2) + (351491600322659/20000000000000 : ℝ)*(sp3) + (115396149/1000000000000 : ℝ)*(sp4) + (6822390487/100000000000000 : ℝ)*(sp7) + (878732412001891/50000000000000 : ℝ)*(f.failure) + (117941935396311/3125000000000 : ℝ)*(f.sum) + (373154850884639/114970000000000000000000000000 : ℝ)*base65 + (37334072239292855259/5748500000000000000000000000000000 : ℝ)*base68 + (1232098861696025001/287425000000000000000000000000000 : ℝ)*base69 + (26766679276080355259/5748500000000000000000000000000000 : ℝ)*base72 + (333778439248891/114970000000000000000000000000 : ℝ)*base74 + (2991113705850674999/287425000000000000000000000000000 : ℝ)*base76 + (7536375055803905259/5748500000000000000000000000000000 : ℝ)*base78 + (33722075000165905259/5748500000000000000000000000000000 : ℝ)*base80 + (56902298342691/57485000000000000000000000000 : ℝ)*base82 + (5079393/1000000000000000000000 : ℝ)*base89 + (5079393/1000000000000000000000 : ℝ)*base91 + (4920607/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (84939088236793017722800797/11497000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (54977677/6250000000000 : ℝ)*(base19) + (15130481/500000000000 : ℝ)*(base23) + (99571417/50000000000000 : ℝ)*(upper3) + (1527657/500000000000 : ℝ)*(lower4) + (82231021/100000000000000 : ℝ)*(upper5) + (11194404031973/400000000000 : ℝ)*(major0) + (11194404031973/400000000000 : ℝ)*(major1) + (11194404031973/400000000000 : ℝ)*(major2) + (1797780553/50000000000000 : ℝ)*(sp1) + (44899632487/100000000000000 : ℝ)*(sp2) + (1909448270256267/50000000000000 : ℝ)*(sp4) + (954723016327149/25000000000000 : ℝ)*(sp5) + (477356076847981/12500000000000 : ℝ)*(sp6) + (111144076825591/6250000000000 : ℝ)*(sp7) + (111144076825591/6250000000000 : ℝ)*(f.failure) + (1909448270256267/50000000000000 : ℝ)*(f.sum) + (10088519075253/5748500000000000000000000000 : ℝ)*base66 + (203861486488811467/22994000000000000000000000000000 : ℝ)*base67 + (212171253795775467/22994000000000000000000000000000 : ℝ)*base69 + (25756719229723467/22994000000000000000000000000000 : ℝ)*base71 + (2662184764231/5748500000000000000000000000 : ℝ)*base73 + (271298250277095467/22994000000000000000000000000000 : ℝ)*base75 + (40979968900943467/22994000000000000000000000000000 : ℝ)*base77 + (229576746714601467/22994000000000000000000000000000 : ℝ)*base79 + (51370281216623/11497000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1345507/125000000000000000000 : ℝ)*base90 + (1345507/125000000000000000000 : ℝ)*base92 + (1345507/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1409_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31474923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18981/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1871/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5129/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15863/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1409_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1409_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31474923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5129/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15863/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1409_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1409_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1409_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31474923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5129/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15863/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1409_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
