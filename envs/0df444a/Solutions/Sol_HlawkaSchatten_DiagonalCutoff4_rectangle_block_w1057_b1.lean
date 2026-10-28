-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1057_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:00:11.473549+00:00
-- url     : https://prove2.me/submissions/03098c65-8030-49e4-a5cf-53d2af4766c8

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
theorem support_rectangle_w1057_s3_0 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-110167127/500000000 : ℝ)*x 0 + (2719301419/5000000000 : ℝ)*x 1 + (1305844473/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (110167127/500000000 : ℝ)^4125 ≤ (417837269037/3125000000000 : ℝ)^3101 := by
    have hnat : (110167127 : ℕ)^4125*3125000000000^3101 ≤ 417837269037^3101*500000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110167127 500000000 417837269037 3125000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2719301419/5000000000 : ℝ)^4125 ≤ (11119391643201/25000000000000 : ℝ)^3101 := by
    have hnat : (2719301419 : ℕ)^4125*25000000000000^3101 ≤ 11119391643201^3101*5000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719301419 5000000000 11119391643201 25000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1305844473/2500000000 : ℝ)^4125 ≤ (42151640801993/100000000000000 : ℝ)^3101 := by
    have hnat : (1305844473 : ℕ)^4125*100000000000000^3101 ≤ 42151640801993^3101*2500000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305844473 2500000000 42151640801993 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-110167127/500000000 : ℝ), (2719301419/5000000000 : ℝ), (1305844473/2500000000 : ℝ)] ![(417837269037/3125000000000 : ℝ), (11119391643201/25000000000000 : ℝ), (42151640801993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-110167127/500000000 : ℝ)|^4125 ≤ (417837269037/3125000000000 : ℝ)^3101
        have hw : |(-110167127/500000000 : ℝ)|=(110167127/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2719301419/5000000000 : ℝ)|^4125 ≤ (11119391643201/25000000000000 : ℝ)^3101
        have hw : |(2719301419/5000000000 : ℝ)|=(2719301419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1305844473/2500000000 : ℝ)|^4125 ≤ (42151640801993/100000000000000 : ℝ)^3101
        have hw : |(1305844473/2500000000 : ℝ)|=(1305844473/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1057_s3_1 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677963309/5000000000 : ℝ)*x 0 + (-231358011/1000000000 : ℝ)*x 1 + (81615281/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677963309/5000000000 : ℝ)^4125 ≤ (871608485993/2000000000000 : ℝ)^3101 := by
    have hnat : (2677963309 : ℕ)^4125*2000000000000^3101 ≤ 871608485993^3101*5000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677963309 5000000000 871608485993 2000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (231358011/1000000000 : ℝ)^4125 ≤ (14267933895973/100000000000000 : ℝ)^3101 := by
    have hnat : (231358011 : ℕ)^4125*100000000000000^3101 ≤ 14267933895973^3101*1000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      231358011 1000000000 14267933895973 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81615281/156250000 : ℝ)^4125 ≤ (1686065671583/4000000000000 : ℝ)^3101 := by
    have hnat : (81615281 : ℕ)^4125*4000000000000^3101 ≤ 1686065671583^3101*156250000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81615281 156250000 1686065671583 4000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677963309/5000000000 : ℝ), (-231358011/1000000000 : ℝ), (81615281/156250000 : ℝ)] ![(871608485993/2000000000000 : ℝ), (14267933895973/100000000000000 : ℝ), (1686065671583/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677963309/5000000000 : ℝ)|^4125 ≤ (871608485993/2000000000000 : ℝ)^3101
        have hw : |(2677963309/5000000000 : ℝ)|=(2677963309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-231358011/1000000000 : ℝ)|^4125 ≤ (14267933895973/100000000000000 : ℝ)^3101
        have hw : |(-231358011/1000000000 : ℝ)|=(231358011/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(81615281/156250000 : ℝ)|^4125 ≤ (1686065671583/4000000000000 : ℝ)^3101
        have hw : |(81615281/156250000 : ℝ)|=(81615281/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1057_s3_2 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5355926619/10000000000 : ℝ)*x 0 + (5223378149/10000000000 : ℝ)*x 1 + (-578394973/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355926619/10000000000 : ℝ)^4125 ≤ (21790212155237/50000000000000 : ℝ)^3101 := by
    have hnat : (5355926619 : ℕ)^4125*50000000000000^3101 ≤ 21790212155237^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355926619 10000000000 21790212155237 50000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5223378149/10000000000 : ℝ)^4125 ≤ (42151643560781/100000000000000 : ℝ)^3101 := by
    have hnat : (5223378149 : ℕ)^4125*100000000000000^3101 ≤ 42151643560781^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5223378149 10000000000 42151643560781 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (578394973/2500000000 : ℝ)^4125 ≤ (3566983026903/25000000000000 : ℝ)^3101 := by
    have hnat : (578394973 : ℕ)^4125*25000000000000^3101 ≤ 3566983026903^3101*2500000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      578394973 2500000000 3566983026903 25000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355926619/10000000000 : ℝ), (5223378149/10000000000 : ℝ), (-578394973/2500000000 : ℝ)] ![(21790212155237/50000000000000 : ℝ), (42151643560781/100000000000000 : ℝ), (3566983026903/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355926619/10000000000 : ℝ)|^4125 ≤ (21790212155237/50000000000000 : ℝ)^3101
        have hw : |(5355926619/10000000000 : ℝ)|=(5355926619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5223378149/10000000000 : ℝ)|^4125 ≤ (42151643560781/100000000000000 : ℝ)^3101
        have hw : |(5223378149/10000000000 : ℝ)|=(5223378149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-578394973/2500000000 : ℝ)|^4125 ≤ (3566983026903/25000000000000 : ℝ)^3101
        have hw : |(-578394973/2500000000 : ℝ)|=(578394973/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1057_s3_3 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4373912521/10000000000 : ℝ)*x 0 + (4168519777/10000000000 : ℝ)*x 1 + (229478821/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4373912521/10000000000 : ℝ)^4125 ≤ (8321845311493/25000000000000 : ℝ)^3101 := by
    have hnat : (4373912521 : ℕ)^4125*25000000000000^3101 ≤ 8321845311493^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4373912521 10000000000 8321845311493 25000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4168519777/10000000000 : ℝ)^4125 ≤ (31224376552043/100000000000000 : ℝ)^3101 := by
    have hnat : (4168519777 : ℕ)^4125*100000000000000^3101 ≤ 31224376552043^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4168519777 10000000000 31224376552043 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (229478821/500000000 : ℝ)^4125 ≤ (35488242183817/100000000000000 : ℝ)^3101 := by
    have hnat : (229478821 : ℕ)^4125*100000000000000^3101 ≤ 35488242183817^3101*500000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229478821 500000000 35488242183817 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4373912521/10000000000 : ℝ), (4168519777/10000000000 : ℝ), (229478821/500000000 : ℝ)] ![(8321845311493/25000000000000 : ℝ), (31224376552043/100000000000000 : ℝ), (35488242183817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4373912521/10000000000 : ℝ)|^4125 ≤ (8321845311493/25000000000000 : ℝ)^3101
        have hw : |(4373912521/10000000000 : ℝ)|=(4373912521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4168519777/10000000000 : ℝ)|^4125 ≤ (31224376552043/100000000000000 : ℝ)^3101
        have hw : |(4168519777/10000000000 : ℝ)|=(4168519777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(229478821/500000000 : ℝ)|^4125 ≤ (35488242183817/100000000000000 : ℝ)^3101
        have hw : |(229478821/500000000 : ℝ)|=(229478821/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1057_s3_4 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-550841417/2500000000 : ℝ)*x 0 + (5224266421/10000000000 : ℝ)*x 1 + (5437708867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (550841417/2500000000 : ℝ)^4125 ≤ (13370979305673/100000000000000 : ℝ)^3101 := by
    have hnat : (550841417 : ℕ)^4125*100000000000000^3101 ≤ 13370979305673^3101*2500000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550841417 2500000000 13370979305673 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5224266421/10000000000 : ℝ)^4125 ≤ (8432235811837/20000000000000 : ℝ)^3101 := by
    have hnat : (5224266421 : ℕ)^4125*20000000000000^3101 ≤ 8432235811837^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5224266421 10000000000 8432235811837 20000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5437708867/10000000000 : ℝ)^4125 ≤ (11116960404993/25000000000000 : ℝ)^3101 := by
    have hnat : (5437708867 : ℕ)^4125*25000000000000^3101 ≤ 11116960404993^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437708867 10000000000 11116960404993 25000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-550841417/2500000000 : ℝ), (5224266421/10000000000 : ℝ), (5437708867/10000000000 : ℝ)] ![(13370979305673/100000000000000 : ℝ), (8432235811837/20000000000000 : ℝ), (11116960404993/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-550841417/2500000000 : ℝ)|^4125 ≤ (13370979305673/100000000000000 : ℝ)^3101
        have hw : |(-550841417/2500000000 : ℝ)|=(550841417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5224266421/10000000000 : ℝ)|^4125 ≤ (8432235811837/20000000000000 : ℝ)^3101
        have hw : |(5224266421/10000000000 : ℝ)|=(5224266421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5437708867/10000000000 : ℝ)|^4125 ≤ (11116960404993/25000000000000 : ℝ)^3101
        have hw : |(5437708867/10000000000 : ℝ)|=(5437708867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1057_s3_5 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (132543759/250000000 : ℝ)*x 0 + (-1049624193/5000000000 : ℝ)*x 1 + (1359427359/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132543759/250000000 : ℝ)^4125 ≤ (42995013866693/100000000000000 : ℝ)^3101 := by
    have hnat : (132543759 : ℕ)^4125*100000000000000^3101 ≤ 42995013866693^3101*250000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132543759 250000000 42995013866693 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049624193/5000000000 : ℝ)^4125 ≤ (6268569150683/50000000000000 : ℝ)^3101 := by
    have hnat : (1049624193 : ℕ)^4125*50000000000000^3101 ≤ 6268569150683^3101*5000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049624193 5000000000 6268569150683 50000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1359427359/2500000000 : ℝ)^4125 ≤ (27792404881/62500000000 : ℝ)^3101 := by
    have hnat : (1359427359 : ℕ)^4125*62500000000^3101 ≤ 27792404881^3101*2500000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359427359 2500000000 27792404881 62500000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132543759/250000000 : ℝ), (-1049624193/5000000000 : ℝ), (1359427359/2500000000 : ℝ)] ![(42995013866693/100000000000000 : ℝ), (6268569150683/50000000000000 : ℝ), (27792404881/62500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132543759/250000000 : ℝ)|^4125 ≤ (42995013866693/100000000000000 : ℝ)^3101
        have hw : |(132543759/250000000 : ℝ)|=(132543759/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1049624193/5000000000 : ℝ)|^4125 ≤ (6268569150683/50000000000000 : ℝ)^3101
        have hw : |(-1049624193/5000000000 : ℝ)|=(1049624193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1359427359/2500000000 : ℝ)|^4125 ≤ (27792404881/62500000000 : ℝ)^3101
        have hw : |(1359427359/2500000000 : ℝ)|=(1359427359/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1057_s3_6 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1325437509/2500000000 : ℝ)*x 0 + (2718854647/5000000000 : ℝ)*x 1 + (-2099249021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325437509/2500000000 : ℝ)^4125 ≤ (42995010371541/100000000000000 : ℝ)^3101 := by
    have hnat : (1325437509 : ℕ)^4125*100000000000000^3101 ≤ 42995010371541^3101*2500000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325437509 2500000000 42995010371541 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2718854647/5000000000 : ℝ)^4125 ≤ (44467846264913/100000000000000 : ℝ)^3101 := by
    have hnat : (2718854647 : ℕ)^4125*100000000000000^3101 ≤ 44467846264913^3101*5000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718854647 5000000000 44467846264913 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2099249021/10000000000 : ℝ)^4125 ≤ (1253714334601/10000000000000 : ℝ)^3101 := by
    have hnat : (2099249021 : ℕ)^4125*10000000000000^3101 ≤ 1253714334601^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2099249021 10000000000 1253714334601 10000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325437509/2500000000 : ℝ), (2718854647/5000000000 : ℝ), (-2099249021/10000000000 : ℝ)] ![(42995010371541/100000000000000 : ℝ), (44467846264913/100000000000000 : ℝ), (1253714334601/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325437509/2500000000 : ℝ)|^4125 ≤ (42995010371541/100000000000000 : ℝ)^3101
        have hw : |(1325437509/2500000000 : ℝ)|=(1325437509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2718854647/5000000000 : ℝ)|^4125 ≤ (44467846264913/100000000000000 : ℝ)^3101
        have hw : |(2718854647/5000000000 : ℝ)|=(2718854647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2099249021/10000000000 : ℝ)|^4125 ≤ (1253714334601/10000000000000 : ℝ)^3101
        have hw : |(-2099249021/10000000000 : ℝ)|=(2099249021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1057_s3_7 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2186978553/5000000000 : ℝ)*x 0 + (229391969/500000000 : ℝ)*x 1 + (4170267367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2186978553/5000000000 : ℝ)^4125 ≤ (33287832604057/100000000000000 : ℝ)^3101 := by
    have hnat : (2186978553 : ℕ)^4125*100000000000000^3101 ≤ 33287832604057^3101*5000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186978553 5000000000 33287832604057 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (229391969/500000000 : ℝ)^4125 ≤ (35470376619169/100000000000000 : ℝ)^3101 := by
    have hnat : (229391969 : ℕ)^4125*100000000000000^3101 ≤ 35470376619169^3101*500000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229391969 500000000 35470376619169 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4170267367/10000000000 : ℝ)^4125 ≤ (15620895379563/50000000000000 : ℝ)^3101 := by
    have hnat : (4170267367 : ℕ)^4125*50000000000000^3101 ≤ 15620895379563^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170267367 10000000000 15620895379563 50000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2186978553/5000000000 : ℝ), (229391969/500000000 : ℝ), (4170267367/10000000000 : ℝ)] ![(33287832604057/100000000000000 : ℝ), (35470376619169/100000000000000 : ℝ), (15620895379563/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2186978553/5000000000 : ℝ)|^4125 ≤ (33287832604057/100000000000000 : ℝ)^3101
        have hw : |(2186978553/5000000000 : ℝ)|=(2186978553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(229391969/500000000 : ℝ)|^4125 ≤ (35470376619169/100000000000000 : ℝ)^3101
        have hw : |(229391969/500000000 : ℝ)|=(229391969/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4170267367/10000000000 : ℝ)|^4125 ≤ (15620895379563/50000000000000 : ℝ)^3101
        have hw : |(4170267367/10000000000 : ℝ)|=(4170267367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1057_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36954497/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16771/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8667/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5183/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14919/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16771/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8667/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16771/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8667/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16771/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8667/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16771/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8667/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16771/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8667/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16771/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8667/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8667/100000 : ℝ) ^ (8249/2048 : ℝ) ≤ (1054250736472017/20000000000000000000 : ℝ) := by
    have hpowers : (8667/100000 : ℝ)^8249 ≤ (1054250736472017/20000000000000000000 : ℝ)^2048 := by
      have hnat : (8667 : ℕ)^8249*20000000000000000000^2048 ≤ 1054250736472017^2048*100000^8249 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8667 100000 1054250736472017 20000000000000000000 8249 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8667/100000 : ℝ)) (X := (1054250736472017/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8249 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (16771/100000 : ℝ) ^ (8249/2048 : ℝ) ≤ (15055103036073953/20000000000000000000 : ℝ) := by
    have hpowers : (16771/100000 : ℝ)^8249 ≤ (15055103036073953/20000000000000000000 : ℝ)^2048 := by
      have hnat : (16771 : ℕ)^8249*20000000000000000000^2048 ≤ 15055103036073953^2048*100000^8249 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16771 100000 15055103036073953 20000000000000000000 8249 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16771/100000 : ℝ)) (X := (15055103036073953/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8249 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001054250736472017/10000000000000000000 : ℝ) ≤ (10000261731113833/10000000000000000 : ℝ) ^ (8249/2048 : ℝ) := by
    have hpowers : (10001054250736472017/10000000000000000000 : ℝ)^2048 ≤ (10000261731113833/10000000000000000 : ℝ)^8249 := by
      have hnat : (10001054250736472017 : ℕ)^2048*10000000000000000^8249 ≤ 10000261731113833^8249*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001054250736472017 10000000000000000000 10000261731113833 10000000000000000 2048 8249 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000261731113833/10000000000000000 : ℝ)) (X := (10001054250736472017/10000000000000000000 : ℝ)) (by norm_num) 8249 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (2001610935377254597/2000000000000000000 : ℝ) ≤ (5000999574888929/5000000000000000 : ℝ) ^ (8249/2048 : ℝ) := by
    have hpowers : (2001610935377254597/2000000000000000000 : ℝ)^2048 ≤ (5000999574888929/5000000000000000 : ℝ)^8249 := by
      have hnat : (2001610935377254597 : ℕ)^2048*5000000000000000^8249 ≤ 5000999574888929^8249*2000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001610935377254597 2000000000000000000 5000999574888929 5000000000000000 2048 8249 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000999574888929/5000000000000000 : ℝ)) (X := (2001610935377254597/2000000000000000000 : ℝ)) (by norm_num) 8249 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10015055103036073953/10000000000000000000 : ℝ) ≤ (10003736568441883/10000000000000000 : ℝ) ^ (8249/2048 : ℝ) := by
    have hpowers : (10015055103036073953/10000000000000000000 : ℝ)^2048 ≤ (10003736568441883/10000000000000000 : ℝ)^8249 := by
      have hnat : (10015055103036073953 : ℕ)^2048*10000000000000000^8249 ≤ 10003736568441883^8249*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10015055103036073953 10000000000000000000 10003736568441883 10000000000000000 2048 8249 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003736568441883/10000000000000000 : ℝ)) (X := (10015055103036073953/10000000000000000000 : ℝ)) (by norm_num) 8249 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1054250736472017/20000000000000000000 : ℝ) ≤ ((40506002326912146641/40520000000000000000 : ℝ)+2*(69496746561/32416000000000 : ℝ)*(8667/100000 : ℝ))^(8249/2048 : ℝ) := by
    rw [show (40506002326912146641/40520000000000000000 : ℝ)+2*(69496746561/32416000000000 : ℝ)*(8667/100000 : ℝ)=(10000261731113833/10000000000000000 : ℝ) by norm_num, show 1+2*(1054250736472017/20000000000000000000 : ℝ)=(10001054250736472017/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15055103036073953/20000000000000000000 : ℝ)+(1054250736472017/20000000000000000000 : ℝ) ≤ ((40506002326912146641/40520000000000000000 : ℝ)+(69496746561/32416000000000 : ℝ)*((16771/100000 : ℝ)+(8667/100000 : ℝ)))^(8249/2048 : ℝ) := by
    rw [show (40506002326912146641/40520000000000000000 : ℝ)+(69496746561/32416000000000 : ℝ)*((16771/100000 : ℝ)+(8667/100000 : ℝ))=(5000999574888929/5000000000000000 : ℝ) by norm_num, show 1+(15055103036073953/20000000000000000000 : ℝ)+(1054250736472017/20000000000000000000 : ℝ)=(2001610935377254597/2000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15055103036073953/20000000000000000000 : ℝ) ≤ ((40506002326912146641/40520000000000000000 : ℝ)+2*(69496746561/32416000000000 : ℝ)*(16771/100000 : ℝ))^(8249/2048 : ℝ) := by
    rw [show (40506002326912146641/40520000000000000000 : ℝ)+2*(69496746561/32416000000000 : ℝ)*(16771/100000 : ℝ)=(10003736568441883/10000000000000000 : ℝ) by norm_num, show 1+2*(15055103036073953/20000000000000000000 : ℝ)=(10015055103036073953/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (40506002326912146641/40520000000000000000 : ℝ)*(X 1 0+X 2 0)+(69496746561/32416000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8249/2048 : ℝ)) (lo := (8667/100000 : ℝ)) (hi := (16771/100000 : ℝ)) (c := (40506002326912146641/40520000000000000000 : ℝ)) (alpha := (69496746561/32416000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (40506002326912146641/40520000000000000000 : ℝ)*(X 0 1+X 2 1)+(69496746561/32416000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8249/2048 : ℝ)) (lo := (8667/100000 : ℝ)) (hi := (16771/100000 : ℝ)) (c := (40506002326912146641/40520000000000000000 : ℝ)) (alpha := (69496746561/32416000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (40506002326912146641/40520000000000000000 : ℝ)*(X 0 2+X 1 2)+(69496746561/32416000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8249/2048 : ℝ)) (lo := (8667/100000 : ℝ)) (hi := (16771/100000 : ℝ)) (c := (40506002326912146641/40520000000000000000 : ℝ)) (alpha := (69496746561/32416000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-110167127/500000000 : ℝ)*X 0 0+(2719301419/5000000000 : ℝ)*X 0 1+(1305844473/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677963309/5000000000 : ℝ)*X 1 0+(-231358011/1000000000 : ℝ)*X 1 1+(81615281/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5355926619/10000000000 : ℝ)*X 2 0+(5223378149/10000000000 : ℝ)*X 2 1+(-578394973/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4373912521/10000000000 : ℝ)*X 0 0+(4168519777/10000000000 : ℝ)*X 0 1+(229478821/500000000 : ℝ)*X 0 2+(4373912521/10000000000 : ℝ)*X 1 0+(4168519777/10000000000 : ℝ)*X 1 1+(229478821/500000000 : ℝ)*X 1 2+(4373912521/10000000000 : ℝ)*X 2 0+(4168519777/10000000000 : ℝ)*X 2 1+(229478821/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-550841417/2500000000 : ℝ)*X 0 0+(5224266421/10000000000 : ℝ)*X 0 1+(5437708867/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((132543759/250000000 : ℝ)*X 1 0+(-1049624193/5000000000 : ℝ)*X 1 1+(1359427359/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1325437509/2500000000 : ℝ)*X 2 0+(2718854647/5000000000 : ℝ)*X 2 1+(-2099249021/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2186978553/5000000000 : ℝ)*X 0 0+(229391969/500000000 : ℝ)*X 0 1+(4170267367/10000000000 : ℝ)*X 0 2+(2186978553/5000000000 : ℝ)*X 1 0+(229391969/500000000 : ℝ)*X 1 1+(4170267367/10000000000 : ℝ)*X 1 2+(2186978553/5000000000 : ℝ)*X 2 0+(229391969/500000000 : ℝ)*X 2 1+(4170267367/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1509827095446087055061918553/506500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (440986477/50000000000000 : ℝ)*(base19) + (680316019/100000000000000 : ℝ)*(base23) + (108470609/100000000000000 : ℝ)*(lower2) + (1489109/4000000000000 : ℝ)*(upper3) + (90546899/100000000000000 : ℝ)*(upper5) + (1755332369957189/50000000000000 : ℝ)*(major0) + (1755332369957189/50000000000000 : ℝ)*(major1) + (1755332369957189/50000000000000 : ℝ)*(major2) + (4646317906654949/100000000000000 : ℝ)*(sp0) + (145198029311977/3125000000000 : ℝ)*(sp1) + (4646337139640199/100000000000000 : ℝ)*(sp2) + (1187492210866883/50000000000000 : ℝ)*(sp3) + (19913301269/100000000000000 : ℝ)*(sp4) + (7138775349/100000000000000 : ℝ)*(sp7) + (593747890127279/25000000000000 : ℝ)*(f.failure) + (2323168909978109/50000000000000 : ℝ)*(f.sum) + (24488704324889/4052000000000000000000000000 : ℝ)*base65 + (7386637078408402149/2026000000000000000000000000000000 : ℝ)*base67 + (4223165925337597851/2026000000000000000000000000000000 : ℝ)*base70 + (6821954574514402149/2026000000000000000000000000000000 : ℝ)*base71 + (18133329389521/4052000000000000000000000000 : ℝ)*base73 + (31079033063492402149/2026000000000000000000000000000000 : ℝ)*base75 + (20982811179760402149/2026000000000000000000000000000000 : ℝ)*base77 + (4211736766768402149/2026000000000000000000000000000000 : ℝ)*base79 + (828103354039/810400000000000000000000000 : ℝ)*base82 + (1076337/625000000000000000000 : ℝ)*base90 + (1076337/625000000000000000000 : ℝ)*base92 + (1076337/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4000763818960714710457842087/1013000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1274021001/100000000000000 : ℝ)*(base19) + (194827107/20000000000000 : ℝ)*(base23) + (842997/2000000000000 : ℝ)*(upper2) + (216786819/100000000000000 : ℝ)*(upper3) + (1769973998545377/50000000000000 : ℝ)*(major0) + (1769973998545377/50000000000000 : ℝ)*(major1) + (1769973998545377/50000000000000 : ℝ)*(major2) + (2944226899/10000000000000 : ℝ)*(sp1) + (10166991423/50000000000000 : ℝ)*(sp2) + (414480431/20000000000000 : ℝ)*(sp3) + (234254697723339/5000000000000 : ℝ)*(sp4) + (4685063238176789/100000000000000 : ℝ)*(sp5) + (11712681615871/250000000000 : ℝ)*(sp6) + (1197399917832593/50000000000000 : ℝ)*(sp7) + (1197400954033671/50000000000000 : ℝ)*(f.failure) + (234254697723339/5000000000000 : ℝ)*(f.sum) + (21336260226073/4052000000000000000000000000 : ℝ)*base65 + (1924988613767878657/2026000000000000000000000000000000 : ℝ)*base67 + (15809024536465878657/2026000000000000000000000000000000 : ℝ)*base69 + (23096838870031878657/2026000000000000000000000000000000 : ℝ)*base71 + (9702331130113/4052000000000000000000000000 : ℝ)*base73 + (18867354796961878657/2026000000000000000000000000000000 : ℝ)*base75 + (12018771736467878657/2026000000000000000000000000000000 : ℝ)*base77 + (5844757116643878657/2026000000000000000000000000000000 : ℝ)*base79 + (1175886542533/162080000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (7868487/1250000000000000000000 : ℝ)*base89 + (7868487/1250000000000000000000 : ℝ)*base91 + (7868487/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1057_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36954497/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16771/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8667/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5183/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14919/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1057_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1057_s4_0 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2207110077/10000000000 : ℝ)*x 0 + (5406317707/10000000000 : ℝ)*x 1 + (1313300559/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2207110077/10000000000 : ℝ)^4125 ≤ (13401213882813/100000000000000 : ℝ)^3101 := by
    have hnat : (2207110077 : ℕ)^4125*100000000000000^3101 ≤ 13401213882813^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2207110077 10000000000 13401213882813 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406317707/10000000000 : ℝ)^4125 ≤ (44126691938201/100000000000000 : ℝ)^3101 := by
    have hnat : (5406317707 : ℕ)^4125*100000000000000^3101 ≤ 44126691938201^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406317707 10000000000 44126691938201 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313300559/2500000000 : ℝ)^4125 ≤ (42472094165559/100000000000000 : ℝ)^3101 := by
    have hnat : (1313300559 : ℕ)^4125*100000000000000^3101 ≤ 42472094165559^3101*2500000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313300559 2500000000 42472094165559 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2207110077/10000000000 : ℝ), (5406317707/10000000000 : ℝ), (1313300559/2500000000 : ℝ)] ![(13401213882813/100000000000000 : ℝ), (44126691938201/100000000000000 : ℝ), (42472094165559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2207110077/10000000000 : ℝ)|^4125 ≤ (13401213882813/100000000000000 : ℝ)^3101
        have hw : |(-2207110077/10000000000 : ℝ)|=(2207110077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406317707/10000000000 : ℝ)|^4125 ≤ (44126691938201/100000000000000 : ℝ)^3101
        have hw : |(5406317707/10000000000 : ℝ)|=(5406317707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1313300559/2500000000 : ℝ)|^4125 ≤ (42472094165559/100000000000000 : ℝ)^3101
        have hw : |(1313300559/2500000000 : ℝ)|=(1313300559/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1057_s4_1 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347937189/10000000000 : ℝ)*x 0 + (-2284997511/10000000000 : ℝ)*x 1 + (1313300551/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347937189/10000000000 : ℝ)^4125 ≤ (21746984884979/50000000000000 : ℝ)^3101 := by
    have hnat : (5347937189 : ℕ)^4125*50000000000000^3101 ≤ 21746984884979^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347937189 10000000000 21746984884979 50000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2284997511/10000000000 : ℝ)^4125 ≤ (112271491181/800000000000 : ℝ)^3101 := by
    have hnat : (2284997511 : ℕ)^4125*800000000000^3101 ≤ 112271491181^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2284997511 10000000000 112271491181 800000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313300551/2500000000 : ℝ)^4125 ≤ (21236046910703/50000000000000 : ℝ)^3101 := by
    have hnat : (1313300551 : ℕ)^4125*50000000000000^3101 ≤ 21236046910703^3101*2500000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313300551 2500000000 21236046910703 50000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347937189/10000000000 : ℝ), (-2284997511/10000000000 : ℝ), (1313300551/2500000000 : ℝ)] ![(21746984884979/50000000000000 : ℝ), (112271491181/800000000000 : ℝ), (21236046910703/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347937189/10000000000 : ℝ)|^4125 ≤ (21746984884979/50000000000000 : ℝ)^3101
        have hw : |(5347937189/10000000000 : ℝ)|=(5347937189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2284997511/10000000000 : ℝ)|^4125 ≤ (112271491181/800000000000 : ℝ)^3101
        have hw : |(-2284997511/10000000000 : ℝ)|=(2284997511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1313300551/2500000000 : ℝ)|^4125 ≤ (21236046910703/50000000000000 : ℝ)^3101
        have hw : |(1313300551/2500000000 : ℝ)|=(1313300551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1057_s4_2 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336984317/2500000000 : ℝ)*x 0 + (5253202179/10000000000 : ℝ)*x 1 + (-1142498719/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336984317/2500000000 : ℝ)^4125 ≤ (8698794124923/20000000000000 : ℝ)^3101 := by
    have hnat : (1336984317 : ℕ)^4125*20000000000000^3101 ≤ 8698794124923^3101*2500000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336984317 2500000000 8698794124923 20000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5253202179/10000000000 : ℝ)^4125 ≤ (5309011694067/12500000000000 : ℝ)^3101 := by
    have hnat : (5253202179 : ℕ)^4125*12500000000000^3101 ≤ 5309011694067^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253202179 10000000000 5309011694067 12500000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1142498719/5000000000 : ℝ)^4125 ≤ (1754241975153/12500000000000 : ℝ)^3101 := by
    have hnat : (1142498719 : ℕ)^4125*12500000000000^3101 ≤ 1754241975153^3101*5000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1142498719 5000000000 1754241975153 12500000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336984317/2500000000 : ℝ), (5253202179/10000000000 : ℝ), (-1142498719/5000000000 : ℝ)] ![(8698794124923/20000000000000 : ℝ), (5309011694067/12500000000000 : ℝ), (1754241975153/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336984317/2500000000 : ℝ)|^4125 ≤ (8698794124923/20000000000000 : ℝ)^3101
        have hw : |(1336984317/2500000000 : ℝ)|=(1336984317/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5253202179/10000000000 : ℝ)|^4125 ≤ (5309011694067/12500000000000 : ℝ)^3101
        have hw : |(5253202179/10000000000 : ℝ)|=(5253202179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1142498719/5000000000 : ℝ)|^4125 ≤ (1754241975153/12500000000000 : ℝ)^3101
        have hw : |(-1142498719/5000000000 : ℝ)|=(1142498719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1057_s4_3 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2188076399/5000000000 : ℝ)*x 0 + (4228979349/10000000000 : ℝ)*x 1 + (4528528371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2188076399/5000000000 : ℝ)^4125 ≤ (16655031331017/50000000000000 : ℝ)^3101 := by
    have hnat : (2188076399 : ℕ)^4125*50000000000000^3101 ≤ 16655031331017^3101*5000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188076399 5000000000 16655031331017 50000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4228979349/10000000000 : ℝ)^4125 ≤ (15914117111361/50000000000000 : ℝ)^3101 := by
    have hnat : (4228979349 : ℕ)^4125*50000000000000^3101 ≤ 15914117111361^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4228979349 10000000000 15914117111361 50000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4528528371/10000000000 : ℝ)^4125 ≤ (3486170310049/10000000000000 : ℝ)^3101 := by
    have hnat : (4528528371 : ℕ)^4125*10000000000000^3101 ≤ 3486170310049^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4528528371 10000000000 3486170310049 10000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2188076399/5000000000 : ℝ), (4228979349/10000000000 : ℝ), (4528528371/10000000000 : ℝ)] ![(16655031331017/50000000000000 : ℝ), (15914117111361/50000000000000 : ℝ), (3486170310049/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2188076399/5000000000 : ℝ)|^4125 ≤ (16655031331017/50000000000000 : ℝ)^3101
        have hw : |(2188076399/5000000000 : ℝ)|=(2188076399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4228979349/10000000000 : ℝ)|^4125 ≤ (15914117111361/50000000000000 : ℝ)^3101
        have hw : |(4228979349/10000000000 : ℝ)|=(4228979349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4528528371/10000000000 : ℝ)|^4125 ≤ (3486170310049/10000000000000 : ℝ)^3101
        have hw : |(4528528371/10000000000 : ℝ)|=(4528528371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1057_s4_4 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2207118237/10000000000 : ℝ)*x 0 + (1050730563/2000000000 : ℝ)*x 1 + (54058653/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2207118237/10000000000 : ℝ)^4125 ≤ (13401279789997/100000000000000 : ℝ)^3101 := by
    have hnat : (2207118237 : ℕ)^4125*100000000000000^3101 ≤ 13401279789997^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2207118237 10000000000 13401279789997 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1050730563/2000000000 : ℝ)^4125 ≤ (849538802291/2000000000000 : ℝ)^3101 := by
    have hnat : (1050730563 : ℕ)^4125*2000000000000^3101 ≤ 849538802291^3101*2000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050730563 2000000000 849538802291 2000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54058653/100000000 : ℝ)^4125 ≤ (44121780085787/100000000000000 : ℝ)^3101 := by
    have hnat : (54058653 : ℕ)^4125*100000000000000^3101 ≤ 44121780085787^3101*100000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54058653 100000000 44121780085787 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2207118237/10000000000 : ℝ), (1050730563/2000000000 : ℝ), (54058653/100000000 : ℝ)] ![(13401279789997/100000000000000 : ℝ), (849538802291/2000000000000 : ℝ), (44121780085787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2207118237/10000000000 : ℝ)|^4125 ≤ (13401279789997/100000000000000 : ℝ)^3101
        have hw : |(-2207118237/10000000000 : ℝ)|=(2207118237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1050730563/2000000000 : ℝ)|^4125 ≤ (849538802291/2000000000000 : ℝ)^3101
        have hw : |(1050730563/2000000000 : ℝ)|=(1050730563/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(54058653/100000000 : ℝ)|^4125 ≤ (44121780085787/100000000000000 : ℝ)^3101
        have hw : |(54058653/100000000 : ℝ)|=(54058653/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1057_s4_5 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (33183753/62500000 : ℝ)*x 0 + (-426466707/2000000000 : ℝ)*x 1 + (5405865463/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33183753/62500000 : ℝ)^4125 ≤ (10769389807071/25000000000000 : ℝ)^3101 := by
    have hnat : (33183753 : ℕ)^4125*25000000000000^3101 ≤ 10769389807071^3101*62500000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33183753 62500000 10769389807071 25000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (426466707/2000000000 : ℝ)^4125 ≤ (12800658903903/100000000000000 : ℝ)^3101 := by
    have hnat : (426466707 : ℕ)^4125*100000000000000^3101 ≤ 12800658903903^3101*2000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426466707 2000000000 12800658903903 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5405865463/10000000000 : ℝ)^4125 ≤ (44121781855479/100000000000000 : ℝ)^3101 := by
    have hnat : (5405865463 : ℕ)^4125*100000000000000^3101 ≤ 44121781855479^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405865463 10000000000 44121781855479 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33183753/62500000 : ℝ), (-426466707/2000000000 : ℝ), (5405865463/10000000000 : ℝ)] ![(10769389807071/25000000000000 : ℝ), (12800658903903/100000000000000 : ℝ), (44121781855479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33183753/62500000 : ℝ)|^4125 ≤ (10769389807071/25000000000000 : ℝ)^3101
        have hw : |(33183753/62500000 : ℝ)|=(33183753/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-426466707/2000000000 : ℝ)|^4125 ≤ (12800658903903/100000000000000 : ℝ)^3101
        have hw : |(-426466707/2000000000 : ℝ)|=(426466707/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5405865463/10000000000 : ℝ)|^4125 ≤ (44121781855479/100000000000000 : ℝ)^3101
        have hw : |(5405865463/10000000000 : ℝ)|=(5405865463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1057_s4_6 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061879977/2000000000 : ℝ)*x 0 + (1081173123/2000000000 : ℝ)*x 1 + (-2132334133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061879977/2000000000 : ℝ)^4125 ≤ (21538776403331/50000000000000 : ℝ)^3101 := by
    have hnat : (1061879977 : ℕ)^4125*50000000000000^3101 ≤ 21538776403331^3101*2000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061879977 2000000000 21538776403331 50000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081173123/2000000000 : ℝ)^4125 ≤ (2757611469109/6250000000000 : ℝ)^3101 := by
    have hnat : (1081173123 : ℕ)^4125*6250000000000^3101 ≤ 2757611469109^3101*2000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081173123 2000000000 2757611469109 6250000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2132334133/10000000000 : ℝ)^4125 ≤ (6400331839601/50000000000000 : ℝ)^3101 := by
    have hnat : (2132334133 : ℕ)^4125*50000000000000^3101 ≤ 6400331839601^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132334133 10000000000 6400331839601 50000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061879977/2000000000 : ℝ), (1081173123/2000000000 : ℝ), (-2132334133/10000000000 : ℝ)] ![(21538776403331/50000000000000 : ℝ), (2757611469109/6250000000000 : ℝ), (6400331839601/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061879977/2000000000 : ℝ)|^4125 ≤ (21538776403331/50000000000000 : ℝ)^3101
        have hw : |(1061879977/2000000000 : ℝ)|=(1061879977/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081173123/2000000000 : ℝ)|^4125 ≤ (2757611469109/6250000000000 : ℝ)^3101
        have hw : |(1081173123/2000000000 : ℝ)|=(1081173123/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2132334133/10000000000 : ℝ)|^4125 ≤ (6400331839601/50000000000000 : ℝ)^3101
        have hw : |(-2132334133/10000000000 : ℝ)|=(2132334133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1057_s4_7 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2188084451/5000000000 : ℝ)*x 0 + (2263823417/5000000000 : ℝ)*x 1 + (264366543/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2188084451/5000000000 : ℝ)^4125 ≤ (6662045143787/20000000000000 : ℝ)^3101 := by
    have hnat : (2188084451 : ℕ)^4125*20000000000000^3101 ≤ 6662045143787^3101*5000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188084451 5000000000 6662045143787 20000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2263823417/5000000000 : ℝ)^4125 ≤ (3485267616623/10000000000000 : ℝ)^3101 := by
    have hnat : (2263823417 : ℕ)^4125*10000000000000^3101 ≤ 3485267616623^3101*5000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2263823417 5000000000 3485267616623 10000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (264366543/625000000 : ℝ)^4125 ≤ (7959274525201/25000000000000 : ℝ)^3101 := by
    have hnat : (264366543 : ℕ)^4125*25000000000000^3101 ≤ 7959274525201^3101*625000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264366543 625000000 7959274525201 25000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2188084451/5000000000 : ℝ), (2263823417/5000000000 : ℝ), (264366543/625000000 : ℝ)] ![(6662045143787/20000000000000 : ℝ), (3485267616623/10000000000000 : ℝ), (7959274525201/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2188084451/5000000000 : ℝ)|^4125 ≤ (6662045143787/20000000000000 : ℝ)^3101
        have hw : |(2188084451/5000000000 : ℝ)|=(2188084451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2263823417/5000000000 : ℝ)|^4125 ≤ (3485267616623/10000000000000 : ℝ)^3101
        have hw : |(2263823417/5000000000 : ℝ)|=(2263823417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(264366543/625000000 : ℝ)|^4125 ≤ (7959274525201/25000000000000 : ℝ)^3101
        have hw : |(264366543/625000000 : ℝ)|=(264366543/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1057_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36954497/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14919/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5183/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11003/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2849/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14919/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5183/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14919/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5183/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14919/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5183/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14919/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5183/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14919/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5183/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14919/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5183/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5183/50000 : ℝ) ^ (8249/2048 : ℝ) ≤ (2710112298049501/25000000000000000000 : ℝ) := by
    have hpowers : (5183/50000 : ℝ)^8249 ≤ (2710112298049501/25000000000000000000 : ℝ)^2048 := by
      have hnat : (5183 : ℕ)^8249*25000000000000000000^2048 ≤ 2710112298049501^2048*50000^8249 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5183 50000 2710112298049501 25000000000000000000 8249 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5183/50000 : ℝ)) (X := (2710112298049501/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8249 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14919/100000 : ℝ) ^ (8249/2048 : ℝ) ≤ (11746334454135323/25000000000000000000 : ℝ) := by
    have hpowers : (14919/100000 : ℝ)^8249 ≤ (11746334454135323/25000000000000000000 : ℝ)^2048 := by
      have hnat : (14919 : ℕ)^8249*25000000000000000000^2048 ≤ 11746334454135323^2048*100000^8249 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14919 100000 11746334454135323 25000000000000000000 8249 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14919/100000 : ℝ)) (X := (11746334454135323/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8249 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502710112298049501/12500000000000000000 : ℝ) ≤ (10000538233264189/10000000000000000 : ℝ) ^ (8249/2048 : ℝ) := by
    have hpowers : (12502710112298049501/12500000000000000000 : ℝ)^2048 ≤ (10000538233264189/10000000000000000 : ℝ)^8249 := by
      have hnat : (12502710112298049501 : ℕ)^2048*10000000000000000^8249 ≤ 10000538233264189^8249*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502710112298049501 12500000000000000000 10000538233264189 10000000000000000 2048 8249 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000538233264189/10000000000000000 : ℝ)) (X := (12502710112298049501/12500000000000000000 : ℝ)) (by norm_num) 8249 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (3126807055844023103/3125000000000000000 : ℝ) ≤ (2500358835861259/2500000000000000 : ℝ) ^ (8249/2048 : ℝ) := by
    have hpowers : (3126807055844023103/3125000000000000000 : ℝ)^2048 ≤ (2500358835861259/2500000000000000 : ℝ)^8249 := by
      have hnat : (3126807055844023103 : ℕ)^2048*2500000000000000^8249 ≤ 2500358835861259^8249*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126807055844023103 3125000000000000000 2500358835861259 2500000000000000 2048 8249 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500358835861259/2500000000000000 : ℝ)) (X := (3126807055844023103/3125000000000000000 : ℝ)) (by norm_num) 8249 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12511746334454135323/12500000000000000000 : ℝ) ≤ (10002332453625883/10000000000000000 : ℝ) ^ (8249/2048 : ℝ) := by
    have hpowers : (12511746334454135323/12500000000000000000 : ℝ)^2048 ≤ (10002332453625883/10000000000000000 : ℝ)^8249 := by
      have hnat : (12511746334454135323 : ℕ)^2048*10000000000000000^8249 ≤ 10002332453625883^8249*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12511746334454135323 12500000000000000000 10002332453625883 10000000000000000 2048 8249 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002332453625883/10000000000000000 : ℝ)) (X := (12511746334454135323/12500000000000000000 : ℝ)) (by norm_num) 8249 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2710112298049501/25000000000000000000 : ℝ) ≤ ((45513851687782532513/45530000000000000000 : ℝ)+2*(897110180847/455300000000000 : ℝ)*(5183/50000 : ℝ))^(8249/2048 : ℝ) := by
    rw [show (45513851687782532513/45530000000000000000 : ℝ)+2*(897110180847/455300000000000 : ℝ)*(5183/50000 : ℝ)=(10000538233264189/10000000000000000 : ℝ) by norm_num, show 1+2*(2710112298049501/25000000000000000000 : ℝ)=(12502710112298049501/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11746334454135323/25000000000000000000 : ℝ)+(2710112298049501/25000000000000000000 : ℝ) ≤ ((45513851687782532513/45530000000000000000 : ℝ)+(897110180847/455300000000000 : ℝ)*((14919/100000 : ℝ)+(5183/50000 : ℝ)))^(8249/2048 : ℝ) := by
    rw [show (45513851687782532513/45530000000000000000 : ℝ)+(897110180847/455300000000000 : ℝ)*((14919/100000 : ℝ)+(5183/50000 : ℝ))=(2500358835861259/2500000000000000 : ℝ) by norm_num, show 1+(11746334454135323/25000000000000000000 : ℝ)+(2710112298049501/25000000000000000000 : ℝ)=(3126807055844023103/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11746334454135323/25000000000000000000 : ℝ) ≤ ((45513851687782532513/45530000000000000000 : ℝ)+2*(897110180847/455300000000000 : ℝ)*(14919/100000 : ℝ))^(8249/2048 : ℝ) := by
    rw [show (45513851687782532513/45530000000000000000 : ℝ)+2*(897110180847/455300000000000 : ℝ)*(14919/100000 : ℝ)=(10002332453625883/10000000000000000 : ℝ) by norm_num, show 1+2*(11746334454135323/25000000000000000000 : ℝ)=(12511746334454135323/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (45513851687782532513/45530000000000000000 : ℝ)*(X 1 0+X 2 0)+(897110180847/455300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8249/2048 : ℝ)) (lo := (5183/50000 : ℝ)) (hi := (14919/100000 : ℝ)) (c := (45513851687782532513/45530000000000000000 : ℝ)) (alpha := (897110180847/455300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (45513851687782532513/45530000000000000000 : ℝ)*(X 0 1+X 2 1)+(897110180847/455300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8249/2048 : ℝ)) (lo := (5183/50000 : ℝ)) (hi := (14919/100000 : ℝ)) (c := (45513851687782532513/45530000000000000000 : ℝ)) (alpha := (897110180847/455300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (45513851687782532513/45530000000000000000 : ℝ)*(X 0 2+X 1 2)+(897110180847/455300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8249/2048 : ℝ)) (lo := (5183/50000 : ℝ)) (hi := (14919/100000 : ℝ)) (c := (45513851687782532513/45530000000000000000 : ℝ)) (alpha := (897110180847/455300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2207110077/10000000000 : ℝ)*X 0 0+(5406317707/10000000000 : ℝ)*X 0 1+(1313300559/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347937189/10000000000 : ℝ)*X 1 0+(-2284997511/10000000000 : ℝ)*X 1 1+(1313300551/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336984317/2500000000 : ℝ)*X 2 0+(5253202179/10000000000 : ℝ)*X 2 1+(-1142498719/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2188076399/5000000000 : ℝ)*X 0 0+(4228979349/10000000000 : ℝ)*X 0 1+(4528528371/10000000000 : ℝ)*X 0 2+(2188076399/5000000000 : ℝ)*X 1 0+(4228979349/10000000000 : ℝ)*X 1 1+(4528528371/10000000000 : ℝ)*X 1 2+(2188076399/5000000000 : ℝ)*X 2 0+(4228979349/10000000000 : ℝ)*X 2 1+(4528528371/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2207118237/10000000000 : ℝ)*X 0 0+(1050730563/2000000000 : ℝ)*X 0 1+(54058653/100000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((33183753/62500000 : ℝ)*X 1 0+(-426466707/2000000000 : ℝ)*X 1 1+(5405865463/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061879977/2000000000 : ℝ)*X 2 0+(1081173123/2000000000 : ℝ)*X 2 1+(-2132334133/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2188084451/5000000000 : ℝ)*X 0 0+(2263823417/5000000000 : ℝ)*X 0 1+(264366543/625000000 : ℝ)*X 0 2+(2188084451/5000000000 : ℝ)*X 1 0+(2263823417/5000000000 : ℝ)*X 1 1+(264366543/625000000 : ℝ)*X 1 2+(2188084451/5000000000 : ℝ)*X 2 0+(2263823417/5000000000 : ℝ)*X 2 1+(264366543/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1959824764059045437716749813/569125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (46005273/10000000000000 : ℝ)*(base19) + (78744163/20000000000000 : ℝ)*(base23) + (87069081/100000000000000 : ℝ)*(lower2) + (3742039/10000000000000 : ℝ)*(upper3) + (15026243/50000000000000 : ℝ)*(upper5) + (2467349759177367/50000000000000 : ℝ)*(major0) + (2467349759177367/50000000000000 : ℝ)*(major1) + (2467349759177367/50000000000000 : ℝ)*(major2) + (6531026452546269/100000000000000 : ℝ)*(sp0) + (816379559611323/12500000000000 : ℝ)*(sp1) + (2612414617289/40000000000 : ℝ)*(sp2) + (417294522695951/12500000000000 : ℝ)*(sp3) + (5242198523/50000000000000 : ℝ)*(sp4) + (362713293/6250000000000 : ℝ)*(sp7) + (417295248122537/12500000000000 : ℝ)*(f.failure) + (1306207387388663/20000000000000 : ℝ)*(f.sum) + (4801858803773/22765000000000000000000000000 : ℝ)*base65 + (44139799516864366729/2276500000000000000000000000000000 : ℝ)*base68 + (45576504446897866729/2276500000000000000000000000000000 : ℝ)*base70 + (4715594427807866729/2276500000000000000000000000000000 : ℝ)*base72 + (120070279234351/11382500000000000000000000000 : ℝ)*base74 + (91874790988975866729/2276500000000000000000000000000000 : ℝ)*base76 + (1411373975156133271/2276500000000000000000000000000000 : ℝ)*base77 + (69305955710029866729/2276500000000000000000000000000000 : ℝ)*base80 + (26078060180991/11382500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (5448889/312500000000000000000 : ℝ)*base89 + (5448889/312500000000000000000 : ℝ)*base91 + (5448889/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4971756510431361696021912417/569125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (577567499/25000000000000 : ℝ)*(base19) + (214419363/12500000000000 : ℝ)*(base23) + (54058483/100000000000000 : ℝ)*(upper3) + (173418683/100000000000000 : ℝ)*(lower4) + (1344059/1000000000000 : ℝ)*(upper5) + (2481976826083203/50000000000000 : ℝ)*(major0) + (2481976826083203/50000000000000 : ℝ)*(major1) + (2481976826083203/50000000000000 : ℝ)*(major2) + (72997107393/100000000000000 : ℝ)*(sp1) + (5933335623/12500000000000 : ℝ)*(sp2) + (6569754382780359/100000000000000 : ℝ)*(sp4) + (6569679075402971/100000000000000 : ℝ)*(sp5) + (6569705200740471/100000000000000 : ℝ)*(sp6) + (839538157589861/25000000000000 : ℝ)*(sp7) + (839538157589861/25000000000000 : ℝ)*(f.failure) + (6569754382780359/100000000000000 : ℝ)*(f.sum) + (99503461988943/22765000000000000000000000000 : ℝ)*base66 + (31720836930511720861/2276500000000000000000000000000000 : ℝ)*base68 + (2330150189526779139/2276500000000000000000000000000000 : ℝ)*base69 + (27348167519557720861/2276500000000000000000000000000000 : ℝ)*base72 + (6514912992969/11382500000000000000000000000 : ℝ)*base74 + (11395191675915720861/2276500000000000000000000000000000 : ℝ)*base76 + (18514130024592720861/2276500000000000000000000000000000 : ℝ)*base78 + (13477248708235720861/2276500000000000000000000000000000 : ℝ)*base80 + (11665675453423/22765000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (8054917/625000000000000000000 : ℝ)*base89 + (8054917/625000000000000000000 : ℝ)*base91 + (8054917/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1057_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36954497/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14919/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5183/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11003/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2849/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1057_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1057_s5_0 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2207963591/10000000000 : ℝ)*x 0 + (5397259599/10000000000 : ℝ)*x 1 + (2630850429/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2207963591/10000000000 : ℝ)^4125 ≤ (1340810803247/10000000000000 : ℝ)^3101 := by
    have hnat : (2207963591 : ℕ)^4125*10000000000000^3101 ≤ 1340810803247^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2207963591 10000000000 1340810803247 10000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5397259599/10000000000 : ℝ)^4125 ≤ (44028372523109/100000000000000 : ℝ)^3101 := by
    have hnat : (5397259599 : ℕ)^4125*100000000000000^3101 ≤ 44028372523109^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397259599 10000000000 44028372523109 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2630850429/5000000000 : ℝ)^4125 ≤ (42563519425189/100000000000000 : ℝ)^3101 := by
    have hnat : (2630850429 : ℕ)^4125*100000000000000^3101 ≤ 42563519425189^3101*5000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630850429 5000000000 42563519425189 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2207963591/10000000000 : ℝ), (5397259599/10000000000 : ℝ), (2630850429/5000000000 : ℝ)] ![(1340810803247/10000000000000 : ℝ), (44028372523109/100000000000000 : ℝ), (42563519425189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2207963591/10000000000 : ℝ)|^4125 ≤ (1340810803247/10000000000000 : ℝ)^3101
        have hw : |(-2207963591/10000000000 : ℝ)|=(2207963591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5397259599/10000000000 : ℝ)|^4125 ≤ (44028372523109/100000000000000 : ℝ)^3101
        have hw : |(5397259599/10000000000 : ℝ)|=(5397259599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2630850429/5000000000 : ℝ)|^4125 ≤ (42563519425189/100000000000000 : ℝ)^3101
        have hw : |(2630850429/5000000000 : ℝ)|=(2630850429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1057_s5_1 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345684139/10000000000 : ℝ)*x 0 + (-2276785223/10000000000 : ℝ)*x 1 + (5261700933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345684139/10000000000 : ℝ)^4125 ≤ (43469596962711/100000000000000 : ℝ)^3101 := by
    have hnat : (5345684139 : ℕ)^4125*100000000000000^3101 ≤ 43469596962711^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345684139 10000000000 43469596962711 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2276785223/10000000000 : ℝ)^4125 ≤ (13966882791793/100000000000000 : ℝ)^3101 := by
    have hnat : (2276785223 : ℕ)^4125*100000000000000^3101 ≤ 13966882791793^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2276785223 10000000000 13966882791793 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5261700933/10000000000 : ℝ)^4125 ≤ (42563520232229/100000000000000 : ℝ)^3101 := by
    have hnat : (5261700933 : ℕ)^4125*100000000000000^3101 ≤ 42563520232229^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261700933 10000000000 42563520232229 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345684139/10000000000 : ℝ), (-2276785223/10000000000 : ℝ), (5261700933/10000000000 : ℝ)] ![(43469596962711/100000000000000 : ℝ), (13966882791793/100000000000000 : ℝ), (42563520232229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345684139/10000000000 : ℝ)|^4125 ≤ (43469596962711/100000000000000 : ℝ)^3101
        have hw : |(5345684139/10000000000 : ℝ)|=(5345684139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2276785223/10000000000 : ℝ)|^4125 ≤ (13966882791793/100000000000000 : ℝ)^3101
        have hw : |(-2276785223/10000000000 : ℝ)|=(2276785223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5261700933/10000000000 : ℝ)|^4125 ≤ (42563520232229/100000000000000 : ℝ)^3101
        have hw : |(5261700933/10000000000 : ℝ)|=(5261700933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1057_s5_2 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345683903/10000000000 : ℝ)*x 0 + (526170091/1000000000 : ℝ)*x 1 + (-1138392783/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345683903/10000000000 : ℝ)^4125 ≤ (5433699301239/12500000000000 : ℝ)^3101 := by
    have hnat : (5345683903 : ℕ)^4125*12500000000000^3101 ≤ 5433699301239^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345683903 10000000000 5433699301239 12500000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526170091/1000000000 : ℝ)^4125 ≤ (1330109999523/3125000000000 : ℝ)^3101 := by
    have hnat : (526170091 : ℕ)^4125*3125000000000^3101 ≤ 1330109999523^3101*1000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526170091 1000000000 1330109999523 3125000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1138392783/5000000000 : ℝ)^4125 ≤ (6983442795367/50000000000000 : ℝ)^3101 := by
    have hnat : (1138392783 : ℕ)^4125*50000000000000^3101 ≤ 6983442795367^3101*5000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1138392783 5000000000 6983442795367 50000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345683903/10000000000 : ℝ), (526170091/1000000000 : ℝ), (-1138392783/5000000000 : ℝ)] ![(5433699301239/12500000000000 : ℝ), (1330109999523/3125000000000 : ℝ), (6983442795367/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345683903/10000000000 : ℝ)|^4125 ≤ (5433699301239/12500000000000 : ℝ)^3101
        have hw : |(5345683903/10000000000 : ℝ)|=(5345683903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526170091/1000000000 : ℝ)|^4125 ≤ (1330109999523/3125000000000 : ℝ)^3101
        have hw : |(526170091/1000000000 : ℝ)|=(526170091/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1138392783/5000000000 : ℝ)|^4125 ≤ (6983442795367/50000000000000 : ℝ)^3101
        have hw : |(-1138392783/5000000000 : ℝ)|=(1138392783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1057_s5_3 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4376649287/10000000000 : ℝ)*x 0 + (2123043639/5000000000 : ℝ)*x 1 + (22556449/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4376649287/10000000000 : ℝ)^4125 ≤ (6663017964909/20000000000000 : ℝ)^3101 := by
    have hnat : (4376649287 : ℕ)^4125*20000000000000^3101 ≤ 6663017964909^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4376649287 10000000000 6663017964909 20000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2123043639/5000000000 : ℝ)^4125 ≤ (31999624557201/100000000000000 : ℝ)^3101 := by
    have hnat : (2123043639 : ℕ)^4125*100000000000000^3101 ≤ 31999624557201^3101*5000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123043639 5000000000 31999624557201 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (22556449/50000000 : ℝ)^4125 ≤ (8671321398571/25000000000000 : ℝ)^3101 := by
    have hnat : (22556449 : ℕ)^4125*25000000000000^3101 ≤ 8671321398571^3101*50000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22556449 50000000 8671321398571 25000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4376649287/10000000000 : ℝ), (2123043639/5000000000 : ℝ), (22556449/50000000 : ℝ)] ![(6663017964909/20000000000000 : ℝ), (31999624557201/100000000000000 : ℝ), (8671321398571/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4376649287/10000000000 : ℝ)|^4125 ≤ (6663017964909/20000000000000 : ℝ)^3101
        have hw : |(4376649287/10000000000 : ℝ)|=(4376649287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2123043639/5000000000 : ℝ)|^4125 ≤ (31999624557201/100000000000000 : ℝ)^3101
        have hw : |(2123043639/5000000000 : ℝ)|=(2123043639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(22556449/50000000 : ℝ)|^4125 ≤ (8671321398571/25000000000000 : ℝ)^3101
        have hw : |(22556449/50000000 : ℝ)|=(22556449/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1057_s5_4 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-220796943/1000000000 : ℝ)*x 0 + (1315513497/2500000000 : ℝ)*x 1 + (1349226267/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (220796943/1000000000 : ℝ)^4125 ≤ (6704077599637/50000000000000 : ℝ)^3101 := by
    have hnat : (220796943 : ℕ)^4125*50000000000000^3101 ≤ 6704077599637^3101*1000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220796943 1000000000 6704077599637 50000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315513497/2500000000 : ℝ)^4125 ≤ (42567319332391/100000000000000 : ℝ)^3101 := by
    have hnat : (1315513497 : ℕ)^4125*100000000000000^3101 ≤ 42567319332391^3101*2500000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315513497 2500000000 42567319332391 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1349226267/2500000000 : ℝ)^4125 ≤ (8804905088977/20000000000000 : ℝ)^3101 := by
    have hnat : (1349226267 : ℕ)^4125*20000000000000^3101 ≤ 8804905088977^3101*2500000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349226267 2500000000 8804905088977 20000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-220796943/1000000000 : ℝ), (1315513497/2500000000 : ℝ), (1349226267/2500000000 : ℝ)] ![(6704077599637/50000000000000 : ℝ), (42567319332391/100000000000000 : ℝ), (8804905088977/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-220796943/1000000000 : ℝ)|^4125 ≤ (6704077599637/50000000000000 : ℝ)^3101
        have hw : |(-220796943/1000000000 : ℝ)|=(220796943/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1315513497/2500000000 : ℝ)|^4125 ≤ (42567319332391/100000000000000 : ℝ)^3101
        have hw : |(1315513497/2500000000 : ℝ)|=(1315513497/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1349226267/2500000000 : ℝ)|^4125 ≤ (8804905088977/20000000000000 : ℝ)^3101
        have hw : |(1349226267/2500000000 : ℝ)|=(1349226267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1057_s5_5 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5311564493/10000000000 : ℝ)*x 0 + (-2141581213/10000000000 : ℝ)*x 1 + (5396905043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311564493/10000000000 : ℝ)^4125 ≤ (43100916218441/100000000000000 : ℝ)^3101 := by
    have hnat : (5311564493 : ℕ)^4125*100000000000000^3101 ≤ 43100916218441^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311564493 10000000000 43100916218441 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2141581213/10000000000 : ℝ)^4125 ≤ (12874558598027/100000000000000 : ℝ)^3101 := by
    have hnat : (2141581213 : ℕ)^4125*100000000000000^3101 ≤ 12874558598027^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141581213 10000000000 12874558598027 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396905043/10000000000 : ℝ)^4125 ≤ (5503065646701/12500000000000 : ℝ)^3101 := by
    have hnat : (5396905043 : ℕ)^4125*12500000000000^3101 ≤ 5503065646701^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396905043 10000000000 5503065646701 12500000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311564493/10000000000 : ℝ), (-2141581213/10000000000 : ℝ), (5396905043/10000000000 : ℝ)] ![(43100916218441/100000000000000 : ℝ), (12874558598027/100000000000000 : ℝ), (5503065646701/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311564493/10000000000 : ℝ)|^4125 ≤ (43100916218441/100000000000000 : ℝ)^3101
        have hw : |(5311564493/10000000000 : ℝ)|=(5311564493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2141581213/10000000000 : ℝ)|^4125 ≤ (12874558598027/100000000000000 : ℝ)^3101
        have hw : |(-2141581213/10000000000 : ℝ)|=(2141581213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5396905043/10000000000 : ℝ)|^4125 ≤ (5503065646701/12500000000000 : ℝ)^3101
        have hw : |(5396905043/10000000000 : ℝ)|=(5396905043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1057_s5_6 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062312901/2000000000 : ℝ)*x 0 + (2698452517/5000000000 : ℝ)*x 1 + (-2141581209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062312901/2000000000 : ℝ)^4125 ≤ (4310091634797/10000000000000 : ℝ)^3101 := by
    have hnat : (1062312901 : ℕ)^4125*10000000000000^3101 ≤ 4310091634797^3101*2000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062312901 2000000000 4310091634797 10000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2698452517/5000000000 : ℝ)^4125 ≤ (44024525075949/100000000000000 : ℝ)^3101 := by
    have hnat : (2698452517 : ℕ)^4125*100000000000000^3101 ≤ 44024525075949^3101*5000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698452517 5000000000 44024525075949 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2141581209/10000000000 : ℝ)^4125 ≤ (12874558566039/100000000000000 : ℝ)^3101 := by
    have hnat : (2141581209 : ℕ)^4125*100000000000000^3101 ≤ 12874558566039^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141581209 10000000000 12874558566039 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062312901/2000000000 : ℝ), (2698452517/5000000000 : ℝ), (-2141581209/10000000000 : ℝ)] ![(4310091634797/10000000000000 : ℝ), (44024525075949/100000000000000 : ℝ), (12874558566039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062312901/2000000000 : ℝ)|^4125 ≤ (4310091634797/10000000000000 : ℝ)^3101
        have hw : |(1062312901/2000000000 : ℝ)|=(1062312901/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2698452517/5000000000 : ℝ)|^4125 ≤ (44024525075949/100000000000000 : ℝ)^3101
        have hw : |(2698452517/5000000000 : ℝ)|=(2698452517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2141581209/10000000000 : ℝ)|^4125 ≤ (12874558566039/100000000000000 : ℝ)^3101
        have hw : |(-2141581209/10000000000 : ℝ)|=(2141581209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1057_s5_7 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4376660527/10000000000 : ℝ)*x 0 + (2255299209/5000000000 : ℝ)*x 1 + (4246781243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4376660527/10000000000 : ℝ)^4125 ≤ (3331520363651/10000000000000 : ℝ)^3101 := by
    have hnat : (4376660527 : ℕ)^4125*10000000000000^3101 ≤ 3331520363651^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4376660527 10000000000 3331520363651 10000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2255299209/5000000000 : ℝ)^4125 ≤ (34678214708639/100000000000000 : ℝ)^3101 := by
    have hnat : (2255299209 : ℕ)^4125*100000000000000^3101 ≤ 34678214708639^3101*5000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255299209 5000000000 34678214708639 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4246781243/10000000000 : ℝ)^4125 ≤ (32006581644273/100000000000000 : ℝ)^3101 := by
    have hnat : (4246781243 : ℕ)^4125*100000000000000^3101 ≤ 32006581644273^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4246781243 10000000000 32006581644273 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4376660527/10000000000 : ℝ), (2255299209/5000000000 : ℝ), (4246781243/10000000000 : ℝ)] ![(3331520363651/10000000000000 : ℝ), (34678214708639/100000000000000 : ℝ), (32006581644273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4376660527/10000000000 : ℝ)|^4125 ≤ (3331520363651/10000000000000 : ℝ)^3101
        have hw : |(4376660527/10000000000 : ℝ)|=(4376660527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2255299209/5000000000 : ℝ)|^4125 ≤ (34678214708639/100000000000000 : ℝ)^3101
        have hw : |(2255299209/5000000000 : ℝ)|=(2255299209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4246781243/10000000000 : ℝ)|^4125 ≤ (32006581644273/100000000000000 : ℝ)^3101
        have hw : |(4246781243/10000000000 : ℝ)|=(4246781243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1057_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36954497/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2849/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11003/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (699/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2811/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2849/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11003/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2849/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11003/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2849/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11003/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2849/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11003/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2849/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11003/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2849/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11003/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11003/100000 : ℝ) ^ (8249/2048 : ℝ) ≤ (6891880896939341/50000000000000000000 : ℝ) := by
    have hpowers : (11003/100000 : ℝ)^8249 ≤ (6891880896939341/50000000000000000000 : ℝ)^2048 := by
      have hnat : (11003 : ℕ)^8249*50000000000000000000^2048 ≤ 6891880896939341^2048*100000^8249 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11003 100000 6891880896939341 50000000000000000000 8249 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11003/100000 : ℝ)) (X := (6891880896939341/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8249 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2849/20000 : ℝ) ^ (8249/2048 : ℝ) ≤ (4875335801917757/12500000000000000000 : ℝ) := by
    have hpowers : (2849/20000 : ℝ)^8249 ≤ (4875335801917757/12500000000000000000 : ℝ)^2048 := by
      have hnat : (2849 : ℕ)^8249*12500000000000000000^2048 ≤ 4875335801917757^2048*20000^8249 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2849 20000 4875335801917757 12500000000000000000 8249 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2849/20000 : ℝ)) (X := (4875335801917757/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8249 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006891880896939341/25000000000000000000 : ℝ) ≤ (1000068435494301/1000000000000000 : ℝ) ^ (8249/2048 : ℝ) := by
    have hpowers : (25006891880896939341/25000000000000000000 : ℝ)^2048 ≤ (1000068435494301/1000000000000000 : ℝ)^8249 := by
      have hnat : (25006891880896939341 : ℕ)^2048*1000000000000000^8249 ≤ 1000068435494301^8249*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006891880896939341 25000000000000000000 1000068435494301 1000000000000000 2048 8249 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000068435494301/1000000000000000 : ℝ)) (X := (25006891880896939341/25000000000000000000 : ℝ)) (by norm_num) 8249 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50026393224104610369/50000000000000000000 : ℝ) ≤ (2500327570625619/2500000000000000 : ℝ) ^ (8249/2048 : ℝ) := by
    have hpowers : (50026393224104610369/50000000000000000000 : ℝ)^2048 ≤ (2500327570625619/2500000000000000 : ℝ)^8249 := by
      have hnat : (50026393224104610369 : ℕ)^2048*2500000000000000^8249 ≤ 2500327570625619^8249*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026393224104610369 50000000000000000000 2500327570625619 2500000000000000 2048 8249 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500327570625619/2500000000000000 : ℝ)) (X := (50026393224104610369/50000000000000000000 : ℝ)) (by norm_num) 8249 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254875335801917757/6250000000000000000 : ℝ) ≤ (5000968105030971/5000000000000000 : ℝ) ^ (8249/2048 : ℝ) := by
    have hpowers : (6254875335801917757/6250000000000000000 : ℝ)^2048 ≤ (5000968105030971/5000000000000000 : ℝ)^8249 := by
      have hnat : (6254875335801917757 : ℕ)^2048*5000000000000000^8249 ≤ 5000968105030971^8249*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254875335801917757 6250000000000000000 5000968105030971 5000000000000000 2048 8249 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000968105030971/5000000000000000 : ℝ)) (X := (6254875335801917757/6250000000000000000 : ℝ)) (by norm_num) 8249 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6891880896939341/50000000000000000000 : ℝ) ≤ ((4051055564606453703/4052500000000000000 : ℝ)+2*(312963779733/162100000000000 : ℝ)*(11003/100000 : ℝ))^(8249/2048 : ℝ) := by
    rw [show (4051055564606453703/4052500000000000000 : ℝ)+2*(312963779733/162100000000000 : ℝ)*(11003/100000 : ℝ)=(1000068435494301/1000000000000000 : ℝ) by norm_num, show 1+2*(6891880896939341/50000000000000000000 : ℝ)=(25006891880896939341/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4875335801917757/12500000000000000000 : ℝ)+(6891880896939341/50000000000000000000 : ℝ) ≤ ((4051055564606453703/4052500000000000000 : ℝ)+(312963779733/162100000000000 : ℝ)*((2849/20000 : ℝ)+(11003/100000 : ℝ)))^(8249/2048 : ℝ) := by
    rw [show (4051055564606453703/4052500000000000000 : ℝ)+(312963779733/162100000000000 : ℝ)*((2849/20000 : ℝ)+(11003/100000 : ℝ))=(2500327570625619/2500000000000000 : ℝ) by norm_num, show 1+(4875335801917757/12500000000000000000 : ℝ)+(6891880896939341/50000000000000000000 : ℝ)=(50026393224104610369/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4875335801917757/12500000000000000000 : ℝ) ≤ ((4051055564606453703/4052500000000000000 : ℝ)+2*(312963779733/162100000000000 : ℝ)*(2849/20000 : ℝ))^(8249/2048 : ℝ) := by
    rw [show (4051055564606453703/4052500000000000000 : ℝ)+2*(312963779733/162100000000000 : ℝ)*(2849/20000 : ℝ)=(5000968105030971/5000000000000000 : ℝ) by norm_num, show 1+2*(4875335801917757/12500000000000000000 : ℝ)=(6254875335801917757/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4051055564606453703/4052500000000000000 : ℝ)*(X 1 0+X 2 0)+(312963779733/162100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8249/2048 : ℝ)) (lo := (11003/100000 : ℝ)) (hi := (2849/20000 : ℝ)) (c := (4051055564606453703/4052500000000000000 : ℝ)) (alpha := (312963779733/162100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4051055564606453703/4052500000000000000 : ℝ)*(X 0 1+X 2 1)+(312963779733/162100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8249/2048 : ℝ)) (lo := (11003/100000 : ℝ)) (hi := (2849/20000 : ℝ)) (c := (4051055564606453703/4052500000000000000 : ℝ)) (alpha := (312963779733/162100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4051055564606453703/4052500000000000000 : ℝ)*(X 0 2+X 1 2)+(312963779733/162100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8249/2048 : ℝ)) (lo := (11003/100000 : ℝ)) (hi := (2849/20000 : ℝ)) (c := (4051055564606453703/4052500000000000000 : ℝ)) (alpha := (312963779733/162100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2207963591/10000000000 : ℝ)*X 0 0+(5397259599/10000000000 : ℝ)*X 0 1+(2630850429/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345684139/10000000000 : ℝ)*X 1 0+(-2276785223/10000000000 : ℝ)*X 1 1+(5261700933/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345683903/10000000000 : ℝ)*X 2 0+(526170091/1000000000 : ℝ)*X 2 1+(-1138392783/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4376649287/10000000000 : ℝ)*X 0 0+(2123043639/5000000000 : ℝ)*X 0 1+(22556449/50000000 : ℝ)*X 0 2+(4376649287/10000000000 : ℝ)*X 1 0+(2123043639/5000000000 : ℝ)*X 1 1+(22556449/50000000 : ℝ)*X 1 2+(4376649287/10000000000 : ℝ)*X 2 0+(2123043639/5000000000 : ℝ)*X 2 1+(22556449/50000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-220796943/1000000000 : ℝ)*X 0 0+(1315513497/2500000000 : ℝ)*X 0 1+(1349226267/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311564493/10000000000 : ℝ)*X 1 0+(-2141581213/10000000000 : ℝ)*X 1 1+(5396905043/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062312901/2000000000 : ℝ)*X 2 0+(2698452517/5000000000 : ℝ)*X 2 1+(-2141581209/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4376660527/10000000000 : ℝ)*X 0 0+(2255299209/5000000000 : ℝ)*X 0 1+(4246781243/10000000000 : ℝ)*X 0 2+(4376660527/10000000000 : ℝ)*X 1 0+(2255299209/5000000000 : ℝ)*X 1 1+(4246781243/10000000000 : ℝ)*X 1 2+(4376660527/10000000000 : ℝ)*X 2 0+(2255299209/5000000000 : ℝ)*X 2 1+(4246781243/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (144628222838175667096666161/25328125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (351210833/50000000000000 : ℝ)*(base19) + (540475257/100000000000000 : ℝ)*(base23) + (121261997/100000000000000 : ℝ)*(upper3) + (12453393/10000000000000 : ℝ)*(lower4) + (1393458802516029/25000000000000 : ℝ)*(major0) + (1393458802516029/25000000000000 : ℝ)*(major1) + (1393458802516029/25000000000000 : ℝ)*(major2) + (7376908318618969/100000000000000 : ℝ)*(sp0) + (3688463678107661/50000000000000 : ℝ)*(sp1) + (7376916670996019/100000000000000 : ℝ)*(sp2) + (3770723053145457/100000000000000 : ℝ)*(sp3) + (9870009009/50000000000000 : ℝ)*(sp4) + (677947857/6250000000000 : ℝ)*(sp6) + (382360127/2000000000000 : ℝ)*(sp7) + (1885371085575903/50000000000000 : ℝ)*(f.failure) + (7376928058636987/100000000000000 : ℝ)*(f.sum) + (7977887165539/4052500000000000000000000000 : ℝ)*base65 + (1766919545763482113/101312500000000000000000000000000 : ℝ)*base68 + (844578925826919613/101312500000000000000000000000000 : ℝ)*base70 + (37993751358857113/101312500000000000000000000000000 : ℝ)*base72 + (2052181883167/506562500000000000000000000 : ℝ)*base74 + (3154342312126919613/101312500000000000000000000000000 : ℝ)*base76 + (815720390482455387/101312500000000000000000000000000 : ℝ)*base77 + (3168697763309919613/101312500000000000000000000000000 : ℝ)*base80 + (3857590106947/2026250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (685791/1250000000000000000000 : ℝ)*base89 + (685791/1250000000000000000000 : ℝ)*base91 + (685791/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (372429853269924528193844469/50656250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1254871061/100000000000000 : ℝ)*(base19) + (35455103/2500000000000 : ℝ)*(base23) + (61286429/50000000000000 : ℝ)*(upper3) + (8450571/12500000000000 : ℝ)*(lower4) + (4477491/3125000000000 : ℝ)*(upper5) + (1400761279309653/25000000000000 : ℝ)*(major0) + (1400761279309653/25000000000000 : ℝ)*(major1) + (1400761279309653/25000000000000 : ℝ)*(major2) + (16142898319/50000000000000 : ℝ)*(sp1) + (35290813647/100000000000000 : ℝ)*(sp2) + (3707793546267357/50000000000000 : ℝ)*(sp4) + (1483110710373403/20000000000000 : ℝ)*(sp5) + (1853887595879237/25000000000000 : ℝ)*(sp6) + (1895251448436239/50000000000000 : ℝ)*(sp7) + (1895251448436239/50000000000000 : ℝ)*(f.failure) + (3707793546267357/50000000000000 : ℝ)*(f.sum) + (6239955929783/4052500000000000000000000000 : ℝ)*base65 + (974046337314470059/101312500000000000000000000000000 : ℝ)*base67 + (438449552135095059/101312500000000000000000000000000 : ℝ)*base69 + (704796236696532559/101312500000000000000000000000000 : ℝ)*base71 + (1577167585421/8105000000000000000000000000 : ℝ)*base73 + (926857931417157559/101312500000000000000000000000000 : ℝ)*base75 + (589772923172532559/101312500000000000000000000000000 : ℝ)*base77 + (1833815054878845059/101312500000000000000000000000000 : ℝ)*base79 + (936542149719/506562500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (1183217/1250000000000000000000 : ℝ)*base90 + (1183217/1250000000000000000000 : ℝ)*base92 + (1183217/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1057_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36954497/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2849/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11003/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (699/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2811/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1057_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1057_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36954497/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16771/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8667/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (699/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2811/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1057_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1057_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1057_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36954497/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16771/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8667/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (699/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2811/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1057_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
