-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1259_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:53:38.096673+00:00
-- url     : https://prove2.me/submissions/09f833e3-cafd-4d42-a059-5b9b51abfa5e

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
theorem support_rectangle_w1259_box_0 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1988989311/10000000000 : ℝ)*x 0 + (537458633/1000000000 : ℝ)*x 1 + (107491727/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1988989311/10000000000 : ℝ)^2113 ≤ (2373367628371/20000000000000 : ℝ)^1601 := by
    have hnat : (1988989311 : ℕ)^2113*20000000000000^1601 ≤ 2373367628371^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1988989311 10000000000 2373367628371 20000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (537458633/1000000000 : ℝ)^2113 ≤ (44066580813939/100000000000000 : ℝ)^1601 := by
    have hnat : (537458633 : ℕ)^2113*100000000000000^1601 ≤ 44066580813939^1601*1000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537458633 1000000000 44066580813939 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (107491727/200000000 : ℝ)^2113 ≤ (44066581030361/100000000000000 : ℝ)^1601 := by
    have hnat : (107491727 : ℕ)^2113*100000000000000^1601 ≤ 44066581030361^1601*200000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107491727 200000000 44066581030361 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1988989311/10000000000 : ℝ), (537458633/1000000000 : ℝ), (107491727/200000000 : ℝ)] ![(2373367628371/20000000000000 : ℝ), (44066580813939/100000000000000 : ℝ), (44066581030361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1988989311/10000000000 : ℝ)|^2113 ≤ (2373367628371/20000000000000 : ℝ)^1601
        have hw : |(-1988989311/10000000000 : ℝ)|=(1988989311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(537458633/1000000000 : ℝ)|^2113 ≤ (44066580813939/100000000000000 : ℝ)^1601
        have hw : |(537458633/1000000000 : ℝ)|=(537458633/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(107491727/200000000 : ℝ)|^2113 ≤ (44066581030361/100000000000000 : ℝ)^1601
        have hw : |(107491727/200000000 : ℝ)|=(107491727/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_box_1 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5296908591/10000000000 : ℝ)*x 0 + (-2094603311/10000000000 : ℝ)*x 1 + (1074917267/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296908591/10000000000 : ℝ)^2113 ≤ (43227969110769/100000000000000 : ℝ)^1601 := by
    have hnat : (5296908591 : ℕ)^2113*100000000000000^1601 ≤ 43227969110769^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296908591 10000000000 43227969110769 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2094603311/10000000000 : ℝ)^2113 ≤ (6352725007501/50000000000000 : ℝ)^1601 := by
    have hnat : (2094603311 : ℕ)^2113*50000000000000^1601 ≤ 6352725007501^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2094603311 10000000000 6352725007501 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1074917267/2000000000 : ℝ)^2113 ≤ (11016645217011/25000000000000 : ℝ)^1601 := by
    have hnat : (1074917267 : ℕ)^2113*25000000000000^1601 ≤ 11016645217011^1601*2000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074917267 2000000000 11016645217011 25000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296908591/10000000000 : ℝ), (-2094603311/10000000000 : ℝ), (1074917267/2000000000 : ℝ)] ![(43227969110769/100000000000000 : ℝ), (6352725007501/50000000000000 : ℝ), (11016645217011/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296908591/10000000000 : ℝ)|^2113 ≤ (43227969110769/100000000000000 : ℝ)^1601
        have hw : |(5296908591/10000000000 : ℝ)|=(5296908591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2094603311/10000000000 : ℝ)|^2113 ≤ (6352725007501/50000000000000 : ℝ)^1601
        have hw : |(-2094603311/10000000000 : ℝ)|=(2094603311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1074917267/2000000000 : ℝ)|^2113 ≤ (11016645217011/25000000000000 : ℝ)^1601
        have hw : |(1074917267/2000000000 : ℝ)|=(1074917267/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_box_2 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5296908543/10000000000 : ℝ)*x 0 + (10497239/19531250 : ℝ)*x 1 + (-209460333/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296908543/10000000000 : ℝ)^2113 ≤ (5403496074221/12500000000000 : ℝ)^1601 := by
    have hnat : (5296908543 : ℕ)^2113*12500000000000^1601 ≤ 5403496074221^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296908543 10000000000 5403496074221 12500000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10497239/19531250 : ℝ)^2113 ≤ (22033290612571/50000000000000 : ℝ)^1601 := by
    have hnat : (10497239 : ℕ)^2113*50000000000000^1601 ≤ 22033290612571^1601*19531250^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10497239 19531250 22033290612571 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209460333/1000000000 : ℝ)^2113 ≤ (12705450167109/100000000000000 : ℝ)^1601 := by
    have hnat : (209460333 : ℕ)^2113*100000000000000^1601 ≤ 12705450167109^1601*1000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209460333 1000000000 12705450167109 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296908543/10000000000 : ℝ), (10497239/19531250 : ℝ), (-209460333/1000000000 : ℝ)] ![(5403496074221/12500000000000 : ℝ), (22033290612571/50000000000000 : ℝ), (12705450167109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296908543/10000000000 : ℝ)|^2113 ≤ (5403496074221/12500000000000 : ℝ)^1601
        have hw : |(5296908543/10000000000 : ℝ)|=(5296908543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(10497239/19531250 : ℝ)|^2113 ≤ (22033290612571/50000000000000 : ℝ)^1601
        have hw : |(10497239/19531250 : ℝ)|=(10497239/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-209460333/1000000000 : ℝ)|^2113 ≤ (12705450167109/100000000000000 : ℝ)^1601
        have hw : |(-209460333/1000000000 : ℝ)|=(209460333/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_box_3 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5568521/12500000 : ℝ)*x 0 + (4297295991/10000000000 : ℝ)*x 1 + (4297296001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5568521/12500000 : ℝ)^2113 ≤ (8599349481873/25000000000000 : ℝ)^1601 := by
    have hnat : (5568521 : ℕ)^2113*25000000000000^1601 ≤ 8599349481873^1601*12500000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5568521 12500000 8599349481873 25000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4297295991/10000000000 : ℝ)^2113 ≤ (3280130097691/10000000000000 : ℝ)^1601 := by
    have hnat : (4297295991 : ℕ)^2113*10000000000000^1601 ≤ 3280130097691^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4297295991 10000000000 3280130097691 10000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4297296001/10000000000 : ℝ)^2113 ≤ (656026021553/2000000000000 : ℝ)^1601 := by
    have hnat : (4297296001 : ℕ)^2113*2000000000000^1601 ≤ 656026021553^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4297296001 10000000000 656026021553 2000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5568521/12500000 : ℝ), (4297295991/10000000000 : ℝ), (4297296001/10000000000 : ℝ)] ![(8599349481873/25000000000000 : ℝ), (3280130097691/10000000000000 : ℝ), (656026021553/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5568521/12500000 : ℝ)|^2113 ≤ (8599349481873/25000000000000 : ℝ)^1601
        have hw : |(5568521/12500000 : ℝ)|=(5568521/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4297295991/10000000000 : ℝ)|^2113 ≤ (3280130097691/10000000000000 : ℝ)^1601
        have hw : |(4297295991/10000000000 : ℝ)|=(4297295991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4297296001/10000000000 : ℝ)|^2113 ≤ (656026021553/2000000000000 : ℝ)^1601
        have hw : |(4297296001/10000000000 : ℝ)|=(4297296001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_box_4 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2236717463/10000000000 : ℝ)*x 0 + (2641226493/5000000000 : ℝ)*x 1 + (5282453031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2236717463/10000000000 : ℝ)^2113 ≤ (1731915500483/12500000000000 : ℝ)^1601 := by
    have hnat : (2236717463 : ℕ)^2113*12500000000000^1601 ≤ 1731915500483^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2236717463 10000000000 1731915500483 12500000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2641226493/5000000000 : ℝ)^2113 ≤ (10768084437329/25000000000000 : ℝ)^1601 := by
    have hnat : (2641226493 : ℕ)^2113*25000000000000^1601 ≤ 10768084437329^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641226493 5000000000 10768084437329 25000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5282453031/10000000000 : ℝ)^2113 ≤ (21536169116791/50000000000000 : ℝ)^1601 := by
    have hnat : (5282453031 : ℕ)^2113*50000000000000^1601 ≤ 21536169116791^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282453031 10000000000 21536169116791 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2236717463/10000000000 : ℝ), (2641226493/5000000000 : ℝ), (5282453031/10000000000 : ℝ)] ![(1731915500483/12500000000000 : ℝ), (10768084437329/25000000000000 : ℝ), (21536169116791/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2236717463/10000000000 : ℝ)|^2113 ≤ (1731915500483/12500000000000 : ℝ)^1601
        have hw : |(-2236717463/10000000000 : ℝ)|=(2236717463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2641226493/5000000000 : ℝ)|^2113 ≤ (10768084437329/25000000000000 : ℝ)^1601
        have hw : |(2641226493/5000000000 : ℝ)|=(2641226493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5282453031/10000000000 : ℝ)|^2113 ≤ (21536169116791/50000000000000 : ℝ)^1601
        have hw : |(5282453031/10000000000 : ℝ)|=(5282453031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_box_5 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5361831757/10000000000 : ℝ)*x 0 + (-1065587713/5000000000 : ℝ)*x 1 + (2641226503/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5361831757/10000000000 : ℝ)^2113 ≤ (21964307183301/50000000000000 : ℝ)^1601 := by
    have hnat : (5361831757 : ℕ)^2113*50000000000000^1601 ≤ 21964307183301^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5361831757 10000000000 21964307183301 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1065587713/5000000000 : ℝ)^2113 ≤ (16248809573/125000000000 : ℝ)^1601 := by
    have hnat : (1065587713 : ℕ)^2113*125000000000^1601 ≤ 16248809573^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065587713 5000000000 16248809573 125000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2641226503/5000000000 : ℝ)^2113 ≤ (21536168982273/50000000000000 : ℝ)^1601 := by
    have hnat : (2641226503 : ℕ)^2113*50000000000000^1601 ≤ 21536168982273^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641226503 5000000000 21536168982273 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5361831757/10000000000 : ℝ), (-1065587713/5000000000 : ℝ), (2641226503/5000000000 : ℝ)] ![(21964307183301/50000000000000 : ℝ), (16248809573/125000000000 : ℝ), (21536168982273/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5361831757/10000000000 : ℝ)|^2113 ≤ (21964307183301/50000000000000 : ℝ)^1601
        have hw : |(5361831757/10000000000 : ℝ)|=(5361831757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1065587713/5000000000 : ℝ)|^2113 ≤ (16248809573/125000000000 : ℝ)^1601
        have hw : |(-1065587713/5000000000 : ℝ)|=(1065587713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2641226503/5000000000 : ℝ)|^2113 ≤ (21536168982273/50000000000000 : ℝ)^1601
        have hw : |(2641226503/5000000000 : ℝ)|=(2641226503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_box_6 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2680915903/5000000000 : ℝ)*x 0 + (2641226511/5000000000 : ℝ)*x 1 + (-1065587669/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2680915903/5000000000 : ℝ)^2113 ≤ (21964307448217/50000000000000 : ℝ)^1601 := by
    have hnat : (2680915903 : ℕ)^2113*50000000000000^1601 ≤ 21964307448217^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2680915903 5000000000 21964307448217 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2641226511/5000000000 : ℝ)^2113 ≤ (43072338136729/100000000000000 : ℝ)^1601 := by
    have hnat : (2641226511 : ℕ)^2113*100000000000000^1601 ≤ 43072338136729^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641226511 5000000000 43072338136729 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1065587669/5000000000 : ℝ)^2113 ≤ (12999046949993/100000000000000 : ℝ)^1601 := by
    have hnat : (1065587669 : ℕ)^2113*100000000000000^1601 ≤ 12999046949993^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065587669 5000000000 12999046949993 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2680915903/5000000000 : ℝ), (2641226511/5000000000 : ℝ), (-1065587669/5000000000 : ℝ)] ![(21964307448217/50000000000000 : ℝ), (43072338136729/100000000000000 : ℝ), (12999046949993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2680915903/5000000000 : ℝ)|^2113 ≤ (21964307448217/50000000000000 : ℝ)^1601
        have hw : |(2680915903/5000000000 : ℝ)|=(2680915903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2641226511/5000000000 : ℝ)|^2113 ≤ (43072338136729/100000000000000 : ℝ)^1601
        have hw : |(2641226511/5000000000 : ℝ)|=(2641226511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1065587669/5000000000 : ℝ)|^2113 ≤ (12999046949993/100000000000000 : ℝ)^1601
        have hw : |(-1065587669/5000000000 : ℝ)|=(1065587669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_box_7 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2120835841/5000000000 : ℝ)*x 0 + (2201924263/5000000000 : ℝ)*x 1 + (4403848619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2120835841/5000000000 : ℝ)^2113 ≤ (6448420462807/20000000000000 : ℝ)^1601 := by
    have hnat : (2120835841 : ℕ)^2113*20000000000000^1601 ≤ 6448420462807^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120835841 5000000000 6448420462807 20000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2201924263/5000000000 : ℝ)^2113 ≤ (4234868545291/12500000000000 : ℝ)^1601 := by
    have hnat : (2201924263 : ℕ)^2113*12500000000000^1601 ≤ 4234868545291^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2201924263 5000000000 4234868545291 12500000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4403848619/10000000000 : ℝ)^2113 ≤ (16939474653291/50000000000000 : ℝ)^1601 := by
    have hnat : (4403848619 : ℕ)^2113*50000000000000^1601 ≤ 16939474653291^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4403848619 10000000000 16939474653291 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2120835841/5000000000 : ℝ), (2201924263/5000000000 : ℝ), (4403848619/10000000000 : ℝ)] ![(6448420462807/20000000000000 : ℝ), (4234868545291/12500000000000 : ℝ), (16939474653291/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2120835841/5000000000 : ℝ)|^2113 ≤ (6448420462807/20000000000000 : ℝ)^1601
        have hw : |(2120835841/5000000000 : ℝ)|=(2120835841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2201924263/5000000000 : ℝ)|^2113 ≤ (4234868545291/12500000000000 : ℝ)^1601
        have hw : |(2201924263/5000000000 : ℝ)|=(2201924263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4403848619/10000000000 : ℝ)|^2113 ≤ (16939474653291/50000000000000 : ℝ)^1601
        have hw : |(4403848619/10000000000 : ℝ)|=(4403848619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_box_8 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2184789121/10000000000 : ℝ)*x 0 + (1043915387/2000000000 : ℝ)*x 1 + (5384199867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184789121/10000000000 : ℝ)^2113 ≤ (13432368822641/100000000000000 : ℝ)^1601 := by
    have hnat : (2184789121 : ℕ)^2113*100000000000000^1601 ≤ 13432368822641^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184789121 10000000000 13432368822641 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043915387/2000000000 : ℝ)^2113 ≤ (42396991306813/100000000000000 : ℝ)^1601 := by
    have hnat : (1043915387 : ℕ)^2113*100000000000000^1601 ≤ 42396991306813^1601*2000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043915387 2000000000 42396991306813 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5384199867/10000000000 : ℝ)^2113 ≤ (44170639856211/100000000000000 : ℝ)^1601 := by
    have hnat : (5384199867 : ℕ)^2113*100000000000000^1601 ≤ 44170639856211^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384199867 10000000000 44170639856211 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2184789121/10000000000 : ℝ), (1043915387/2000000000 : ℝ), (5384199867/10000000000 : ℝ)] ![(13432368822641/100000000000000 : ℝ), (42396991306813/100000000000000 : ℝ), (44170639856211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2184789121/10000000000 : ℝ)|^2113 ≤ (13432368822641/100000000000000 : ℝ)^1601
        have hw : |(-2184789121/10000000000 : ℝ)|=(2184789121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043915387/2000000000 : ℝ)|^2113 ≤ (42396991306813/100000000000000 : ℝ)^1601
        have hw : |(1043915387/2000000000 : ℝ)|=(1043915387/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5384199867/10000000000 : ℝ)|^2113 ≤ (44170639856211/100000000000000 : ℝ)^1601
        have hw : |(5384199867/10000000000 : ℝ)|=(5384199867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_box_9 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2645065841/5000000000 : ℝ)*x 0 + (-522680089/2500000000 : ℝ)*x 1 + (2692099729/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2645065841/5000000000 : ℝ)^2113 ≤ (21577495443273/50000000000000 : ℝ)^1601 := by
    have hnat : (2645065841 : ℕ)^2113*50000000000000^1601 ≤ 21577495443273^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2645065841 5000000000 21577495443273 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (522680089/2500000000 : ℝ)^2113 ≤ (6337186833307/50000000000000 : ℝ)^1601 := by
    have hnat : (522680089 : ℕ)^2113*50000000000000^1601 ≤ 6337186833307^1601*2500000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522680089 2500000000 6337186833307 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2692099729/5000000000 : ℝ)^2113 ≤ (539192327/1220703125 : ℝ)^1601 := by
    have hnat : (2692099729 : ℕ)^2113*1220703125^1601 ≤ 539192327^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692099729 5000000000 539192327 1220703125 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2645065841/5000000000 : ℝ), (-522680089/2500000000 : ℝ), (2692099729/5000000000 : ℝ)] ![(21577495443273/50000000000000 : ℝ), (6337186833307/50000000000000 : ℝ), (539192327/1220703125 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2645065841/5000000000 : ℝ)|^2113 ≤ (21577495443273/50000000000000 : ℝ)^1601
        have hw : |(2645065841/5000000000 : ℝ)|=(2645065841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-522680089/2500000000 : ℝ)|^2113 ≤ (6337186833307/50000000000000 : ℝ)^1601
        have hw : |(-522680089/2500000000 : ℝ)|=(522680089/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2692099729/5000000000 : ℝ)|^2113 ≤ (539192327/1220703125 : ℝ)^1601
        have hw : |(2692099729/5000000000 : ℝ)|=(2692099729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_box_10 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2645065617/5000000000 : ℝ)*x 0 + (215368017/400000000 : ℝ)*x 1 + (-2090719651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2645065617/5000000000 : ℝ)^2113 ≤ (1726199442527/4000000000000 : ℝ)^1601 := by
    have hnat : (2645065617 : ℕ)^2113*4000000000000^1601 ≤ 1726199442527^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2645065617 5000000000 1726199442527 4000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215368017/400000000 : ℝ)^2113 ≤ (11042661474463/25000000000000 : ℝ)^1601 := by
    have hnat : (215368017 : ℕ)^2113*25000000000000^1601 ≤ 11042661474463^1601*400000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215368017 400000000 11042661474463 25000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2090719651/10000000000 : ℝ)^2113 ≤ (12674368025981/100000000000000 : ℝ)^1601 := by
    have hnat : (2090719651 : ℕ)^2113*100000000000000^1601 ≤ 12674368025981^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2090719651 10000000000 12674368025981 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2645065617/5000000000 : ℝ), (215368017/400000000 : ℝ), (-2090719651/10000000000 : ℝ)] ![(1726199442527/4000000000000 : ℝ), (11042661474463/25000000000000 : ℝ), (12674368025981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2645065617/5000000000 : ℝ)|^2113 ≤ (1726199442527/4000000000000 : ℝ)^1601
        have hw : |(2645065617/5000000000 : ℝ)|=(2645065617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(215368017/400000000 : ℝ)|^2113 ≤ (11042661474463/25000000000000 : ℝ)^1601
        have hw : |(215368017/400000000 : ℝ)|=(215368017/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2090719651/10000000000 : ℝ)|^2113 ≤ (12674368025981/100000000000000 : ℝ)^1601
        have hw : |(-2090719651/10000000000 : ℝ)|=(2090719651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_box_11 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4476784869/10000000000 : ℝ)*x 0 + (857234299/2000000000 : ℝ)*x 1 + (857234267/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4476784869/10000000000 : ℝ)^2113 ≤ (34621444199763/100000000000000 : ℝ)^1601 := by
    have hnat : (4476784869 : ℕ)^2113*100000000000000^1601 ≤ 34621444199763^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4476784869 10000000000 34621444199763 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (857234299/2000000000 : ℝ)^2113 ≤ (817231967491/2500000000000 : ℝ)^1601 := by
    have hnat : (857234299 : ℕ)^2113*2500000000000^1601 ≤ 817231967491^1601*2000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      857234299 2000000000 817231967491 2500000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (857234267/2000000000 : ℝ)^2113 ≤ (4086159636141/12500000000000 : ℝ)^1601 := by
    have hnat : (857234267 : ℕ)^2113*12500000000000^1601 ≤ 4086159636141^1601*2000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      857234267 2000000000 4086159636141 12500000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4476784869/10000000000 : ℝ), (857234299/2000000000 : ℝ), (857234267/2000000000 : ℝ)] ![(34621444199763/100000000000000 : ℝ), (817231967491/2500000000000 : ℝ), (4086159636141/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4476784869/10000000000 : ℝ)|^2113 ≤ (34621444199763/100000000000000 : ℝ)^1601
        have hw : |(4476784869/10000000000 : ℝ)|=(4476784869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(857234299/2000000000 : ℝ)|^2113 ≤ (817231967491/2500000000000 : ℝ)^1601
        have hw : |(857234299/2000000000 : ℝ)|=(857234299/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(857234267/2000000000 : ℝ)|^2113 ≤ (4086159636141/12500000000000 : ℝ)^1601
        have hw : |(857234267/2000000000 : ℝ)|=(857234267/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_box_12 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1020583991/5000000000 : ℝ)*x 0 + (5436265097/10000000000 : ℝ)*x 1 + (5274367083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1020583991/5000000000 : ℝ)^2113 ≤ (9823536689/80000000000 : ℝ)^1601 := by
    have hnat : (1020583991 : ℕ)^2113*80000000000^1601 ≤ 9823536689^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1020583991 5000000000 9823536689 80000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5436265097/10000000000 : ℝ)^2113 ≤ (447352361359/1000000000000 : ℝ)^1601 := by
    have hnat : (5436265097 : ℕ)^2113*1000000000000^1601 ≤ 447352361359^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436265097 10000000000 447352361359 1000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5274367083/10000000000 : ℝ)^2113 ≤ (42985342978689/100000000000000 : ℝ)^1601 := by
    have hnat : (5274367083 : ℕ)^2113*100000000000000^1601 ≤ 42985342978689^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274367083 10000000000 42985342978689 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1020583991/5000000000 : ℝ), (5436265097/10000000000 : ℝ), (5274367083/10000000000 : ℝ)] ![(9823536689/80000000000 : ℝ), (447352361359/1000000000000 : ℝ), (42985342978689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1020583991/5000000000 : ℝ)|^2113 ≤ (9823536689/80000000000 : ℝ)^1601
        have hw : |(-1020583991/5000000000 : ℝ)|=(1020583991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5436265097/10000000000 : ℝ)|^2113 ≤ (447352361359/1000000000000 : ℝ)^1601
        have hw : |(5436265097/10000000000 : ℝ)|=(5436265097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5274367083/10000000000 : ℝ)|^2113 ≤ (42985342978689/100000000000000 : ℝ)^1601
        have hw : |(5274367083/10000000000 : ℝ)|=(5274367083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_box_13 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2683763989/5000000000 : ℝ)*x 0 + (-213432887/1000000000 : ℝ)*x 1 + (659295889/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2683763989/5000000000 : ℝ)^2113 ≤ (2749388596103/6250000000000 : ℝ)^1601 := by
    have hnat : (2683763989 : ℕ)^2113*6250000000000^1601 ≤ 2749388596103^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2683763989 5000000000 2749388596103 6250000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (213432887/1000000000 : ℝ)^2113 ≤ (6512219578449/50000000000000 : ℝ)^1601 := by
    have hnat : (213432887 : ℕ)^2113*50000000000000^1601 ≤ 6512219578449^1601*1000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213432887 1000000000 6512219578449 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (659295889/1250000000 : ℝ)^2113 ≤ (21492671645309/50000000000000 : ℝ)^1601 := by
    have hnat : (659295889 : ℕ)^2113*50000000000000^1601 ≤ 21492671645309^1601*1250000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659295889 1250000000 21492671645309 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2683763989/5000000000 : ℝ), (-213432887/1000000000 : ℝ), (659295889/1250000000 : ℝ)] ![(2749388596103/6250000000000 : ℝ), (6512219578449/50000000000000 : ℝ), (21492671645309/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2683763989/5000000000 : ℝ)|^2113 ≤ (2749388596103/6250000000000 : ℝ)^1601
        have hw : |(2683763989/5000000000 : ℝ)|=(2683763989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-213432887/1000000000 : ℝ)|^2113 ≤ (6512219578449/50000000000000 : ℝ)^1601
        have hw : |(-213432887/1000000000 : ℝ)|=(213432887/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(659295889/1250000000 : ℝ)|^2113 ≤ (21492671645309/50000000000000 : ℝ)^1601
        have hw : |(659295889/1250000000 : ℝ)|=(659295889/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_box_14 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5367527977/10000000000 : ℝ)*x 0 + (2637183547/5000000000 : ℝ)*x 1 + (-1067164447/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5367527977/10000000000 : ℝ)^2113 ≤ (43990217526831/100000000000000 : ℝ)^1601 := by
    have hnat : (5367527977 : ℕ)^2113*100000000000000^1601 ≤ 43990217526831^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5367527977 10000000000 43990217526831 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2637183547/5000000000 : ℝ)^2113 ≤ (42985343097007/100000000000000 : ℝ)^1601 := by
    have hnat : (2637183547 : ℕ)^2113*100000000000000^1601 ≤ 42985343097007^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637183547 5000000000 42985343097007 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1067164447/5000000000 : ℝ)^2113 ≤ (13024439350191/100000000000000 : ℝ)^1601 := by
    have hnat : (1067164447 : ℕ)^2113*100000000000000^1601 ≤ 13024439350191^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067164447 5000000000 13024439350191 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5367527977/10000000000 : ℝ), (2637183547/5000000000 : ℝ), (-1067164447/5000000000 : ℝ)] ![(43990217526831/100000000000000 : ℝ), (42985343097007/100000000000000 : ℝ), (13024439350191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5367527977/10000000000 : ℝ)|^2113 ≤ (43990217526831/100000000000000 : ℝ)^1601
        have hw : |(5367527977/10000000000 : ℝ)|=(5367527977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2637183547/5000000000 : ℝ)|^2113 ≤ (42985343097007/100000000000000 : ℝ)^1601
        have hw : |(2637183547/5000000000 : ℝ)|=(2637183547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1067164447/5000000000 : ℝ)|^2113 ≤ (13024439350191/100000000000000 : ℝ)^1601
        have hw : |(-1067164447/5000000000 : ℝ)|=(1067164447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_box_15 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2111366869/5000000000 : ℝ)*x 0 + (441319471/1000000000 : ℝ)*x 1 + (2206597391/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2111366869/5000000000 : ℝ)^2113 ≤ (16026124797397/50000000000000 : ℝ)^1601 := by
    have hnat : (2111366869 : ℕ)^2113*50000000000000^1601 ≤ 16026124797397^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111366869 5000000000 16026124797397 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (441319471/1000000000 : ℝ)^2113 ≤ (16986937415283/50000000000000 : ℝ)^1601 := by
    have hnat : (441319471 : ℕ)^2113*50000000000000^1601 ≤ 16986937415283^1601*1000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441319471 1000000000 16986937415283 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2206597391/5000000000 : ℝ)^2113 ≤ (33973875562097/100000000000000 : ℝ)^1601 := by
    have hnat : (2206597391 : ℕ)^2113*100000000000000^1601 ≤ 33973875562097^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2206597391 5000000000 33973875562097 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2111366869/5000000000 : ℝ), (441319471/1000000000 : ℝ), (2206597391/5000000000 : ℝ)] ![(16026124797397/50000000000000 : ℝ), (16986937415283/50000000000000 : ℝ), (33973875562097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2111366869/5000000000 : ℝ)|^2113 ≤ (16026124797397/50000000000000 : ℝ)^1601
        have hw : |(2111366869/5000000000 : ℝ)|=(2111366869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(441319471/1000000000 : ℝ)|^2113 ≤ (16986937415283/50000000000000 : ℝ)^1601
        have hw : |(441319471/1000000000 : ℝ)|=(441319471/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2206597391/5000000000 : ℝ)|^2113 ≤ (33973875562097/100000000000000 : ℝ)^1601
        have hw : |(2206597391/5000000000 : ℝ)|=(2206597391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1259_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15176157/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14113/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11499/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(249/400 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59391/100000 : ℝ) ∧ (80159/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (83383/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14113/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11499/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14113/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11499/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14113/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11499/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14113/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11499/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14113/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11499/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14113/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11499/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11499/100000 : ℝ) ^ (8451/2048 : ℝ) ≤ (1329985232870237/10000000000000000000 : ℝ) := by
    have hpowers : (11499/100000 : ℝ)^8451 ≤ (1329985232870237/10000000000000000000 : ℝ)^2048 := by
      have hnat : (11499 : ℕ)^8451*10000000000000000000^2048 ≤ 1329985232870237^2048*100000^8451 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11499 100000 1329985232870237 10000000000000000000 8451 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11499/100000 : ℝ)) (X := (1329985232870237/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14113/100000 : ℝ) ^ (8451/2048 : ℝ) ≤ (1238779758306383/4000000000000000000 : ℝ) := by
    have hpowers : (14113/100000 : ℝ)^8451 ≤ (1238779758306383/4000000000000000000 : ℝ)^2048 := by
      have hnat : (14113 : ℕ)^8451*4000000000000000000^2048 ≤ 1238779758306383^2048*100000^8451 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14113 100000 1238779758306383 4000000000000000000 8451 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14113/100000 : ℝ)) (X := (1238779758306383/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001329985232870237/5000000000000000000 : ℝ) ≤ (40002578189873/40000000000000 : ℝ) ^ (8451/2048 : ℝ) := by
    have hpowers : (5001329985232870237/5000000000000000000 : ℝ)^2048 ≤ (40002578189873/40000000000000 : ℝ)^8451 := by
      have hnat : (5001329985232870237 : ℕ)^2048*40000000000000^8451 ≤ 40002578189873^8451*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001329985232870237 5000000000000000000 40002578189873 40000000000000 2048 8451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (40002578189873/40000000000000 : ℝ)) (X := (5001329985232870237/5000000000000000000 : ℝ)) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20008853869257272389/20000000000000000000 : ℝ) ≤ (1000107263543139/1000000000000000 : ℝ) ^ (8451/2048 : ℝ) := by
    have hpowers : (20008853869257272389/20000000000000000000 : ℝ)^2048 ≤ (1000107263543139/1000000000000000 : ℝ)^8451 := by
      have hnat : (20008853869257272389 : ℕ)^2048*1000000000000000^8451 ≤ 1000107263543139^8451*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20008853869257272389 20000000000000000000 1000107263543139 1000000000000000 2048 8451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000107263543139/1000000000000000 : ℝ)) (X := (20008853869257272389/20000000000000000000 : ℝ)) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (2001238779758306383/2000000000000000000 : ℝ) ≤ (1000150072339453/1000000000000000 : ℝ) ^ (8451/2048 : ℝ) := by
    have hpowers : (2001238779758306383/2000000000000000000 : ℝ)^2048 ≤ (1000150072339453/1000000000000000 : ℝ)^8451 := by
      have hnat : (2001238779758306383 : ℕ)^2048*1000000000000000^8451 ≤ 1000150072339453^8451*2000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001238779758306383 2000000000000000000 1000150072339453 1000000000000000 2048 8451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000150072339453/1000000000000000 : ℝ)) (X := (2001238779758306383/2000000000000000000 : ℝ)) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1329985232870237/10000000000000000000 : ℝ) ≤ ((1306591984005285589/1307000000000000000 : ℝ)+2*(21404398157/13070000000000 : ℝ)*(11499/100000 : ℝ))^(8451/2048 : ℝ) := by
    rw [show (1306591984005285589/1307000000000000000 : ℝ)+2*(21404398157/13070000000000 : ℝ)*(11499/100000 : ℝ)=(40002578189873/40000000000000 : ℝ) by norm_num, show 1+2*(1329985232870237/10000000000000000000 : ℝ)=(5001329985232870237/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1238779758306383/4000000000000000000 : ℝ)+(1329985232870237/10000000000000000000 : ℝ) ≤ ((1306591984005285589/1307000000000000000 : ℝ)+(21404398157/13070000000000 : ℝ)*((14113/100000 : ℝ)+(11499/100000 : ℝ)))^(8451/2048 : ℝ) := by
    rw [show (1306591984005285589/1307000000000000000 : ℝ)+(21404398157/13070000000000 : ℝ)*((14113/100000 : ℝ)+(11499/100000 : ℝ))=(1000107263543139/1000000000000000 : ℝ) by norm_num, show 1+(1238779758306383/4000000000000000000 : ℝ)+(1329985232870237/10000000000000000000 : ℝ)=(20008853869257272389/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1238779758306383/4000000000000000000 : ℝ) ≤ ((1306591984005285589/1307000000000000000 : ℝ)+2*(21404398157/13070000000000 : ℝ)*(14113/100000 : ℝ))^(8451/2048 : ℝ) := by
    rw [show (1306591984005285589/1307000000000000000 : ℝ)+2*(21404398157/13070000000000 : ℝ)*(14113/100000 : ℝ)=(1000150072339453/1000000000000000 : ℝ) by norm_num, show 1+2*(1238779758306383/4000000000000000000 : ℝ)=(2001238779758306383/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1306591984005285589/1307000000000000000 : ℝ)*(X 1 0+X 2 0)+(21404398157/13070000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8451/2048 : ℝ)) (lo := (11499/100000 : ℝ)) (hi := (14113/100000 : ℝ)) (c := (1306591984005285589/1307000000000000000 : ℝ)) (alpha := (21404398157/13070000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1306591984005285589/1307000000000000000 : ℝ)*(X 0 1+X 2 1)+(21404398157/13070000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8451/2048 : ℝ)) (lo := (11499/100000 : ℝ)) (hi := (14113/100000 : ℝ)) (c := (1306591984005285589/1307000000000000000 : ℝ)) (alpha := (21404398157/13070000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1306591984005285589/1307000000000000000 : ℝ)*(X 0 2+X 1 2)+(21404398157/13070000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8451/2048 : ℝ)) (lo := (11499/100000 : ℝ)) (hi := (14113/100000 : ℝ)) (c := (1306591984005285589/1307000000000000000 : ℝ)) (alpha := (21404398157/13070000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1988989311/10000000000 : ℝ)*X 0 0+(537458633/1000000000 : ℝ)*X 0 1+(107491727/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5296908591/10000000000 : ℝ)*X 1 0+(-2094603311/10000000000 : ℝ)*X 1 1+(1074917267/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5296908543/10000000000 : ℝ)*X 2 0+(10497239/19531250 : ℝ)*X 2 1+(-209460333/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5568521/12500000 : ℝ)*X 0 0+(4297295991/10000000000 : ℝ)*X 0 1+(4297296001/10000000000 : ℝ)*X 0 2+(5568521/12500000 : ℝ)*X 1 0+(4297295991/10000000000 : ℝ)*X 1 1+(4297296001/10000000000 : ℝ)*X 1 2+(5568521/12500000 : ℝ)*X 2 0+(4297295991/10000000000 : ℝ)*X 2 1+(4297296001/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2236717463/10000000000 : ℝ)*X 0 0+(2641226493/5000000000 : ℝ)*X 0 1+(5282453031/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5361831757/10000000000 : ℝ)*X 1 0+(-1065587713/5000000000 : ℝ)*X 1 1+(2641226503/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2680915903/5000000000 : ℝ)*X 2 0+(2641226511/5000000000 : ℝ)*X 2 1+(-1065587669/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2120835841/5000000000 : ℝ)*X 0 0+(2201924263/5000000000 : ℝ)*X 0 1+(4403848619/10000000000 : ℝ)*X 0 2+(2120835841/5000000000 : ℝ)*X 1 0+(2201924263/5000000000 : ℝ)*X 1 1+(4403848619/10000000000 : ℝ)*X 1 2+(2120835841/5000000000 : ℝ)*X 2 0+(2201924263/5000000000 : ℝ)*X 2 1+(4403848619/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2184789121/10000000000 : ℝ)*X 0 0+(1043915387/2000000000 : ℝ)*X 0 1+(5384199867/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2645065841/5000000000 : ℝ)*X 1 0+(-522680089/2500000000 : ℝ)*X 1 1+(2692099729/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2645065617/5000000000 : ℝ)*X 2 0+(215368017/400000000 : ℝ)*X 2 1+(-2090719651/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4476784869/10000000000 : ℝ)*X 0 0+(857234299/2000000000 : ℝ)*X 0 1+(857234267/2000000000 : ℝ)*X 0 2+(4476784869/10000000000 : ℝ)*X 1 0+(857234299/2000000000 : ℝ)*X 1 1+(857234267/2000000000 : ℝ)*X 1 2+(4476784869/10000000000 : ℝ)*X 2 0+(857234299/2000000000 : ℝ)*X 2 1+(857234267/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1020583991/5000000000 : ℝ)*X 0 0+(5436265097/10000000000 : ℝ)*X 0 1+(5274367083/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2683763989/5000000000 : ℝ)*X 1 0+(-213432887/1000000000 : ℝ)*X 1 1+(659295889/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5367527977/10000000000 : ℝ)*X 2 0+(2637183547/5000000000 : ℝ)*X 2 1+(-1067164447/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2111366869/5000000000 : ℝ)*X 0 0+(441319471/1000000000 : ℝ)*X 0 1+(2206597391/5000000000 : ℝ)*X 0 2+(2111366869/5000000000 : ℝ)*X 1 0+(441319471/1000000000 : ℝ)*X 1 1+(2206597391/5000000000 : ℝ)*X 1 2+(2111366869/5000000000 : ℝ)*X 2 0+(441319471/1000000000 : ℝ)*X 2 1+(2206597391/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-249/400 : ℝ) ≤ (-635606459024444016619616266323/1021093750000000000000000000000 : ℝ) := by norm_num
    linear_combination (58005437/100000000000000 : ℝ)*(upper0) + (97518589/100000000000000 : ℝ)*(upper1) + (12466873/50000000000000 : ℝ)*(upper3) + (37894263/25000000000000 : ℝ)*(upper5) + (251057081337549/6250000000000 : ℝ)*(major0) + (251057081337549/6250000000000 : ℝ)*(major1) + (251057081337549/6250000000000 : ℝ)*(major2) + (408140569/10000000000000 : ℝ)*(sp2) + (7587793351/100000000000000 : ℝ)*(sp3) + (5407711971504411/100000000000000 : ℝ)*(sp4) + (5407717776652841/100000000000000 : ℝ)*(sp5) + (5407713695247151/100000000000000 : ℝ)*(sp6) + (132342522090621/5000000000000 : ℝ)*(sp7) + (580514843/10000000000000 : ℝ)*(sp8) + (661714507401443/25000000000000 : ℝ)*(f.failure) + (5407717776652841/100000000000000 : ℝ)*(f.sum) + (6176954922657/1307000000000000000000000000 : ℝ)*base65 + (53881762542037389/8168750000000000000000000000000 : ℝ)*base68 + (79761864162506139/8168750000000000000000000000000 : ℝ)*base70 + (69840272122087611/8168750000000000000000000000000 : ℝ)*base71 + (1127130377789/1307000000000000000000000000 : ℝ)*base74 + (82382493062287389/8168750000000000000000000000000 : ℝ)*base76 + (102234081372881361/8168750000000000000000000000000 : ℝ)*base77 + (554706934207174889/8168750000000000000000000000000 : ℝ)*base80 + (65661129969/10456000000000000000000000 : ℝ)*base81 + (994551/250000000000000000000 : ℝ)*base89 + (994551/250000000000000000000 : ℝ)*base91 + (994551/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (59391/100000 : ℝ) ≤ (1212927075550540509934363768113/2042187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (4153413/100000000000000 : ℝ)*(lower0) + (10527621/50000000000000 : ℝ)*(upper2) + (1282673/20000000000000 : ℝ)*(upper3) + (510373537619097/12500000000000 : ℝ)*(major0) + (510373537619097/12500000000000 : ℝ)*(major1) + (510373537619097/12500000000000 : ℝ)*(major2) + (5455780565963713/100000000000000 : ℝ)*(sp0) + (136394550519649/2500000000000 : ℝ)*(sp1) + (5455781230235409/100000000000000 : ℝ)*(sp2) + (1345197408591697/50000000000000 : ℝ)*(sp3) + (33473/160000000000 : ℝ)*(sp5) + (101433897/12500000000000 : ℝ)*(sp6) + (475613923/25000000000000 : ℝ)*(sp7) + (184467859/12500000000000 : ℝ)*(sp12) + (1345198359819543/50000000000000 : ℝ)*(f.failure) + (1091156408341317/20000000000000 : ℝ)*(f.sum) + (61281143623/261400000000000000000000000 : ℝ)*base66 + (45662753092693133/16337500000000000000000000000000 : ℝ)*base67 + (187355744694743133/16337500000000000000000000000000 : ℝ)*base69 + (188695305969405633/16337500000000000000000000000000 : ℝ)*base71 + (11137043095103/326750000000000000000000000 : ℝ)*base73 + (163491469830143133/16337500000000000000000000000000 : ℝ)*base75 + (101048662686830633/16337500000000000000000000000000 : ℝ)*base77 + (480460564139431867/16337500000000000000000000000000 : ℝ)*base80 + (2160985776869/326750000000000000000000000 : ℝ)*base81 + (3763749/500000000000000000000 : ℝ)*base90 + (3763749/500000000000000000000 : ℝ)*base92 + (3763749/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (80159/100000 : ℝ) ≤ (6548176343000437718101764216273/8168750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (373011939/100000000000000 : ℝ)*(lower3) + (204797331/100000000000000 : ℝ)*(upper4) + (2128231/800000000000 : ℝ)*(lower5) + (1137383263389369/25000000000000 : ℝ)*(major0) + (1137383263389369/25000000000000 : ℝ)*(major1) + (1137383263389369/25000000000000 : ℝ)*(major2) + (3703622819/12500000000000 : ℝ)*(sp0) + (159206908707/100000000000000 : ℝ)*(sp1) + (862922615683/100000000000000 : ℝ)*(sp2) + (348290980769/100000000000000 : ℝ)*(sp3) + (6074499763324279/100000000000000 : ℝ)*(sp8) + (1518592546349531/25000000000000 : ℝ)*(sp9) + (1518416617422787/25000000000000 : ℝ)*(sp10) + (374683498735623/12500000000000 : ℝ)*(sp11) + (2997816280865753/100000000000000 : ℝ)*(f.failure) + (6074529392306831/100000000000000 : ℝ)*(f.sum) + (1242568972091/1307000000000000000000000000 : ℝ)*base66 + (34783968507603341/32675000000000000000000000000000 : ℝ)*base67 + (208635871608046659/32675000000000000000000000000000 : ℝ)*base70 + (258884081260371659/32675000000000000000000000000000 : ℝ)*base72 + (2704095177049/653500000000000000000000000 : ℝ)*base73 + (213625329208246659/32675000000000000000000000000000 : ℝ)*base76 + (237313029647171659/32675000000000000000000000000000 : ℝ)*base78 + (163015066048221659/32675000000000000000000000000000 : ℝ)*base80 + (3936568881533/1307000000000000000000000000 : ℝ)*base82 + (3451221/1000000000000000000000 : ℝ)*base89 + (3451221/1000000000000000000000 : ℝ)*base91 + (3451221/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-83383/100000 : ℝ) ≤ (-27244537548704816860279124112081/32675000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6794231/100000000000000 : ℝ)*(lower1) + (5445639/50000000000000 : ℝ)*(upper3) + (3902991/20000000000000 : ℝ)*(lower4) + (21487941/100000000000000 : ℝ)*(upper5) + (4585091000526657/100000000000000 : ℝ)*(major0) + (4585091000526657/100000000000000 : ℝ)*(major1) + (4585091000526657/100000000000000 : ℝ)*(major2) + (280736923/100000000000000 : ℝ)*(sp4) + (1327016507/4000000000000 : ℝ)*(sp6) + (3058103563/20000000000000 : ℝ)*(sp7) + (1544182189672499/25000000000000 : ℝ)*(sp12) + (154418225985673/2500000000000 : ℝ)*(sp13) + (1235339172802849/20000000000000 : ℝ)*(sp14) + (755307782364923/25000000000000 : ℝ)*(sp15) + (1510623209988753/50000000000000 : ℝ)*(f.failure) + (154418225985673/2500000000000 : ℝ)*(f.sum) + (4342128757937/1307000000000000000000000000 : ℝ)*base66 + (762438192617345973/130700000000000000000000000000000 : ℝ)*base67 + (2719533738429654027/130700000000000000000000000000000 : ℝ)*base70 + (1072508719272854027/130700000000000000000000000000000 : ℝ)*base72 + (1591749318007/326750000000000000000000000 : ℝ)*base73 + (7066183089930954027/130700000000000000000000000000000 : ℝ)*base76 + (728533198381354027/130700000000000000000000000000000 : ℝ)*base78 + (1691017415654027/130700000000000000000000000000000 : ℝ)*base80 + (37436471986909/261400000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1237779/500000000000000000000 : ℝ)*base90 + (1237779/500000000000000000000 : ℝ)*base92 + (1237779/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1259_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15176157/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14113/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11499/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(249/400 : ℝ) ≤ X j i ∧ X j i ≤ -(59391/100000 : ℝ) else (80159/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83383/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1259_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1259_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15176157/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14113/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11499/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(249/400 : ℝ) ≤ X j i ∧ X j i ≤ -(59391/100000 : ℝ) else (80159/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83383/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1259_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15176157/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14113/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11499/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(249/400 : ℝ) ≤ X j i ∧ X j i ≤ -(59391/100000 : ℝ) else (80159/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83383/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1259_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
