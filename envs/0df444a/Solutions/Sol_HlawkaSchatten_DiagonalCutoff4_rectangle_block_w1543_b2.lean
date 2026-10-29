-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1543_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:08:08.675894+00:00
-- url     : https://prove2.me/submissions/06574a89-34f9-40ce-827d-de5b7041b60f

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
theorem support_rectangle_w1543_box_0 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-322985019/2000000000 : ℝ)*x 0 + (539949107/1000000000 : ℝ)*x 1 + (2699745389/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (322985019/2000000000 : ℝ)^4583 ≤ (1911397338693/20000000000000 : ℝ)^3559 := by
    have hnat : (322985019 : ℕ)^4583*20000000000000^3559 ≤ 1911397338693^3559*2000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      322985019 2000000000 1911397338693 20000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539949107/1000000000 : ℝ)^4583 ≤ (4522150822209/10000000000000 : ℝ)^3559 := by
    have hnat : (539949107 : ℕ)^4583*10000000000000^3559 ≤ 4522150822209^3559*1000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539949107 1000000000 4522150822209 10000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2699745389/5000000000 : ℝ)^4583 ≤ (22610752536457/50000000000000 : ℝ)^3559 := by
    have hnat : (2699745389 : ℕ)^4583*50000000000000^3559 ≤ 22610752536457^3559*5000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699745389 5000000000 22610752536457 50000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-322985019/2000000000 : ℝ), (539949107/1000000000 : ℝ), (2699745389/5000000000 : ℝ)] ![(1911397338693/20000000000000 : ℝ), (4522150822209/10000000000000 : ℝ), (22610752536457/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-322985019/2000000000 : ℝ)|^4583 ≤ (1911397338693/20000000000000 : ℝ)^3559
        have hw : |(-322985019/2000000000 : ℝ)|=(322985019/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539949107/1000000000 : ℝ)|^4583 ≤ (4522150822209/10000000000000 : ℝ)^3559
        have hw : |(539949107/1000000000 : ℝ)|=(539949107/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2699745389/5000000000 : ℝ)|^4583 ≤ (22610752536457/50000000000000 : ℝ)^3559
        have hw : |(2699745389/5000000000 : ℝ)|=(2699745389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_box_1 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2635531829/5000000000 : ℝ)*x 0 + (-1793288949/10000000000 : ℝ)*x 1 + (5399491177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2635531829/5000000000 : ℝ)^4583 ≤ (21920602157321/50000000000000 : ℝ)^3559 := by
    have hnat : (2635531829 : ℕ)^4583*50000000000000^3559 ≤ 21920602157321^3559*5000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635531829 5000000000 21920602157321 50000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1793288949/10000000000 : ℝ)^4583 ≤ (109372863011/1000000000000 : ℝ)^3559 := by
    have hnat : (1793288949 : ℕ)^4583*1000000000000^3559 ≤ 109372863011^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1793288949 10000000000 109372863011 1000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5399491177/10000000000 : ℝ)^4583 ≤ (45221509376069/100000000000000 : ℝ)^3559 := by
    have hnat : (5399491177 : ℕ)^4583*100000000000000^3559 ≤ 45221509376069^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399491177 10000000000 45221509376069 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2635531829/5000000000 : ℝ), (-1793288949/10000000000 : ℝ), (5399491177/10000000000 : ℝ)] ![(21920602157321/50000000000000 : ℝ), (109372863011/1000000000000 : ℝ), (45221509376069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2635531829/5000000000 : ℝ)|^4583 ≤ (21920602157321/50000000000000 : ℝ)^3559
        have hw : |(2635531829/5000000000 : ℝ)|=(2635531829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1793288949/10000000000 : ℝ)|^4583 ≤ (109372863011/1000000000000 : ℝ)^3559
        have hw : |(-1793288949/10000000000 : ℝ)|=(1793288949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5399491177/10000000000 : ℝ)|^4583 ≤ (45221509376069/100000000000000 : ℝ)^3559
        have hw : |(5399491177/10000000000 : ℝ)|=(5399491177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_box_2 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1054212707/2000000000 : ℝ)*x 0 + (5399491521/10000000000 : ℝ)*x 1 + (-448322161/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054212707/2000000000 : ℝ)^4583 ≤ (43841202997261/100000000000000 : ℝ)^3559 := by
    have hnat : (1054212707 : ℕ)^4583*100000000000000^3559 ≤ 43841202997261^3559*2000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054212707 2000000000 43841202997261 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5399491521/10000000000 : ℝ)^4583 ≤ (45221513086057/100000000000000 : ℝ)^3559 := by
    have hnat : (5399491521 : ℕ)^4583*100000000000000^3559 ≤ 45221513086057^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399491521 10000000000 45221513086057 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (448322161/2500000000 : ℝ)^4583 ≤ (2734320976421/25000000000000 : ℝ)^3559 := by
    have hnat : (448322161 : ℕ)^4583*25000000000000^3559 ≤ 2734320976421^3559*2500000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448322161 2500000000 2734320976421 25000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1054212707/2000000000 : ℝ), (5399491521/10000000000 : ℝ), (-448322161/2500000000 : ℝ)] ![(43841202997261/100000000000000 : ℝ), (45221513086057/100000000000000 : ℝ), (2734320976421/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1054212707/2000000000 : ℝ)|^4583 ≤ (43841202997261/100000000000000 : ℝ)^3559
        have hw : |(1054212707/2000000000 : ℝ)|=(1054212707/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5399491521/10000000000 : ℝ)|^4583 ≤ (45221513086057/100000000000000 : ℝ)^3559
        have hw : |(5399491521/10000000000 : ℝ)|=(5399491521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-448322161/2500000000 : ℝ)|^4583 ≤ (2734320976421/25000000000000 : ℝ)^3559
        have hw : |(-448322161/2500000000 : ℝ)|=(448322161/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_box_3 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1114321341/2500000000 : ℝ)*x 0 + (4161473119/10000000000 : ℝ)*x 1 + (2080736737/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1114321341/2500000000 : ℝ)^4583 ≤ (35326494221357/100000000000000 : ℝ)^3559 := by
    have hnat : (1114321341 : ℕ)^4583*100000000000000^3559 ≤ 35326494221357^3559*2500000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1114321341 2500000000 35326494221357 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4161473119/10000000000 : ℝ)^4583 ≤ (32336751103097/100000000000000 : ℝ)^3559 := by
    have hnat : (4161473119 : ℕ)^4583*100000000000000^3559 ≤ 32336751103097^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4161473119 10000000000 32336751103097 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2080736737/5000000000 : ℝ)^4583 ≤ (16168377327657/50000000000000 : ℝ)^3559 := by
    have hnat : (2080736737 : ℕ)^4583*50000000000000^3559 ≤ 16168377327657^3559*5000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080736737 5000000000 16168377327657 50000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1114321341/2500000000 : ℝ), (4161473119/10000000000 : ℝ), (2080736737/5000000000 : ℝ)] ![(35326494221357/100000000000000 : ℝ), (32336751103097/100000000000000 : ℝ), (16168377327657/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1114321341/2500000000 : ℝ)|^4583 ≤ (35326494221357/100000000000000 : ℝ)^3559
        have hw : |(1114321341/2500000000 : ℝ)|=(1114321341/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4161473119/10000000000 : ℝ)|^4583 ≤ (32336751103097/100000000000000 : ℝ)^3559
        have hw : |(4161473119/10000000000 : ℝ)|=(4161473119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2080736737/5000000000 : ℝ)|^4583 ≤ (16168377327657/50000000000000 : ℝ)^3559
        have hw : |(2080736737/5000000000 : ℝ)|=(2080736737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_box_4 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2036836091/10000000000 : ℝ)*x 0 + (524449573/1000000000 : ℝ)*x 1 + (5244494853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2036836091/10000000000 : ℝ)^4583 ≤ (6443147183519/50000000000000 : ℝ)^3559 := by
    have hnat : (2036836091 : ℕ)^4583*50000000000000^3559 ≤ 6443147183519^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2036836091 10000000000 6443147183519 50000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524449573/1000000000 : ℝ)^4583 ≤ (2722303593739/6250000000000 : ℝ)^3559 := by
    have hnat : (524449573 : ℕ)^4583*6250000000000^3559 ≤ 2722303593739^3559*1000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524449573 1000000000 2722303593739 6250000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244494853/10000000000 : ℝ)^4583 ≤ (43556848120441/100000000000000 : ℝ)^3559 := by
    have hnat : (5244494853 : ℕ)^4583*100000000000000^3559 ≤ 43556848120441^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244494853 10000000000 43556848120441 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2036836091/10000000000 : ℝ), (524449573/1000000000 : ℝ), (5244494853/10000000000 : ℝ)] ![(6443147183519/50000000000000 : ℝ), (2722303593739/6250000000000 : ℝ), (43556848120441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2036836091/10000000000 : ℝ)|^4583 ≤ (6443147183519/50000000000000 : ℝ)^3559
        have hw : |(-2036836091/10000000000 : ℝ)|=(2036836091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524449573/1000000000 : ℝ)|^4583 ≤ (2722303593739/6250000000000 : ℝ)^3559
        have hw : |(524449573/1000000000 : ℝ)|=(524449573/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244494853/10000000000 : ℝ)|^4583 ≤ (43556848120441/100000000000000 : ℝ)^3559
        have hw : |(5244494853/10000000000 : ℝ)|=(5244494853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_box_5 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5378720029/10000000000 : ℝ)*x 0 + (-1857671777/10000000000 : ℝ)*x 1 + (5244495291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378720029/10000000000 : ℝ)^4583 ≤ (22498809878721/50000000000000 : ℝ)^3559 := by
    have hnat : (5378720029 : ℕ)^4583*50000000000000^3559 ≤ 22498809878721^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378720029 10000000000 22498809878721 50000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1857671777/10000000000 : ℝ)^4583 ≤ (5722763713819/50000000000000 : ℝ)^3559 := by
    have hnat : (1857671777 : ℕ)^4583*50000000000000^3559 ≤ 5722763713819^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1857671777 10000000000 5722763713819 50000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244495291/10000000000 : ℝ)^4583 ≤ (8711370560957/20000000000000 : ℝ)^3559 := by
    have hnat : (5244495291 : ℕ)^4583*20000000000000^3559 ≤ 8711370560957^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244495291 10000000000 8711370560957 20000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378720029/10000000000 : ℝ), (-1857671777/10000000000 : ℝ), (5244495291/10000000000 : ℝ)] ![(22498809878721/50000000000000 : ℝ), (5722763713819/50000000000000 : ℝ), (8711370560957/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378720029/10000000000 : ℝ)|^4583 ≤ (22498809878721/50000000000000 : ℝ)^3559
        have hw : |(5378720029/10000000000 : ℝ)|=(5378720029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1857671777/10000000000 : ℝ)|^4583 ≤ (5722763713819/50000000000000 : ℝ)^3559
        have hw : |(-1857671777/10000000000 : ℝ)|=(1857671777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244495291/10000000000 : ℝ)|^4583 ≤ (8711370560957/20000000000000 : ℝ)^3559
        have hw : |(5244495291/10000000000 : ℝ)|=(5244495291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_box_6 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5378720667/10000000000 : ℝ)*x 0 + (5244494817/10000000000 : ℝ)*x 1 + (-464417887/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378720667/10000000000 : ℝ)^4583 ≤ (899952532611/2000000000000 : ℝ)^3559 := by
    have hnat : (5378720667 : ℕ)^4583*2000000000000^3559 ≤ 899952532611^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378720667 10000000000 899952532611 2000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244494817/10000000000 : ℝ)^4583 ≤ (43556847735427/100000000000000 : ℝ)^3559 := by
    have hnat : (5244494817 : ℕ)^4583*100000000000000^3559 ≤ 43556847735427^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244494817 10000000000 43556847735427 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (464417887/2500000000 : ℝ)^4583 ≤ (11445525610767/100000000000000 : ℝ)^3559 := by
    have hnat : (464417887 : ℕ)^4583*100000000000000^3559 ≤ 11445525610767^3559*2500000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      464417887 2500000000 11445525610767 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378720667/10000000000 : ℝ), (5244494817/10000000000 : ℝ), (-464417887/2500000000 : ℝ)] ![(899952532611/2000000000000 : ℝ), (43556847735427/100000000000000 : ℝ), (11445525610767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378720667/10000000000 : ℝ)|^4583 ≤ (899952532611/2000000000000 : ℝ)^3559
        have hw : |(5378720667/10000000000 : ℝ)|=(5378720667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244494817/10000000000 : ℝ)|^4583 ≤ (43556847735427/100000000000000 : ℝ)^3559
        have hw : |(5244494817/10000000000 : ℝ)|=(5244494817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-464417887/2500000000 : ℝ)|^4583 ≤ (11445525610767/100000000000000 : ℝ)^3559
        have hw : |(-464417887/2500000000 : ℝ)|=(464417887/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_box_7 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4051247997/10000000000 : ℝ)*x 0 + (2182180461/5000000000 : ℝ)*x 1 + (4364362061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4051247997/10000000000 : ℝ)^4583 ≤ (6247608176061/20000000000000 : ℝ)^3559 := by
    have hnat : (4051247997 : ℕ)^4583*20000000000000^3559 ≤ 6247608176061^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4051247997 10000000000 6247608176061 20000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2182180461/5000000000 : ℝ)^4583 ≤ (4297621721561/12500000000000 : ℝ)^3559 := by
    have hnat : (2182180461 : ℕ)^4583*12500000000000^3559 ≤ 4297621721561^3559*5000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182180461 5000000000 4297621721561 12500000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4364362061/10000000000 : ℝ)^4583 ≤ (1375239413071/4000000000000 : ℝ)^3559 := by
    have hnat : (4364362061 : ℕ)^4583*4000000000000^3559 ≤ 1375239413071^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364362061 10000000000 1375239413071 4000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4051247997/10000000000 : ℝ), (2182180461/5000000000 : ℝ), (4364362061/10000000000 : ℝ)] ![(6247608176061/20000000000000 : ℝ), (4297621721561/12500000000000 : ℝ), (1375239413071/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4051247997/10000000000 : ℝ)|^4583 ≤ (6247608176061/20000000000000 : ℝ)^3559
        have hw : |(4051247997/10000000000 : ℝ)|=(4051247997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2182180461/5000000000 : ℝ)|^4583 ≤ (4297621721561/12500000000000 : ℝ)^3559
        have hw : |(2182180461/5000000000 : ℝ)|=(2182180461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4364362061/10000000000 : ℝ)|^4583 ≤ (1375239413071/4000000000000 : ℝ)^3559
        have hw : |(4364362061/10000000000 : ℝ)|=(4364362061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_box_8 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-389504851/2000000000 : ℝ)*x 0 + (1027115619/2000000000 : ℝ)*x 1 + (10585643/19531250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (389504851/2000000000 : ℝ)^4583 ≤ (1216331588597/10000000000000 : ℝ)^3559 := by
    have hnat : (389504851 : ℕ)^4583*10000000000000^3559 ≤ 1216331588597^3559*2000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389504851 2000000000 1216331588597 10000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1027115619/2000000000 : ℝ)^4583 ≤ (42395497355549/100000000000000 : ℝ)^3559 := by
    have hnat : (1027115619 : ℕ)^4583*100000000000000^3559 ≤ 42395497355549^3559*2000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027115619 2000000000 42395497355549 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10585643/19531250 : ℝ)^4583 ≤ (11360296686357/25000000000000 : ℝ)^3559 := by
    have hnat : (10585643 : ℕ)^4583*25000000000000^3559 ≤ 11360296686357^3559*19531250^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10585643 19531250 11360296686357 25000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-389504851/2000000000 : ℝ), (1027115619/2000000000 : ℝ), (10585643/19531250 : ℝ)] ![(1216331588597/10000000000000 : ℝ), (42395497355549/100000000000000 : ℝ), (11360296686357/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-389504851/2000000000 : ℝ)|^4583 ≤ (1216331588597/10000000000000 : ℝ)^3559
        have hw : |(-389504851/2000000000 : ℝ)|=(389504851/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1027115619/2000000000 : ℝ)|^4583 ≤ (42395497355549/100000000000000 : ℝ)^3559
        have hw : |(1027115619/2000000000 : ℝ)|=(1027115619/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(10585643/19531250 : ℝ)|^4583 ≤ (11360296686357/25000000000000 : ℝ)^3559
        have hw : |(10585643/19531250 : ℝ)|=(10585643/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_box_9 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256918993/10000000000 : ℝ)*x 0 + (-1784594061/10000000000 : ℝ)*x 1 + (1354962297/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256918993/10000000000 : ℝ)^4583 ≤ (43689767678553/100000000000000 : ℝ)^3559 := by
    have hnat : (5256918993 : ℕ)^4583*100000000000000^3559 ≤ 43689767678553^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256918993 10000000000 43689767678553 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1784594061/10000000000 : ℝ)^4583 ≤ (2173809173237/20000000000000 : ℝ)^3559 := by
    have hnat : (1784594061 : ℕ)^4583*20000000000000^3559 ≤ 2173809173237^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1784594061 10000000000 2173809173237 20000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1354962297/2500000000 : ℝ)^4583 ≤ (72705898309/160000000000 : ℝ)^3559 := by
    have hnat : (1354962297 : ℕ)^4583*160000000000^3559 ≤ 72705898309^3559*2500000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354962297 2500000000 72705898309 160000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256918993/10000000000 : ℝ), (-1784594061/10000000000 : ℝ), (1354962297/2500000000 : ℝ)] ![(43689767678553/100000000000000 : ℝ), (2173809173237/20000000000000 : ℝ), (72705898309/160000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256918993/10000000000 : ℝ)|^4583 ≤ (43689767678553/100000000000000 : ℝ)^3559
        have hw : |(5256918993/10000000000 : ℝ)|=(5256918993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1784594061/10000000000 : ℝ)|^4583 ≤ (2173809173237/20000000000000 : ℝ)^3559
        have hw : |(-1784594061/10000000000 : ℝ)|=(1784594061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1354962297/2500000000 : ℝ)|^4583 ≤ (72705898309/160000000000 : ℝ)^3559
        have hw : |(1354962297/2500000000 : ℝ)|=(1354962297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_box_10 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256919133/10000000000 : ℝ)*x 0 + (270992449/500000000 : ℝ)*x 1 + (-446148539/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256919133/10000000000 : ℝ)^4583 ≤ (10922442294213/25000000000000 : ℝ)^3559 := by
    have hnat : (5256919133 : ℕ)^4583*25000000000000^3559 ≤ 10922442294213^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256919133 10000000000 10922442294213 25000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270992449/500000000 : ℝ)^4583 ≤ (22720592098723/50000000000000 : ℝ)^3559 := by
    have hnat : (270992449 : ℕ)^4583*50000000000000^3559 ≤ 22720592098723^3559*500000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270992449 500000000 22720592098723 50000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (446148539/2500000000 : ℝ)^4583 ≤ (1358630826407/12500000000000 : ℝ)^3559 := by
    have hnat : (446148539 : ℕ)^4583*12500000000000^3559 ≤ 1358630826407^3559*2500000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      446148539 2500000000 1358630826407 12500000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256919133/10000000000 : ℝ), (270992449/500000000 : ℝ), (-446148539/2500000000 : ℝ)] ![(10922442294213/25000000000000 : ℝ), (22720592098723/50000000000000 : ℝ), (1358630826407/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256919133/10000000000 : ℝ)|^4583 ≤ (10922442294213/25000000000000 : ℝ)^3559
        have hw : |(5256919133/10000000000 : ℝ)|=(5256919133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270992449/500000000 : ℝ)|^4583 ≤ (22720592098723/50000000000000 : ℝ)^3559
        have hw : |(270992449/500000000 : ℝ)|=(270992449/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-446148539/2500000000 : ℝ)|^4583 ≤ (1358630826407/12500000000000 : ℝ)^3559
        have hw : |(-446148539/2500000000 : ℝ)|=(446148539/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_box_11 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (450947/1000000 : ℝ)*x 0 + (826958179/2000000000 : ℝ)*x 1 + (826958209/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (450947/1000000 : ℝ)^4583 ≤ (35859980762087/100000000000000 : ℝ)^3559 := by
    have hnat : (450947 : ℕ)^4583*100000000000000^3559 ≤ 35859980762087^3559*1000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450947 1000000 35859980762087 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (826958179/2000000000 : ℝ)^4583 ≤ (6414001772201/20000000000000 : ℝ)^3559 := by
    have hnat : (826958179 : ℕ)^4583*20000000000000^3559 ≤ 6414001772201^3559*2000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      826958179 2000000000 6414001772201 20000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (826958209/2000000000 : ℝ)^4583 ≤ (16035005179583/50000000000000 : ℝ)^3559 := by
    have hnat : (826958209 : ℕ)^4583*50000000000000^3559 ≤ 16035005179583^3559*2000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      826958209 2000000000 16035005179583 50000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(450947/1000000 : ℝ), (826958179/2000000000 : ℝ), (826958209/2000000000 : ℝ)] ![(35859980762087/100000000000000 : ℝ), (6414001772201/20000000000000 : ℝ), (16035005179583/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(450947/1000000 : ℝ)|^4583 ≤ (35859980762087/100000000000000 : ℝ)^3559
        have hw : |(450947/1000000 : ℝ)|=(450947/1000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(826958179/2000000000 : ℝ)|^4583 ≤ (6414001772201/20000000000000 : ℝ)^3559
        have hw : |(826958179/2000000000 : ℝ)|=(826958179/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(826958209/2000000000 : ℝ)|^4583 ≤ (16035005179583/50000000000000 : ℝ)^3559
        have hw : |(826958209/2000000000 : ℝ)|=(826958209/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_box_12 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-426006771/2500000000 : ℝ)*x 0 + (688125823/1250000000 : ℝ)*x 1 + (5229450591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (426006771/2500000000 : ℝ)^4583 ≤ (1280164992611/12500000000000 : ℝ)^3559 := by
    have hnat : (426006771 : ℕ)^4583*12500000000000^3559 ≤ 1280164992611^3559*2500000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426006771 2500000000 1280164992611 12500000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (688125823/1250000000 : ℝ)^4583 ≤ (46362661588387/100000000000000 : ℝ)^3559 := by
    have hnat : (688125823 : ℕ)^4583*100000000000000^3559 ≤ 46362661588387^3559*1250000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      688125823 1250000000 46362661588387 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5229450591/10000000000 : ℝ)^4583 ≤ (43396018455437/100000000000000 : ℝ)^3559 := by
    have hnat : (5229450591 : ℕ)^4583*100000000000000^3559 ≤ 43396018455437^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229450591 10000000000 43396018455437 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-426006771/2500000000 : ℝ), (688125823/1250000000 : ℝ), (5229450591/10000000000 : ℝ)] ![(1280164992611/12500000000000 : ℝ), (46362661588387/100000000000000 : ℝ), (43396018455437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-426006771/2500000000 : ℝ)|^4583 ≤ (1280164992611/12500000000000 : ℝ)^3559
        have hw : |(-426006771/2500000000 : ℝ)|=(426006771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(688125823/1250000000 : ℝ)|^4583 ≤ (46362661588387/100000000000000 : ℝ)^3559
        have hw : |(688125823/1250000000 : ℝ)|=(688125823/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5229450591/10000000000 : ℝ)|^4583 ≤ (43396018455437/100000000000000 : ℝ)^3559
        have hw : |(5229450591/10000000000 : ℝ)|=(5229450591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_box_13 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5389170677/10000000000 : ℝ)*x 0 + (-1863747063/10000000000 : ℝ)*x 1 + (209178007/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5389170677/10000000000 : ℝ)^4583 ≤ (45110234957021/100000000000000 : ℝ)^3559 := by
    have hnat : (5389170677 : ℕ)^4583*100000000000000^3559 ≤ 45110234957021^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389170677 10000000000 45110234957021 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1863747063/10000000000 : ℝ)^4583 ≤ (459750040731/4000000000000 : ℝ)^3559 := by
    have hnat : (1863747063 : ℕ)^4583*4000000000000^3559 ≤ 459750040731^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1863747063 10000000000 459750040731 4000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209178007/400000000 : ℝ)^4583 ≤ (8679202802011/20000000000000 : ℝ)^3559 := by
    have hnat : (209178007 : ℕ)^4583*20000000000000^3559 ≤ 8679202802011^3559*400000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209178007 400000000 8679202802011 20000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5389170677/10000000000 : ℝ), (-1863747063/10000000000 : ℝ), (209178007/400000000 : ℝ)] ![(45110234957021/100000000000000 : ℝ), (459750040731/4000000000000 : ℝ), (8679202802011/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5389170677/10000000000 : ℝ)|^4583 ≤ (45110234957021/100000000000000 : ℝ)^3559
        have hw : |(5389170677/10000000000 : ℝ)|=(5389170677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1863747063/10000000000 : ℝ)|^4583 ≤ (459750040731/4000000000000 : ℝ)^3559
        have hw : |(-1863747063/10000000000 : ℝ)|=(1863747063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(209178007/400000000 : ℝ)|^4583 ≤ (8679202802011/20000000000000 : ℝ)^3559
        have hw : |(209178007/400000000 : ℝ)|=(209178007/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_box_14 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5389170631/10000000000 : ℝ)*x 0 + (5229450249/10000000000 : ℝ)*x 1 + (-74549881/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5389170631/10000000000 : ℝ)^4583 ≤ (45110234461191/100000000000000 : ℝ)^3559 := by
    have hnat : (5389170631 : ℕ)^4583*100000000000000^3559 ≤ 45110234461191^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389170631 10000000000 45110234461191 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5229450249/10000000000 : ℝ)^4583 ≤ (2169800740041/5000000000000 : ℝ)^3559 := by
    have hnat : (5229450249 : ℕ)^4583*5000000000000^3559 ≤ 2169800740041^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229450249 10000000000 2169800740041 5000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (74549881/400000000 : ℝ)^4583 ≤ (5746875358251/50000000000000 : ℝ)^3559 := by
    have hnat : (74549881 : ℕ)^4583*50000000000000^3559 ≤ 5746875358251^3559*400000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74549881 400000000 5746875358251 50000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5389170631/10000000000 : ℝ), (5229450249/10000000000 : ℝ), (-74549881/400000000 : ℝ)] ![(45110234461191/100000000000000 : ℝ), (2169800740041/5000000000000 : ℝ), (5746875358251/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5389170631/10000000000 : ℝ)|^4583 ≤ (45110234461191/100000000000000 : ℝ)^3559
        have hw : |(5389170631/10000000000 : ℝ)|=(5389170631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5229450249/10000000000 : ℝ)|^4583 ≤ (2169800740041/5000000000000 : ℝ)^3559
        have hw : |(5229450249/10000000000 : ℝ)|=(5229450249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-74549881/400000000 : ℝ)|^4583 ≤ (5746875358251/50000000000000 : ℝ)^3559
        have hw : |(-74549881/400000000 : ℝ)|=(74549881/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_box_15 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2005486671/5000000000 : ℝ)*x 0 + (4384031491/10000000000 : ℝ)*x 1 + (4384030649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2005486671/5000000000 : ℝ)^4583 ≤ (30838716682729/100000000000000 : ℝ)^3559 := by
    have hnat : (2005486671 : ℕ)^4583*100000000000000^3559 ≤ 30838716682729^3559*5000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2005486671 5000000000 30838716682729 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4384031491/10000000000 : ℝ)^4583 ≤ (6916129185771/20000000000000 : ℝ)^3559 := by
    have hnat : (4384031491 : ℕ)^4583*20000000000000^3559 ≤ 6916129185771^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4384031491 10000000000 6916129185771 20000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4384030649/10000000000 : ℝ)^4583 ≤ (34580637376349/100000000000000 : ℝ)^3559 := by
    have hnat : (4384030649 : ℕ)^4583*100000000000000^3559 ≤ 34580637376349^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4384030649 10000000000 34580637376349 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2005486671/5000000000 : ℝ), (4384031491/10000000000 : ℝ), (4384030649/10000000000 : ℝ)] ![(30838716682729/100000000000000 : ℝ), (6916129185771/20000000000000 : ℝ), (34580637376349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2005486671/5000000000 : ℝ)|^4583 ≤ (30838716682729/100000000000000 : ℝ)^3559
        have hw : |(2005486671/5000000000 : ℝ)|=(2005486671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4384031491/10000000000 : ℝ)|^4583 ≤ (6916129185771/20000000000000 : ℝ)^3559
        have hw : |(4384031491/10000000000 : ℝ)|=(4384031491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4384030649/10000000000 : ℝ)|^4583 ≤ (34580637376349/100000000000000 : ℝ)^3559
        have hw : |(4384030649/10000000000 : ℝ)|=(4384030649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1543_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165860297/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1103/10000 : ℝ)*pair X i i ≤ pair X i h) :
    -(7973/12500 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29387/50000 : ℝ) ∧ (40323/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (86199/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1103/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1103/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1103/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1103/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1103/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1103/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1103/10000 : ℝ) ^ (4581/1024 : ℝ) ≤ (52099600958433/1000000000000000000 : ℝ) := by
    have hpowers : (1103/10000 : ℝ)^4581 ≤ (52099600958433/1000000000000000000 : ℝ)^1024 := by
      have hnat : (1103 : ℕ)^4581*1000000000000000000^1024 ≤ 52099600958433^1024*10000^4581 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1103 10000 52099600958433 1000000000000000000 4581 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1103/10000 : ℝ)) (X := (52099600958433/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4581 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3097/20000 : ℝ) ^ (4581/1024 : ℝ) ≤ (2970778140568721/12500000000000000000 : ℝ) := by
    have hpowers : (3097/20000 : ℝ)^4581 ≤ (2970778140568721/12500000000000000000 : ℝ)^1024 := by
      have hnat : (3097 : ℕ)^4581*12500000000000000000^1024 ≤ 2970778140568721^1024*20000^4581 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3097 20000 2970778140568721 12500000000000000000 4581 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3097/20000 : ℝ)) (X := (2970778140568721/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4581 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (500052099600958433/500000000000000000 : ℝ) ≤ (5000116454558637/5000000000000000 : ℝ) ^ (4581/1024 : ℝ) := by
    have hpowers : (500052099600958433/500000000000000000 : ℝ)^1024 ≤ (5000116454558637/5000000000000000 : ℝ)^4581 := by
      have hnat : (500052099600958433 : ℕ)^1024*5000000000000000^4581 ≤ 5000116454558637^4581*500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500052099600958433 500000000000000000 5000116454558637 5000000000000000 1024 4581 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000116454558637/5000000000000000 : ℝ)) (X := (500052099600958433/500000000000000000 : ℝ)) (by norm_num) 4581 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25007244046305098267/25000000000000000000 : ℝ) ≤ (10000647637553331/10000000000000000 : ℝ) ^ (4581/1024 : ℝ) := by
    have hpowers : (25007244046305098267/25000000000000000000 : ℝ)^1024 ≤ (10000647637553331/10000000000000000 : ℝ)^4581 := by
      have hnat : (25007244046305098267 : ℕ)^1024*10000000000000000^4581 ≤ 10000647637553331^4581*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007244046305098267 25000000000000000000 10000647637553331 10000000000000000 1024 4581 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000647637553331/10000000000000000 : ℝ)) (X := (25007244046305098267/25000000000000000000 : ℝ)) (by norm_num) 4581 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6252970778140568721/6250000000000000000 : ℝ) ≤ (2500265591497347/2500000000000000 : ℝ) ^ (4581/1024 : ℝ) := by
    have hpowers : (6252970778140568721/6250000000000000000 : ℝ)^1024 ≤ (2500265591497347/2500000000000000 : ℝ)^4581 := by
      have hnat : (6252970778140568721 : ℕ)^1024*2500000000000000^4581 ≤ 2500265591497347^4581*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252970778140568721 6250000000000000000 2500265591497347 2500000000000000 1024 4581 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500265591497347/2500000000000000 : ℝ)) (X := (6252970778140568721/6250000000000000000 : ℝ)) (by norm_num) 4581 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(52099600958433/1000000000000000000 : ℝ) ≤ ((59389184934424051/59400000000000000 : ℝ)+2*(138242812019/148500000000000 : ℝ)*(1103/10000 : ℝ))^(4581/1024 : ℝ) := by
    rw [show (59389184934424051/59400000000000000 : ℝ)+2*(138242812019/148500000000000 : ℝ)*(1103/10000 : ℝ)=(5000116454558637/5000000000000000 : ℝ) by norm_num, show 1+2*(52099600958433/1000000000000000000 : ℝ)=(500052099600958433/500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2970778140568721/12500000000000000000 : ℝ)+(52099600958433/1000000000000000000 : ℝ) ≤ ((59389184934424051/59400000000000000 : ℝ)+(138242812019/148500000000000 : ℝ)*((3097/20000 : ℝ)+(1103/10000 : ℝ)))^(4581/1024 : ℝ) := by
    rw [show (59389184934424051/59400000000000000 : ℝ)+(138242812019/148500000000000 : ℝ)*((3097/20000 : ℝ)+(1103/10000 : ℝ))=(10000647637553331/10000000000000000 : ℝ) by norm_num, show 1+(2970778140568721/12500000000000000000 : ℝ)+(52099600958433/1000000000000000000 : ℝ)=(25007244046305098267/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2970778140568721/12500000000000000000 : ℝ) ≤ ((59389184934424051/59400000000000000 : ℝ)+2*(138242812019/148500000000000 : ℝ)*(3097/20000 : ℝ))^(4581/1024 : ℝ) := by
    rw [show (59389184934424051/59400000000000000 : ℝ)+2*(138242812019/148500000000000 : ℝ)*(3097/20000 : ℝ)=(2500265591497347/2500000000000000 : ℝ) by norm_num, show 1+2*(2970778140568721/12500000000000000000 : ℝ)=(6252970778140568721/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (59389184934424051/59400000000000000 : ℝ)*(X 1 0+X 2 0)+(138242812019/148500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4581/1024 : ℝ)) (lo := (1103/10000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (59389184934424051/59400000000000000 : ℝ)) (alpha := (138242812019/148500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (59389184934424051/59400000000000000 : ℝ)*(X 0 1+X 2 1)+(138242812019/148500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4581/1024 : ℝ)) (lo := (1103/10000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (59389184934424051/59400000000000000 : ℝ)) (alpha := (138242812019/148500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (59389184934424051/59400000000000000 : ℝ)*(X 0 2+X 1 2)+(138242812019/148500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4581/1024 : ℝ)) (lo := (1103/10000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (59389184934424051/59400000000000000 : ℝ)) (alpha := (138242812019/148500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-322985019/2000000000 : ℝ)*X 0 0+(539949107/1000000000 : ℝ)*X 0 1+(2699745389/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2635531829/5000000000 : ℝ)*X 1 0+(-1793288949/10000000000 : ℝ)*X 1 1+(5399491177/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1054212707/2000000000 : ℝ)*X 2 0+(5399491521/10000000000 : ℝ)*X 2 1+(-448322161/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1114321341/2500000000 : ℝ)*X 0 0+(4161473119/10000000000 : ℝ)*X 0 1+(2080736737/5000000000 : ℝ)*X 0 2+(1114321341/2500000000 : ℝ)*X 1 0+(4161473119/10000000000 : ℝ)*X 1 1+(2080736737/5000000000 : ℝ)*X 1 2+(1114321341/2500000000 : ℝ)*X 2 0+(4161473119/10000000000 : ℝ)*X 2 1+(2080736737/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2036836091/10000000000 : ℝ)*X 0 0+(524449573/1000000000 : ℝ)*X 0 1+(5244494853/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5378720029/10000000000 : ℝ)*X 1 0+(-1857671777/10000000000 : ℝ)*X 1 1+(5244495291/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5378720667/10000000000 : ℝ)*X 2 0+(5244494817/10000000000 : ℝ)*X 2 1+(-464417887/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4051247997/10000000000 : ℝ)*X 0 0+(2182180461/5000000000 : ℝ)*X 0 1+(4364362061/10000000000 : ℝ)*X 0 2+(4051247997/10000000000 : ℝ)*X 1 0+(2182180461/5000000000 : ℝ)*X 1 1+(4364362061/10000000000 : ℝ)*X 1 2+(4051247997/10000000000 : ℝ)*X 2 0+(2182180461/5000000000 : ℝ)*X 2 1+(4364362061/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-389504851/2000000000 : ℝ)*X 0 0+(1027115619/2000000000 : ℝ)*X 0 1+(10585643/19531250 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5256918993/10000000000 : ℝ)*X 1 0+(-1784594061/10000000000 : ℝ)*X 1 1+(1354962297/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5256919133/10000000000 : ℝ)*X 2 0+(270992449/500000000 : ℝ)*X 2 1+(-446148539/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((450947/1000000 : ℝ)*X 0 0+(826958179/2000000000 : ℝ)*X 0 1+(826958209/2000000000 : ℝ)*X 0 2+(450947/1000000 : ℝ)*X 1 0+(826958179/2000000000 : ℝ)*X 1 1+(826958209/2000000000 : ℝ)*X 1 2+(450947/1000000 : ℝ)*X 2 0+(826958179/2000000000 : ℝ)*X 2 1+(826958209/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-426006771/2500000000 : ℝ)*X 0 0+(688125823/1250000000 : ℝ)*X 0 1+(5229450591/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5389170677/10000000000 : ℝ)*X 1 0+(-1863747063/10000000000 : ℝ)*X 1 1+(209178007/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5389170631/10000000000 : ℝ)*X 2 0+(5229450249/10000000000 : ℝ)*X 2 1+(-74549881/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2005486671/5000000000 : ℝ)*X 0 0+(4384031491/10000000000 : ℝ)*X 0 1+(4384030649/10000000000 : ℝ)*X 0 2+(2005486671/5000000000 : ℝ)*X 1 0+(4384031491/10000000000 : ℝ)*X 1 1+(4384030649/10000000000 : ℝ)*X 1 2+(2005486671/5000000000 : ℝ)*X 2 0+(4384031491/10000000000 : ℝ)*X 2 1+(4384030649/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-7973/12500 : ℝ) ≤ (-14350798577737720934413075519/22500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (213271719/100000000000000 : ℝ)*(upper0) + (32741687/100000000000000 : ℝ)*(lower1) + (87278923/50000000000000 : ℝ)*(lower2) + (1134383122292441/50000000000000 : ℝ)*(major0) + (1134383122292441/50000000000000 : ℝ)*(major1) + (1134383122292441/50000000000000 : ℝ)*(major2) + (1493941281/100000000000000 : ℝ)*(sp2) + (2787735659/100000000000000 : ℝ)*(sp3) + (398863756596981/12500000000000 : ℝ)*(sp4) + (319090271234369/10000000000000 : ℝ)*(sp5) + (1595456799818833/50000000000000 : ℝ)*(sp6) + (273575010038507/20000000000000 : ℝ)*(sp7) + (5040803099/100000000000000 : ℝ)*(sp8) + (12381235257/100000000000000 : ℝ)*(sp13) + (273575567585639/20000000000000 : ℝ)*(f.failure) + (1595457546789473/50000000000000 : ℝ)*(f.sum) + (6214255356527/1856250000000000000000000000 : ℝ)*base65 + (1558206758741101/330000000000000000000000000000 : ℝ)*base68 + (1256600484431101/330000000000000000000000000000 : ℝ)*base70 + (374962897038899/330000000000000000000000000000 : ℝ)*base71 + (4236486925123/1856250000000000000000000000 : ℝ)*base74 + (2540020986641101/330000000000000000000000000000 : ℝ)*base76 + (1122710937101101/330000000000000000000000000000 : ℝ)*base78 + (13481341084481101/330000000000000000000000000000 : ℝ)*base80 + (45863213584433/7425000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (17474783/2000000000000000000000 : ℝ)*base89 + (17474783/2000000000000000000000 : ℝ)*base91 + (17474783/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (29387/50000 : ℝ) ≤ (32327089105958690059450085533/55000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12730461/20000000000000 : ℝ)*(upper0) + (4156657/20000000000000 : ℝ)*(lower1) + (68960427/100000000000000 : ℝ)*(upper4) + (1173568096658847/50000000000000 : ℝ)*(major0) + (1173568096658847/50000000000000 : ℝ)*(major1) + (1173568096658847/50000000000000 : ℝ)*(major2) + (325954983904663/10000000000000 : ℝ)*(sp0) + (1629772501302779/50000000000000 : ℝ)*(sp1) + (101860464781341/3125000000000 : ℝ)*(sp2) + (70755389865143/5000000000000 : ℝ)*(sp3) + (6793050009/100000000000000 : ℝ)*(sp5) + (1057665791/6250000000000 : ℝ)*(sp6) + (978304469/50000000000000 : ℝ)*(sp8) + (20618461217/100000000000000 : ℝ)*(sp11) + (1415128415764077/100000000000000 : ℝ)*(f.failure) + (203721987228473/6250000000000 : ℝ)*(f.sum) + (1098540094031/1237500000000000000000000000 : ℝ)*base65 + (41513177795689/110000000000000000000000000000 : ℝ)*base68 + (345603930475689/110000000000000000000000000000 : ℝ)*base70 + (695076995204311/110000000000000000000000000000 : ℝ)*base71 + (8639363881781/1237500000000000000000000000 : ℝ)*base73 + (843386780545689/110000000000000000000000000000 : ℝ)*base76 + (343944450034311/110000000000000000000000000000 : ℝ)*base77 + (1247441626135689/110000000000000000000000000000 : ℝ)*base80 + (3315744080287/2475000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (106849131/10000000000000000000000 : ℝ)*base90 + (106849131/10000000000000000000000 : ℝ)*base92 + (106849131/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (40323/50000 : ℝ) ≤ (133069759140603527073687488551/165000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (25906461/100000000000000 : ℝ)*(upper0) + (194607/800000000000 : ℝ)*(lower3) + (3043163/10000000000000 : ℝ)*(lower5) + (1268591681604103/50000000000000 : ℝ)*(major0) + (1268591681604103/50000000000000 : ℝ)*(major1) + (1268591681604103/50000000000000 : ℝ)*(major2) + (17408973533/50000000000000 : ℝ)*(sp1) + (839181391/25000000000000 : ℝ)*(sp3) + (69643441/12500000000000 : ℝ)*(sp4) + (3517769846558817/100000000000000 : ℝ)*(sp8) + (1374116419989/39062500000 : ℝ)*(sp9) + (1758886426559453/50000000000000 : ℝ)*(sp10) + (95606733559223/6250000000000 : ℝ)*(sp11) + (30617657/1250000000000 : ℝ)*(sp12) + (1529711093673133/100000000000000 : ℝ)*(f.failure) + (1758886426559453/50000000000000 : ℝ)*(f.sum) + (12862453995889/7425000000000000000000000000 : ℝ)*base65 + (7260420642577117/330000000000000000000000000000 : ℝ)*base67 + (656239803952883/330000000000000000000000000000 : ℝ)*base70 + (457530612487117/330000000000000000000000000000 : ℝ)*base71 + (20806907010383/928125000000000000000000000 : ℝ)*base73 + (496740503332883/330000000000000000000000000000 : ℝ)*base76 + (268582891012883/330000000000000000000000000000 : ℝ)*base78 + (2468029446472883/330000000000000000000000000000 : ℝ)*base80 + (4291662434957/3712500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (60300501/10000000000000000000000 : ℝ)*base89 + (60300501/10000000000000000000000 : ℝ)*base91 + (60300501/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-86199/100000 : ℝ) ≤ (-85334298776692022588499899399/99000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14834421/100000000000000 : ℝ)*(upper1) + (35749183/50000000000000 : ℝ)*(lower2) + (162120471/100000000000000 : ℝ)*(upper3) + (8668727/100000000000000 : ℝ)*(upper5) + (257700932667217/10000000000000 : ℝ)*(major0) + (257700932667217/10000000000000 : ℝ)*(major1) + (257700932667217/10000000000000 : ℝ)*(major2) + (99119744717/50000000000000 : ℝ)*(sp5) + (113858017097/100000000000000 : ℝ)*(sp6) + (22652687131/50000000000000 : ℝ)*(sp7) + (1814513947315729/50000000000000 : ℝ)*(sp12) + (453603706892753/12500000000000 : ℝ)*(sp13) + (1814457018307181/50000000000000 : ℝ)*(sp14) + (155367754046881/10000000000000 : ℝ)*(sp15) + (12138459733149/781250000000 : ℝ)*(f.failure) + (1814513947315729/50000000000000 : ℝ)*(f.sum) + (1896114566081/371250000000000000000000000 : ℝ)*base66 + (97279724737637/66000000000000000000000000000 : ℝ)*base68 + (813664752601637/66000000000000000000000000000 : ℝ)*base70 + (185654735989637/66000000000000000000000000000 : ℝ)*base72 + (390720514703/742500000000000000000000000 : ℝ)*base73 + (1483473528457637/66000000000000000000000000000 : ℝ)*base76 + (597200526931637/66000000000000000000000000000 : ℝ)*base78 + (430463757127637/66000000000000000000000000000 : ℝ)*base80 + (3458017775059/371250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1072753/78125000000000000000 : ℝ)*base89 + (1072753/78125000000000000000 : ℝ)*base91 + (1072753/78125000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1543_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165860297/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1103/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7973/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(29387/50000 : ℝ) else (40323/50000 : ℝ) ≤ X j i ∧ X j i ≤ (86199/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1543_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1543_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165860297/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1103/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7973/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(29387/50000 : ℝ) else (40323/50000 : ℝ) ≤ X j i ∧ X j i ≤ (86199/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1543_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165860297/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1103/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7973/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(29387/50000 : ℝ) else (40323/50000 : ℝ) ≤ X j i ∧ X j i ≤ (86199/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1543_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
