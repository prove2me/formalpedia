-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1218_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:09:48.362617+00:00
-- url     : https://prove2.me/submissions/f588948c-dc08-4654-83f7-aed9892f48c2

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
theorem support_rectangle_w1218_box_0 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1003310661/5000000000 : ℝ)*x 0 + (268760117/500000000 : ℝ)*x 1 + (5375201267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1003310661/5000000000 : ℝ)^8411 ≤ (11966204352647/100000000000000 : ℝ)^6363 := by
    have hnat : (1003310661 : ℕ)^8411*100000000000000^6363 ≤ 11966204352647^6363*5000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003310661 5000000000 11966204352647 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (268760117/500000000 : ℝ)^8411 ≤ (44016903622467/100000000000000 : ℝ)^6363 := by
    have hnat : (268760117 : ℕ)^8411*100000000000000^6363 ≤ 44016903622467^6363*500000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268760117 500000000 44016903622467 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5375201267/10000000000 : ℝ)^8411 ≤ (1375527875241/3125000000000 : ℝ)^6363 := by
    have hnat : (5375201267 : ℕ)^8411*3125000000000^6363 ≤ 1375527875241^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375201267 10000000000 1375527875241 3125000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1003310661/5000000000 : ℝ), (268760117/500000000 : ℝ), (5375201267/10000000000 : ℝ)] ![(11966204352647/100000000000000 : ℝ), (44016903622467/100000000000000 : ℝ), (1375527875241/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1003310661/5000000000 : ℝ)|^8411 ≤ (11966204352647/100000000000000 : ℝ)^6363
        have hw : |(-1003310661/5000000000 : ℝ)|=(1003310661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(268760117/500000000 : ℝ)|^8411 ≤ (44016903622467/100000000000000 : ℝ)^6363
        have hw : |(268760117/500000000 : ℝ)|=(268760117/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5375201267/10000000000 : ℝ)|^8411 ≤ (1375527875241/3125000000000 : ℝ)^6363
        have hw : |(5375201267/10000000000 : ℝ)|=(5375201267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_box_1 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5296622623/10000000000 : ℝ)*x 0 + (-1056684387/5000000000 : ℝ)*x 1 + (215008061/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296622623/10000000000 : ℝ)^8411 ≤ (43168320287861/100000000000000 : ℝ)^6363 := by
    have hnat : (5296622623 : ℕ)^8411*100000000000000^6363 ≤ 43168320287861^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296622623 10000000000 43168320287861 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056684387/5000000000 : ℝ)^8411 ≤ (1601848111421/12500000000000 : ℝ)^6363 := by
    have hnat : (1056684387 : ℕ)^8411*12500000000000^6363 ≤ 1601848111421^6363*5000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056684387 5000000000 1601848111421 12500000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215008061/400000000 : ℝ)^8411 ≤ (44016894800449/100000000000000 : ℝ)^6363 := by
    have hnat : (215008061 : ℕ)^8411*100000000000000^6363 ≤ 44016894800449^6363*400000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215008061 400000000 44016894800449 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296622623/10000000000 : ℝ), (-1056684387/5000000000 : ℝ), (215008061/400000000 : ℝ)] ![(43168320287861/100000000000000 : ℝ), (1601848111421/12500000000000 : ℝ), (44016894800449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296622623/10000000000 : ℝ)|^8411 ≤ (43168320287861/100000000000000 : ℝ)^6363
        have hw : |(5296622623/10000000000 : ℝ)|=(5296622623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1056684387/5000000000 : ℝ)|^8411 ≤ (1601848111421/12500000000000 : ℝ)^6363
        have hw : |(-1056684387/5000000000 : ℝ)|=(1056684387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215008061/400000000 : ℝ)|^8411 ≤ (44016894800449/100000000000000 : ℝ)^6363
        have hw : |(215008061/400000000 : ℝ)|=(215008061/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_box_2 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2648311161/5000000000 : ℝ)*x 0 + (5375201853/10000000000 : ℝ)*x 1 + (-2113368737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2648311161/5000000000 : ℝ)^8411 ≤ (1726732681803/4000000000000 : ℝ)^6363 := by
    have hnat : (2648311161 : ℕ)^8411*4000000000000^6363 ≤ 1726732681803^6363*5000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2648311161 5000000000 1726732681803 4000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5375201853/10000000000 : ℝ)^8411 ≤ (8803379670181/20000000000000 : ℝ)^6363 := by
    have hnat : (5375201853 : ℕ)^8411*20000000000000^6363 ≤ 8803379670181^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375201853 10000000000 8803379670181 20000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2113368737/10000000000 : ℝ)^8411 ≤ (12814784594801/100000000000000 : ℝ)^6363 := by
    have hnat : (2113368737 : ℕ)^8411*100000000000000^6363 ≤ 12814784594801^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113368737 10000000000 12814784594801 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2648311161/5000000000 : ℝ), (5375201853/10000000000 : ℝ), (-2113368737/10000000000 : ℝ)] ![(1726732681803/4000000000000 : ℝ), (8803379670181/20000000000000 : ℝ), (12814784594801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2648311161/5000000000 : ℝ)|^8411 ≤ (1726732681803/4000000000000 : ℝ)^6363
        have hw : |(2648311161/5000000000 : ℝ)|=(2648311161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5375201853/10000000000 : ℝ)|^8411 ≤ (8803379670181/20000000000000 : ℝ)^6363
        have hw : |(5375201853/10000000000 : ℝ)|=(5375201853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2113368737/10000000000 : ℝ)|^8411 ≤ (12814784594801/100000000000000 : ℝ)^6363
        have hw : |(-2113368737/10000000000 : ℝ)|=(2113368737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_box_3 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4460839851/10000000000 : ℝ)*x 0 + (268922027/625000000 : ℝ)*x 1 + (4302754099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4460839851/10000000000 : ℝ)^8411 ≤ (8600379436431/25000000000000 : ℝ)^6363 := by
    have hnat : (4460839851 : ℕ)^8411*25000000000000^6363 ≤ 8600379436431^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4460839851 10000000000 8600379436431 25000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (268922027/625000000 : ℝ)^8411 ≤ (819980818101/2500000000000 : ℝ)^6363 := by
    have hnat : (268922027 : ℕ)^8411*2500000000000^6363 ≤ 819980818101^6363*625000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268922027 625000000 819980818101 2500000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4302754099/10000000000 : ℝ)^8411 ≤ (8199812380327/25000000000000 : ℝ)^6363 := by
    have hnat : (4302754099 : ℕ)^8411*25000000000000^6363 ≤ 8199812380327^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4302754099 10000000000 8199812380327 25000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4460839851/10000000000 : ℝ), (268922027/625000000 : ℝ), (4302754099/10000000000 : ℝ)] ![(8600379436431/25000000000000 : ℝ), (819980818101/2500000000000 : ℝ), (8199812380327/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4460839851/10000000000 : ℝ)|^8411 ≤ (8600379436431/25000000000000 : ℝ)^6363
        have hw : |(4460839851/10000000000 : ℝ)|=(4460839851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(268922027/625000000 : ℝ)|^8411 ≤ (819980818101/2500000000000 : ℝ)^6363
        have hw : |(268922027/625000000 : ℝ)|=(268922027/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4302754099/10000000000 : ℝ)|^8411 ≤ (8199812380327/25000000000000 : ℝ)^6363
        have hw : |(4302754099/10000000000 : ℝ)|=(4302754099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_box_4 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2256891553/10000000000 : ℝ)*x 0 + (2641017083/5000000000 : ℝ)*x 1 + (660254279/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2256891553/10000000000 : ℝ)^8411 ≤ (1397755315149/10000000000000 : ℝ)^6363 := by
    have hnat : (2256891553 : ℕ)^8411*10000000000000^6363 ≤ 1397755315149^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2256891553 10000000000 1397755315149 10000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2641017083/5000000000 : ℝ)^8411 ≤ (43011223058793/100000000000000 : ℝ)^6363 := by
    have hnat : (2641017083 : ℕ)^8411*100000000000000^6363 ≤ 43011223058793^6363*5000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641017083 5000000000 43011223058793 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (660254279/1250000000 : ℝ)^8411 ≤ (10752805942301/25000000000000 : ℝ)^6363 := by
    have hnat : (660254279 : ℕ)^8411*25000000000000^6363 ≤ 10752805942301^6363*1250000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660254279 1250000000 10752805942301 25000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2256891553/10000000000 : ℝ), (2641017083/5000000000 : ℝ), (660254279/1250000000 : ℝ)] ![(1397755315149/10000000000000 : ℝ), (43011223058793/100000000000000 : ℝ), (10752805942301/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2256891553/10000000000 : ℝ)|^8411 ≤ (1397755315149/10000000000000 : ℝ)^6363
        have hw : |(-2256891553/10000000000 : ℝ)|=(2256891553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2641017083/5000000000 : ℝ)|^8411 ≤ (43011223058793/100000000000000 : ℝ)^6363
        have hw : |(2641017083/5000000000 : ℝ)|=(2641017083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(660254279/1250000000 : ℝ)|^8411 ≤ (10752805942301/25000000000000 : ℝ)^6363
        have hw : |(660254279/1250000000 : ℝ)|=(660254279/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_box_5 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5362333577/10000000000 : ℝ)*x 0 + (-26877957/125000000 : ℝ)*x 1 + (5282034109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362333577/10000000000 : ℝ)^8411 ≤ (1371176830697/3125000000000 : ℝ)^6363 := by
    have hnat : (5362333577 : ℕ)^8411*3125000000000^6363 ≤ 1371176830697^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362333577 10000000000 1371176830697 3125000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (26877957/125000000 : ℝ)^8411 ≤ (1311111896261/10000000000000 : ℝ)^6363 := by
    have hnat : (26877957 : ℕ)^8411*10000000000000^6363 ≤ 1311111896261^6363*125000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26877957 125000000 1311111896261 10000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5282034109/10000000000 : ℝ)^8411 ≤ (8602244489051/20000000000000 : ℝ)^6363 := by
    have hnat : (5282034109 : ℕ)^8411*20000000000000^6363 ≤ 8602244489051^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282034109 10000000000 8602244489051 20000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362333577/10000000000 : ℝ), (-26877957/125000000 : ℝ), (5282034109/10000000000 : ℝ)] ![(1371176830697/3125000000000 : ℝ), (1311111896261/10000000000000 : ℝ), (8602244489051/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362333577/10000000000 : ℝ)|^8411 ≤ (1371176830697/3125000000000 : ℝ)^6363
        have hw : |(5362333577/10000000000 : ℝ)|=(5362333577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-26877957/125000000 : ℝ)|^8411 ≤ (1311111896261/10000000000000 : ℝ)^6363
        have hw : |(-26877957/125000000 : ℝ)|=(26877957/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5282034109/10000000000 : ℝ)|^8411 ≤ (8602244489051/20000000000000 : ℝ)^6363
        have hw : |(5282034109/10000000000 : ℝ)|=(5282034109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_box_6 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1340583337/2500000000 : ℝ)*x 0 + (5282034267/10000000000 : ℝ)*x 1 + (-134389791/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1340583337/2500000000 : ℝ)^8411 ≤ (43877656105391/100000000000000 : ℝ)^6363 := by
    have hnat : (1340583337 : ℕ)^8411*100000000000000^6363 ≤ 43877656105391^6363*2500000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1340583337 2500000000 43877656105391 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5282034267/10000000000 : ℝ)^8411 ≤ (21505612072969/50000000000000 : ℝ)^6363 := by
    have hnat : (5282034267 : ℕ)^8411*50000000000000^6363 ≤ 21505612072969^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282034267 10000000000 21505612072969 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (134389791/625000000 : ℝ)^8411 ≤ (6555559868189/50000000000000 : ℝ)^6363 := by
    have hnat : (134389791 : ℕ)^8411*50000000000000^6363 ≤ 6555559868189^6363*625000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134389791 625000000 6555559868189 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1340583337/2500000000 : ℝ), (5282034267/10000000000 : ℝ), (-134389791/625000000 : ℝ)] ![(43877656105391/100000000000000 : ℝ), (21505612072969/50000000000000 : ℝ), (6555559868189/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1340583337/2500000000 : ℝ)|^8411 ≤ (43877656105391/100000000000000 : ℝ)^6363
        have hw : |(1340583337/2500000000 : ℝ)|=(1340583337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5282034267/10000000000 : ℝ)|^8411 ≤ (21505612072969/50000000000000 : ℝ)^6363
        have hw : |(5282034267/10000000000 : ℝ)|=(5282034267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-134389791/625000000 : ℝ)|^8411 ≤ (6555559868189/50000000000000 : ℝ)^6363
        have hw : |(-134389791/625000000 : ℝ)|=(134389791/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_box_7 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2123461083/5000000000 : ℝ)*x 0 + (551211481/1250000000 : ℝ)*x 1 + (1102422957/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2123461083/5000000000 : ℝ)^8411 ≤ (8059461469383/25000000000000 : ℝ)^6363 := by
    have hnat : (2123461083 : ℕ)^8411*25000000000000^6363 ≤ 8059461469383^6363*5000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123461083 5000000000 8059461469383 25000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (551211481/1250000000 : ℝ)^8411 ≤ (33881077156801/100000000000000 : ℝ)^6363 := by
    have hnat : (551211481 : ℕ)^8411*100000000000000^6363 ≤ 33881077156801^6363*1250000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551211481 1250000000 33881077156801 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1102422957/2500000000 : ℝ)^8411 ≤ (1355243078147/4000000000000 : ℝ)^6363 := by
    have hnat : (1102422957 : ℕ)^8411*4000000000000^6363 ≤ 1355243078147^6363*2500000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102422957 2500000000 1355243078147 4000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2123461083/5000000000 : ℝ), (551211481/1250000000 : ℝ), (1102422957/2500000000 : ℝ)] ![(8059461469383/25000000000000 : ℝ), (33881077156801/100000000000000 : ℝ), (1355243078147/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2123461083/5000000000 : ℝ)|^8411 ≤ (8059461469383/25000000000000 : ℝ)^6363
        have hw : |(2123461083/5000000000 : ℝ)|=(2123461083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(551211481/1250000000 : ℝ)|^8411 ≤ (33881077156801/100000000000000 : ℝ)^6363
        have hw : |(551211481/1250000000 : ℝ)|=(551211481/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1102422957/2500000000 : ℝ)|^8411 ≤ (1355243078147/4000000000000 : ℝ)^6363
        have hw : |(1102422957/2500000000 : ℝ)|=(1102422957/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_box_8 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1102236441/5000000000 : ℝ)*x 0 + (5218528589/10000000000 : ℝ)*x 1 + (215392579/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1102236441/5000000000 : ℝ)^8411 ≤ (13550032399139/100000000000000 : ℝ)^6363 := by
    have hnat : (1102236441 : ℕ)^8411*100000000000000^6363 ≤ 13550032399139^6363*5000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102236441 5000000000 13550032399139 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218528589/10000000000 : ℝ)^8411 ≤ (21164493436127/50000000000000 : ℝ)^6363 := by
    have hnat : (5218528589 : ℕ)^8411*50000000000000^6363 ≤ 21164493436127^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218528589 10000000000 21164493436127 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215392579/400000000 : ℝ)^8411 ≤ (44120980716251/100000000000000 : ℝ)^6363 := by
    have hnat : (215392579 : ℕ)^8411*100000000000000^6363 ≤ 44120980716251^6363*400000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215392579 400000000 44120980716251 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1102236441/5000000000 : ℝ), (5218528589/10000000000 : ℝ), (215392579/400000000 : ℝ)] ![(13550032399139/100000000000000 : ℝ), (21164493436127/50000000000000 : ℝ), (44120980716251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1102236441/5000000000 : ℝ)|^8411 ≤ (13550032399139/100000000000000 : ℝ)^6363
        have hw : |(-1102236441/5000000000 : ℝ)|=(1102236441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218528589/10000000000 : ℝ)|^8411 ≤ (21164493436127/50000000000000 : ℝ)^6363
        have hw : |(5218528589/10000000000 : ℝ)|=(5218528589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215392579/400000000 : ℝ)|^8411 ≤ (44120980716251/100000000000000 : ℝ)^6363
        have hw : |(215392579/400000000 : ℝ)|=(215392579/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_box_9 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (661229891/1250000000 : ℝ)*x 0 + (-2109497637/10000000000 : ℝ)*x 1 + (5384814427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661229891/1250000000 : ℝ)^8411 ≤ (43095254210591/100000000000000 : ℝ)^6363 := by
    have hnat : (661229891 : ℕ)^8411*100000000000000^6363 ≤ 43095254210591^6363*1250000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661229891 1250000000 43095254210591 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2109497637/10000000000 : ℝ)^8411 ≤ (639188278861/5000000000000 : ℝ)^6363 := by
    have hnat : (2109497637 : ℕ)^8411*5000000000000^6363 ≤ 639188278861^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109497637 10000000000 639188278861 5000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5384814427/10000000000 : ℝ)^8411 ≤ (44120980196373/100000000000000 : ℝ)^6363 := by
    have hnat : (5384814427 : ℕ)^8411*100000000000000^6363 ≤ 44120980196373^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384814427 10000000000 44120980196373 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661229891/1250000000 : ℝ), (-2109497637/10000000000 : ℝ), (5384814427/10000000000 : ℝ)] ![(43095254210591/100000000000000 : ℝ), (639188278861/5000000000000 : ℝ), (44120980196373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661229891/1250000000 : ℝ)|^8411 ≤ (43095254210591/100000000000000 : ℝ)^6363
        have hw : |(661229891/1250000000 : ℝ)|=(661229891/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2109497637/10000000000 : ℝ)|^8411 ≤ (639188278861/5000000000000 : ℝ)^6363
        have hw : |(-2109497637/10000000000 : ℝ)|=(2109497637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5384814427/10000000000 : ℝ)|^8411 ≤ (44120980196373/100000000000000 : ℝ)^6363
        have hw : |(5384814427/10000000000 : ℝ)|=(5384814427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_box_10 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2644919581/5000000000 : ℝ)*x 0 + (1076962897/2000000000 : ℝ)*x 1 + (-2109497513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644919581/5000000000 : ℝ)^8411 ≤ (8619050915347/20000000000000 : ℝ)^6363 := by
    have hnat : (2644919581 : ℕ)^8411*20000000000000^6363 ≤ 8619050915347^6363*5000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644919581 5000000000 8619050915347 20000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1076962897/2000000000 : ℝ)^8411 ≤ (44120980824559/100000000000000 : ℝ)^6363 := by
    have hnat : (1076962897 : ℕ)^8411*100000000000000^6363 ≤ 44120980824559^6363*2000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076962897 2000000000 44120980824559 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2109497513/10000000000 : ℝ)^8411 ≤ (2556752916781/20000000000000 : ℝ)^6363 := by
    have hnat : (2109497513 : ℕ)^8411*20000000000000^6363 ≤ 2556752916781^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109497513 10000000000 2556752916781 20000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644919581/5000000000 : ℝ), (1076962897/2000000000 : ℝ), (-2109497513/10000000000 : ℝ)] ![(8619050915347/20000000000000 : ℝ), (44120980824559/100000000000000 : ℝ), (2556752916781/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644919581/5000000000 : ℝ)|^8411 ≤ (8619050915347/20000000000000 : ℝ)^6363
        have hw : |(2644919581/5000000000 : ℝ)|=(2644919581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1076962897/2000000000 : ℝ)|^8411 ≤ (44120980824559/100000000000000 : ℝ)^6363
        have hw : |(1076962897/2000000000 : ℝ)|=(1076962897/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2109497513/10000000000 : ℝ)|^8411 ≤ (2556752916781/20000000000000 : ℝ)^6363
        have hw : |(-2109497513/10000000000 : ℝ)|=(2109497513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_box_11 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4482638193/10000000000 : ℝ)*x 0 + (536464189/1250000000 : ℝ)*x 1 + (4291713603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4482638193/10000000000 : ℝ)^8411 ≤ (1384956226021/4000000000000 : ℝ)^6363 := by
    have hnat : (4482638193 : ℕ)^8411*4000000000000^6363 ≤ 1384956226021^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4482638193 10000000000 1384956226021 4000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (536464189/1250000000 : ℝ)^8411 ≤ (16344023353763/50000000000000 : ℝ)^6363 := by
    have hnat : (536464189 : ℕ)^8411*50000000000000^6363 ≤ 16344023353763^6363*1250000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536464189 1250000000 16344023353763 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4291713603/10000000000 : ℝ)^8411 ≤ (8172011905929/25000000000000 : ℝ)^6363 := by
    have hnat : (4291713603 : ℕ)^8411*25000000000000^6363 ≤ 8172011905929^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4291713603 10000000000 8172011905929 25000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4482638193/10000000000 : ℝ), (536464189/1250000000 : ℝ), (4291713603/10000000000 : ℝ)] ![(1384956226021/4000000000000 : ℝ), (16344023353763/50000000000000 : ℝ), (8172011905929/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4482638193/10000000000 : ℝ)|^8411 ≤ (1384956226021/4000000000000 : ℝ)^6363
        have hw : |(4482638193/10000000000 : ℝ)|=(4482638193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(536464189/1250000000 : ℝ)|^8411 ≤ (16344023353763/50000000000000 : ℝ)^6363
        have hw : |(536464189/1250000000 : ℝ)|=(536464189/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4291713603/10000000000 : ℝ)|^8411 ≤ (8172011905929/25000000000000 : ℝ)^6363
        have hw : |(4291713603/10000000000 : ℝ)|=(4291713603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_box_12 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-514828441/2500000000 : ℝ)*x 0 + (1087496593/2000000000 : ℝ)*x 1 + (1054792683/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (514828441/2500000000 : ℝ)^8411 ≤ (3095827416783/25000000000000 : ℝ)^6363 := by
    have hnat : (514828441 : ℕ)^8411*25000000000000^6363 ≤ 3095827416783^6363*2500000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514828441 2500000000 3095827416783 25000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1087496593/2000000000 : ℝ)^8411 ≤ (22346158989501/50000000000000 : ℝ)^6363 := by
    have hnat : (1087496593 : ℕ)^8411*50000000000000^6363 ≤ 22346158989501^6363*2000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087496593 2000000000 22346158989501 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054792683/2000000000 : ℝ)^8411 ≤ (5365546542843/12500000000000 : ℝ)^6363 := by
    have hnat : (1054792683 : ℕ)^8411*12500000000000^6363 ≤ 5365546542843^6363*2000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054792683 2000000000 5365546542843 12500000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-514828441/2500000000 : ℝ), (1087496593/2000000000 : ℝ), (1054792683/2000000000 : ℝ)] ![(3095827416783/25000000000000 : ℝ), (22346158989501/50000000000000 : ℝ), (5365546542843/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-514828441/2500000000 : ℝ)|^8411 ≤ (3095827416783/25000000000000 : ℝ)^6363
        have hw : |(-514828441/2500000000 : ℝ)|=(514828441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1087496593/2000000000 : ℝ)|^8411 ≤ (22346158989501/50000000000000 : ℝ)^6363
        have hw : |(1087496593/2000000000 : ℝ)|=(1087496593/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1054792683/2000000000 : ℝ)|^8411 ≤ (5365546542843/12500000000000 : ℝ)^6363
        have hw : |(1054792683/2000000000 : ℝ)|=(1054792683/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_box_13 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5368023861/10000000000 : ℝ)*x 0 + (-2153373647/10000000000 : ℝ)*x 1 + (2636981761/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368023861/10000000000 : ℝ)^8411 ≤ (1373100513369/3125000000000 : ℝ)^6363 := by
    have hnat : (5368023861 : ℕ)^8411*3125000000000^6363 ≤ 1373100513369^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368023861 10000000000 1373100513369 3125000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2153373647/10000000000 : ℝ)^8411 ≤ (13136410062161/100000000000000 : ℝ)^6363 := by
    have hnat : (2153373647 : ℕ)^8411*100000000000000^6363 ≤ 13136410062161^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153373647 10000000000 13136410062161 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2636981761/5000000000 : ℝ)^8411 ≤ (8584874698781/20000000000000 : ℝ)^6363 := by
    have hnat : (2636981761 : ℕ)^8411*20000000000000^6363 ≤ 8584874698781^6363*5000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636981761 5000000000 8584874698781 20000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368023861/10000000000 : ℝ), (-2153373647/10000000000 : ℝ), (2636981761/5000000000 : ℝ)] ![(1373100513369/3125000000000 : ℝ), (13136410062161/100000000000000 : ℝ), (8584874698781/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368023861/10000000000 : ℝ)|^8411 ≤ (1373100513369/3125000000000 : ℝ)^6363
        have hw : |(5368023861/10000000000 : ℝ)|=(5368023861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2153373647/10000000000 : ℝ)|^8411 ≤ (13136410062161/100000000000000 : ℝ)^6363
        have hw : |(-2153373647/10000000000 : ℝ)|=(2153373647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2636981761/5000000000 : ℝ)|^8411 ≤ (8584874698781/20000000000000 : ℝ)^6363
        have hw : |(2636981761/5000000000 : ℝ)|=(2636981761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_box_14 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (536802381/1000000000 : ℝ)*x 0 + (5273963537/10000000000 : ℝ)*x 1 + (-2102904/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536802381/1000000000 : ℝ)^8411 ≤ (43939215875993/100000000000000 : ℝ)^6363 := by
    have hnat : (536802381 : ℕ)^8411*100000000000000^6363 ≤ 43939215875993^6363*1000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536802381 1000000000 43939215875993 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5273963537/10000000000 : ℝ)^8411 ≤ (42924373655283/100000000000000 : ℝ)^6363 := by
    have hnat : (5273963537 : ℕ)^8411*100000000000000^6363 ≤ 42924373655283^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273963537 10000000000 42924373655283 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2102904/9765625 : ℝ)^8411 ≤ (1313641045729/10000000000000 : ℝ)^6363 := by
    have hnat : (2102904 : ℕ)^8411*10000000000000^6363 ≤ 1313641045729^6363*9765625^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2102904 9765625 1313641045729 10000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536802381/1000000000 : ℝ), (5273963537/10000000000 : ℝ), (-2102904/9765625 : ℝ)] ![(43939215875993/100000000000000 : ℝ), (42924373655283/100000000000000 : ℝ), (1313641045729/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536802381/1000000000 : ℝ)|^8411 ≤ (43939215875993/100000000000000 : ℝ)^6363
        have hw : |(536802381/1000000000 : ℝ)|=(536802381/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5273963537/10000000000 : ℝ)|^8411 ≤ (42924373655283/100000000000000 : ℝ)^6363
        have hw : |(5273963537/10000000000 : ℝ)|=(5273963537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2102904/9765625 : ℝ)|^8411 ≤ (1313641045729/10000000000000 : ℝ)^6363
        have hw : |(-2102904/9765625 : ℝ)|=(2102904/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_box_15 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2114080217/5000000000 : ℝ)*x 0 + (4418950071/10000000000 : ℝ)*x 1 + (2209475073/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2114080217/5000000000 : ℝ)^8411 ≤ (32049723191119/100000000000000 : ℝ)^6363 := by
    have hnat : (2114080217 : ℕ)^8411*100000000000000^6363 ≤ 32049723191119^6363*5000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114080217 5000000000 32049723191119 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4418950071/10000000000 : ℝ)^8411 ≤ (16987569009759/50000000000000 : ℝ)^6363 := by
    have hnat : (4418950071 : ℕ)^8411*50000000000000^6363 ≤ 16987569009759^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4418950071 10000000000 16987569009759 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2209475073/5000000000 : ℝ)^8411 ≤ (33975138781753/100000000000000 : ℝ)^6363 := by
    have hnat : (2209475073 : ℕ)^8411*100000000000000^6363 ≤ 33975138781753^6363*5000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2209475073 5000000000 33975138781753 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2114080217/5000000000 : ℝ), (4418950071/10000000000 : ℝ), (2209475073/5000000000 : ℝ)] ![(32049723191119/100000000000000 : ℝ), (16987569009759/50000000000000 : ℝ), (33975138781753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2114080217/5000000000 : ℝ)|^8411 ≤ (32049723191119/100000000000000 : ℝ)^6363
        have hw : |(2114080217/5000000000 : ℝ)|=(2114080217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4418950071/10000000000 : ℝ)|^8411 ≤ (16987569009759/50000000000000 : ℝ)^6363
        have hw : |(4418950071/10000000000 : ℝ)|=(4418950071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2209475073/5000000000 : ℝ)|^8411 ≤ (33975138781753/100000000000000 : ℝ)^6363
        have hw : |(2209475073/5000000000 : ℝ)|=(2209475073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1218_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150958703/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14091/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (229/2000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31121/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29679/50000 : ℝ) ∧ (40019/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (83293/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14091/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (229/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14091/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (229/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14091/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (229/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14091/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (229/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14091/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (229/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14091/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (229/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (229/2000 : ℝ) ^ (4205/1024 : ℝ) ≤ (2729393784839467/20000000000000000000 : ℝ) := by
    have hpowers : (229/2000 : ℝ)^4205 ≤ (2729393784839467/20000000000000000000 : ℝ)^1024 := by
      have hnat : (229 : ℕ)^4205*20000000000000000000^1024 ≤ 2729393784839467^1024*2000^4205 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        229 2000 2729393784839467 20000000000000000000 4205 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (229/2000 : ℝ)) (X := (2729393784839467/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14091/100000 : ℝ) ^ (4205/1024 : ℝ) ≤ (8000481288349473/25000000000000000000 : ℝ) := by
    have hpowers : (14091/100000 : ℝ)^4205 ≤ (8000481288349473/25000000000000000000 : ℝ)^1024 := by
      have hnat : (14091 : ℕ)^4205*25000000000000000000^1024 ≤ 8000481288349473^1024*100000^4205 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14091 100000 8000481288349473 25000000000000000000 4205 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14091/100000 : ℝ)) (X := (8000481288349473/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002729393784839467/10000000000000000000 : ℝ) ≤ (625041537020597/625000000000000 : ℝ) ^ (4205/1024 : ℝ) := by
    have hpowers : (10002729393784839467/10000000000000000000 : ℝ)^1024 ≤ (625041537020597/625000000000000 : ℝ)^4205 := by
      have hnat : (10002729393784839467 : ℕ)^1024*625000000000000^4205 ≤ 625041537020597^4205*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002729393784839467 10000000000000000000 625041537020597 625000000000000 1024 4205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625041537020597/625000000000000 : ℝ)) (X := (10002729393784839467/10000000000000000000 : ℝ)) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045648894077595227/100000000000000000000 : ℝ) ≤ (25002778620611/25000000000000 : ℝ) ^ (4205/1024 : ℝ) := by
    have hpowers : (100045648894077595227/100000000000000000000 : ℝ)^1024 ≤ (25002778620611/25000000000000 : ℝ)^4205 := by
      have hnat : (100045648894077595227 : ℕ)^1024*25000000000000^4205 ≤ 25002778620611^4205*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045648894077595227 100000000000000000000 25002778620611 25000000000000 1024 4205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (25002778620611/25000000000000 : ℝ)) (X := (100045648894077595227/100000000000000000000 : ℝ)) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508000481288349473/12500000000000000000 : ℝ) ≤ (625097394009953/625000000000000 : ℝ) ^ (4205/1024 : ℝ) := by
    have hpowers : (12508000481288349473/12500000000000000000 : ℝ)^1024 ≤ (625097394009953/625000000000000 : ℝ)^4205 := by
      have hnat : (12508000481288349473 : ℕ)^1024*625000000000000^4205 ≤ 625097394009953^4205*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508000481288349473 12500000000000000000 625097394009953 625000000000000 1024 4205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625097394009953/625000000000000 : ℝ)) (X := (12508000481288349473/12500000000000000000 : ℝ)) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2729393784839467/20000000000000000000 : ℝ) ≤ ((1650095136743270477/1650625000000000000 : ℝ)+2*(13964247339/8253125000000 : ℝ)*(229/2000 : ℝ))^(4205/1024 : ℝ) := by
    rw [show (1650095136743270477/1650625000000000000 : ℝ)+2*(13964247339/8253125000000 : ℝ)*(229/2000 : ℝ)=(625041537020597/625000000000000 : ℝ) by norm_num, show 1+2*(2729393784839467/20000000000000000000 : ℝ)=(10002729393784839467/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8000481288349473/25000000000000000000 : ℝ)+(2729393784839467/20000000000000000000 : ℝ) ≤ ((1650095136743270477/1650625000000000000 : ℝ)+(13964247339/8253125000000 : ℝ)*((14091/100000 : ℝ)+(229/2000 : ℝ)))^(4205/1024 : ℝ) := by
    rw [show (1650095136743270477/1650625000000000000 : ℝ)+(13964247339/8253125000000 : ℝ)*((14091/100000 : ℝ)+(229/2000 : ℝ))=(25002778620611/25000000000000 : ℝ) by norm_num, show 1+(8000481288349473/25000000000000000000 : ℝ)+(2729393784839467/20000000000000000000 : ℝ)=(100045648894077595227/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8000481288349473/25000000000000000000 : ℝ) ≤ ((1650095136743270477/1650625000000000000 : ℝ)+2*(13964247339/8253125000000 : ℝ)*(14091/100000 : ℝ))^(4205/1024 : ℝ) := by
    rw [show (1650095136743270477/1650625000000000000 : ℝ)+2*(13964247339/8253125000000 : ℝ)*(14091/100000 : ℝ)=(625097394009953/625000000000000 : ℝ) by norm_num, show 1+2*(8000481288349473/25000000000000000000 : ℝ)=(12508000481288349473/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1650095136743270477/1650625000000000000 : ℝ)*(X 1 0+X 2 0)+(13964247339/8253125000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4205/1024 : ℝ)) (lo := (229/2000 : ℝ)) (hi := (14091/100000 : ℝ)) (c := (1650095136743270477/1650625000000000000 : ℝ)) (alpha := (13964247339/8253125000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1650095136743270477/1650625000000000000 : ℝ)*(X 0 1+X 2 1)+(13964247339/8253125000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4205/1024 : ℝ)) (lo := (229/2000 : ℝ)) (hi := (14091/100000 : ℝ)) (c := (1650095136743270477/1650625000000000000 : ℝ)) (alpha := (13964247339/8253125000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1650095136743270477/1650625000000000000 : ℝ)*(X 0 2+X 1 2)+(13964247339/8253125000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4205/1024 : ℝ)) (lo := (229/2000 : ℝ)) (hi := (14091/100000 : ℝ)) (c := (1650095136743270477/1650625000000000000 : ℝ)) (alpha := (13964247339/8253125000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1003310661/5000000000 : ℝ)*X 0 0+(268760117/500000000 : ℝ)*X 0 1+(5375201267/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5296622623/10000000000 : ℝ)*X 1 0+(-1056684387/5000000000 : ℝ)*X 1 1+(215008061/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2648311161/5000000000 : ℝ)*X 2 0+(5375201853/10000000000 : ℝ)*X 2 1+(-2113368737/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4460839851/10000000000 : ℝ)*X 0 0+(268922027/625000000 : ℝ)*X 0 1+(4302754099/10000000000 : ℝ)*X 0 2+(4460839851/10000000000 : ℝ)*X 1 0+(268922027/625000000 : ℝ)*X 1 1+(4302754099/10000000000 : ℝ)*X 1 2+(4460839851/10000000000 : ℝ)*X 2 0+(268922027/625000000 : ℝ)*X 2 1+(4302754099/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2256891553/10000000000 : ℝ)*X 0 0+(2641017083/5000000000 : ℝ)*X 0 1+(660254279/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5362333577/10000000000 : ℝ)*X 1 0+(-26877957/125000000 : ℝ)*X 1 1+(5282034109/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1340583337/2500000000 : ℝ)*X 2 0+(5282034267/10000000000 : ℝ)*X 2 1+(-134389791/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2123461083/5000000000 : ℝ)*X 0 0+(551211481/1250000000 : ℝ)*X 0 1+(1102422957/2500000000 : ℝ)*X 0 2+(2123461083/5000000000 : ℝ)*X 1 0+(551211481/1250000000 : ℝ)*X 1 1+(1102422957/2500000000 : ℝ)*X 1 2+(2123461083/5000000000 : ℝ)*X 2 0+(551211481/1250000000 : ℝ)*X 2 1+(1102422957/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1102236441/5000000000 : ℝ)*X 0 0+(5218528589/10000000000 : ℝ)*X 0 1+(215392579/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((661229891/1250000000 : ℝ)*X 1 0+(-2109497637/10000000000 : ℝ)*X 1 1+(5384814427/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2644919581/5000000000 : ℝ)*X 2 0+(1076962897/2000000000 : ℝ)*X 2 1+(-2109497513/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4482638193/10000000000 : ℝ)*X 0 0+(536464189/1250000000 : ℝ)*X 0 1+(4291713603/10000000000 : ℝ)*X 0 2+(4482638193/10000000000 : ℝ)*X 1 0+(536464189/1250000000 : ℝ)*X 1 1+(4291713603/10000000000 : ℝ)*X 1 2+(4482638193/10000000000 : ℝ)*X 2 0+(536464189/1250000000 : ℝ)*X 2 1+(4291713603/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-514828441/2500000000 : ℝ)*X 0 0+(1087496593/2000000000 : ℝ)*X 0 1+(1054792683/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5368023861/10000000000 : ℝ)*X 1 0+(-2153373647/10000000000 : ℝ)*X 1 1+(2636981761/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((536802381/1000000000 : ℝ)*X 2 0+(5273963537/10000000000 : ℝ)*X 2 1+(-2102904/9765625 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2114080217/5000000000 : ℝ)*X 0 0+(4418950071/10000000000 : ℝ)*X 0 1+(2209475073/5000000000 : ℝ)*X 0 2+(2114080217/5000000000 : ℝ)*X 1 0+(4418950071/10000000000 : ℝ)*X 1 1+(2209475073/5000000000 : ℝ)*X 1 2+(2114080217/5000000000 : ℝ)*X 2 0+(4418950071/10000000000 : ℝ)*X 2 1+(2209475073/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31121/50000 : ℝ) ≤ (-1605225803788447407357279459963/2579101562500000000000000000000 : ℝ) := by norm_num
    linear_combination (280311/390625000000 : ℝ)*(upper1) + (118047209/100000000000000 : ℝ)*(lower4) + (3171067/25000000000000 : ℝ)*(upper5) + (995866804389653/25000000000000 : ℝ)*(major0) + (995866804389653/25000000000000 : ℝ)*(major1) + (995866804389653/25000000000000 : ℝ)*(major2) + (398068459/10000000000000 : ℝ)*(sp3) + (668612474181921/12500000000000 : ℝ)*(sp4) + (5348892398495023/100000000000000 : ℝ)*(sp5) + (106977691832363/2000000000000 : ℝ)*(sp6) + (2638775459251783/100000000000000 : ℝ)*(sp7) + (444452191/25000000000000 : ℝ)*(sp12) + (9172769109/100000000000000 : ℝ)*(sp13) + (8489822991/50000000000000 : ℝ)*(sp14) + (659694859984093/25000000000000 : ℝ)*(f.failure) + (5348901571264133/100000000000000 : ℝ)*(f.sum) + (10558727226491/3301250000000000000000000000 : ℝ)*base66 + (250338069691761981/41265625000000000000000000000000 : ℝ)*base67 + (408175208081168231/41265625000000000000000000000000 : ℝ)*base69 + (270561569447761981/41265625000000000000000000000000 : ℝ)*base71 + (34424053596529/13205000000000000000000000000 : ℝ)*base74 + (104954058938013803/20632812500000000000000000000000 : ℝ)*base75 + (306961956627449481/41265625000000000000000000000000 : ℝ)*base77 + (115568828581199481/41265625000000000000000000000000 : ℝ)*base79 + (29554023273367/6602500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (20088621/2500000000000000000000 : ℝ)*base90 + (20088621/2500000000000000000000 : ℝ)*base92 + (20088621/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (29679/50000 : ℝ) ≤ (6123880047440622109933230581859/10316406250000000000000000000000 : ℝ) := by norm_num
    linear_combination (103311483/20000000000000 : ℝ)*(lower1) + (22751419/100000000000000 : ℝ)*(lower3) + (82460063/50000000000000 : ℝ)*(lower5) + (506109835696143/12500000000000 : ℝ)*(major0) + (506109835696143/12500000000000 : ℝ)*(major1) + (506109835696143/12500000000000 : ℝ)*(major2) + (2697929368804611/50000000000000 : ℝ)*(sp0) + (2697754304331911/50000000000000 : ℝ)*(sp1) + (1348937007607009/25000000000000 : ℝ)*(sp2) + (20953926644149/781250000000 : ℝ)*(sp3) + (7532989379/100000000000000 : ℝ)*(sp7) + (351754309217/100000000000000 : ℝ)*(sp9) + (56166272501/50000000000000 : ℝ)*(sp10) + (203170477/12500000000000 : ℝ)*(sp12) + (2682110143440451/100000000000000 : ℝ)*(f.failure) + (2697930181486519/50000000000000 : ℝ)*(f.sum) + (18551330585439/6602500000000000000000000000 : ℝ)*base66 + (201958323892132711/20632812500000000000000000000000 : ℝ)*base67 + (140675443174252917/2579101562500000000000000000000 : ℝ)*base69 + (64416495369226461/20632812500000000000000000000000 : ℝ)*base71 + (39628625860117/13205000000000000000000000000 : ℝ)*base73 + (351127827104062703/41265625000000000000000000000000 : ℝ)*base76 + (30058610580990209/5158203125000000000000000000000 : ℝ)*base77 + (21361565090458959/5158203125000000000000000000000 : ℝ)*base79 + (155964641432901/6602500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (40695053/10000000000000000000000 : ℝ)*base89 + (40695053/10000000000000000000000 : ℝ)*base91 + (40695053/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (40019/50000 : ℝ) ≤ (33029074400605994955695068025643/41265625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11630091/12500000000000 : ℝ)*(lower3) + (18491861/50000000000000 : ℝ)*(upper4) + (340057/50000000000000 : ℝ)*(lower5) + (2257989750558049/50000000000000 : ℝ)*(major0) + (2257989750558049/50000000000000 : ℝ)*(major1) + (2257989750558049/50000000000000 : ℝ)*(major2) + (765316881/50000000000000 : ℝ)*(sp0) + (8536207083/12500000000000 : ℝ)*(sp1) + (46336251271/50000000000000 : ℝ)*(sp2) + (2206126573/5000000000000 : ℝ)*(sp3) + (60137443605731/1000000000000 : ℝ)*(sp8) + (6013677601550199/100000000000000 : ℝ)*(sp9) + (18792666308451/312500000000 : ℝ)*(sp10) + (2991488933443523/100000000000000 : ℝ)*(sp11) + (2991533055974983/100000000000000 : ℝ)*(f.failure) + (3006872945603431/50000000000000 : ℝ)*(f.sum) + (29979304706929/13205000000000000000000000000 : ℝ)*base65 + (456954281508744373/82531250000000000000000000000000 : ℝ)*base67 + (577916671319150623/82531250000000000000000000000000 : ℝ)*base69 + (1020664996916650623/82531250000000000000000000000000 : ℝ)*base71 + (44060667616281/13205000000000000000000000000 : ℝ)*base74 + (65551561044806873/82531250000000000000000000000000 : ℝ)*base75 + (787759645447275623/82531250000000000000000000000000 : ℝ)*base77 + (851954906259181873/82531250000000000000000000000000 : ℝ)*base79 + (23871655332371/13205000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (34127049/10000000000000000000000 : ℝ)*base89 + (34127049/10000000000000000000000 : ℝ)*base91 + (34127049/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-83293/100000 : ℝ) ≤ (-34370407725904906786547860335357/41265625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (57795017/100000000000000 : ℝ)*(lower0) + (57680313/100000000000000 : ℝ)*(lower1) + (8865011/20000000000000 : ℝ)*(lower4) + (4551344954642647/100000000000000 : ℝ)*(major0) + (4551344954642647/100000000000000 : ℝ)*(major1) + (4551344954642647/100000000000000 : ℝ)*(major2) + (3690292223/25000000000000 : ℝ)*(sp0) + (87777654579/50000000000000 : ℝ)*(sp5) + (99317064799/50000000000000 : ℝ)*(sp6) + (351790799/4000000000000 : ℝ)*(sp7) + (6115478405227579/100000000000000 : ℝ)*(sp12) + (6115317611087313/100000000000000 : ℝ)*(sp13) + (3057647266133437/50000000000000 : ℝ)*(sp14) + (94217234327241/3125000000000 : ℝ)*(sp15) + (3014960293241687/100000000000000 : ℝ)*(f.failure) + (6115493166396471/100000000000000 : ℝ)*(f.sum) + (2593955235833/6602500000000000000000000000 : ℝ)*base65 + (1342897134913895119/165062500000000000000000000000000 : ℝ)*base67 + (622384741783020119/165062500000000000000000000000000 : ℝ)*base69 + (931573244654520119/165062500000000000000000000000000 : ℝ)*base71 + (86374266534349/13205000000000000000000000000 : ℝ)*base74 + (120486104413082619/165062500000000000000000000000000 : ℝ)*base75 + (218811847980457619/165062500000000000000000000000000 : ℝ)*base77 + (3379476448832917381/165062500000000000000000000000000 : ℝ)*base80 + (8260477948089/3301250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (35051961/10000000000000000000000 : ℝ)*base89 + (35051961/10000000000000000000000 : ℝ)*base91 + (35051961/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1218_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150958703/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14091/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (229/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31121/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29679/50000 : ℝ) else (40019/50000 : ℝ) ≤ X j i ∧ X j i ≤ (83293/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1218_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1218_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150958703/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14091/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (229/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31121/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29679/50000 : ℝ) else (40019/50000 : ℝ) ≤ X j i ∧ X j i ≤ (83293/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1218_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150958703/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14091/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (229/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31121/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29679/50000 : ℝ) else (40019/50000 : ℝ) ≤ X j i ∧ X j i ≤ (83293/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1218_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
