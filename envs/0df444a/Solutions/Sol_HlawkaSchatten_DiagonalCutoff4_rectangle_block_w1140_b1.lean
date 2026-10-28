-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1140_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:30:55.684161+00:00
-- url     : https://prove2.me/submissions/e638f2a0-4996-4388-bddb-35d78fdc9381

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
theorem support_rectangle_w1140_s3_0 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2164020923/10000000000 : ℝ)*x 0 + (5429381769/10000000000 : ℝ)*x 1 + (2615948623/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2164020923/10000000000 : ℝ)^8333 ≤ (13141742002089/100000000000000 : ℝ)^6285 := by
    have hnat : (2164020923 : ℕ)^8333*100000000000000^6285 ≤ 13141742002089^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2164020923 10000000000 13141742002089 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5429381769/10000000000 : ℝ)^8333 ≤ (1779825402329/4000000000000 : ℝ)^6285 := by
    have hnat : (5429381769 : ℕ)^8333*4000000000000^6285 ≤ 1779825402329^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429381769 10000000000 1779825402329 4000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2615948623/5000000000 : ℝ)^8333 ≤ (42362622931411/100000000000000 : ℝ)^6285 := by
    have hnat : (2615948623 : ℕ)^8333*100000000000000^6285 ≤ 42362622931411^6285*5000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615948623 5000000000 42362622931411 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2164020923/10000000000 : ℝ), (5429381769/10000000000 : ℝ), (2615948623/5000000000 : ℝ)] ![(13141742002089/100000000000000 : ℝ), (1779825402329/4000000000000 : ℝ), (42362622931411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2164020923/10000000000 : ℝ)|^8333 ≤ (13141742002089/100000000000000 : ℝ)^6285
        have hw : |(-2164020923/10000000000 : ℝ)|=(2164020923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5429381769/10000000000 : ℝ)|^8333 ≤ (1779825402329/4000000000000 : ℝ)^6285
        have hw : |(5429381769/10000000000 : ℝ)|=(5429381769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2615948623/5000000000 : ℝ)|^8333 ≤ (42362622931411/100000000000000 : ℝ)^6285
        have hw : |(2615948623/5000000000 : ℝ)|=(2615948623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s3_1 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5353841097/10000000000 : ℝ)*x 0 + (-17695099/78125000 : ℝ)*x 1 + (523189709/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353841097/10000000000 : ℝ)^8333 ≤ (43676689057221/100000000000000 : ℝ)^6285 := by
    have hnat : (5353841097 : ℕ)^8333*100000000000000^6285 ≤ 43676689057221^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353841097 10000000000 43676689057221 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17695099/78125000 : ℝ)^8333 ≤ (13960689670739/100000000000000 : ℝ)^6285 := by
    have hnat : (17695099 : ℕ)^8333*100000000000000^6285 ≤ 13960689670739^6285*78125000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17695099 78125000 13960689670739 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (523189709/1000000000 : ℝ)^8333 ≤ (42362621256683/100000000000000 : ℝ)^6285 := by
    have hnat : (523189709 : ℕ)^8333*100000000000000^6285 ≤ 42362621256683^6285*1000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523189709 1000000000 42362621256683 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353841097/10000000000 : ℝ), (-17695099/78125000 : ℝ), (523189709/1000000000 : ℝ)] ![(43676689057221/100000000000000 : ℝ), (13960689670739/100000000000000 : ℝ), (42362621256683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353841097/10000000000 : ℝ)|^8333 ≤ (43676689057221/100000000000000 : ℝ)^6285
        have hw : |(5353841097/10000000000 : ℝ)|=(5353841097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-17695099/78125000 : ℝ)|^8333 ≤ (13960689670739/100000000000000 : ℝ)^6285
        have hw : |(-17695099/78125000 : ℝ)|=(17695099/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(523189709/1000000000 : ℝ)|^8333 ≤ (42362621256683/100000000000000 : ℝ)^6285
        have hw : |(523189709/1000000000 : ℝ)|=(523189709/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s3_2 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (267692059/500000000 : ℝ)*x 0 + (5231897173/10000000000 : ℝ)*x 1 + (-2264972453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267692059/500000000 : ℝ)^8333 ≤ (43676689954977/100000000000000 : ℝ)^6285 := by
    have hnat : (267692059 : ℕ)^8333*100000000000000^6285 ≤ 43676689954977^6285*500000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267692059 500000000 43676689954977 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5231897173/10000000000 : ℝ)^8333 ≤ (10590655536931/25000000000000 : ℝ)^6285 := by
    have hnat : (5231897173 : ℕ)^8333*25000000000000^6285 ≤ 10590655536931^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5231897173 10000000000 10590655536931 25000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2264972453/10000000000 : ℝ)^8333 ≤ (13960687881023/100000000000000 : ℝ)^6285 := by
    have hnat : (2264972453 : ℕ)^8333*100000000000000^6285 ≤ 13960687881023^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2264972453 10000000000 13960687881023 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267692059/500000000 : ℝ), (5231897173/10000000000 : ℝ), (-2264972453/10000000000 : ℝ)] ![(43676689954977/100000000000000 : ℝ), (10590655536931/25000000000000 : ℝ), (13960687881023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267692059/500000000 : ℝ)|^8333 ≤ (43676689954977/100000000000000 : ℝ)^6285
        have hw : |(267692059/500000000 : ℝ)|=(267692059/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5231897173/10000000000 : ℝ)|^8333 ≤ (10590655536931/25000000000000 : ℝ)^6285
        have hw : |(5231897173/10000000000 : ℝ)|=(5231897173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2264972453/10000000000 : ℝ)|^8333 ≤ (13960687881023/100000000000000 : ℝ)^6285
        have hw : |(-2264972453/10000000000 : ℝ)|=(2264972453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s3_3 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (872536947/2000000000 : ℝ)*x 0 + (4170710373/10000000000 : ℝ)*x 1 + (4563446331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (872536947/2000000000 : ℝ)^8333 ≤ (4161747733547/12500000000000 : ℝ)^6285 := by
    have hnat : (872536947 : ℕ)^8333*12500000000000^6285 ≤ 4161747733547^6285*2000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872536947 2000000000 4161747733547 12500000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4170710373/10000000000 : ℝ)^8333 ≤ (15682796115397/50000000000000 : ℝ)^6285 := by
    have hnat : (4170710373 : ℕ)^8333*50000000000000^6285 ≤ 15682796115397^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170710373 10000000000 15682796115397 50000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4563446331/10000000000 : ℝ)^8333 ≤ (35340425883893/100000000000000 : ℝ)^6285 := by
    have hnat : (4563446331 : ℕ)^8333*100000000000000^6285 ≤ 35340425883893^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4563446331 10000000000 35340425883893 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(872536947/2000000000 : ℝ), (4170710373/10000000000 : ℝ), (4563446331/10000000000 : ℝ)] ![(4161747733547/12500000000000 : ℝ), (15682796115397/50000000000000 : ℝ), (35340425883893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(872536947/2000000000 : ℝ)|^8333 ≤ (4161747733547/12500000000000 : ℝ)^6285
        have hw : |(872536947/2000000000 : ℝ)|=(872536947/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4170710373/10000000000 : ℝ)|^8333 ≤ (15682796115397/50000000000000 : ℝ)^6285
        have hw : |(4170710373/10000000000 : ℝ)|=(4170710373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4563446331/10000000000 : ℝ)|^8333 ≤ (35340425883893/100000000000000 : ℝ)^6285
        have hw : |(4563446331/10000000000 : ℝ)|=(4563446331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s3_4 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2164039089/10000000000 : ℝ)*x 0 + (5232664333/10000000000 : ℝ)*x 1 + (542861039/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2164039089/10000000000 : ℝ)^8333 ≤ (1314188826947/10000000000000 : ℝ)^6285 := by
    have hnat : (2164039089 : ℕ)^8333*10000000000000^6285 ≤ 1314188826947^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2164039089 10000000000 1314188826947 10000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5232664333/10000000000 : ℝ)^8333 ≤ (10592714535611/25000000000000 : ℝ)^6285 := by
    have hnat : (5232664333 : ℕ)^8333*25000000000000^6285 ≤ 10592714535611^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5232664333 10000000000 10592714535611 25000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (542861039/1000000000 : ℝ)^8333 ≤ (22243626787433/50000000000000 : ℝ)^6285 := by
    have hnat : (542861039 : ℕ)^8333*50000000000000^6285 ≤ 22243626787433^6285*1000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542861039 1000000000 22243626787433 50000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2164039089/10000000000 : ℝ), (5232664333/10000000000 : ℝ), (542861039/1000000000 : ℝ)] ![(1314188826947/10000000000000 : ℝ), (10592714535611/25000000000000 : ℝ), (22243626787433/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2164039089/10000000000 : ℝ)|^8333 ≤ (1314188826947/10000000000000 : ℝ)^6285
        have hw : |(-2164039089/10000000000 : ℝ)|=(2164039089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5232664333/10000000000 : ℝ)|^8333 ≤ (10592714535611/25000000000000 : ℝ)^6285
        have hw : |(5232664333/10000000000 : ℝ)|=(5232664333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(542861039/1000000000 : ℝ)|^8333 ≤ (22243626787433/50000000000000 : ℝ)^6285
        have hw : |(542861039/1000000000 : ℝ)|=(542861039/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s3_5 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5303816461/10000000000 : ℝ)*x 0 + (-2068259937/10000000000 : ℝ)*x 1 + (5428610091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303816461/10000000000 : ℝ)^8333 ≤ (43136431036451/100000000000000 : ℝ)^6285 := by
    have hnat : (5303816461 : ℕ)^8333*100000000000000^6285 ≤ 43136431036451^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303816461 10000000000 43136431036451 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2068259937/10000000000 : ℝ)^8333 ≤ (2475263724483/20000000000000 : ℝ)^6285 := by
    have hnat : (2068259937 : ℕ)^8333*20000000000000^6285 ≤ 2475263724483^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068259937 10000000000 2475263724483 20000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5428610091/10000000000 : ℝ)^8333 ≤ (44487250326131/100000000000000 : ℝ)^6285 := by
    have hnat : (5428610091 : ℕ)^8333*100000000000000^6285 ≤ 44487250326131^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428610091 10000000000 44487250326131 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303816461/10000000000 : ℝ), (-2068259937/10000000000 : ℝ), (5428610091/10000000000 : ℝ)] ![(43136431036451/100000000000000 : ℝ), (2475263724483/20000000000000 : ℝ), (44487250326131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303816461/10000000000 : ℝ)|^8333 ≤ (43136431036451/100000000000000 : ℝ)^6285
        have hw : |(5303816461/10000000000 : ℝ)|=(5303816461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2068259937/10000000000 : ℝ)|^8333 ≤ (2475263724483/20000000000000 : ℝ)^6285
        have hw : |(-2068259937/10000000000 : ℝ)|=(2068259937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5428610091/10000000000 : ℝ)|^8333 ≤ (44487250326131/100000000000000 : ℝ)^6285
        have hw : |(5428610091/10000000000 : ℝ)|=(5428610091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s3_6 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1060763449/2000000000 : ℝ)*x 0 + (5428609517/10000000000 : ℝ)*x 1 + (-2068259657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060763449/2000000000 : ℝ)^8333 ≤ (43136439490561/100000000000000 : ℝ)^6285 := by
    have hnat : (1060763449 : ℕ)^8333*100000000000000^6285 ≤ 43136439490561^6285*2000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060763449 2000000000 43136439490561 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5428609517/10000000000 : ℝ)^8333 ≤ (44487244089431/100000000000000 : ℝ)^6285 := by
    have hnat : (5428609517 : ℕ)^8333*100000000000000^6285 ≤ 44487244089431^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428609517 10000000000 44487244089431 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2068259657/10000000000 : ℝ)^8333 ≤ (773519775059/6250000000000 : ℝ)^6285 := by
    have hnat : (2068259657 : ℕ)^8333*6250000000000^6285 ≤ 773519775059^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068259657 10000000000 773519775059 6250000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060763449/2000000000 : ℝ), (5428609517/10000000000 : ℝ), (-2068259657/10000000000 : ℝ)] ![(43136439490561/100000000000000 : ℝ), (44487244089431/100000000000000 : ℝ), (773519775059/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060763449/2000000000 : ℝ)|^8333 ≤ (43136439490561/100000000000000 : ℝ)^6285
        have hw : |(1060763449/2000000000 : ℝ)|=(1060763449/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5428609517/10000000000 : ℝ)|^8333 ≤ (44487244089431/100000000000000 : ℝ)^6285
        have hw : |(5428609517/10000000000 : ℝ)|=(5428609517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2068259657/10000000000 : ℝ)|^8333 ≤ (773519775059/6250000000000 : ℝ)^6285
        have hw : |(-2068259657/10000000000 : ℝ)|=(2068259657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s3_7 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (21813603/50000000 : ℝ)*x 0 + (912384173/2000000000 : ℝ)*x 1 + (2086122331/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21813603/50000000 : ℝ)^8333 ≤ (33294344762073/100000000000000 : ℝ)^6285 := by
    have hnat : (21813603 : ℕ)^8333*100000000000000^6285 ≤ 33294344762073^6285*50000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21813603 50000000 33294344762073 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (912384173/2000000000 : ℝ)^8333 ≤ (2207797727893/6250000000000 : ℝ)^6285 := by
    have hnat : (912384173 : ℕ)^8333*6250000000000^6285 ≤ 2207797727893^6285*2000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      912384173 2000000000 2207797727893 6250000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086122331/5000000000 : ℝ)^8333 ≤ (6276178314597/20000000000000 : ℝ)^6285 := by
    have hnat : (2086122331 : ℕ)^8333*20000000000000^6285 ≤ 6276178314597^6285*5000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086122331 5000000000 6276178314597 20000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21813603/50000000 : ℝ), (912384173/2000000000 : ℝ), (2086122331/5000000000 : ℝ)] ![(33294344762073/100000000000000 : ℝ), (2207797727893/6250000000000 : ℝ), (6276178314597/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21813603/50000000 : ℝ)|^8333 ≤ (33294344762073/100000000000000 : ℝ)^6285
        have hw : |(21813603/50000000 : ℝ)|=(21813603/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(912384173/2000000000 : ℝ)|^8333 ≤ (2207797727893/6250000000000 : ℝ)^6285
        have hw : |(912384173/2000000000 : ℝ)|=(912384173/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2086122331/5000000000 : ℝ)|^8333 ≤ (6276178314597/20000000000000 : ℝ)^6285
        have hw : |(2086122331/5000000000 : ℝ)|=(2086122331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1140_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149434687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4127/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9061/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10629/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1851/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4127/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9061/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4127/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9061/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4127/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9061/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4127/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9061/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4127/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9061/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4127/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9061/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9061/100000 : ℝ) ^ (2083/512 : ℝ) ≤ (228811435092061/4000000000000000000 : ℝ) := by
    have hpowers : (9061/100000 : ℝ)^2083 ≤ (228811435092061/4000000000000000000 : ℝ)^512 := by
      have hnat : (9061 : ℕ)^2083*4000000000000000000^512 ≤ 228811435092061^512*100000^2083 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9061 100000 228811435092061 4000000000000000000 2083 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9061/100000 : ℝ)) (X := (228811435092061/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2083 512 (by norm_num) hpowers
    exact h
  have hpowhi : (4127/25000 : ℝ) ^ (2083/512 : ℝ) ≤ (65659855565795567/100000000000000000000 : ℝ) := by
    have hpowers : (4127/25000 : ℝ)^2083 ≤ (65659855565795567/100000000000000000000 : ℝ)^512 := by
      have hnat : (4127 : ℕ)^2083*100000000000000000000^512 ≤ 65659855565795567^512*25000^2083 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4127 25000 65659855565795567 100000000000000000000 2083 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4127/25000 : ℝ)) (X := (65659855565795567/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2083 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000228811435092061/2000000000000000000 : ℝ) ≤ (1250035149544199/1250000000000000 : ℝ) ^ (2083/512 : ℝ) := by
    have hpowers : (2000228811435092061/2000000000000000000 : ℝ)^512 ≤ (1250035149544199/1250000000000000 : ℝ)^2083 := by
      have hnat : (2000228811435092061 : ℕ)^512*1250000000000000^2083 ≤ 1250035149544199^2083*2000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000228811435092061 2000000000000000000 1250035149544199 1250000000000000 512 2083 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250035149544199/1250000000000000 : ℝ)) (X := (2000228811435092061/2000000000000000000 : ℝ)) (by norm_num) 2083 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25017845035360774273/25000000000000000000 : ℝ) ≤ (500087702350197/500000000000000 : ℝ) ^ (2083/512 : ℝ) := by
    have hpowers : (25017845035360774273/25000000000000000000 : ℝ)^512 ≤ (500087702350197/500000000000000 : ℝ)^2083 := by
      have hnat : (25017845035360774273 : ℕ)^512*500000000000000^2083 ≤ 500087702350197^2083*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017845035360774273 25000000000000000000 500087702350197 500000000000000 512 2083 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500087702350197/500000000000000 : ℝ)) (X := (25017845035360774273/25000000000000000000 : ℝ)) (by norm_num) 2083 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50065659855565795567/50000000000000000000 : ℝ) ≤ (625201681103393/625000000000000 : ℝ) ^ (2083/512 : ℝ) := by
    have hpowers : (50065659855565795567/50000000000000000000 : ℝ)^512 ≤ (625201681103393/625000000000000 : ℝ)^2083 := by
      have hnat : (50065659855565795567 : ℕ)^512*625000000000000^2083 ≤ 625201681103393^2083*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50065659855565795567 50000000000000000000 625201681103393 625000000000000 512 2083 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625201681103393/625000000000000 : ℝ)) (X := (50065659855565795567/50000000000000000000 : ℝ)) (by norm_num) 2083 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(228811435092061/4000000000000000000 : ℝ) ≤ ((422985244714543143/423125000000000000 : ℝ)+2*(33473878417/16925000000000 : ℝ)*(9061/100000 : ℝ))^(2083/512 : ℝ) := by
    rw [show (422985244714543143/423125000000000000 : ℝ)+2*(33473878417/16925000000000 : ℝ)*(9061/100000 : ℝ)=(1250035149544199/1250000000000000 : ℝ) by norm_num, show 1+2*(228811435092061/4000000000000000000 : ℝ)=(2000228811435092061/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(65659855565795567/100000000000000000000 : ℝ)+(228811435092061/4000000000000000000 : ℝ) ≤ ((422985244714543143/423125000000000000 : ℝ)+(33473878417/16925000000000 : ℝ)*((4127/25000 : ℝ)+(9061/100000 : ℝ)))^(2083/512 : ℝ) := by
    rw [show (422985244714543143/423125000000000000 : ℝ)+(33473878417/16925000000000 : ℝ)*((4127/25000 : ℝ)+(9061/100000 : ℝ))=(500087702350197/500000000000000 : ℝ) by norm_num, show 1+(65659855565795567/100000000000000000000 : ℝ)+(228811435092061/4000000000000000000 : ℝ)=(25017845035360774273/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(65659855565795567/100000000000000000000 : ℝ) ≤ ((422985244714543143/423125000000000000 : ℝ)+2*(33473878417/16925000000000 : ℝ)*(4127/25000 : ℝ))^(2083/512 : ℝ) := by
    rw [show (422985244714543143/423125000000000000 : ℝ)+2*(33473878417/16925000000000 : ℝ)*(4127/25000 : ℝ)=(625201681103393/625000000000000 : ℝ) by norm_num, show 1+2*(65659855565795567/100000000000000000000 : ℝ)=(50065659855565795567/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (422985244714543143/423125000000000000 : ℝ)*(X 1 0+X 2 0)+(33473878417/16925000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2083/512 : ℝ)) (lo := (9061/100000 : ℝ)) (hi := (4127/25000 : ℝ)) (c := (422985244714543143/423125000000000000 : ℝ)) (alpha := (33473878417/16925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (422985244714543143/423125000000000000 : ℝ)*(X 0 1+X 2 1)+(33473878417/16925000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2083/512 : ℝ)) (lo := (9061/100000 : ℝ)) (hi := (4127/25000 : ℝ)) (c := (422985244714543143/423125000000000000 : ℝ)) (alpha := (33473878417/16925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (422985244714543143/423125000000000000 : ℝ)*(X 0 2+X 1 2)+(33473878417/16925000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2083/512 : ℝ)) (lo := (9061/100000 : ℝ)) (hi := (4127/25000 : ℝ)) (c := (422985244714543143/423125000000000000 : ℝ)) (alpha := (33473878417/16925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2164020923/10000000000 : ℝ)*X 0 0+(5429381769/10000000000 : ℝ)*X 0 1+(2615948623/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353841097/10000000000 : ℝ)*X 1 0+(-17695099/78125000 : ℝ)*X 1 1+(523189709/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267692059/500000000 : ℝ)*X 2 0+(5231897173/10000000000 : ℝ)*X 2 1+(-2264972453/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((872536947/2000000000 : ℝ)*X 0 0+(4170710373/10000000000 : ℝ)*X 0 1+(4563446331/10000000000 : ℝ)*X 0 2+(872536947/2000000000 : ℝ)*X 1 0+(4170710373/10000000000 : ℝ)*X 1 1+(4563446331/10000000000 : ℝ)*X 1 2+(872536947/2000000000 : ℝ)*X 2 0+(4170710373/10000000000 : ℝ)*X 2 1+(4563446331/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2164039089/10000000000 : ℝ)*X 0 0+(5232664333/10000000000 : ℝ)*X 0 1+(542861039/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5303816461/10000000000 : ℝ)*X 1 0+(-2068259937/10000000000 : ℝ)*X 1 1+(5428610091/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1060763449/2000000000 : ℝ)*X 2 0+(5428609517/10000000000 : ℝ)*X 2 1+(-2068259657/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((21813603/50000000 : ℝ)*X 0 0+(912384173/2000000000 : ℝ)*X 0 1+(2086122331/5000000000 : ℝ)*X 0 2+(21813603/50000000 : ℝ)*X 1 0+(912384173/2000000000 : ℝ)*X 1 1+(2086122331/5000000000 : ℝ)*X 1 2+(21813603/50000000 : ℝ)*X 2 0+(912384173/2000000000 : ℝ)*X 2 1+(2086122331/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (31314202391729967295368087/5289062500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1558238721/100000000000000 : ℝ)*(base19) + (295222533/20000000000000 : ℝ)*(base23) + (42999013/50000000000000 : ℝ)*(lower2) + (76479989/100000000000000 : ℝ)*(upper3) + (199794021/100000000000000 : ℝ)*(upper5) + (3805003347452437/100000000000000 : ℝ)*(major0) + (3805003347452437/100000000000000 : ℝ)*(major1) + (1902501673726219/50000000000000 : ℝ)*(major2) + (5063711487677291/100000000000000 : ℝ)*(sp0) + (5063739795765279/100000000000000 : ℝ)*(sp1) + (2531869938945667/50000000000000 : ℝ)*(sp2) + (2546252911787183/100000000000000 : ℝ)*(sp3) + (29866326709/100000000000000 : ℝ)*(sp4) + (6115880871/50000000000000 : ℝ)*(sp7) + (1273132571774463/50000000000000 : ℝ)*(f.failure) + (5063741354003999/100000000000000 : ℝ)*(f.sum) + (3439858952703/677000000000000000000000000 : ℝ)*base65 + (201259754250923009/42312500000000000000000000000000 : ℝ)*base68 + (44238963489527433/21156250000000000000000000000000 : ℝ)*base70 + (550385853290360509/42312500000000000000000000000000 : ℝ)*base72 + (1447927546273/677000000000000000000000000 : ℝ)*base73 + (302167310879464933/21156250000000000000000000000000 : ℝ)*base76 + (477533918350098009/42312500000000000000000000000000 : ℝ)*base78 + (21655829546473009/42312500000000000000000000000000 : ℝ)*base80 + (6467141311041/3385000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (62998081/5000000000000000000000 : ℝ)*base89 + (62998081/5000000000000000000000 : ℝ)*base91 + (12998081/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (33135578922746580500229921/5289062500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1161915057/100000000000000 : ℝ)*(base19) + (203895377/10000000000000 : ℝ)*(base23) + (51412833/100000000000000 : ℝ)*(upper3) + (678033/3125000000000 : ℝ)*(lower4) + (39595781/25000000000000 : ℝ)*(upper5) + (239677769344003/6250000000000 : ℝ)*(major0) + (239677769344003/6250000000000 : ℝ)*(major1) + (239677769344003/6250000000000 : ℝ)*(major2) + (1663085651/10000000000000 : ℝ)*(sp1) + (1011937973/4000000000000 : ℝ)*(sp2) + (1275863508202687/25000000000000 : ℝ)*(sp4) + (5103436240039181/100000000000000 : ℝ)*(sp5) + (5103426695407653/100000000000000 : ℝ)*(sp6) + (1283117188683257/50000000000000 : ℝ)*(sp7) + (1283117188683257/50000000000000 : ℝ)*(f.failure) + (1275863508202687/25000000000000 : ℝ)*(f.sum) + (681964547429/846250000000000000000000000 : ℝ)*base66 + (71726314487229017/5289062500000000000000000000000 : ℝ)*base68 + (7935581944729799/661132812500000000000000000000 : ℝ)*base70 + (30769920563661159/10578125000000000000000000000000 : ℝ)*base72 + (24142615443741/3385000000000000000000000000 : ℝ)*base74 + (4283432888588841/10578125000000000000000000000000 : ℝ)*base75 + (47629649026129909/10578125000000000000000000000000 : ℝ)*base78 + (3564925213232087/330566406250000000000000000000 : ℝ)*base80 + (7925733305703/1692500000000000000000000000 : ℝ)*base82 + (51935559/5000000000000000000000 : ℝ)*base89 + (51935559/5000000000000000000000 : ℝ)*base91 + (51935559/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1140_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149434687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4127/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9061/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10629/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1851/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1140_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1140_s4_0 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2167036587/10000000000 : ℝ)*x 0 + (2700994161/5000000000 : ℝ)*x 1 + (1314329553/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2167036587/10000000000 : ℝ)^8333 ≤ (13166028734963/100000000000000 : ℝ)^6285 := by
    have hnat : (2167036587 : ℕ)^8333*100000000000000^6285 ≤ 13166028734963^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2167036587 10000000000 13166028734963 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2700994161/5000000000 : ℝ)^8333 ≤ (22099113663237/50000000000000 : ℝ)^6285 := by
    have hnat : (2700994161 : ℕ)^8333*50000000000000^6285 ≤ 22099113663237^6285*5000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700994161 5000000000 22099113663237 50000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1314329553/2500000000 : ℝ)^8333 ≤ (4263574392279/10000000000000 : ℝ)^6285 := by
    have hnat : (1314329553 : ℕ)^8333*10000000000000^6285 ≤ 4263574392279^6285*2500000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314329553 2500000000 4263574392279 10000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2167036587/10000000000 : ℝ), (2700994161/5000000000 : ℝ), (1314329553/2500000000 : ℝ)] ![(13166028734963/100000000000000 : ℝ), (22099113663237/50000000000000 : ℝ), (4263574392279/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2167036587/10000000000 : ℝ)|^8333 ≤ (13166028734963/100000000000000 : ℝ)^6285
        have hw : |(-2167036587/10000000000 : ℝ)|=(2167036587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2700994161/5000000000 : ℝ)|^8333 ≤ (22099113663237/50000000000000 : ℝ)^6285
        have hw : |(2700994161/5000000000 : ℝ)|=(2700994161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1314329553/2500000000 : ℝ)|^8333 ≤ (4263574392279/10000000000000 : ℝ)^6285
        have hw : |(1314329553/2500000000 : ℝ)|=(1314329553/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s4_1 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1069400307/2000000000 : ℝ)*x 0 + (-1120279351/5000000000 : ℝ)*x 1 + (5257318773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069400307/2000000000 : ℝ)^8333 ≤ (43602725431451/100000000000000 : ℝ)^6285 := by
    have hnat : (1069400307 : ℕ)^8333*100000000000000^6285 ≤ 43602725431451^6285*2000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069400307 2000000000 43602725431451 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1120279351/5000000000 : ℝ)^8333 ≤ (3440381149117/25000000000000 : ℝ)^6285 := by
    have hnat : (1120279351 : ℕ)^8333*25000000000000^6285 ≤ 3440381149117^6285*5000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120279351 5000000000 3440381149117 25000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5257318773/10000000000 : ℝ)^8333 ≤ (4263574995489/10000000000000 : ℝ)^6285 := by
    have hnat : (5257318773 : ℕ)^8333*10000000000000^6285 ≤ 4263574995489^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257318773 10000000000 4263574995489 10000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069400307/2000000000 : ℝ), (-1120279351/5000000000 : ℝ), (5257318773/10000000000 : ℝ)] ![(43602725431451/100000000000000 : ℝ), (3440381149117/25000000000000 : ℝ), (4263574995489/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069400307/2000000000 : ℝ)|^8333 ≤ (43602725431451/100000000000000 : ℝ)^6285
        have hw : |(1069400307/2000000000 : ℝ)|=(1069400307/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1120279351/5000000000 : ℝ)|^8333 ≤ (3440381149117/25000000000000 : ℝ)^6285
        have hw : |(-1120279351/5000000000 : ℝ)|=(1120279351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5257318773/10000000000 : ℝ)|^8333 ≤ (4263574995489/10000000000000 : ℝ)^6285
        have hw : |(5257318773/10000000000 : ℝ)|=(5257318773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s4_2 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5347002037/10000000000 : ℝ)*x 0 + (2628658907/5000000000 : ℝ)*x 1 + (-1120279651/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347002037/10000000000 : ℝ)^8333 ≤ (43602730858993/100000000000000 : ℝ)^6285 := by
    have hnat : (5347002037 : ℕ)^8333*100000000000000^6285 ≤ 43602730858993^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347002037 10000000000 43602730858993 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2628658907/5000000000 : ℝ)^8333 ≤ (10658934910833/25000000000000 : ℝ)^6285 := by
    have hnat : (2628658907 : ℕ)^8333*25000000000000^6285 ≤ 10658934910833^6285*5000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628658907 5000000000 10658934910833 25000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1120279651/5000000000 : ℝ)^8333 ≤ (2752305896503/20000000000000 : ℝ)^6285 := by
    have hnat : (1120279651 : ℕ)^8333*20000000000000^6285 ≤ 2752305896503^6285*5000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120279651 5000000000 2752305896503 20000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347002037/10000000000 : ℝ), (2628658907/5000000000 : ℝ), (-1120279651/5000000000 : ℝ)] ![(43602730858993/100000000000000 : ℝ), (10658934910833/25000000000000 : ℝ), (2752305896503/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347002037/10000000000 : ℝ)|^8333 ≤ (43602730858993/100000000000000 : ℝ)^6285
        have hw : |(5347002037/10000000000 : ℝ)|=(5347002037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2628658907/5000000000 : ℝ)|^8333 ≤ (10658934910833/25000000000000 : ℝ)^6285
        have hw : |(2628658907/5000000000 : ℝ)|=(2628658907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1120279651/5000000000 : ℝ)|^8333 ≤ (2752305896503/20000000000000 : ℝ)^6285
        have hw : |(-1120279651/5000000000 : ℝ)|=(1120279651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s4_3 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (174579441/400000000 : ℝ)*x 0 + (422299121/1000000000 : ℝ)*x 1 + (4510698141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174579441/400000000 : ℝ)^8333 ≤ (16656104553049/50000000000000 : ℝ)^6285 := by
    have hnat : (174579441 : ℕ)^8333*50000000000000^6285 ≤ 16656104553049^6285*400000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174579441 400000000 16656104553049 50000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (422299121/1000000000 : ℝ)^8333 ≤ (7971986785387/25000000000000 : ℝ)^6285 := by
    have hnat : (422299121 : ℕ)^8333*25000000000000^6285 ≤ 7971986785387^6285*1000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422299121 1000000000 7971986785387 25000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4510698141/10000000000 : ℝ)^8333 ≤ (6959968748147/20000000000000 : ℝ)^6285 := by
    have hnat : (4510698141 : ℕ)^8333*20000000000000^6285 ≤ 6959968748147^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4510698141 10000000000 6959968748147 20000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(174579441/400000000 : ℝ), (422299121/1000000000 : ℝ), (4510698141/10000000000 : ℝ)] ![(16656104553049/50000000000000 : ℝ), (7971986785387/25000000000000 : ℝ), (6959968748147/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(174579441/400000000 : ℝ)|^8333 ≤ (16656104553049/50000000000000 : ℝ)^6285
        have hw : |(174579441/400000000 : ℝ)|=(174579441/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(422299121/1000000000 : ℝ)|^8333 ≤ (7971986785387/25000000000000 : ℝ)^6285
        have hw : |(422299121/1000000000 : ℝ)|=(422299121/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4510698141/10000000000 : ℝ)|^8333 ≤ (6959968748147/20000000000000 : ℝ)^6285
        have hw : |(4510698141/10000000000 : ℝ)|=(4510698141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s4_4 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2167044451/10000000000 : ℝ)*x 0 + (2628865007/5000000000 : ℝ)*x 1 + (5401574297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2167044451/10000000000 : ℝ)^8333 ≤ (3291523020577/25000000000000 : ℝ)^6285 := by
    have hnat : (2167044451 : ℕ)^8333*25000000000000^6285 ≤ 3291523020577^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2167044451 10000000000 3291523020577 25000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2628865007/5000000000 : ℝ)^8333 ≤ (666252685029/1562500000000 : ℝ)^6285 := by
    have hnat : (2628865007 : ℕ)^8333*1562500000000^6285 ≤ 666252685029^6285*5000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628865007 5000000000 666252685029 1562500000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5401574297/10000000000 : ℝ)^8333 ≤ (5524217007979/12500000000000 : ℝ)^6285 := by
    have hnat : (5401574297 : ℕ)^8333*12500000000000^6285 ≤ 5524217007979^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401574297 10000000000 5524217007979 12500000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2167044451/10000000000 : ℝ), (2628865007/5000000000 : ℝ), (5401574297/10000000000 : ℝ)] ![(3291523020577/25000000000000 : ℝ), (666252685029/1562500000000 : ℝ), (5524217007979/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2167044451/10000000000 : ℝ)|^8333 ≤ (3291523020577/25000000000000 : ℝ)^6285
        have hw : |(-2167044451/10000000000 : ℝ)|=(2167044451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2628865007/5000000000 : ℝ)|^8333 ≤ (666252685029/1562500000000 : ℝ)^6285
        have hw : |(2628865007/5000000000 : ℝ)|=(2628865007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5401574297/10000000000 : ℝ)|^8333 ≤ (5524217007979/12500000000000 : ℝ)^6285
        have hw : |(5401574297/10000000000 : ℝ)|=(5401574297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s4_5 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (331897309/625000000 : ℝ)*x 0 + (-2096302153/10000000000 : ℝ)*x 1 + (5401574311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331897309/625000000 : ℝ)^8333 ≤ (10801743303773/25000000000000 : ℝ)^6285 := by
    have hnat : (331897309 : ℕ)^8333*25000000000000^6285 ≤ 10801743303773^6285*625000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331897309 625000000 10801743303773 25000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2096302153/10000000000 : ℝ)^8333 ≤ (3149822639501/25000000000000 : ℝ)^6285 := by
    have hnat : (2096302153 : ℕ)^8333*25000000000000^6285 ≤ 3149822639501^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096302153 10000000000 3149822639501 25000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5401574311/10000000000 : ℝ)^8333 ≤ (44193736215699/100000000000000 : ℝ)^6285 := by
    have hnat : (5401574311 : ℕ)^8333*100000000000000^6285 ≤ 44193736215699^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401574311 10000000000 44193736215699 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331897309/625000000 : ℝ), (-2096302153/10000000000 : ℝ), (5401574311/10000000000 : ℝ)] ![(10801743303773/25000000000000 : ℝ), (3149822639501/25000000000000 : ℝ), (44193736215699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331897309/625000000 : ℝ)|^8333 ≤ (10801743303773/25000000000000 : ℝ)^6285
        have hw : |(331897309/625000000 : ℝ)|=(331897309/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2096302153/10000000000 : ℝ)|^8333 ≤ (3149822639501/25000000000000 : ℝ)^6285
        have hw : |(-2096302153/10000000000 : ℝ)|=(2096302153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5401574311/10000000000 : ℝ)|^8333 ≤ (44193736215699/100000000000000 : ℝ)^6285
        have hw : |(5401574311/10000000000 : ℝ)|=(5401574311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s4_6 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (66379463/125000000 : ℝ)*x 0 + (67519677/125000000 : ℝ)*x 1 + (-2096302229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66379463/125000000 : ℝ)^8333 ≤ (8641394850141/20000000000000 : ℝ)^6285 := by
    have hnat : (66379463 : ℕ)^8333*20000000000000^6285 ≤ 8641394850141^6285*125000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66379463 125000000 8641394850141 20000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67519677/125000000 : ℝ)^8333 ≤ (44193734577701/100000000000000 : ℝ)^6285 := by
    have hnat : (67519677 : ℕ)^8333*100000000000000^6285 ≤ 44193734577701^6285*125000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67519677 125000000 44193734577701 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2096302229/10000000000 : ℝ)^8333 ≤ (6299645581813/50000000000000 : ℝ)^6285 := by
    have hnat : (2096302229 : ℕ)^8333*50000000000000^6285 ≤ 6299645581813^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096302229 10000000000 6299645581813 50000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66379463/125000000 : ℝ), (67519677/125000000 : ℝ), (-2096302229/10000000000 : ℝ)] ![(8641394850141/20000000000000 : ℝ), (44193734577701/100000000000000 : ℝ), (6299645581813/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66379463/125000000 : ℝ)|^8333 ≤ (8641394850141/20000000000000 : ℝ)^6285
        have hw : |(66379463/125000000 : ℝ)|=(66379463/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(67519677/125000000 : ℝ)|^8333 ≤ (44193734577701/100000000000000 : ℝ)^6285
        have hw : |(67519677/125000000 : ℝ)|=(67519677/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2096302229/10000000000 : ℝ)|^8333 ≤ (6299645581813/50000000000000 : ℝ)^6285
        have hw : |(-2096302229/10000000000 : ℝ)|=(2096302229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s4_7 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4364499893/10000000000 : ℝ)*x 0 + (4404177/9765625 : ℝ)*x 1 + (2111907927/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4364499893/10000000000 : ℝ)^8333 ≤ (33312349445779/100000000000000 : ℝ)^6285 := by
    have hnat : (4364499893 : ℕ)^8333*100000000000000^6285 ≤ 33312349445779^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364499893 10000000000 33312349445779 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4404177/9765625 : ℝ)^8333 ≤ (17395723571927/50000000000000 : ℝ)^6285 := by
    have hnat : (4404177 : ℕ)^8333*50000000000000^6285 ≤ 17395723571927^6285*9765625^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4404177 9765625 17395723571927 50000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2111907927/5000000000 : ℝ)^8333 ≤ (7974050847739/25000000000000 : ℝ)^6285 := by
    have hnat : (2111907927 : ℕ)^8333*25000000000000^6285 ≤ 7974050847739^6285*5000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111907927 5000000000 7974050847739 25000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4364499893/10000000000 : ℝ), (4404177/9765625 : ℝ), (2111907927/5000000000 : ℝ)] ![(33312349445779/100000000000000 : ℝ), (17395723571927/50000000000000 : ℝ), (7974050847739/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4364499893/10000000000 : ℝ)|^8333 ≤ (33312349445779/100000000000000 : ℝ)^6285
        have hw : |(4364499893/10000000000 : ℝ)|=(4364499893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4404177/9765625 : ℝ)|^8333 ≤ (17395723571927/50000000000000 : ℝ)^6285
        have hw : |(4404177/9765625 : ℝ)|=(4404177/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2111907927/5000000000 : ℝ)|^8333 ≤ (7974050847739/25000000000000 : ℝ)^6285
        have hw : |(2111907927/5000000000 : ℝ)|=(2111907927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1140_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149434687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1851/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10629/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2793/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2847/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1851/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10629/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1851/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10629/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1851/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10629/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1851/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10629/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1851/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10629/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1851/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10629/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
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
  have hpowlo : (10629/100000 : ℝ) ^ (2083/512 : ℝ) ≤ (2737544996185809/25000000000000000000 : ℝ) := by
    have hpowers : (10629/100000 : ℝ)^2083 ≤ (2737544996185809/25000000000000000000 : ℝ)^512 := by
      have hnat : (10629 : ℕ)^2083*25000000000000000000^512 ≤ 2737544996185809^512*100000^2083 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10629 100000 2737544996185809 25000000000000000000 2083 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10629/100000 : ℝ)) (X := (2737544996185809/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2083 512 (by norm_num) hpowers
    exact h
  have hpowhi : (1851/12500 : ℝ) ^ (2083/512 : ℝ) ≤ (2637310677401743/6250000000000000000 : ℝ) := by
    have hpowers : (1851/12500 : ℝ)^2083 ≤ (2637310677401743/6250000000000000000 : ℝ)^512 := by
      have hnat : (1851 : ℕ)^2083*6250000000000000000^512 ≤ 2637310677401743^512*12500^2083 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1851 12500 2637310677401743 6250000000000000000 2083 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1851/12500 : ℝ)) (X := (2637310677401743/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 2083 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502737544996185809/12500000000000000000 : ℝ) ≤ (10000538264924807/10000000000000000 : ℝ) ^ (2083/512 : ℝ) := by
    have hpowers : (12502737544996185809/12500000000000000000 : ℝ)^512 ≤ (10000538264924807/10000000000000000 : ℝ)^2083 := by
      have hnat : (12502737544996185809 : ℕ)^512*10000000000000000^2083 ≤ 10000538264924807^2083*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502737544996185809 12500000000000000000 10000538264924807 10000000000000000 512 2083 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000538264924807/10000000000000000 : ℝ)) (X := (12502737544996185809/12500000000000000000 : ℝ)) (by norm_num) 2083 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25013286787705792781/25000000000000000000 : ℝ) ≤ (625081630728729/625000000000000 : ℝ) ^ (2083/512 : ℝ) := by
    have hpowers : (25013286787705792781/25000000000000000000 : ℝ)^512 ≤ (625081630728729/625000000000000 : ℝ)^2083 := by
      have hnat : (25013286787705792781 : ℕ)^512*625000000000000^2083 ≤ 625081630728729^2083*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013286787705792781 25000000000000000000 625081630728729 625000000000000 512 2083 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625081630728729/625000000000000 : ℝ)) (X := (25013286787705792781/25000000000000000000 : ℝ)) (by norm_num) 2083 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (3127637310677401743/3125000000000000000 : ℝ) ≤ (10002073918394521/10000000000000000 : ℝ) ^ (2083/512 : ℝ) := by
    have hpowers : (3127637310677401743/3125000000000000000 : ℝ)^512 ≤ (10002073918394521/10000000000000000 : ℝ)^2083 := by
      have hnat : (3127637310677401743 : ℕ)^512*10000000000000000^2083 ≤ 10002073918394521^2083*3125000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3127637310677401743 3125000000000000000 10002073918394521 10000000000000000 512 2083 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002073918394521/10000000000000000 : ℝ)) (X := (3127637310677401743/3125000000000000000 : ℝ)) (by norm_num) 2083 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2737544996185809/25000000000000000000 : ℝ) ≤ ((1989329854685294207/1990000000000000000 : ℝ)+2*(109689533551/59700000000000 : ℝ)*(10629/100000 : ℝ))^(2083/512 : ℝ) := by
    rw [show (1989329854685294207/1990000000000000000 : ℝ)+2*(109689533551/59700000000000 : ℝ)*(10629/100000 : ℝ)=(10000538264924807/10000000000000000 : ℝ) by norm_num, show 1+2*(2737544996185809/25000000000000000000 : ℝ)=(12502737544996185809/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2637310677401743/6250000000000000000 : ℝ)+(2737544996185809/25000000000000000000 : ℝ) ≤ ((1989329854685294207/1990000000000000000 : ℝ)+(109689533551/59700000000000 : ℝ)*((1851/12500 : ℝ)+(10629/100000 : ℝ)))^(2083/512 : ℝ) := by
    rw [show (1989329854685294207/1990000000000000000 : ℝ)+(109689533551/59700000000000 : ℝ)*((1851/12500 : ℝ)+(10629/100000 : ℝ))=(625081630728729/625000000000000 : ℝ) by norm_num, show 1+(2637310677401743/6250000000000000000 : ℝ)+(2737544996185809/25000000000000000000 : ℝ)=(25013286787705792781/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2637310677401743/6250000000000000000 : ℝ) ≤ ((1989329854685294207/1990000000000000000 : ℝ)+2*(109689533551/59700000000000 : ℝ)*(1851/12500 : ℝ))^(2083/512 : ℝ) := by
    rw [show (1989329854685294207/1990000000000000000 : ℝ)+2*(109689533551/59700000000000 : ℝ)*(1851/12500 : ℝ)=(10002073918394521/10000000000000000 : ℝ) by norm_num, show 1+2*(2637310677401743/6250000000000000000 : ℝ)=(3127637310677401743/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1989329854685294207/1990000000000000000 : ℝ)*(X 1 0+X 2 0)+(109689533551/59700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2083/512 : ℝ)) (lo := (10629/100000 : ℝ)) (hi := (1851/12500 : ℝ)) (c := (1989329854685294207/1990000000000000000 : ℝ)) (alpha := (109689533551/59700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1989329854685294207/1990000000000000000 : ℝ)*(X 0 1+X 2 1)+(109689533551/59700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2083/512 : ℝ)) (lo := (10629/100000 : ℝ)) (hi := (1851/12500 : ℝ)) (c := (1989329854685294207/1990000000000000000 : ℝ)) (alpha := (109689533551/59700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1989329854685294207/1990000000000000000 : ℝ)*(X 0 2+X 1 2)+(109689533551/59700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2083/512 : ℝ)) (lo := (10629/100000 : ℝ)) (hi := (1851/12500 : ℝ)) (c := (1989329854685294207/1990000000000000000 : ℝ)) (alpha := (109689533551/59700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2167036587/10000000000 : ℝ)*X 0 0+(2700994161/5000000000 : ℝ)*X 0 1+(1314329553/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069400307/2000000000 : ℝ)*X 1 0+(-1120279351/5000000000 : ℝ)*X 1 1+(5257318773/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347002037/10000000000 : ℝ)*X 2 0+(2628658907/5000000000 : ℝ)*X 2 1+(-1120279651/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((174579441/400000000 : ℝ)*X 0 0+(422299121/1000000000 : ℝ)*X 0 1+(4510698141/10000000000 : ℝ)*X 0 2+(174579441/400000000 : ℝ)*X 1 0+(422299121/1000000000 : ℝ)*X 1 1+(4510698141/10000000000 : ℝ)*X 1 2+(174579441/400000000 : ℝ)*X 2 0+(422299121/1000000000 : ℝ)*X 2 1+(4510698141/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2167044451/10000000000 : ℝ)*X 0 0+(2628865007/5000000000 : ℝ)*X 0 1+(5401574297/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((331897309/625000000 : ℝ)*X 1 0+(-2096302153/10000000000 : ℝ)*X 1 1+(5401574311/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((66379463/125000000 : ℝ)*X 2 0+(67519677/125000000 : ℝ)*X 2 1+(-2096302229/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4364499893/10000000000 : ℝ)*X 0 0+(4404177/9765625 : ℝ)*X 0 1+(2111907927/5000000000 : ℝ)*X 0 2+(4364499893/10000000000 : ℝ)*X 1 0+(4404177/9765625 : ℝ)*X 1 1+(2111907927/5000000000 : ℝ)*X 1 2+(4364499893/10000000000 : ℝ)*X 2 0+(4404177/9765625 : ℝ)*X 2 1+(2111907927/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (64368517644341265385869187/49750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (36722791/100000000000000 : ℝ)*(base8) + (1255501/1000000000000 : ℝ)*(base15) + (651045371/100000000000000 : ℝ)*(base29) + (294953479/100000000000000 : ℝ)*(lower2) + (68147801/50000000000000 : ℝ)*(lower4) + (5194027915425721/100000000000000 : ℝ)*(major0) + (1298507141617773/25000000000000 : ℝ)*(major1) + (5194028566471093/100000000000000 : ℝ)*(major2) + (1728067991368943/25000000000000 : ℝ)*(sp0) + (1728067806400773/25000000000000 : ℝ)*(sp1) + (1728058974388573/25000000000000 : ℝ)*(sp2) + (868942722500633/25000000000000 : ℝ)*(sp3) + (354535989/1000000000000 : ℝ)*(sp6) + (14197613097/100000000000000 : ℝ)*(sp7) + (347578508761563/10000000000000 : ℝ)*(f.failure) + (6912272002198563/100000000000000 : ℝ)*(f.sum) + (6390774303929/1194000000000000000000000000 : ℝ)*base65 + (1877875787386498033/149250000000000000000000000000000 : ℝ)*base67 + (616451086436258251/199000000000000000000000000000000 : ℝ)*base69 + (988606009567594741/597000000000000000000000000000000 : ℝ)*base71 + (574256240137/2985000000000000000000000000 : ℝ)*base73 + (4207262873222674753/597000000000000000000000000000000 : ℝ)*base75 + (252527104521498247/199000000000000000000000000000000 : ℝ)*base77 + (1621025975215198033/149250000000000000000000000000000 : ℝ)*base79 + (13518472893943/5970000000000000000000000000 : ℝ)*base81 + (4535781/1000000000000000000000 : ℝ)*base89 + (4535781/1000000000000000000000 : ℝ)*base91 + (5464219/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (153865241354430436683136323/49750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (255323473/20000000000000 : ℝ)*(base19) + (815772807/50000000000000 : ℝ)*(base23) + (71775253/50000000000000 : ℝ)*(upper2) + (5607799/10000000000000 : ℝ)*(upper3) + (326371433/100000000000000 : ℝ)*(upper5) + (5223859170067263/100000000000000 : ℝ)*(major0) + (5223859170067263/100000000000000 : ℝ)*(major1) + (5223859170067263/100000000000000 : ℝ)*(major2) + (18740971223/50000000000000 : ℝ)*(sp1) + (6305974263/20000000000000 : ℝ)*(sp2) + (695197084737007/10000000000000 : ℝ)*(sp4) + (3475966044405129/50000000000000 : ℝ)*(sp5) + (3475968842976571/50000000000000 : ℝ)*(sp6) + (21848421185451/625000000000 : ℝ)*(sp7) + (21848421185451/625000000000 : ℝ)*(f.failure) + (695197084737007/10000000000000 : ℝ)*(f.sum) + (3700735076479/995000000000000000000000000 : ℝ)*base66 + (287016135508654559/199000000000000000000000000000000 : ℝ)*base68 + (237787270738654559/199000000000000000000000000000000 : ℝ)*base70 + (559337156473345441/199000000000000000000000000000000 : ℝ)*base71 + (1500559958541/995000000000000000000000000 : ℝ)*base73 + (211584981732654559/199000000000000000000000000000000 : ℝ)*base76 + (1942152975953654559/199000000000000000000000000000000 : ℝ)*base78 + (1136912330358654559/199000000000000000000000000000000 : ℝ)*base80 + (3729972999931/995000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (236163/62500000000000000000 : ℝ)*base90 + (236163/62500000000000000000 : ℝ)*base92 + (236163/62500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1140_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149434687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1851/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10629/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2793/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1140_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1140_s5_0 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1083838891/5000000000 : ℝ)*x 0 + (215798533/400000000 : ℝ)*x 1 + (2631961193/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083838891/5000000000 : ℝ)^8333 ≤ (1646399254617/12500000000000 : ℝ)^6285 := by
    have hnat : (1083838891 : ℕ)^8333*12500000000000^6285 ≤ 1646399254617^6285*5000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083838891 5000000000 1646399254617 12500000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215798533/400000000 : ℝ)^8333 ≤ (11030509181391/25000000000000 : ℝ)^6285 := by
    have hnat : (215798533 : ℕ)^8333*25000000000000^6285 ≤ 11030509181391^6285*400000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215798533 400000000 11030509181391 25000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631961193/5000000000 : ℝ)^8333 ≤ (42706769216651/100000000000000 : ℝ)^6285 := by
    have hnat : (2631961193 : ℕ)^8333*100000000000000^6285 ≤ 42706769216651^6285*5000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631961193 5000000000 42706769216651 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1083838891/5000000000 : ℝ), (215798533/400000000 : ℝ), (2631961193/5000000000 : ℝ)] ![(1646399254617/12500000000000 : ℝ), (11030509181391/25000000000000 : ℝ), (42706769216651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1083838891/5000000000 : ℝ)|^8333 ≤ (1646399254617/12500000000000 : ℝ)^6285
        have hw : |(-1083838891/5000000000 : ℝ)|=(1083838891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(215798533/400000000 : ℝ)|^8333 ≤ (11030509181391/25000000000000 : ℝ)^6285
        have hw : |(215798533/400000000 : ℝ)|=(215798533/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631961193/5000000000 : ℝ)|^8333 ≤ (42706769216651/100000000000000 : ℝ)^6285
        have hw : |(2631961193/5000000000 : ℝ)|=(2631961193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s5_1 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672620559/5000000000 : ℝ)*x 0 + (-279271477/1250000000 : ℝ)*x 1 + (5263922379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672620559/5000000000 : ℝ)^8333 ≤ (43583693113583/100000000000000 : ℝ)^6285 := by
    have hnat : (2672620559 : ℕ)^8333*100000000000000^6285 ≤ 43583693113583^6285*5000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672620559 5000000000 43583693113583 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (279271477/1250000000 : ℝ)^8333 ≤ (13709537733803/100000000000000 : ℝ)^6285 := by
    have hnat : (279271477 : ℕ)^8333*100000000000000^6285 ≤ 13709537733803^6285*1250000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279271477 1250000000 13709537733803 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263922379/10000000000 : ℝ)^8333 ≤ (42706769141353/100000000000000 : ℝ)^6285 := by
    have hnat : (5263922379 : ℕ)^8333*100000000000000^6285 ≤ 42706769141353^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263922379 10000000000 42706769141353 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672620559/5000000000 : ℝ), (-279271477/1250000000 : ℝ), (5263922379/10000000000 : ℝ)] ![(43583693113583/100000000000000 : ℝ), (13709537733803/100000000000000 : ℝ), (42706769141353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672620559/5000000000 : ℝ)|^8333 ≤ (43583693113583/100000000000000 : ℝ)^6285
        have hw : |(2672620559/5000000000 : ℝ)|=(2672620559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-279271477/1250000000 : ℝ)|^8333 ≤ (13709537733803/100000000000000 : ℝ)^6285
        have hw : |(-279271477/1250000000 : ℝ)|=(279271477/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263922379/10000000000 : ℝ)|^8333 ≤ (42706769141353/100000000000000 : ℝ)^6285
        have hw : |(5263922379/10000000000 : ℝ)|=(5263922379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s5_2 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345241119/10000000000 : ℝ)*x 0 + (1315980593/2500000000 : ℝ)*x 1 + (-2234171823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345241119/10000000000 : ℝ)^8333 ≤ (21791846562197/50000000000000 : ℝ)^6285 := by
    have hnat : (5345241119 : ℕ)^8333*50000000000000^6285 ≤ 21791846562197^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345241119 10000000000 21791846562197 50000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315980593/2500000000 : ℝ)^8333 ≤ (8541353813211/20000000000000 : ℝ)^6285 := by
    have hnat : (1315980593 : ℕ)^8333*20000000000000^6285 ≤ 8541353813211^6285*2500000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315980593 2500000000 8541353813211 20000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2234171823/10000000000 : ℝ)^8333 ≤ (13709537790753/100000000000000 : ℝ)^6285 := by
    have hnat : (2234171823 : ℕ)^8333*100000000000000^6285 ≤ 13709537790753^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2234171823 10000000000 13709537790753 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345241119/10000000000 : ℝ), (1315980593/2500000000 : ℝ), (-2234171823/10000000000 : ℝ)] ![(21791846562197/50000000000000 : ℝ), (8541353813211/20000000000000 : ℝ), (13709537790753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345241119/10000000000 : ℝ)|^8333 ≤ (21791846562197/50000000000000 : ℝ)^6285
        have hw : |(5345241119/10000000000 : ℝ)|=(5345241119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1315980593/2500000000 : ℝ)|^8333 ≤ (8541353813211/20000000000000 : ℝ)^6285
        have hw : |(1315980593/2500000000 : ℝ)|=(1315980593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2234171823/10000000000 : ℝ)|^8333 ≤ (13709537790753/100000000000000 : ℝ)^6285
        have hw : |(-2234171823/10000000000 : ℝ)|=(2234171823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s5_3 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4364860179/10000000000 : ℝ)*x 0 + (1059124029/2500000000 : ℝ)*x 1 + (4497096449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4364860179/10000000000 : ℝ)^8333 ≤ (33315995474653/100000000000000 : ℝ)^6285 := by
    have hnat : (4364860179 : ℕ)^8333*100000000000000^6285 ≤ 33315995474653^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364860179 10000000000 33315995474653 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1059124029/2500000000 : ℝ)^8333 ≤ (500362858459/1562500000000 : ℝ)^6285 := by
    have hnat : (1059124029 : ℕ)^8333*1562500000000^6285 ≤ 500362858459^6285*2500000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059124029 2500000000 500362858459 1562500000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4497096449/10000000000 : ℝ)^8333 ≤ (34660781571227/100000000000000 : ℝ)^6285 := by
    have hnat : (4497096449 : ℕ)^8333*100000000000000^6285 ≤ 34660781571227^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497096449 10000000000 34660781571227 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4364860179/10000000000 : ℝ), (1059124029/2500000000 : ℝ), (4497096449/10000000000 : ℝ)] ![(33315995474653/100000000000000 : ℝ), (500362858459/1562500000000 : ℝ), (34660781571227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4364860179/10000000000 : ℝ)|^8333 ≤ (33315995474653/100000000000000 : ℝ)^6285
        have hw : |(4364860179/10000000000 : ℝ)|=(4364860179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1059124029/2500000000 : ℝ)|^8333 ≤ (500362858459/1562500000000 : ℝ)^6285
        have hw : |(1059124029/2500000000 : ℝ)|=(1059124029/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4497096449/10000000000 : ℝ)|^8333 ≤ (34660781571227/100000000000000 : ℝ)^6285
        have hw : |(4497096449/10000000000 : ℝ)|=(4497096449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s5_4 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1083841521/5000000000 : ℝ)*x 0 + (2632130641/5000000000 : ℝ)*x 1 + (5394623219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083841521/5000000000 : ℝ)^8333 ≤ (6585618206101/50000000000000 : ℝ)^6285 := by
    have hnat : (1083841521 : ℕ)^8333*50000000000000^6285 ≤ 6585618206101^6285*5000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083841521 5000000000 6585618206101 50000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632130641/5000000000 : ℝ)^8333 ≤ (42710414693453/100000000000000 : ℝ)^6285 := by
    have hnat : (2632130641 : ℕ)^8333*100000000000000^6285 ≤ 42710414693453^6285*5000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632130641 5000000000 42710414693453 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394623219/10000000000 : ℝ)^8333 ≤ (2757396804861/6250000000000 : ℝ)^6285 := by
    have hnat : (5394623219 : ℕ)^8333*6250000000000^6285 ≤ 2757396804861^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394623219 10000000000 2757396804861 6250000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1083841521/5000000000 : ℝ), (2632130641/5000000000 : ℝ), (5394623219/10000000000 : ℝ)] ![(6585618206101/50000000000000 : ℝ), (42710414693453/100000000000000 : ℝ), (2757396804861/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1083841521/5000000000 : ℝ)|^8333 ≤ (6585618206101/50000000000000 : ℝ)^6285
        have hw : |(-1083841521/5000000000 : ℝ)|=(1083841521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632130641/5000000000 : ℝ)|^8333 ≤ (42710414693453/100000000000000 : ℝ)^6285
        have hw : |(2632130641/5000000000 : ℝ)|=(2632130641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394623219/10000000000 : ℝ)|^8333 ≤ (2757396804861/6250000000000 : ℝ)^6285
        have hw : |(5394623219/10000000000 : ℝ)|=(5394623219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s5_5 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664005879/1250000000 : ℝ)*x 0 + (-262933801/1250000000 : ℝ)*x 1 + (5394623289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664005879/1250000000 : ℝ)^8333 ≤ (21612603106149/50000000000000 : ℝ)^6285 := by
    have hnat : (664005879 : ℕ)^8333*50000000000000^6285 ≤ 21612603106149^6285*1250000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664005879 1250000000 21612603106149 50000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262933801/1250000000 : ℝ)^8333 ≤ (3164111035241/25000000000000 : ℝ)^6285 := by
    have hnat : (262933801 : ℕ)^8333*25000000000000^6285 ≤ 3164111035241^6285*1250000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262933801 1250000000 3164111035241 25000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394623289/10000000000 : ℝ)^8333 ≤ (22059174818397/50000000000000 : ℝ)^6285 := by
    have hnat : (5394623289 : ℕ)^8333*50000000000000^6285 ≤ 22059174818397^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394623289 10000000000 22059174818397 50000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664005879/1250000000 : ℝ), (-262933801/1250000000 : ℝ), (5394623289/10000000000 : ℝ)] ![(21612603106149/50000000000000 : ℝ), (3164111035241/25000000000000 : ℝ), (22059174818397/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664005879/1250000000 : ℝ)|^8333 ≤ (21612603106149/50000000000000 : ℝ)^6285
        have hw : |(664005879/1250000000 : ℝ)|=(664005879/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-262933801/1250000000 : ℝ)|^8333 ≤ (3164111035241/25000000000000 : ℝ)^6285
        have hw : |(-262933801/1250000000 : ℝ)|=(262933801/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394623289/10000000000 : ℝ)|^8333 ≤ (22059174818397/50000000000000 : ℝ)^6285
        have hw : |(5394623289/10000000000 : ℝ)|=(5394623289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s5_6 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062409329/2000000000 : ℝ)*x 0 + (5394623527/10000000000 : ℝ)*x 1 + (-131466913/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062409329/2000000000 : ℝ)^8333 ≤ (864504040741/2000000000000 : ℝ)^6285 := by
    have hnat : (1062409329 : ℕ)^8333*2000000000000^6285 ≤ 864504040741^6285*2000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062409329 2000000000 864504040741 2000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394623527/10000000000 : ℝ)^8333 ≤ (44118352217457/100000000000000 : ℝ)^6285 := by
    have hnat : (5394623527 : ℕ)^8333*100000000000000^6285 ≤ 44118352217457^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394623527 10000000000 44118352217457 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131466913/625000000 : ℝ)^8333 ≤ (12656445736481/100000000000000 : ℝ)^6285 := by
    have hnat : (131466913 : ℕ)^8333*100000000000000^6285 ≤ 12656445736481^6285*625000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131466913 625000000 12656445736481 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062409329/2000000000 : ℝ), (5394623527/10000000000 : ℝ), (-131466913/625000000 : ℝ)] ![(864504040741/2000000000000 : ℝ), (44118352217457/100000000000000 : ℝ), (12656445736481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062409329/2000000000 : ℝ)|^8333 ≤ (864504040741/2000000000000 : ℝ)^6285
        have hw : |(1062409329/2000000000 : ℝ)|=(1062409329/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394623527/10000000000 : ℝ)|^8333 ≤ (44118352217457/100000000000000 : ℝ)^6285
        have hw : |(5394623527/10000000000 : ℝ)|=(5394623527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-131466913/625000000 : ℝ)|^8333 ≤ (12656445736481/100000000000000 : ℝ)^6285
        have hw : |(-131466913/625000000 : ℝ)|=(131466913/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s5_7 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (68201109/156250000 : ℝ)*x 0 + (899284531/2000000000 : ℝ)*x 1 + (264823263/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (68201109/156250000 : ℝ)^8333 ≤ (16658052369923/50000000000000 : ℝ)^6285 := by
    have hnat : (68201109 : ℕ)^8333*50000000000000^6285 ≤ 16658052369923^6285*156250000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68201109 156250000 16658052369923 50000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (899284531/2000000000 : ℝ)^8333 ≤ (34653896335929/100000000000000 : ℝ)^6285 := by
    have hnat : (899284531 : ℕ)^8333*100000000000000^6285 ≤ 34653896335929^6285*2000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899284531 2000000000 34653896335929 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (264823263/625000000 : ℝ)^8333 ≤ (8007499727611/25000000000000 : ℝ)^6285 := by
    have hnat : (264823263 : ℕ)^8333*25000000000000^6285 ≤ 8007499727611^6285*625000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264823263 625000000 8007499727611 25000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(68201109/156250000 : ℝ), (899284531/2000000000 : ℝ), (264823263/625000000 : ℝ)] ![(16658052369923/50000000000000 : ℝ), (34653896335929/100000000000000 : ℝ), (8007499727611/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(68201109/156250000 : ℝ)|^8333 ≤ (16658052369923/50000000000000 : ℝ)^6285
        have hw : |(68201109/156250000 : ℝ)|=(68201109/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(899284531/2000000000 : ℝ)|^8333 ≤ (34653896335929/100000000000000 : ℝ)^6285
        have hw : |(899284531/2000000000 : ℝ)|=(899284531/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(264823263/625000000 : ℝ)|^8333 ≤ (8007499727611/25000000000000 : ℝ)^6285
        have hw : |(264823263/625000000 : ℝ)|=(264823263/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1140_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149434687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2793/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (707/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1761/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2793/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2793/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2793/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2793/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2793/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2793/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2793/25000 : ℝ) ^ (2083/512 : ℝ) ≤ (3352698822201757/25000000000000000000 : ℝ) := by
    have hpowers : (2793/25000 : ℝ)^2083 ≤ (3352698822201757/25000000000000000000 : ℝ)^512 := by
      have hnat : (2793 : ℕ)^2083*25000000000000000000^512 ≤ 3352698822201757^512*25000^2083 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2793 25000 3352698822201757 25000000000000000000 2083 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2793/25000 : ℝ)) (X := (3352698822201757/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2083 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2847/20000 : ℝ) ^ (2083/512 : ℝ) ≤ (8984500568585019/25000000000000000000 : ℝ) := by
    have hpowers : (2847/20000 : ℝ)^2083 ≤ (8984500568585019/25000000000000000000 : ℝ)^512 := by
      have hnat : (2847 : ℕ)^2083*25000000000000000000^512 ≤ 8984500568585019^512*20000^2083 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 20000 8984500568585019 25000000000000000000 2083 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/20000 : ℝ)) (X := (8984500568585019/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2083 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503352698822201757/12500000000000000000 : ℝ) ≤ (5000329603111227/5000000000000000 : ℝ) ^ (2083/512 : ℝ) := by
    have hpowers : (12503352698822201757/12500000000000000000 : ℝ)^512 ≤ (5000329603111227/5000000000000000 : ℝ)^2083 := by
      have hnat : (12503352698822201757 : ℕ)^512*5000000000000000^2083 ≤ 5000329603111227^2083*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503352698822201757 12500000000000000000 5000329603111227 5000000000000000 512 2083 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000329603111227/5000000000000000 : ℝ)) (X := (12503352698822201757/12500000000000000000 : ℝ)) (by norm_num) 2083 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (3126542149923848347/3125000000000000000 : ℝ) ≤ (10001212764461679/10000000000000000 : ℝ) ^ (2083/512 : ℝ) := by
    have hpowers : (3126542149923848347/3125000000000000000 : ℝ)^512 ≤ (10001212764461679/10000000000000000 : ℝ)^2083 := by
      have hnat : (3126542149923848347 : ℕ)^512*10000000000000000^2083 ≤ 10001212764461679^2083*3125000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126542149923848347 3125000000000000000 10001212764461679 10000000000000000 512 2083 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001212764461679/10000000000000000 : ℝ)) (X := (3126542149923848347/3125000000000000000 : ℝ)) (by norm_num) 2083 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508984500568585019/12500000000000000000 : ℝ) ≤ (1250220790337613/1250000000000000 : ℝ) ^ (2083/512 : ℝ) := by
    have hpowers : (12508984500568585019/12500000000000000000 : ℝ)^512 ≤ (1250220790337613/1250000000000000 : ℝ)^2083 := by
      have hnat : (12508984500568585019 : ℕ)^512*1250000000000000^2083 ≤ 1250220790337613^2083*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508984500568585019 12500000000000000000 1250220790337613 1250000000000000 512 2083 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250220790337613/1250000000000000 : ℝ)) (X := (12508984500568585019/12500000000000000000 : ℝ)) (by norm_num) 2083 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3352698822201757/25000000000000000000 : ℝ) ≤ ((5103275073893688867/5105000000000000000 : ℝ)+2*(7380776523/4084000000000 : ℝ)*(2793/25000 : ℝ))^(2083/512 : ℝ) := by
    rw [show (5103275073893688867/5105000000000000000 : ℝ)+2*(7380776523/4084000000000 : ℝ)*(2793/25000 : ℝ)=(5000329603111227/5000000000000000 : ℝ) by norm_num, show 1+2*(3352698822201757/25000000000000000000 : ℝ)=(12503352698822201757/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8984500568585019/25000000000000000000 : ℝ)+(3352698822201757/25000000000000000000 : ℝ) ≤ ((5103275073893688867/5105000000000000000 : ℝ)+(7380776523/4084000000000 : ℝ)*((2847/20000 : ℝ)+(2793/25000 : ℝ)))^(2083/512 : ℝ) := by
    rw [show (5103275073893688867/5105000000000000000 : ℝ)+(7380776523/4084000000000 : ℝ)*((2847/20000 : ℝ)+(2793/25000 : ℝ))=(10001212764461679/10000000000000000 : ℝ) by norm_num, show 1+(8984500568585019/25000000000000000000 : ℝ)+(3352698822201757/25000000000000000000 : ℝ)=(3126542149923848347/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8984500568585019/25000000000000000000 : ℝ) ≤ ((5103275073893688867/5105000000000000000 : ℝ)+2*(7380776523/4084000000000 : ℝ)*(2847/20000 : ℝ))^(2083/512 : ℝ) := by
    rw [show (5103275073893688867/5105000000000000000 : ℝ)+2*(7380776523/4084000000000 : ℝ)*(2847/20000 : ℝ)=(1250220790337613/1250000000000000 : ℝ) by norm_num, show 1+2*(8984500568585019/25000000000000000000 : ℝ)=(12508984500568585019/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5103275073893688867/5105000000000000000 : ℝ)*(X 1 0+X 2 0)+(7380776523/4084000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2083/512 : ℝ)) (lo := (2793/25000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (5103275073893688867/5105000000000000000 : ℝ)) (alpha := (7380776523/4084000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5103275073893688867/5105000000000000000 : ℝ)*(X 0 1+X 2 1)+(7380776523/4084000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2083/512 : ℝ)) (lo := (2793/25000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (5103275073893688867/5105000000000000000 : ℝ)) (alpha := (7380776523/4084000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5103275073893688867/5105000000000000000 : ℝ)*(X 0 2+X 1 2)+(7380776523/4084000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2083/512 : ℝ)) (lo := (2793/25000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (5103275073893688867/5105000000000000000 : ℝ)) (alpha := (7380776523/4084000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1083838891/5000000000 : ℝ)*X 0 0+(215798533/400000000 : ℝ)*X 0 1+(2631961193/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672620559/5000000000 : ℝ)*X 1 0+(-279271477/1250000000 : ℝ)*X 1 1+(5263922379/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345241119/10000000000 : ℝ)*X 2 0+(1315980593/2500000000 : ℝ)*X 2 1+(-2234171823/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4364860179/10000000000 : ℝ)*X 0 0+(1059124029/2500000000 : ℝ)*X 0 1+(4497096449/10000000000 : ℝ)*X 0 2+(4364860179/10000000000 : ℝ)*X 1 0+(1059124029/2500000000 : ℝ)*X 1 1+(4497096449/10000000000 : ℝ)*X 1 2+(4364860179/10000000000 : ℝ)*X 2 0+(1059124029/2500000000 : ℝ)*X 2 1+(4497096449/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1083841521/5000000000 : ℝ)*X 0 0+(2632130641/5000000000 : ℝ)*X 0 1+(5394623219/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((664005879/1250000000 : ℝ)*X 1 0+(-262933801/1250000000 : ℝ)*X 1 1+(5394623289/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062409329/2000000000 : ℝ)*X 2 0+(5394623527/10000000000 : ℝ)*X 2 1+(-131466913/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((68201109/156250000 : ℝ)*X 0 0+(899284531/2000000000 : ℝ)*X 0 1+(264823263/625000000 : ℝ)*X 0 2+(68201109/156250000 : ℝ)*X 1 0+(899284531/2000000000 : ℝ)*X 1 1+(264823263/625000000 : ℝ)*X 1 2+(68201109/156250000 : ℝ)*X 2 0+(899284531/2000000000 : ℝ)*X 2 1+(264823263/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9818078088235095368043/1021000000000000000000000000 : ℝ) := by norm_num
    linear_combination (190153031/10000000000000 : ℝ)*(base19) + (110197573/6250000000000 : ℝ)*(base23) + (37362387/50000000000000 : ℝ)*(lower2) + (250237531/100000000000000 : ℝ)*(upper3) + (135059641/100000000000000 : ℝ)*(upper5) + (716790665739569/12500000000000 : ℝ)*(major0) + (716790665739569/12500000000000 : ℝ)*(major1) + (5734325325916553/100000000000000 : ℝ)*(major2) + (7631255422469007/100000000000000 : ℝ)*(sp0) + (381565143514267/5000000000000 : ℝ)*(sp1) + (7631303008654481/100000000000000 : ℝ)*(sp2) + (191865900669533/5000000000000 : ℝ)*(sp3) + (24674673321/50000000000000 : ℝ)*(sp4) + (5509217763/20000000000000 : ℝ)*(sp7) + (153493822379179/4000000000000 : ℝ)*(f.failure) + (152626095436313/2000000000000 : ℝ)*(f.sum) + (3293802691611/2042000000000000000000000000 : ℝ)*base65 + (77087581340647073/63812500000000000000000000000000 : ℝ)*base67 + (684144612322884549/510500000000000000000000000000000 : ℝ)*base70 + (207663447654102927/63812500000000000000000000000000 : ℝ)*base72 + (998921471177/408400000000000000000000000 : ℝ)*base73 + (2077531455797115451/510500000000000000000000000000000 : ℝ)*base75 + (751931918795490823/63812500000000000000000000000000 : ℝ)*base77 + (495983001920634177/63812500000000000000000000000000 : ℝ)*base80 + (7708408604457/1021000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (1181973/400000000000000000000 : ℝ)*base89 + (1181973/400000000000000000000 : ℝ)*base91 + (2818027/400000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (671031332158777430188103379/127625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2019708329/100000000000000 : ℝ)*(base19) + (1780734527/100000000000000 : ℝ)*(base23) + (193720121/100000000000000 : ℝ)*(upper3) + (173042961/100000000000000 : ℝ)*(lower4) + (23459653/50000000000000 : ℝ)*(upper5) + (5764102708698021/100000000000000 : ℝ)*(major0) + (5764102708698021/100000000000000 : ℝ)*(major1) + (5764102708698021/100000000000000 : ℝ)*(major2) + (6045315077/10000000000000 : ℝ)*(sp1) + (5951194707/10000000000000 : ℝ)*(sp2) + (767093299536523/10000000000000 : ℝ)*(sp4) + (1917717630626533/25000000000000 : ℝ)*(sp5) + (7670871702683633/100000000000000 : ℝ)*(sp6) + (3857272246769601/100000000000000 : ℝ)*(sp7) + (3857272246769601/100000000000000 : ℝ)*(f.failure) + (767093299536523/10000000000000 : ℝ)*(f.sum) + (6802467899679/1021000000000000000000000000 : ℝ)*base65 + (6162276969253882207/510500000000000000000000000000000 : ℝ)*base67 + (2118895195307617793/510500000000000000000000000000000 : ℝ)*base70 + (1405679872231382207/510500000000000000000000000000000 : ℝ)*base71 + (161147451433/31906250000000000000000000 : ℝ)*base73 + (3775687697308382207/510500000000000000000000000000000 : ℝ)*base75 + (4295175455655882207/510500000000000000000000000000000 : ℝ)*base77 + (4664235766658382207/510500000000000000000000000000000 : ℝ)*base79 + (4673889241299/1021000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (13450113/10000000000000000000000 : ℝ)*base90 + (13450113/10000000000000000000000 : ℝ)*base92 + (13450113/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1140_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149434687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2793/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (707/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1761/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1140_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1140_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149434687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4127/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9061/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (707/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1761/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1140_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1140_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1140_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149434687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4127/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9061/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (707/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1761/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1140_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
