-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1339_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:03:32.463102+00:00
-- url     : https://prove2.me/submissions/7a7f49ee-932d-44ab-8438-96d5cd285c2c

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
theorem support_rectangle_w1339_s0_0 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-452730267/2500000000 : ℝ)*x 0 + (1499553367/2500000000 : ℝ)*x 1 + (4810192743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (452730267/2500000000 : ℝ)^4299 ≤ (10613671985579/100000000000000 : ℝ)^3275 := by
    have hnat : (452730267 : ℕ)^4299*100000000000000^3275 ≤ 10613671985579^3275*2500000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452730267 2500000000 10613671985579 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1499553367/2500000000 : ℝ)^4299 ≤ (51122918743077/100000000000000 : ℝ)^3275 := by
    have hnat : (1499553367 : ℕ)^4299*100000000000000^3275 ≤ 51122918743077^3275*2500000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1499553367 2500000000 51122918743077 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4810192743/10000000000 : ℝ)^4299 ≤ (38263409262997/100000000000000 : ℝ)^3275 := by
    have hnat : (4810192743 : ℕ)^4299*100000000000000^3275 ≤ 38263409262997^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4810192743 10000000000 38263409262997 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-452730267/2500000000 : ℝ), (1499553367/2500000000 : ℝ), (4810192743/10000000000 : ℝ)] ![(10613671985579/100000000000000 : ℝ), (51122918743077/100000000000000 : ℝ), (38263409262997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-452730267/2500000000 : ℝ)|^4299 ≤ (10613671985579/100000000000000 : ℝ)^3275
        have hw : |(-452730267/2500000000 : ℝ)|=(452730267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1499553367/2500000000 : ℝ)|^4299 ≤ (51122918743077/100000000000000 : ℝ)^3275
        have hw : |(1499553367/2500000000 : ℝ)|=(1499553367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4810192743/10000000000 : ℝ)|^4299 ≤ (38263409262997/100000000000000 : ℝ)^3275
        have hw : |(4810192743/10000000000 : ℝ)|=(4810192743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s0_1 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (275107431/500000000 : ℝ)*x 0 + (-621583489/2500000000 : ℝ)*x 1 + (300637071/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (275107431/500000000 : ℝ)^4299 ≤ (45646144534117/100000000000000 : ℝ)^3275 := by
    have hnat : (275107431 : ℕ)^4299*100000000000000^3275 ≤ 45646144534117^3275*500000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275107431 500000000 45646144534117 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (621583489/2500000000 : ℝ)^4299 ≤ (16090442091997/100000000000000 : ℝ)^3275 := by
    have hnat : (621583489 : ℕ)^4299*100000000000000^3275 ≤ 16090442091997^3275*2500000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      621583489 2500000000 16090442091997 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (300637071/625000000 : ℝ)^4299 ≤ (19131706683321/50000000000000 : ℝ)^3275 := by
    have hnat : (300637071 : ℕ)^4299*50000000000000^3275 ≤ 19131706683321^3275*625000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      300637071 625000000 19131706683321 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(275107431/500000000 : ℝ), (-621583489/2500000000 : ℝ), (300637071/625000000 : ℝ)] ![(45646144534117/100000000000000 : ℝ), (16090442091997/100000000000000 : ℝ), (19131706683321/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(275107431/500000000 : ℝ)|^4299 ≤ (45646144534117/100000000000000 : ℝ)^3275
        have hw : |(275107431/500000000 : ℝ)|=(275107431/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-621583489/2500000000 : ℝ)|^4299 ≤ (16090442091997/100000000000000 : ℝ)^3275
        have hw : |(-621583489/2500000000 : ℝ)|=(621583489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(300637071/625000000 : ℝ)|^4299 ≤ (19131706683321/50000000000000 : ℝ)^3275
        have hw : |(300637071/625000000 : ℝ)|=(300637071/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s0_2 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1375537067/2500000000 : ℝ)*x 0 + (1202548251/2500000000 : ℝ)*x 1 + (-2486334569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1375537067/2500000000 : ℝ)^4299 ≤ (45646140700837/100000000000000 : ℝ)^3275 := by
    have hnat : (1375537067 : ℕ)^4299*100000000000000^3275 ≤ 45646140700837^3275*2500000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1375537067 2500000000 45646140700837 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1202548251/2500000000 : ℝ)^4299 ≤ (38263411988319/100000000000000 : ℝ)^3275 := by
    have hnat : (1202548251 : ℕ)^4299*100000000000000^3275 ≤ 38263411988319^3275*2500000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1202548251 2500000000 38263411988319 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2486334569/10000000000 : ℝ)^4299 ≤ (2011305912431/12500000000000 : ℝ)^3275 := by
    have hnat : (2486334569 : ℕ)^4299*12500000000000^3275 ≤ 2011305912431^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2486334569 10000000000 2011305912431 12500000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1375537067/2500000000 : ℝ), (1202548251/2500000000 : ℝ), (-2486334569/10000000000 : ℝ)] ![(45646140700837/100000000000000 : ℝ), (38263411988319/100000000000000 : ℝ), (2011305912431/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1375537067/2500000000 : ℝ)|^4299 ≤ (45646140700837/100000000000000 : ℝ)^3275
        have hw : |(1375537067/2500000000 : ℝ)|=(1375537067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1202548251/2500000000 : ℝ)|^4299 ≤ (38263411988319/100000000000000 : ℝ)^3275
        have hw : |(1202548251/2500000000 : ℝ)|=(1202548251/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2486334569/10000000000 : ℝ)|^4299 ≤ (2011305912431/12500000000000 : ℝ)^3275
        have hw : |(-2486334569/10000000000 : ℝ)|=(2486334569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s0_3 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4179196111/10000000000 : ℝ)*x 0 + (1553357787/5000000000 : ℝ)*x 1 + (5592301519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4179196111/10000000000 : ℝ)^4299 ≤ (7953516109033/25000000000000 : ℝ)^3275 := by
    have hnat : (4179196111 : ℕ)^4299*25000000000000^3275 ≤ 7953516109033^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4179196111 10000000000 7953516109033 25000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1553357787/5000000000 : ℝ)^4299 ≤ (5388880091121/25000000000000 : ℝ)^3275 := by
    have hnat : (1553357787 : ℕ)^4299*25000000000000^3275 ≤ 5388880091121^3275*5000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1553357787 5000000000 5388880091121 25000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5592301519/10000000000 : ℝ)^4299 ≤ (46630415189161/100000000000000 : ℝ)^3275 := by
    have hnat : (5592301519 : ℕ)^4299*100000000000000^3275 ≤ 46630415189161^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5592301519 10000000000 46630415189161 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4179196111/10000000000 : ℝ), (1553357787/5000000000 : ℝ), (5592301519/10000000000 : ℝ)] ![(7953516109033/25000000000000 : ℝ), (5388880091121/25000000000000 : ℝ), (46630415189161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4179196111/10000000000 : ℝ)|^4299 ≤ (7953516109033/25000000000000 : ℝ)^3275
        have hw : |(4179196111/10000000000 : ℝ)|=(4179196111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1553357787/5000000000 : ℝ)|^4299 ≤ (5388880091121/25000000000000 : ℝ)^3275
        have hw : |(1553357787/5000000000 : ℝ)|=(1553357787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5592301519/10000000000 : ℝ)|^4299 ≤ (46630415189161/100000000000000 : ℝ)^3275
        have hw : |(5592301519/10000000000 : ℝ)|=(5592301519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s0_4 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-907696703/5000000000 : ℝ)*x 0 + (121019377/250000000 : ℝ)*x 1 + (745817429/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (907696703/5000000000 : ℝ)^4299 ≤ (266202326557/2500000000000 : ℝ)^3275 := by
    have hnat : (907696703 : ℕ)^4299*2500000000000^3275 ≤ 266202326557^3275*5000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      907696703 5000000000 266202326557 2500000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (121019377/250000000 : ℝ)^4299 ≤ (19291531145621/50000000000000 : ℝ)^3275 := by
    have hnat : (121019377 : ℕ)^4299*50000000000000^3275 ≤ 19291531145621^3275*250000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121019377 250000000 19291531145621 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (745817429/1250000000 : ℝ)^4299 ≤ (50768844644853/100000000000000 : ℝ)^3275 := by
    have hnat : (745817429 : ℕ)^4299*100000000000000^3275 ≤ 50768844644853^3275*1250000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      745817429 1250000000 50768844644853 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-907696703/5000000000 : ℝ), (121019377/250000000 : ℝ), (745817429/1250000000 : ℝ)] ![(266202326557/2500000000000 : ℝ), (19291531145621/50000000000000 : ℝ), (50768844644853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-907696703/5000000000 : ℝ)|^4299 ≤ (266202326557/2500000000000 : ℝ)^3275
        have hw : |(-907696703/5000000000 : ℝ)|=(907696703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(121019377/250000000 : ℝ)|^4299 ≤ (19291531145621/50000000000000 : ℝ)^3275
        have hw : |(121019377/250000000 : ℝ)|=(121019377/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(745817429/1250000000 : ℝ)|^4299 ≤ (50768844644853/100000000000000 : ℝ)^3275
        have hw : |(745817429/1250000000 : ℝ)|=(745817429/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s0_5 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1294598347/2500000000 : ℝ)*x 0 + (-132998859/1000000000 : ℝ)*x 1 + (5966539233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1294598347/2500000000 : ℝ)^4299 ≤ (10538332797721/25000000000000 : ℝ)^3275 := by
    have hnat : (1294598347 : ℕ)^4299*25000000000000^3275 ≤ 10538332797721^3275*2500000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294598347 2500000000 10538332797721 25000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (132998859/1000000000 : ℝ)^4299 ≤ (7077826369909/100000000000000 : ℝ)^3275 := by
    have hnat : (132998859 : ℕ)^4299*100000000000000^3275 ≤ 7077826369909^3275*1000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132998859 1000000000 7077826369909 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5966539233/10000000000 : ℝ)^4299 ≤ (50768842422137/100000000000000 : ℝ)^3275 := by
    have hnat : (5966539233 : ℕ)^4299*100000000000000^3275 ≤ 50768842422137^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5966539233 10000000000 50768842422137 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1294598347/2500000000 : ℝ), (-132998859/1000000000 : ℝ), (5966539233/10000000000 : ℝ)] ![(10538332797721/25000000000000 : ℝ), (7077826369909/100000000000000 : ℝ), (50768842422137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1294598347/2500000000 : ℝ)|^4299 ≤ (10538332797721/25000000000000 : ℝ)^3275
        have hw : |(1294598347/2500000000 : ℝ)|=(1294598347/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-132998859/1000000000 : ℝ)|^4299 ≤ (7077826369909/100000000000000 : ℝ)^3275
        have hw : |(-132998859/1000000000 : ℝ)|=(132998859/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5966539233/10000000000 : ℝ)|^4299 ≤ (50768842422137/100000000000000 : ℝ)^3275
        have hw : |(5966539233/10000000000 : ℝ)|=(5966539233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s0_6 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5178393387/10000000000 : ℝ)*x 0 + (186454357/312500000 : ℝ)*x 1 + (-664994143/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5178393387/10000000000 : ℝ)^4299 ≤ (42153331180199/100000000000000 : ℝ)^3275 := by
    have hnat : (5178393387 : ℕ)^4299*100000000000000^3275 ≤ 42153331180199^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178393387 10000000000 42153331180199 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (186454357/312500000 : ℝ)^4299 ≤ (25384422277749/50000000000000 : ℝ)^3275 := by
    have hnat : (186454357 : ℕ)^4299*50000000000000^3275 ≤ 25384422277749^3275*312500000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      186454357 312500000 25384422277749 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (664994143/5000000000 : ℝ)^4299 ≤ (1415564849253/20000000000000 : ℝ)^3275 := by
    have hnat : (664994143 : ℕ)^4299*20000000000000^3275 ≤ 1415564849253^3275*5000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664994143 5000000000 1415564849253 20000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5178393387/10000000000 : ℝ), (186454357/312500000 : ℝ), (-664994143/5000000000 : ℝ)] ![(42153331180199/100000000000000 : ℝ), (25384422277749/50000000000000 : ℝ), (1415564849253/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5178393387/10000000000 : ℝ)|^4299 ≤ (42153331180199/100000000000000 : ℝ)^3275
        have hw : |(5178393387/10000000000 : ℝ)|=(5178393387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(186454357/312500000 : ℝ)|^4299 ≤ (25384422277749/50000000000000 : ℝ)^3275
        have hw : |(186454357/312500000 : ℝ)|=(186454357/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-664994143/5000000000 : ℝ)|^4299 ≤ (1415564849253/20000000000000 : ℝ)^3275
        have hw : |(-664994143/5000000000 : ℝ)|=(664994143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s0_7 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2094275761/5000000000 : ℝ)*x 0 + (5528317759/10000000000 : ℝ)*x 1 + (3172983617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2094275761/5000000000 : ℝ)^4299 ≤ (638151657733/2000000000000 : ℝ)^3275 := by
    have hnat : (2094275761 : ℕ)^4299*2000000000000^3275 ≤ 638151657733^3275*5000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2094275761 5000000000 638151657733 2000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5528317759/10000000000 : ℝ)^4299 ≤ (4593133815801/10000000000000 : ℝ)^3275 := by
    have hnat : (5528317759 : ℕ)^4299*10000000000000^3275 ≤ 4593133815801^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5528317759 10000000000 4593133815801 10000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3172983617/10000000000 : ℝ)^4299 ≤ (11080539470313/50000000000000 : ℝ)^3275 := by
    have hnat : (3172983617 : ℕ)^4299*50000000000000^3275 ≤ 11080539470313^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3172983617 10000000000 11080539470313 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2094275761/5000000000 : ℝ), (5528317759/10000000000 : ℝ), (3172983617/10000000000 : ℝ)] ![(638151657733/2000000000000 : ℝ), (4593133815801/10000000000000 : ℝ), (11080539470313/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2094275761/5000000000 : ℝ)|^4299 ≤ (638151657733/2000000000000 : ℝ)^3275
        have hw : |(2094275761/5000000000 : ℝ)|=(2094275761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5528317759/10000000000 : ℝ)|^4299 ≤ (4593133815801/10000000000000 : ℝ)^3275
        have hw : |(5528317759/10000000000 : ℝ)|=(5528317759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3172983617/10000000000 : ℝ)|^4299 ≤ (11080539470313/50000000000000 : ℝ)^3275
        have hw : |(3172983617/10000000000 : ℝ)|=(3172983617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1339_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77305211/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (87/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26893/100000 : ℝ)*pair X 0 0 := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
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
  have hpowlo : (0 : ℝ) ^ (2149/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2149 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2149*1^512 ≤ 0^512*1^2149 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2149 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2149 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2149/512 : ℝ) ≤ (2136682931723545427/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2149 ≤ (2136682931723545427/100000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2149*100000000000000000000^512 ≤ 2136682931723545427^512*5^2149 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2136682931723545427 100000000000000000000 2149 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2136682931723545427/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2149 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2149/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2149 := by
      have hnat : (1 : ℕ)^512*1^2149 ≤ 1^2149*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2149 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (102136682931723545427/100000000000000000000 : ℝ) ≤ (10050497386300111/10000000000000000 : ℝ) ^ (2149/512 : ℝ) := by
    have hpowers : (102136682931723545427/100000000000000000000 : ℝ)^512 ≤ (10050497386300111/10000000000000000 : ℝ)^2149 := by
      have hnat : (102136682931723545427 : ℕ)^512*10000000000000000^2149 ≤ 10050497386300111^2149*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102136682931723545427 100000000000000000000 10050497386300111 10000000000000000 512 2149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10050497386300111/10000000000000000 : ℝ)) (X := (102136682931723545427/100000000000000000000 : ℝ)) (by norm_num) 2149 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (52136682931723545427/50000000000000000000 : ℝ) ≤ (5050497386300111/5000000000000000 : ℝ) ^ (2149/512 : ℝ) := by
    have hpowers : (52136682931723545427/50000000000000000000 : ℝ)^512 ≤ (5050497386300111/5000000000000000 : ℝ)^2149 := by
      have hnat : (52136682931723545427 : ℕ)^512*5000000000000000^2149 ≤ 5050497386300111^2149*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52136682931723545427 50000000000000000000 5050497386300111 5000000000000000 512 2149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5050497386300111/5000000000000000 : ℝ)) (X := (52136682931723545427/50000000000000000000 : ℝ)) (by norm_num) 2149 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(50497386300111/4000000000000000 : ℝ)*(0 : ℝ))^(2149/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(50497386300111/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2136682931723545427/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(50497386300111/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2149/512 : ℝ) := by
    rw [show (1 : ℝ)+(50497386300111/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10050497386300111/10000000000000000 : ℝ) by norm_num, show 1+(2136682931723545427/100000000000000000000 : ℝ)+(0 : ℝ)=(102136682931723545427/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2136682931723545427/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(50497386300111/4000000000000000 : ℝ)*(2/5 : ℝ))^(2149/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(50497386300111/4000000000000000 : ℝ)*(2/5 : ℝ)=(5050497386300111/5000000000000000 : ℝ) by norm_num, show 1+2*(2136682931723545427/100000000000000000000 : ℝ)=(52136682931723545427/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(50497386300111/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2149/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (50497386300111/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(50497386300111/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2149/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (50497386300111/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(50497386300111/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2149/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (50497386300111/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-452730267/2500000000 : ℝ)*X 0 0+(1499553367/2500000000 : ℝ)*X 0 1+(4810192743/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((275107431/500000000 : ℝ)*X 1 0+(-621583489/2500000000 : ℝ)*X 1 1+(300637071/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1375537067/2500000000 : ℝ)*X 2 0+(1202548251/2500000000 : ℝ)*X 2 1+(-2486334569/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4179196111/10000000000 : ℝ)*X 0 0+(1553357787/5000000000 : ℝ)*X 0 1+(5592301519/10000000000 : ℝ)*X 0 2+(4179196111/10000000000 : ℝ)*X 1 0+(1553357787/5000000000 : ℝ)*X 1 1+(5592301519/10000000000 : ℝ)*X 1 2+(4179196111/10000000000 : ℝ)*X 2 0+(1553357787/5000000000 : ℝ)*X 2 1+(5592301519/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-907696703/5000000000 : ℝ)*X 0 0+(121019377/250000000 : ℝ)*X 0 1+(745817429/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1294598347/2500000000 : ℝ)*X 1 0+(-132998859/1000000000 : ℝ)*X 1 1+(5966539233/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5178393387/10000000000 : ℝ)*X 2 0+(186454357/312500000 : ℝ)*X 2 1+(-664994143/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2094275761/5000000000 : ℝ)*X 0 0+(5528317759/10000000000 : ℝ)*X 0 1+(3172983617/10000000000 : ℝ)*X 0 2+(2094275761/5000000000 : ℝ)*X 1 0+(5528317759/10000000000 : ℝ)*X 1 1+(3172983617/10000000000 : ℝ)*X 1 2+(2094275761/5000000000 : ℝ)*X 2 0+(5528317759/10000000000 : ℝ)*X 2 1+(3172983617/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (335750734366296387/125000000000000000000000 : ℝ) := by norm_num
    linear_combination (14321929/20000000000000 : ℝ)*(base1) + (16853793/100000000000000 : ℝ)*(base16) + (320570669/50000000000000 : ℝ)*(base19) + (75518103/12500000000000 : ℝ)*(base23) + (58615233/50000000000000 : ℝ)*(upper3) + (311015487259127/50000000000000 : ℝ)*(major0) + (311015487259127/50000000000000 : ℝ)*(major1) + (311015487259127/50000000000000 : ℝ)*(major2) + (420869322856981/50000000000000 : ℝ)*(sp0) + (420869848952127/50000000000000 : ℝ)*(sp1) + (420869875877281/50000000000000 : ℝ)*(sp2) + (402320360358263/100000000000000 : ℝ)*(sp3) + (1781795069/100000000000000 : ℝ)*(sp4) + (1071635681/100000000000000 : ℝ)*(sp7) + (402321503603589/100000000000000 : ℝ)*(f.failure) + (420870177949693/50000000000000 : ℝ)*(f.sum) + (68548321363097/100000000000000000000000000000 : ℝ)*base65 + (315405330463097/200000000000000000000000000000 : ℝ)*base67 + (165476803736903/200000000000000000000000000000 : ℝ)*base70 + (983718614863097/200000000000000000000000000000 : ℝ)*base71 + (170460955836903/100000000000000000000000000000 : ℝ)*base74 + (1998890802263097/200000000000000000000000000000 : ℝ)*base75 + (62515212336903/200000000000000000000000000000 : ℝ)*base78 + (1149132628063097/200000000000000000000000000000 : ℝ)*base79 + (99029743736903/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (8002279/5000000000000000000000 : ℝ)*base89 + (8002279/5000000000000000000000 : ℝ)*base91 + (8002279/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1580733301534048422360459/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1777520373/100000000000000 : ℝ)*(base19) + (359858953/20000000000000 : ℝ)*(base23) + (1675761/12500000000000 : ℝ)*(base32) + (59838901/25000000000000 : ℝ)*(upper3) + (24600039/12500000000000 : ℝ)*(upper5) + (656426842641623/100000000000000 : ℝ)*(major0) + (656426842641623/100000000000000 : ℝ)*(major1) + (656426842641623/100000000000000 : ℝ)*(major2) + (124293289/3125000000000 : ℝ)*(sp1) + (432841023/10000000000000 : ℝ)*(sp2) + (444142560159241/50000000000000 : ℝ)*(sp4) + (888279365412861/100000000000000 : ℝ)*(sp5) + (888278992613487/100000000000000 : ℝ)*(sp6) + (424568288103123/100000000000000 : ℝ)*(sp7) + (424568301509211/100000000000000 : ℝ)*(f.failure) + (444142560159241/50000000000000 : ℝ)*(f.sum) + (85905204679847/200000000000000000000000000000 : ℝ)*base66 + (1559153531320153/400000000000000000000000000000 : ℝ)*base67 + (1602297747879847/400000000000000000000000000000 : ℝ)*base70 + (564979884520153/400000000000000000000000000000 : ℝ)*base71 + (344644642320153/200000000000000000000000000000 : ℝ)*base73 + (1724358194679847/400000000000000000000000000000 : ℝ)*base76 + (1167688627879847/400000000000000000000000000000 : ℝ)*base78 + (583707992120153/400000000000000000000000000000 : ℝ)*base79 + (465066849679847/200000000000000000000000000000 : ℝ)*base82 + (24798521/5000000000000000000000 : ℝ)*base89 + (24798521/5000000000000000000000 : ℝ)*base91 + (24798521/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1339_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77305211/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (87/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26893/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1339_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1339_s1_0 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-99808321/500000000 : ℝ)*x 0 + (1410871597/2500000000 : ℝ)*x 1 + (5046290137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (99808321/500000000 : ℝ)^4299 ≤ (2412226193083/20000000000000 : ℝ)^3275 := by
    have hnat : (99808321 : ℕ)^4299*20000000000000^3275 ≤ 2412226193083^3275*500000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99808321 500000000 2412226193083 20000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1410871597/2500000000 : ℝ)^4299 ≤ (47191458168557/100000000000000 : ℝ)^3275 := by
    have hnat : (1410871597 : ℕ)^4299*100000000000000^3275 ≤ 47191458168557^3275*2500000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1410871597 2500000000 47191458168557 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5046290137/10000000000 : ℝ)^4299 ≤ (40747410846223/100000000000000 : ℝ)^3275 := by
    have hnat : (5046290137 : ℕ)^4299*100000000000000^3275 ≤ 40747410846223^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5046290137 10000000000 40747410846223 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-99808321/500000000 : ℝ), (1410871597/2500000000 : ℝ), (5046290137/10000000000 : ℝ)] ![(2412226193083/20000000000000 : ℝ), (47191458168557/100000000000000 : ℝ), (40747410846223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-99808321/500000000 : ℝ)|^4299 ≤ (2412226193083/20000000000000 : ℝ)^3275
        have hw : |(-99808321/500000000 : ℝ)|=(99808321/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1410871597/2500000000 : ℝ)|^4299 ≤ (47191458168557/100000000000000 : ℝ)^3275
        have hw : |(1410871597/2500000000 : ℝ)|=(1410871597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5046290137/10000000000 : ℝ)|^4299 ≤ (40747410846223/100000000000000 : ℝ)^3275
        have hw : |(5046290137/10000000000 : ℝ)|=(5046290137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s1_1 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5406032373/10000000000 : ℝ)*x 0 + (-2314926651/10000000000 : ℝ)*x 1 + (2523145013/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5406032373/10000000000 : ℝ)^4299 ≤ (44602308585277/100000000000000 : ℝ)^3275 := by
    have hnat : (5406032373 : ℕ)^4299*100000000000000^3275 ≤ 44602308585277^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406032373 10000000000 44602308585277 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2314926651/10000000000 : ℝ)^4299 ≤ (7325140864433/50000000000000 : ℝ)^3275 := by
    have hnat : (2314926651 : ℕ)^4299*50000000000000^3275 ≤ 7325140864433^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2314926651 10000000000 7325140864433 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2523145013/5000000000 : ℝ)^4299 ≤ (40747409669683/100000000000000 : ℝ)^3275 := by
    have hnat : (2523145013 : ℕ)^4299*100000000000000^3275 ≤ 40747409669683^3275*5000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2523145013 5000000000 40747409669683 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5406032373/10000000000 : ℝ), (-2314926651/10000000000 : ℝ), (2523145013/5000000000 : ℝ)] ![(44602308585277/100000000000000 : ℝ), (7325140864433/50000000000000 : ℝ), (40747409669683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5406032373/10000000000 : ℝ)|^4299 ≤ (44602308585277/100000000000000 : ℝ)^3275
        have hw : |(5406032373/10000000000 : ℝ)|=(5406032373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2314926651/10000000000 : ℝ)|^4299 ≤ (7325140864433/50000000000000 : ℝ)^3275
        have hw : |(-2314926651/10000000000 : ℝ)|=(2314926651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2523145013/5000000000 : ℝ)|^4299 ≤ (40747409669683/100000000000000 : ℝ)^3275
        have hw : |(2523145013/5000000000 : ℝ)|=(2523145013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s1_2 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1081206477/2000000000 : ℝ)*x 0 + (5046289811/10000000000 : ℝ)*x 1 + (-231492691/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081206477/2000000000 : ℝ)^4299 ≤ (44602308715239/100000000000000 : ℝ)^3275 := by
    have hnat : (1081206477 : ℕ)^4299*100000000000000^3275 ≤ 44602308715239^3275*2000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081206477 2000000000 44602308715239 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5046289811/10000000000 : ℝ)^4299 ≤ (20373703695399/50000000000000 : ℝ)^3275 := by
    have hnat : (5046289811 : ℕ)^4299*50000000000000^3275 ≤ 20373703695399^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5046289811 10000000000 20373703695399 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (231492691/1000000000 : ℝ)^4299 ≤ (14650283880481/100000000000000 : ℝ)^3275 := by
    have hnat : (231492691 : ℕ)^4299*100000000000000^3275 ≤ 14650283880481^3275*1000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      231492691 1000000000 14650283880481 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081206477/2000000000 : ℝ), (5046289811/10000000000 : ℝ), (-231492691/1000000000 : ℝ)] ![(44602308715239/100000000000000 : ℝ), (20373703695399/50000000000000 : ℝ), (14650283880481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081206477/2000000000 : ℝ)|^4299 ≤ (44602308715239/100000000000000 : ℝ)^3275
        have hw : |(1081206477/2000000000 : ℝ)|=(1081206477/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5046289811/10000000000 : ℝ)|^4299 ≤ (20373703695399/50000000000000 : ℝ)^3275
        have hw : |(5046289811/10000000000 : ℝ)|=(5046289811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-231492691/1000000000 : ℝ)|^4299 ≤ (14650283880481/100000000000000 : ℝ)^3275
        have hw : |(-231492691/1000000000 : ℝ)|=(231492691/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s1_3 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (858568273/2000000000 : ℝ)*x 0 + (3710294121/10000000000 : ℝ)*x 1 + (4959753399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (858568273/2000000000 : ℝ)^4299 ≤ (32954484654573/100000000000000 : ℝ)^3275 := by
    have hnat : (858568273 : ℕ)^4299*100000000000000^3275 ≤ 32954484654573^3275*2000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      858568273 2000000000 32954484654573 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3710294121/10000000000 : ℝ)^4299 ≤ (13606439396591/50000000000000 : ℝ)^3275 := by
    have hnat : (3710294121 : ℕ)^4299*50000000000000^3275 ≤ 13606439396591^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3710294121 10000000000 13606439396591 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4959753399/10000000000 : ℝ)^4299 ≤ (4979079566449/12500000000000 : ℝ)^3275 := by
    have hnat : (4959753399 : ℕ)^4299*12500000000000^3275 ≤ 4979079566449^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4959753399 10000000000 4979079566449 12500000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(858568273/2000000000 : ℝ), (3710294121/10000000000 : ℝ), (4959753399/10000000000 : ℝ)] ![(32954484654573/100000000000000 : ℝ), (13606439396591/50000000000000 : ℝ), (4979079566449/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(858568273/2000000000 : ℝ)|^4299 ≤ (32954484654573/100000000000000 : ℝ)^3275
        have hw : |(858568273/2000000000 : ℝ)|=(858568273/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3710294121/10000000000 : ℝ)|^4299 ≤ (13606439396591/50000000000000 : ℝ)^3275
        have hw : |(3710294121/10000000000 : ℝ)|=(3710294121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4959753399/10000000000 : ℝ)|^4299 ≤ (4979079566449/12500000000000 : ℝ)^3275
        have hw : |(4959753399/10000000000 : ℝ)|=(4959753399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s1_4 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-399341691/2000000000 : ℝ)*x 0 + (25269/50000 : ℝ)*x 1 + (2817919821/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (399341691/2000000000 : ℝ)^4299 ≤ (754089388769/6250000000000 : ℝ)^3275 := by
    have hnat : (399341691 : ℕ)^4299*6250000000000^3275 ≤ 754089388769^3275*2000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399341691 2000000000 754089388769 6250000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (25269/50000 : ℝ)^4299 ≤ (8165405977827/20000000000000 : ℝ)^3275 := by
    have hnat : (25269 : ℕ)^4299*20000000000000^3275 ≤ 8165405977827^3275*50000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25269 50000 8165405977827 20000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2817919821/5000000000 : ℝ)^4299 ≤ (23553769933517/50000000000000 : ℝ)^3275 := by
    have hnat : (2817919821 : ℕ)^4299*50000000000000^3275 ≤ 23553769933517^3275*5000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2817919821 5000000000 23553769933517 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-399341691/2000000000 : ℝ), (25269/50000 : ℝ), (2817919821/5000000000 : ℝ)] ![(754089388769/6250000000000 : ℝ), (8165405977827/20000000000000 : ℝ), (23553769933517/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-399341691/2000000000 : ℝ)|^4299 ≤ (754089388769/6250000000000 : ℝ)^3275
        have hw : |(-399341691/2000000000 : ℝ)|=(399341691/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(25269/50000 : ℝ)|^4299 ≤ (8165405977827/20000000000000 : ℝ)^3275
        have hw : |(25269/50000 : ℝ)|=(25269/50000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2817919821/5000000000 : ℝ)|^4299 ≤ (23553769933517/50000000000000 : ℝ)^3275
        have hw : |(2817919821/5000000000 : ℝ)|=(2817919821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s1_5 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5251106959/10000000000 : ℝ)*x 0 + (-215672191/1250000000 : ℝ)*x 1 + (88059983/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251106959/10000000000 : ℝ)^4299 ≤ (21466004467919/50000000000000 : ℝ)^3275 := by
    have hnat : (5251106959 : ℕ)^4299*50000000000000^3275 ≤ 21466004467919^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251106959 10000000000 21466004467919 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215672191/1250000000 : ℝ)^4299 ≤ (9960459196601/100000000000000 : ℝ)^3275 := by
    have hnat : (215672191 : ℕ)^4299*100000000000000^3275 ≤ 9960459196601^3275*1250000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215672191 1250000000 9960459196601 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (88059983/156250000 : ℝ)^4299 ≤ (9421506371487/20000000000000 : ℝ)^3275 := by
    have hnat : (88059983 : ℕ)^4299*20000000000000^3275 ≤ 9421506371487^3275*156250000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88059983 156250000 9421506371487 20000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251106959/10000000000 : ℝ), (-215672191/1250000000 : ℝ), (88059983/156250000 : ℝ)] ![(21466004467919/50000000000000 : ℝ), (9960459196601/100000000000000 : ℝ), (9421506371487/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251106959/10000000000 : ℝ)|^4299 ≤ (21466004467919/50000000000000 : ℝ)^3275
        have hw : |(5251106959/10000000000 : ℝ)|=(5251106959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-215672191/1250000000 : ℝ)|^4299 ≤ (9960459196601/100000000000000 : ℝ)^3275
        have hw : |(-215672191/1250000000 : ℝ)|=(215672191/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(88059983/156250000 : ℝ)|^4299 ≤ (9421506371487/20000000000000 : ℝ)^3275
        have hw : |(88059983/156250000 : ℝ)|=(88059983/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s1_6 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5251106309/10000000000 : ℝ)*x 0 + (1408959679/2500000000 : ℝ)*x 1 + (-1725378731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251106309/10000000000 : ℝ)^4299 ≤ (5366500244993/12500000000000 : ℝ)^3275 := by
    have hnat : (5251106309 : ℕ)^4299*12500000000000^3275 ≤ 5366500244993^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251106309 10000000000 5366500244993 12500000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1408959679/2500000000 : ℝ)^4299 ≤ (1472110303341/3125000000000 : ℝ)^3275 := by
    have hnat : (1408959679 : ℕ)^4299*3125000000000^3275 ≤ 1472110303341^3275*2500000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1408959679 2500000000 1472110303341 3125000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1725378731/10000000000 : ℝ)^4299 ≤ (2490117078217/25000000000000 : ℝ)^3275 := by
    have hnat : (1725378731 : ℕ)^4299*25000000000000^3275 ≤ 2490117078217^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1725378731 10000000000 2490117078217 25000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251106309/10000000000 : ℝ), (1408959679/2500000000 : ℝ), (-1725378731/10000000000 : ℝ)] ![(5366500244993/12500000000000 : ℝ), (1472110303341/3125000000000 : ℝ), (2490117078217/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251106309/10000000000 : ℝ)|^4299 ≤ (5366500244993/12500000000000 : ℝ)^3275
        have hw : |(5251106309/10000000000 : ℝ)|=(5251106309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1408959679/2500000000 : ℝ)|^4299 ≤ (1472110303341/3125000000000 : ℝ)^3275
        have hw : |(1408959679/2500000000 : ℝ)|=(1408959679/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1725378731/10000000000 : ℝ)|^4299 ≤ (2490117078217/25000000000000 : ℝ)^3275
        have hw : |(-1725378731/10000000000 : ℝ)|=(1725378731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s1_7 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4293974571/10000000000 : ℝ)*x 0 + (1236010037/2500000000 : ℝ)*x 1 + (3726294651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4293974571/10000000000 : ℝ)^4299 ≤ (16482952149899/50000000000000 : ℝ)^3275 := by
    have hnat : (4293974571 : ℕ)^4299*50000000000000^3275 ≤ 16482952149899^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4293974571 10000000000 16482952149899 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1236010037/2500000000 : ℝ)^4299 ≤ (19833532466019/50000000000000 : ℝ)^3275 := by
    have hnat : (1236010037 : ℕ)^4299*50000000000000^3275 ≤ 19833532466019^3275*2500000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1236010037 2500000000 19833532466019 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3726294651/10000000000 : ℝ)^4299 ≤ (27367030759803/100000000000000 : ℝ)^3275 := by
    have hnat : (3726294651 : ℕ)^4299*100000000000000^3275 ≤ 27367030759803^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3726294651 10000000000 27367030759803 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4293974571/10000000000 : ℝ), (1236010037/2500000000 : ℝ), (3726294651/10000000000 : ℝ)] ![(16482952149899/50000000000000 : ℝ), (19833532466019/50000000000000 : ℝ), (27367030759803/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4293974571/10000000000 : ℝ)|^4299 ≤ (16482952149899/50000000000000 : ℝ)^3275
        have hw : |(4293974571/10000000000 : ℝ)|=(4293974571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1236010037/2500000000 : ℝ)|^4299 ≤ (19833532466019/50000000000000 : ℝ)^3275
        have hw : |(1236010037/2500000000 : ℝ)|=(1236010037/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3726294651/10000000000 : ℝ)|^4299 ≤ (27367030759803/100000000000000 : ℝ)^3275
        have hw : |(3726294651/10000000000 : ℝ)|=(3726294651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1339_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77305211/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26893/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (87/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (3431/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4871/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26893/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (87/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26893/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (87/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26893/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (87/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26893/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (87/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26893/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (87/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26893/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (87/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (87/6250 : ℝ) ^ (2149/512 : ℝ) ≤ (807850092339/50000000000000000000 : ℝ) := by
    have hpowers : (87/6250 : ℝ)^2149 ≤ (807850092339/50000000000000000000 : ℝ)^512 := by
      have hnat : (87 : ℕ)^2149*50000000000000000000^512 ≤ 807850092339^512*6250^2149 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        87 6250 807850092339 50000000000000000000 2149 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (87/6250 : ℝ)) (X := (807850092339/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2149 512 (by norm_num) hpowers
    exact h
  have hpowhi : (26893/100000 : ℝ) ^ (2149/512 : ℝ) ≤ (100921674246539751/25000000000000000000 : ℝ) := by
    have hpowers : (26893/100000 : ℝ)^2149 ≤ (100921674246539751/25000000000000000000 : ℝ)^512 := by
      have hnat : (26893 : ℕ)^2149*25000000000000000000^512 ≤ 100921674246539751^512*100000^2149 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26893 100000 100921674246539751 25000000000000000000 2149 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26893/100000 : ℝ)) (X := (100921674246539751/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2149 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000807850092339/25000000000000000000 : ℝ) ≤ (5000000038494113/5000000000000000 : ℝ) ^ (2149/512 : ℝ) := by
    have hpowers : (25000000807850092339/25000000000000000000 : ℝ)^512 ≤ (5000000038494113/5000000000000000 : ℝ)^2149 := by
      have hnat : (25000000807850092339 : ℕ)^512*5000000000000000^2149 ≤ 5000000038494113^2149*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000807850092339 25000000000000000000 5000000038494113 5000000000000000 512 2149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000038494113/5000000000000000 : ℝ)) (X := (25000000807850092339/25000000000000000000 : ℝ)) (by norm_num) 2149 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50201844156343171841/50000000000000000000 : ℝ) ≤ (2001920627028337/2000000000000000 : ℝ) ^ (2149/512 : ℝ) := by
    have hpowers : (50201844156343171841/50000000000000000000 : ℝ)^512 ≤ (2001920627028337/2000000000000000 : ℝ)^2149 := by
      have hnat : (50201844156343171841 : ℕ)^512*2000000000000000^2149 ≤ 2001920627028337^2149*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50201844156343171841 50000000000000000000 2001920627028337 2000000000000000 512 2149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2001920627028337/2000000000000000 : ℝ)) (X := (50201844156343171841/50000000000000000000 : ℝ)) (by norm_num) 2149 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12600921674246539751/12500000000000000000 : ℝ) ≤ (1252400774161893/1250000000000000 : ℝ) ^ (2149/512 : ℝ) := by
    have hpowers : (12600921674246539751/12500000000000000000 : ℝ)^512 ≤ (1252400774161893/1250000000000000 : ℝ)^2149 := by
      have hnat : (12600921674246539751 : ℕ)^512*1250000000000000^2149 ≤ 1252400774161893^2149*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12600921674246539751 12500000000000000000 1252400774161893 1250000000000000 512 2149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1252400774161893/1250000000000000 : ℝ)) (X := (12600921674246539751/12500000000000000000 : ℝ)) (by norm_num) 2149 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(807850092339/50000000000000000000 : ℝ) ≤ ((25498326704937752137/25501000000000000000 : ℝ)+2*(9603058153459/2550100000000000 : ℝ)*(87/6250 : ℝ))^(2149/512 : ℝ) := by
    rw [show (25498326704937752137/25501000000000000000 : ℝ)+2*(9603058153459/2550100000000000 : ℝ)*(87/6250 : ℝ)=(5000000038494113/5000000000000000 : ℝ) by norm_num, show 1+2*(807850092339/50000000000000000000 : ℝ)=(25000000807850092339/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(100921674246539751/25000000000000000000 : ℝ)+(807850092339/50000000000000000000 : ℝ) ≤ ((25498326704937752137/25501000000000000000 : ℝ)+(9603058153459/2550100000000000 : ℝ)*((26893/100000 : ℝ)+(87/6250 : ℝ)))^(2149/512 : ℝ) := by
    rw [show (25498326704937752137/25501000000000000000 : ℝ)+(9603058153459/2550100000000000 : ℝ)*((26893/100000 : ℝ)+(87/6250 : ℝ))=(2001920627028337/2000000000000000 : ℝ) by norm_num, show 1+(100921674246539751/25000000000000000000 : ℝ)+(807850092339/50000000000000000000 : ℝ)=(50201844156343171841/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(100921674246539751/25000000000000000000 : ℝ) ≤ ((25498326704937752137/25501000000000000000 : ℝ)+2*(9603058153459/2550100000000000 : ℝ)*(26893/100000 : ℝ))^(2149/512 : ℝ) := by
    rw [show (25498326704937752137/25501000000000000000 : ℝ)+2*(9603058153459/2550100000000000 : ℝ)*(26893/100000 : ℝ)=(1252400774161893/1250000000000000 : ℝ) by norm_num, show 1+2*(100921674246539751/25000000000000000000 : ℝ)=(12600921674246539751/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (25498326704937752137/25501000000000000000 : ℝ)*(X 1 0+X 2 0)+(9603058153459/2550100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2149/512 : ℝ)) (lo := (87/6250 : ℝ)) (hi := (26893/100000 : ℝ)) (c := (25498326704937752137/25501000000000000000 : ℝ)) (alpha := (9603058153459/2550100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (25498326704937752137/25501000000000000000 : ℝ)*(X 0 1+X 2 1)+(9603058153459/2550100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2149/512 : ℝ)) (lo := (87/6250 : ℝ)) (hi := (26893/100000 : ℝ)) (c := (25498326704937752137/25501000000000000000 : ℝ)) (alpha := (9603058153459/2550100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (25498326704937752137/25501000000000000000 : ℝ)*(X 0 2+X 1 2)+(9603058153459/2550100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2149/512 : ℝ)) (lo := (87/6250 : ℝ)) (hi := (26893/100000 : ℝ)) (c := (25498326704937752137/25501000000000000000 : ℝ)) (alpha := (9603058153459/2550100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-99808321/500000000 : ℝ)*X 0 0+(1410871597/2500000000 : ℝ)*X 0 1+(5046290137/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5406032373/10000000000 : ℝ)*X 1 0+(-2314926651/10000000000 : ℝ)*X 1 1+(2523145013/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1081206477/2000000000 : ℝ)*X 2 0+(5046289811/10000000000 : ℝ)*X 2 1+(-231492691/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((858568273/2000000000 : ℝ)*X 0 0+(3710294121/10000000000 : ℝ)*X 0 1+(4959753399/10000000000 : ℝ)*X 0 2+(858568273/2000000000 : ℝ)*X 1 0+(3710294121/10000000000 : ℝ)*X 1 1+(4959753399/10000000000 : ℝ)*X 1 2+(858568273/2000000000 : ℝ)*X 2 0+(3710294121/10000000000 : ℝ)*X 2 1+(4959753399/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-399341691/2000000000 : ℝ)*X 0 0+(25269/50000 : ℝ)*X 0 1+(2817919821/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5251106959/10000000000 : ℝ)*X 1 0+(-215672191/1250000000 : ℝ)*X 1 1+(88059983/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5251106309/10000000000 : ℝ)*X 2 0+(1408959679/2500000000 : ℝ)*X 2 1+(-1725378731/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4293974571/10000000000 : ℝ)*X 0 0+(1236010037/2500000000 : ℝ)*X 0 1+(3726294651/10000000000 : ℝ)*X 0 2+(4293974571/10000000000 : ℝ)*X 1 0+(1236010037/2500000000 : ℝ)*X 1 1+(3726294651/10000000000 : ℝ)*X 1 2+(4293974571/10000000000 : ℝ)*X 2 0+(1236010037/2500000000 : ℝ)*X 2 1+(3726294651/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (839342634632742462129496251/159381250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (31907549/50000000000000 : ℝ)*(base1) + (72694757/10000000000000 : ℝ)*(base19) + (730664521/100000000000000 : ℝ)*(base23) + (31003089/20000000000000 : ℝ)*(upper3) + (50142533/100000000000000 : ℝ)*(upper5) + (154677958920603/12500000000000 : ℝ)*(major0) + (154677958920603/12500000000000 : ℝ)*(major1) + (154677958920603/12500000000000 : ℝ)*(major2) + (1674495157712497/100000000000000 : ℝ)*(sp0) + (167449698426053/10000000000000 : ℝ)*(sp1) + (1674496980543579/100000000000000 : ℝ)*(sp2) + (16006950575849/2000000000000 : ℝ)*(sp3) + (26173107/1000000000000 : ℝ)*(sp4) + (1863372091/100000000000000 : ℝ)*(sp7) + (800349455979639/100000000000000 : ℝ)*(f.failure) + (16744977112081/1000000000000 : ℝ)*(f.sum) + (63227772641139/127505000000000000000000000000 : ℝ)*base66 + (348366595523203373/45537500000000000000000000000000 : ℝ)*base67 + (627682348807978373/45537500000000000000000000000000 : ℝ)*base69 + (526803324466690873/45537500000000000000000000000000 : ℝ)*base71 + (8943987367243/3984531250000000000000000000 : ℝ)*base73 + (174995778481565873/45537500000000000000000000000000 : ℝ)*base75 + (238474982670753373/45537500000000000000000000000000 : ℝ)*base77 + (245807824319215873/45537500000000000000000000000000 : ℝ)*base79 + (705992178089211/127505000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (4598829/5000000000000000000000 : ℝ)*base89 + (4598829/5000000000000000000000 : ℝ)*base91 + (4598829/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2299960020032112127981081971/318762500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (952985099/100000000000000 : ℝ)*(base19) + (159113997/25000000000000 : ℝ)*(base23) + (1612897/10000000000000 : ℝ)*(upper2) + (42726153/100000000000000 : ℝ)*(upper3) + (18001293/10000000000000 : ℝ)*(upper5) + (317410784693039/25000000000000 : ℝ)*(major0) + (317410784693039/25000000000000 : ℝ)*(major1) + (317410784693039/25000000000000 : ℝ)*(major2) + (179440001/50000000000000 : ℝ)*(sp0) + (4561259307/100000000000000 : ℝ)*(sp1) + (85904854590233/5000000000000 : ℝ)*(sp4) + (26845186506879/1562500000000 : ℝ)*(sp5) + (1718096814228673/100000000000000 : ℝ)*(sp6) + (821188586350379/100000000000000 : ℝ)*(sp7) + (821188586350379/100000000000000 : ℝ)*(f.failure) + (1718097450684661/100000000000000 : ℝ)*(f.sum) + (1355923828093759/127505000000000000000000000000 : ℝ)*base65 + (215050152765512049/91075000000000000000000000000000 : ℝ)*base67 + (115594524978612951/91075000000000000000000000000000 : ℝ)*base70 + (108167214377812049/91075000000000000000000000000000 : ℝ)*base71 + (824472940954769/127505000000000000000000000000 : ℝ)*base73 + (282657173448112951/91075000000000000000000000000000 : ℝ)*base76 + (426919610335162049/91075000000000000000000000000000 : ℝ)*base77 + (392619891561612049/91075000000000000000000000000000 : ℝ)*base79 + (179092895889387/63752500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (31475031/5000000000000000000000 : ℝ)*base90 + (31475031/5000000000000000000000 : ℝ)*base92 + (31475031/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1339_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77305211/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26893/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (87/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3431/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4871/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1339_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1339_s2_0 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2036585513/10000000000 : ℝ)*x 0 + (5480572109/10000000000 : ℝ)*x 1 + (5183317949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2036585513/10000000000 : ℝ)^4299 ≤ (12382719306723/100000000000000 : ℝ)^3275 := by
    have hnat : (2036585513 : ℕ)^4299*100000000000000^3275 ≤ 12382719306723^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2036585513 10000000000 12382719306723 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5480572109/10000000000 : ℝ)^4299 ≤ (45411320485729/100000000000000 : ℝ)^3275 := by
    have hnat : (5480572109 : ℕ)^4299*100000000000000^3275 ≤ 45411320485729^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5480572109 10000000000 45411320485729 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5183317949/10000000000 : ℝ)^4299 ≤ (21102980092663/50000000000000 : ℝ)^3275 := by
    have hnat : (5183317949 : ℕ)^4299*50000000000000^3275 ≤ 21102980092663^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183317949 10000000000 21102980092663 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2036585513/10000000000 : ℝ), (5480572109/10000000000 : ℝ), (5183317949/10000000000 : ℝ)] ![(12382719306723/100000000000000 : ℝ), (45411320485729/100000000000000 : ℝ), (21102980092663/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2036585513/10000000000 : ℝ)|^4299 ≤ (12382719306723/100000000000000 : ℝ)^3275
        have hw : |(-2036585513/10000000000 : ℝ)|=(2036585513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5480572109/10000000000 : ℝ)|^4299 ≤ (45411320485729/100000000000000 : ℝ)^3275
        have hw : |(5480572109/10000000000 : ℝ)|=(5480572109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5183317949/10000000000 : ℝ)|^4299 ≤ (21102980092663/50000000000000 : ℝ)^3275
        have hw : |(5183317949/10000000000 : ℝ)|=(5183317949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s2_1 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1073232973/2000000000 : ℝ)*x 0 + (-2190204129/10000000000 : ℝ)*x 1 + (80989349/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073232973/2000000000 : ℝ)^4299 ≤ (5521379471517/12500000000000 : ℝ)^3275 := by
    have hnat : (1073232973 : ℕ)^4299*12500000000000^3275 ≤ 5521379471517^3275*2000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073232973 2000000000 5521379471517 12500000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2190204129/10000000000 : ℝ)^4299 ≤ (6811499947027/50000000000000 : ℝ)^3275 := by
    have hnat : (2190204129 : ℕ)^4299*50000000000000^3275 ≤ 6811499947027^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190204129 10000000000 6811499947027 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (80989349/156250000 : ℝ)^4299 ≤ (21102982160913/50000000000000 : ℝ)^3275 := by
    have hnat : (80989349 : ℕ)^4299*50000000000000^3275 ≤ 21102982160913^3275*156250000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80989349 156250000 21102982160913 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073232973/2000000000 : ℝ), (-2190204129/10000000000 : ℝ), (80989349/156250000 : ℝ)] ![(5521379471517/12500000000000 : ℝ), (6811499947027/50000000000000 : ℝ), (21102982160913/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073232973/2000000000 : ℝ)|^4299 ≤ (5521379471517/12500000000000 : ℝ)^3275
        have hw : |(1073232973/2000000000 : ℝ)|=(1073232973/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2190204129/10000000000 : ℝ)|^4299 ≤ (6811499947027/50000000000000 : ℝ)^3275
        have hw : |(-2190204129/10000000000 : ℝ)|=(2190204129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(80989349/156250000 : ℝ)|^4299 ≤ (21102982160913/50000000000000 : ℝ)^3275
        have hw : |(80989349/156250000 : ℝ)|=(80989349/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s2_2 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5366164953/10000000000 : ℝ)*x 0 + (2591659117/5000000000 : ℝ)*x 1 + (-1095102073/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5366164953/10000000000 : ℝ)^4299 ≤ (44171036722987/100000000000000 : ℝ)^3275 := by
    have hnat : (5366164953 : ℕ)^4299*100000000000000^3275 ≤ 44171036722987^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5366164953 10000000000 44171036722987 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591659117/5000000000 : ℝ)^4299 ≤ (8441192646317/20000000000000 : ℝ)^3275 := by
    have hnat : (2591659117 : ℕ)^4299*20000000000000^3275 ≤ 8441192646317^3275*5000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591659117 5000000000 8441192646317 20000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1095102073/5000000000 : ℝ)^4299 ≤ (2724600006571/20000000000000 : ℝ)^3275 := by
    have hnat : (1095102073 : ℕ)^4299*20000000000000^3275 ≤ 2724600006571^3275*5000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095102073 5000000000 2724600006571 20000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5366164953/10000000000 : ℝ), (2591659117/5000000000 : ℝ), (-1095102073/5000000000 : ℝ)] ![(44171036722987/100000000000000 : ℝ), (8441192646317/20000000000000 : ℝ), (2724600006571/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5366164953/10000000000 : ℝ)|^4299 ≤ (44171036722987/100000000000000 : ℝ)^3275
        have hw : |(5366164953/10000000000 : ℝ)|=(5366164953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591659117/5000000000 : ℝ)|^4299 ≤ (8441192646317/20000000000000 : ℝ)^3275
        have hw : |(2591659117/5000000000 : ℝ)|=(2591659117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1095102073/5000000000 : ℝ)|^4299 ≤ (2724600006571/20000000000000 : ℝ)^3275
        have hw : |(-1095102073/5000000000 : ℝ)|=(1095102073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s2_3 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4321094187/10000000000 : ℝ)*x 0 + (804115963/2000000000 : ℝ)*x 1 + (2321248373/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4321094187/10000000000 : ℝ)^4299 ≤ (33239477269153/100000000000000 : ℝ)^3275 := by
    have hnat : (4321094187 : ℕ)^4299*100000000000000^3275 ≤ 33239477269153^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4321094187 10000000000 33239477269153 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (804115963/2000000000 : ℝ)^4299 ≤ (188990926739/625000000000 : ℝ)^3275 := by
    have hnat : (804115963 : ℕ)^4299*625000000000^3275 ≤ 188990926739^3275*2000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      804115963 2000000000 188990926739 625000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2321248373/5000000000 : ℝ)^4299 ≤ (18260987219859/50000000000000 : ℝ)^3275 := by
    have hnat : (2321248373 : ℕ)^4299*50000000000000^3275 ≤ 18260987219859^3275*5000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2321248373 5000000000 18260987219859 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4321094187/10000000000 : ℝ), (804115963/2000000000 : ℝ), (2321248373/5000000000 : ℝ)] ![(33239477269153/100000000000000 : ℝ), (188990926739/625000000000 : ℝ), (18260987219859/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4321094187/10000000000 : ℝ)|^4299 ≤ (33239477269153/100000000000000 : ℝ)^3275
        have hw : |(4321094187/10000000000 : ℝ)|=(4321094187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(804115963/2000000000 : ℝ)|^4299 ≤ (188990926739/625000000000 : ℝ)^3275
        have hw : |(804115963/2000000000 : ℝ)|=(804115963/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2321248373/5000000000 : ℝ)|^4299 ≤ (18260987219859/50000000000000 : ℝ)^3275
        have hw : |(2321248373/5000000000 : ℝ)|=(2321248373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s2_4 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-407330473/2000000000 : ℝ)*x 0 + (1037037797/2000000000 : ℝ)*x 1 + (5478684153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (407330473/2000000000 : ℝ)^4299 ≤ (96744163049/781250000000 : ℝ)^3275 := by
    have hnat : (407330473 : ℕ)^4299*781250000000^3275 ≤ 96744163049^3275*2000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      407330473 2000000000 96744163049 781250000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1037037797/2000000000 : ℝ)^4299 ≤ (10556490031709/25000000000000 : ℝ)^3275 := by
    have hnat : (1037037797 : ℕ)^4299*25000000000000^3275 ≤ 10556490031709^3275*2000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037037797 2000000000 10556490031709 25000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5478684153/10000000000 : ℝ)^4299 ≤ (1134769674797/2500000000000 : ℝ)^3275 := by
    have hnat : (5478684153 : ℕ)^4299*2500000000000^3275 ≤ 1134769674797^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5478684153 10000000000 1134769674797 2500000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-407330473/2000000000 : ℝ), (1037037797/2000000000 : ℝ), (5478684153/10000000000 : ℝ)] ![(96744163049/781250000000 : ℝ), (10556490031709/25000000000000 : ℝ), (1134769674797/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-407330473/2000000000 : ℝ)|^4299 ≤ (96744163049/781250000000 : ℝ)^3275
        have hw : |(-407330473/2000000000 : ℝ)|=(407330473/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1037037797/2000000000 : ℝ)|^4299 ≤ (10556490031709/25000000000000 : ℝ)^3275
        have hw : |(1037037797/2000000000 : ℝ)|=(1037037797/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5478684153/10000000000 : ℝ)|^4299 ≤ (1134769674797/2500000000000 : ℝ)^3275
        have hw : |(5478684153/10000000000 : ℝ)|=(5478684153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s2_5 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42316581/80000000 : ℝ)*x 0 + (-1894838013/10000000000 : ℝ)*x 1 + (5478684161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42316581/80000000 : ℝ)^4299 ≤ (21672649983929/50000000000000 : ℝ)^3275 := by
    have hnat : (42316581 : ℕ)^4299*50000000000000^3275 ≤ 21672649983929^3275*80000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42316581 80000000 21672649983929 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1894838013/10000000000 : ℝ)^4299 ≤ (2252782588799/20000000000000 : ℝ)^3275 := by
    have hnat : (1894838013 : ℕ)^4299*20000000000000^3275 ≤ 2252782588799^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1894838013 10000000000 2252782588799 20000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5478684161/10000000000 : ℝ)^4299 ≤ (11347696769721/25000000000000 : ℝ)^3275 := by
    have hnat : (5478684161 : ℕ)^4299*25000000000000^3275 ≤ 11347696769721^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5478684161 10000000000 11347696769721 25000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42316581/80000000 : ℝ), (-1894838013/10000000000 : ℝ), (5478684161/10000000000 : ℝ)] ![(21672649983929/50000000000000 : ℝ), (2252782588799/20000000000000 : ℝ), (11347696769721/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42316581/80000000 : ℝ)|^4299 ≤ (21672649983929/50000000000000 : ℝ)^3275
        have hw : |(42316581/80000000 : ℝ)|=(42316581/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1894838013/10000000000 : ℝ)|^4299 ≤ (2252782588799/20000000000000 : ℝ)^3275
        have hw : |(-1894838013/10000000000 : ℝ)|=(1894838013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5478684161/10000000000 : ℝ)|^4299 ≤ (11347696769721/25000000000000 : ℝ)^3275
        have hw : |(5478684161/10000000000 : ℝ)|=(5478684161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s2_6 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (105791453/200000000 : ℝ)*x 0 + (2140111/3906250 : ℝ)*x 1 + (-1894837979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105791453/200000000 : ℝ)^4299 ≤ (21672650118387/50000000000000 : ℝ)^3275 := by
    have hnat : (105791453 : ℕ)^4299*50000000000000^3275 ≤ 21672650118387^3275*200000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105791453 200000000 21672650118387 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2140111/3906250 : ℝ)^4299 ≤ (5673848383501/12500000000000 : ℝ)^3275 := by
    have hnat : (2140111 : ℕ)^4299*12500000000000^3275 ≤ 5673848383501^3275*3906250^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140111 3906250 5673848383501 12500000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1894837979/10000000000 : ℝ)^4299 ≤ (5631956339343/50000000000000 : ℝ)^3275 := by
    have hnat : (1894837979 : ℕ)^4299*50000000000000^3275 ≤ 5631956339343^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1894837979 10000000000 5631956339343 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105791453/200000000 : ℝ), (2140111/3906250 : ℝ), (-1894837979/10000000000 : ℝ)] ![(21672650118387/50000000000000 : ℝ), (5673848383501/12500000000000 : ℝ), (5631956339343/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105791453/200000000 : ℝ)|^4299 ≤ (21672650118387/50000000000000 : ℝ)^3275
        have hw : |(105791453/200000000 : ℝ)|=(105791453/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2140111/3906250 : ℝ)|^4299 ≤ (5673848383501/12500000000000 : ℝ)^3275
        have hw : |(2140111/3906250 : ℝ)|=(2140111/3906250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1894837979/10000000000 : ℝ)|^4299 ≤ (5631956339343/50000000000000 : ℝ)^3275
        have hw : |(-1894837979/10000000000 : ℝ)|=(1894837979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s2_7 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4321234419/10000000000 : ℝ)*x 0 + (144955713/312500000 : ℝ)*x 1 + (2012264599/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4321234419/10000000000 : ℝ)^4299 ≤ (33240893277863/100000000000000 : ℝ)^3275 := by
    have hnat : (4321234419 : ℕ)^4299*100000000000000^3275 ≤ 33240893277863^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4321234419 10000000000 33240893277863 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (144955713/312500000 : ℝ)^4299 ≤ (36481562045613/100000000000000 : ℝ)^3275 := by
    have hnat : (144955713 : ℕ)^4299*100000000000000^3275 ≤ 36481562045613^3275*312500000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      144955713 312500000 36481562045613 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2012264599/5000000000 : ℝ)^4299 ≤ (30277544660233/100000000000000 : ℝ)^3275 := by
    have hnat : (2012264599 : ℕ)^4299*100000000000000^3275 ≤ 30277544660233^3275*5000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2012264599 5000000000 30277544660233 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4321234419/10000000000 : ℝ), (144955713/312500000 : ℝ), (2012264599/5000000000 : ℝ)] ![(33240893277863/100000000000000 : ℝ), (36481562045613/100000000000000 : ℝ), (30277544660233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4321234419/10000000000 : ℝ)|^4299 ≤ (33240893277863/100000000000000 : ℝ)^3275
        have hw : |(4321234419/10000000000 : ℝ)|=(4321234419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(144955713/312500000 : ℝ)|^4299 ≤ (36481562045613/100000000000000 : ℝ)^3275
        have hw : |(144955713/312500000 : ℝ)|=(144955713/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2012264599/5000000000 : ℝ)|^4299 ≤ (30277544660233/100000000000000 : ℝ)^3275
        have hw : |(2012264599/5000000000 : ℝ)|=(2012264599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1339_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77305211/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3431/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1229/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4029/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3431/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3431/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3431/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3431/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3431/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3431/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3431/50000 : ℝ) ^ (2149/512 : ℝ) ≤ (1306996960802533/100000000000000000000 : ℝ) := by
    have hpowers : (3431/50000 : ℝ)^2149 ≤ (1306996960802533/100000000000000000000 : ℝ)^512 := by
      have hnat : (3431 : ℕ)^2149*100000000000000000000^512 ≤ 1306996960802533^512*50000^2149 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3431 50000 1306996960802533 100000000000000000000 2149 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3431/50000 : ℝ)) (X := (1306996960802533/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2149 512 (by norm_num) hpowers
    exact h
  have hpowhi : (4871/25000 : ℝ) ^ (2149/512 : ℝ) ≤ (10437353534710787/10000000000000000000 : ℝ) := by
    have hpowers : (4871/25000 : ℝ)^2149 ≤ (10437353534710787/10000000000000000000 : ℝ)^512 := by
      have hnat : (4871 : ℕ)^2149*10000000000000000000^512 ≤ 10437353534710787^512*25000^2149 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4871 25000 10437353534710787 10000000000000000000 2149 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4871/25000 : ℝ)) (X := (10437353534710787/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2149 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001306996960802533/50000000000000000000 : ℝ) ≤ (10000062277876373/10000000000000000 : ℝ) ^ (2149/512 : ℝ) := by
    have hpowers : (50001306996960802533/50000000000000000000 : ℝ)^512 ≤ (10000062277876373/10000000000000000 : ℝ)^2149 := by
      have hnat : (50001306996960802533 : ℕ)^512*10000000000000000^2149 ≤ 10000062277876373^2149*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001306996960802533 50000000000000000000 10000062277876373 10000000000000000 512 2149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000062277876373/10000000000000000 : ℝ)) (X := (50001306996960802533/50000000000000000000 : ℝ)) (by norm_num) 2149 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100105680532307910403/100000000000000000000 : ℝ) ≤ (2000503365908177/2000000000000000 : ℝ) ^ (2149/512 : ℝ) := by
    have hpowers : (100105680532307910403/100000000000000000000 : ℝ)^512 ≤ (2000503365908177/2000000000000000 : ℝ)^2149 := by
      have hnat : (100105680532307910403 : ℕ)^512*2000000000000000^2149 ≤ 2000503365908177^2149*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100105680532307910403 100000000000000000000 2000503365908177 2000000000000000 512 2149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000503365908177/2000000000000000 : ℝ)) (X := (100105680532307910403/100000000000000000000 : ℝ)) (by norm_num) 2149 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (5010437353534710787/5000000000000000000 : ℝ) ≤ (10004971381205397/10000000000000000 : ℝ) ^ (2149/512 : ℝ) := by
    have hpowers : (5010437353534710787/5000000000000000000 : ℝ)^512 ≤ (10004971381205397/10000000000000000 : ℝ)^2149 := by
      have hnat : (5010437353534710787 : ℕ)^512*10000000000000000^2149 ≤ 10004971381205397^2149*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5010437353534710787 5000000000000000000 10004971381205397 10000000000000000 512 2149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004971381205397/10000000000000000 : ℝ)) (X := (5010437353534710787/5000000000000000000 : ℝ)) (by norm_num) 2149 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1306996960802533/100000000000000000000 : ℝ) ≤ ((63093549902155908659/63110000000000000000 : ℝ)+2*(19176184879/9860937500000 : ℝ)*(3431/50000 : ℝ))^(2149/512 : ℝ) := by
    rw [show (63093549902155908659/63110000000000000000 : ℝ)+2*(19176184879/9860937500000 : ℝ)*(3431/50000 : ℝ)=(10000062277876373/10000000000000000 : ℝ) by norm_num, show 1+2*(1306996960802533/100000000000000000000 : ℝ)=(50001306996960802533/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10437353534710787/10000000000000000000 : ℝ)+(1306996960802533/100000000000000000000 : ℝ) ≤ ((63093549902155908659/63110000000000000000 : ℝ)+(19176184879/9860937500000 : ℝ)*((4871/25000 : ℝ)+(3431/50000 : ℝ)))^(2149/512 : ℝ) := by
    rw [show (63093549902155908659/63110000000000000000 : ℝ)+(19176184879/9860937500000 : ℝ)*((4871/25000 : ℝ)+(3431/50000 : ℝ))=(2000503365908177/2000000000000000 : ℝ) by norm_num, show 1+(10437353534710787/10000000000000000000 : ℝ)+(1306996960802533/100000000000000000000 : ℝ)=(100105680532307910403/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10437353534710787/10000000000000000000 : ℝ) ≤ ((63093549902155908659/63110000000000000000 : ℝ)+2*(19176184879/9860937500000 : ℝ)*(4871/25000 : ℝ))^(2149/512 : ℝ) := by
    rw [show (63093549902155908659/63110000000000000000 : ℝ)+2*(19176184879/9860937500000 : ℝ)*(4871/25000 : ℝ)=(10004971381205397/10000000000000000 : ℝ) by norm_num, show 1+2*(10437353534710787/10000000000000000000 : ℝ)=(5010437353534710787/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (63093549902155908659/63110000000000000000 : ℝ)*(X 1 0+X 2 0)+(19176184879/9860937500000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2149/512 : ℝ)) (lo := (3431/50000 : ℝ)) (hi := (4871/25000 : ℝ)) (c := (63093549902155908659/63110000000000000000 : ℝ)) (alpha := (19176184879/9860937500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (63093549902155908659/63110000000000000000 : ℝ)*(X 0 1+X 2 1)+(19176184879/9860937500000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2149/512 : ℝ)) (lo := (3431/50000 : ℝ)) (hi := (4871/25000 : ℝ)) (c := (63093549902155908659/63110000000000000000 : ℝ)) (alpha := (19176184879/9860937500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (63093549902155908659/63110000000000000000 : ℝ)*(X 0 2+X 1 2)+(19176184879/9860937500000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2149/512 : ℝ)) (lo := (3431/50000 : ℝ)) (hi := (4871/25000 : ℝ)) (c := (63093549902155908659/63110000000000000000 : ℝ)) (alpha := (19176184879/9860937500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2036585513/10000000000 : ℝ)*X 0 0+(5480572109/10000000000 : ℝ)*X 0 1+(5183317949/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1073232973/2000000000 : ℝ)*X 1 0+(-2190204129/10000000000 : ℝ)*X 1 1+(80989349/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5366164953/10000000000 : ℝ)*X 2 0+(2591659117/5000000000 : ℝ)*X 2 1+(-1095102073/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4321094187/10000000000 : ℝ)*X 0 0+(804115963/2000000000 : ℝ)*X 0 1+(2321248373/5000000000 : ℝ)*X 0 2+(4321094187/10000000000 : ℝ)*X 1 0+(804115963/2000000000 : ℝ)*X 1 1+(2321248373/5000000000 : ℝ)*X 1 2+(4321094187/10000000000 : ℝ)*X 2 0+(804115963/2000000000 : ℝ)*X 2 1+(2321248373/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-407330473/2000000000 : ℝ)*X 0 0+(1037037797/2000000000 : ℝ)*X 0 1+(5478684153/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((42316581/80000000 : ℝ)*X 1 0+(-1894838013/10000000000 : ℝ)*X 1 1+(5478684161/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((105791453/200000000 : ℝ)*X 2 0+(2140111/3906250 : ℝ)*X 2 1+(-1894837979/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4321234419/10000000000 : ℝ)*X 0 0+(144955713/312500000 : ℝ)*X 0 1+(2012264599/5000000000 : ℝ)*X 0 2+(4321234419/10000000000 : ℝ)*X 1 0+(144955713/312500000 : ℝ)*X 1 1+(2012264599/5000000000 : ℝ)*X 1 2+(4321234419/10000000000 : ℝ)*X 2 0+(144955713/312500000 : ℝ)*X 2 1+(2012264599/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (133709917017632118057084639/19721875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1174308721/100000000000000 : ℝ)*(base19) + (1202795519/100000000000000 : ℝ)*(base23) + (14318119/100000000000000 : ℝ)*(lower2) + (157586579/100000000000000 : ℝ)*(upper3) + (1673453/1250000000000 : ℝ)*(upper5) + (7768919371133/312500000000 : ℝ)*(major0) + (7768919371133/312500000000 : ℝ)*(major1) + (7768919371133/312500000000 : ℝ)*(major2) + (1682071294496879/50000000000000 : ℝ)*(sp0) + (168207981863497/5000000000000 : ℝ)*(sp1) + (3364159608783141/100000000000000 : ℝ)*(sp2) + (1607939326092027/100000000000000 : ℝ)*(sp3) + (9111292451/50000000000000 : ℝ)*(sp4) + (4016930929/50000000000000 : ℝ)*(sp7) + (321589471990777/20000000000000 : ℝ)*(f.failure) + (168208040578933/5000000000000 : ℝ)*(f.sum) + (951730219233/1262200000000000000000000000 : ℝ)*base66 + (9882475338476557/4930468750000000000000000000000 : ℝ)*base68 + (60749381029409397/19721875000000000000000000000000 : ℝ)*base69 + (94897685983962489/9860937500000000000000000000000 : ℝ)*base72 + (16485005393569/6311000000000000000000000000 : ℝ)*base73 + (18311661451878103/19721875000000000000000000000000 : ℝ)*base76 + (104257641380121853/19721875000000000000000000000000 : ℝ)*base78 + (7433778340268739/9860937500000000000000000000000 : ℝ)*base80 + (27089914423/394437500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (6038947/1000000000000000000000 : ℝ)*base89 + (6038947/1000000000000000000000 : ℝ)*base91 + (6038947/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11040797917033445830973922369/1577750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (713682081/50000000000000 : ℝ)*(base19) + (1633579071/100000000000000 : ℝ)*(base23) + (3616369/2000000000000 : ℝ)*(upper3) + (74629723/100000000000000 : ℝ)*(lower4) + (104355743/100000000000000 : ℝ)*(upper5) + (1258932928673897/50000000000000 : ℝ)*(major0) + (1258932928673897/50000000000000 : ℝ)*(major1) + (1258932928673897/50000000000000 : ℝ)*(major2) + (1581983077/10000000000000 : ℝ)*(sp1) + (19205423433/100000000000000 : ℝ)*(sp2) + (27257670052209/800000000000 : ℝ)*(sp4) + (3407191509331193/100000000000000 : ℝ)*(sp5) + (3407187917523621/100000000000000 : ℝ)*(sp6) + (814261362454529/50000000000000 : ℝ)*(sp7) + (814261362454529/50000000000000 : ℝ)*(f.failure) + (27257670052209/800000000000 : ℝ)*(f.sum) + (30960356575529/31555000000000000000000000000 : ℝ)*base65 + (3673684603348725877/3155500000000000000000000000000000 : ℝ)*base68 + (18216728251606725877/3155500000000000000000000000000000 : ℝ)*base70 + (12073918536169274123/3155500000000000000000000000000000 : ℝ)*base71 + (30708425977131/31555000000000000000000000000 : ℝ)*base74 + (8694488451980725877/3155500000000000000000000000000000 : ℝ)*base76 + (7770458098362725877/3155500000000000000000000000000000 : ℝ)*base78 + (26166024860537774123/3155500000000000000000000000000000 : ℝ)*base79 + (34175115644121/31555000000000000000000000000 : ℝ)*base82 + (7749381/2500000000000000000000 : ℝ)*base90 + (7749381/2500000000000000000000 : ℝ)*base92 + (7749381/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1339_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77305211/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3431/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1229/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4029/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1339_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1339_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77305211/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1229/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4029/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1339_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1339_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1339_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77305211/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1229/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4029/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1339_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
