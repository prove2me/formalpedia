-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1257_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:52:20.430901+00:00
-- url     : https://prove2.me/submissions/796dcd8e-db8e-4236-8c8d-f108adc57370

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
theorem support_rectangle_w1257_s6_0 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1056531111/5000000000 : ℝ)*x 0 + (2695545769/5000000000 : ℝ)*x 1 + (1053449283/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056531111/5000000000 : ℝ)^4225 ≤ (1606429673599/12500000000000 : ℝ)^3201 := by
    have hnat : (1056531111 : ℕ)^4225*12500000000000^3201 ≤ 1606429673599^3201*5000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056531111 5000000000 1606429673599 12500000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695545769/5000000000 : ℝ)^4225 ≤ (4424254240883/10000000000000 : ℝ)^3201 := by
    have hnat : (2695545769 : ℕ)^4225*10000000000000^3201 ≤ 4424254240883^3201*5000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695545769 5000000000 4424254240883 10000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053449283/2000000000 : ℝ)^4225 ≤ (1716240807437/4000000000000 : ℝ)^3201 := by
    have hnat : (1053449283 : ℕ)^4225*4000000000000^3201 ≤ 1716240807437^3201*2000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053449283 2000000000 1716240807437 4000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1056531111/5000000000 : ℝ), (2695545769/5000000000 : ℝ), (1053449283/2000000000 : ℝ)] ![(1606429673599/12500000000000 : ℝ), (4424254240883/10000000000000 : ℝ), (1716240807437/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1056531111/5000000000 : ℝ)|^4225 ≤ (1606429673599/12500000000000 : ℝ)^3201
        have hw : |(-1056531111/5000000000 : ℝ)|=(1056531111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695545769/5000000000 : ℝ)|^4225 ≤ (4424254240883/10000000000000 : ℝ)^3201
        have hw : |(2695545769/5000000000 : ℝ)|=(2695545769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053449283/2000000000 : ℝ)|^4225 ≤ (1716240807437/4000000000000 : ℝ)^3201
        have hw : |(1053449283/2000000000 : ℝ)|=(1053449283/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s6_1 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534427189/1000000000 : ℝ)*x 0 + (-543963457/2500000000 : ℝ)*x 1 + (5267246409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534427189/1000000000 : ℝ)^4225 ≤ (546701285089/1250000000000 : ℝ)^3201 := by
    have hnat : (534427189 : ℕ)^4225*1250000000000^3201 ≤ 546701285089^3201*1000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534427189 1000000000 546701285089 1250000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (543963457/2500000000 : ℝ)^4225 ≤ (6678938529831/50000000000000 : ℝ)^3201 := by
    have hnat : (543963457 : ℕ)^4225*50000000000000^3201 ≤ 6678938529831^3201*2500000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543963457 2500000000 6678938529831 50000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267246409/10000000000 : ℝ)^4225 ≤ (8581204024283/20000000000000 : ℝ)^3201 := by
    have hnat : (5267246409 : ℕ)^4225*20000000000000^3201 ≤ 8581204024283^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267246409 10000000000 8581204024283 20000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534427189/1000000000 : ℝ), (-543963457/2500000000 : ℝ), (5267246409/10000000000 : ℝ)] ![(546701285089/1250000000000 : ℝ), (6678938529831/50000000000000 : ℝ), (8581204024283/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534427189/1000000000 : ℝ)|^4225 ≤ (546701285089/1250000000000 : ℝ)^3201
        have hw : |(534427189/1000000000 : ℝ)|=(534427189/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-543963457/2500000000 : ℝ)|^4225 ≤ (6678938529831/50000000000000 : ℝ)^3201
        have hw : |(-543963457/2500000000 : ℝ)|=(543963457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267246409/10000000000 : ℝ)|^4225 ≤ (8581204024283/20000000000000 : ℝ)^3201
        have hw : |(5267246409/10000000000 : ℝ)|=(5267246409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s6_2 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672135949/5000000000 : ℝ)*x 0 + (658405801/1250000000 : ℝ)*x 1 + (-1087926909/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672135949/5000000000 : ℝ)^4225 ≤ (21868051446767/50000000000000 : ℝ)^3201 := by
    have hnat : (2672135949 : ℕ)^4225*50000000000000^3201 ≤ 21868051446767^3201*5000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672135949 5000000000 21868051446767 50000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658405801/1250000000 : ℝ)^4225 ≤ (5363252513833/12500000000000 : ℝ)^3201 := by
    have hnat : (658405801 : ℕ)^4225*12500000000000^3201 ≤ 5363252513833^3201*1250000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658405801 1250000000 5363252513833 12500000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1087926909/5000000000 : ℝ)^4225 ≤ (1669734622329/12500000000000 : ℝ)^3201 := by
    have hnat : (1087926909 : ℕ)^4225*12500000000000^3201 ≤ 1669734622329^3201*5000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087926909 5000000000 1669734622329 12500000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672135949/5000000000 : ℝ), (658405801/1250000000 : ℝ), (-1087926909/5000000000 : ℝ)] ![(21868051446767/50000000000000 : ℝ), (5363252513833/12500000000000 : ℝ), (1669734622329/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672135949/5000000000 : ℝ)|^4225 ≤ (21868051446767/50000000000000 : ℝ)^3201
        have hw : |(2672135949/5000000000 : ℝ)|=(2672135949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658405801/1250000000 : ℝ)|^4225 ≤ (5363252513833/12500000000000 : ℝ)^3201
        have hw : |(658405801/1250000000 : ℝ)|=(658405801/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1087926909/5000000000 : ℝ)|^4225 ≤ (1669734622329/12500000000000 : ℝ)^3201
        have hw : |(-1087926909/5000000000 : ℝ)|=(1087926909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s6_3 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4348711443/10000000000 : ℝ)*x 0 + (2112250609/5000000000 : ℝ)*x 1 + (4476457643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4348711443/10000000000 : ℝ)^4225 ≤ (33317479026983/100000000000000 : ℝ)^3201 := by
    have hnat : (4348711443 : ℕ)^4225*100000000000000^3201 ≤ 33317479026983^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4348711443 10000000000 33317479026983 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2112250609/5000000000 : ℝ)^4225 ≤ (12826878543/40000000000 : ℝ)^3201 := by
    have hnat : (2112250609 : ℕ)^4225*40000000000^3201 ≤ 12826878543^3201*5000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112250609 5000000000 12826878543 40000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4476457643/10000000000 : ℝ)^4225 ≤ (34615324605073/100000000000000 : ℝ)^3201 := by
    have hnat : (4476457643 : ℕ)^4225*100000000000000^3201 ≤ 34615324605073^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4476457643 10000000000 34615324605073 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4348711443/10000000000 : ℝ), (2112250609/5000000000 : ℝ), (4476457643/10000000000 : ℝ)] ![(33317479026983/100000000000000 : ℝ), (12826878543/40000000000 : ℝ), (34615324605073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4348711443/10000000000 : ℝ)|^4225 ≤ (33317479026983/100000000000000 : ℝ)^3201
        have hw : |(4348711443/10000000000 : ℝ)|=(4348711443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2112250609/5000000000 : ℝ)|^4225 ≤ (12826878543/40000000000 : ℝ)^3201
        have hw : |(2112250609/5000000000 : ℝ)|=(2112250609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4476457643/10000000000 : ℝ)|^4225 ≤ (34615324605073/100000000000000 : ℝ)^3201
        have hw : |(4476457643/10000000000 : ℝ)|=(4476457643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s6_4 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1056533499/5000000000 : ℝ)*x 0 + (2633779733/5000000000 : ℝ)*x 1 + (269538863/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056533499/5000000000 : ℝ)^4225 ≤ (6425737864079/50000000000000 : ℝ)^3201 := by
    have hnat : (1056533499 : ℕ)^4225*50000000000000^3201 ≤ 6425737864079^3201*5000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056533499 5000000000 6425737864079 50000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633779733/5000000000 : ℝ)^4225 ≤ (10727346509179/25000000000000 : ℝ)^3201 := by
    have hnat : (2633779733 : ℕ)^4225*25000000000000^3201 ≤ 10727346509179^3201*5000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633779733 5000000000 10727346509179 25000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269538863/500000000 : ℝ)^4225 ≤ (4423913821453/10000000000000 : ℝ)^3201 := by
    have hnat : (269538863 : ℕ)^4225*10000000000000^3201 ≤ 4423913821453^3201*500000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269538863 500000000 4423913821453 10000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1056533499/5000000000 : ℝ), (2633779733/5000000000 : ℝ), (269538863/500000000 : ℝ)] ![(6425737864079/50000000000000 : ℝ), (10727346509179/25000000000000 : ℝ), (4423913821453/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1056533499/5000000000 : ℝ)|^4225 ≤ (6425737864079/50000000000000 : ℝ)^3201
        have hw : |(-1056533499/5000000000 : ℝ)|=(1056533499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633779733/5000000000 : ℝ)|^4225 ≤ (10727346509179/25000000000000 : ℝ)^3201
        have hw : |(2633779733/5000000000 : ℝ)|=(2633779733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269538863/500000000 : ℝ)|^4225 ≤ (4423913821453/10000000000000 : ℝ)^3201
        have hw : |(269538863/500000000 : ℝ)|=(269538863/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s6_5 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062528151/2000000000 : ℝ)*x 0 + (-513080777/2500000000 : ℝ)*x 1 + (5390776791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062528151/2000000000 : ℝ)^4225 ≤ (43394756303559/100000000000000 : ℝ)^3201 := by
    have hnat : (1062528151 : ℕ)^4225*100000000000000^3201 ≤ 43394756303559^3201*2000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062528151 2000000000 43394756303559 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (513080777/2500000000 : ℝ)^4225 ≤ (2473222107627/20000000000000 : ℝ)^3201 := by
    have hnat : (513080777 : ℕ)^4225*20000000000000^3201 ≤ 2473222107627^3201*2500000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513080777 2500000000 2473222107627 20000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390776791/10000000000 : ℝ)^4225 ≤ (44239133134467/100000000000000 : ℝ)^3201 := by
    have hnat : (5390776791 : ℕ)^4225*100000000000000^3201 ≤ 44239133134467^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390776791 10000000000 44239133134467 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062528151/2000000000 : ℝ), (-513080777/2500000000 : ℝ), (5390776791/10000000000 : ℝ)] ![(43394756303559/100000000000000 : ℝ), (2473222107627/20000000000000 : ℝ), (44239133134467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062528151/2000000000 : ℝ)|^4225 ≤ (43394756303559/100000000000000 : ℝ)^3201
        have hw : |(1062528151/2000000000 : ℝ)|=(1062528151/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-513080777/2500000000 : ℝ)|^4225 ≤ (2473222107627/20000000000000 : ℝ)^3201
        have hw : |(-513080777/2500000000 : ℝ)|=(513080777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390776791/10000000000 : ℝ)|^4225 ≤ (44239133134467/100000000000000 : ℝ)^3201
        have hw : |(5390776791/10000000000 : ℝ)|=(5390776791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s6_6 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (212505639/400000000 : ℝ)*x 0 + (5390776527/10000000000 : ℝ)*x 1 + (-2052323171/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212505639/400000000 : ℝ)^4225 ≤ (43394758675427/100000000000000 : ℝ)^3201 := by
    have hnat : (212505639 : ℕ)^4225*100000000000000^3201 ≤ 43394758675427^3201*400000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212505639 400000000 43394758675427 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390776527/10000000000 : ℝ)^4225 ≤ (442391302749/1000000000000 : ℝ)^3201 := by
    have hnat : (5390776527 : ℕ)^4225*1000000000000^3201 ≤ 442391302749^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390776527 10000000000 442391302749 1000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2052323171/10000000000 : ℝ)^4225 ≤ (12366111039171/100000000000000 : ℝ)^3201 := by
    have hnat : (2052323171 : ℕ)^4225*100000000000000^3201 ≤ 12366111039171^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2052323171 10000000000 12366111039171 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212505639/400000000 : ℝ), (5390776527/10000000000 : ℝ), (-2052323171/10000000000 : ℝ)] ![(43394758675427/100000000000000 : ℝ), (442391302749/1000000000000 : ℝ), (12366111039171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212505639/400000000 : ℝ)|^4225 ≤ (43394758675427/100000000000000 : ℝ)^3201
        have hw : |(212505639/400000000 : ℝ)|=(212505639/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390776527/10000000000 : ℝ)|^4225 ≤ (442391302749/1000000000000 : ℝ)^3201
        have hw : |(5390776527/10000000000 : ℝ)|=(5390776527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2052323171/10000000000 : ℝ)|^4225 ≤ (12366111039171/100000000000000 : ℝ)^3201
        have hw : |(-2052323171/10000000000 : ℝ)|=(2052323171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s6_7 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1087180173/2500000000 : ℝ)*x 0 + (4475820409/10000000000 : ℝ)*x 1 + (2112570503/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087180173/2500000000 : ℝ)^4225 ≤ (6663514511249/20000000000000 : ℝ)^3201 := by
    have hnat : (1087180173 : ℕ)^4225*20000000000000^3201 ≤ 6663514511249^3201*2500000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087180173 2500000000 6663514511249 20000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4475820409/10000000000 : ℝ)^4225 ≤ (4326102606547/12500000000000 : ℝ)^3201 := by
    have hnat : (4475820409 : ℕ)^4225*12500000000000^3201 ≤ 4326102606547^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4475820409 10000000000 4326102606547 12500000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2112570503/5000000000 : ℝ)^4225 ≤ (32073606581421/100000000000000 : ℝ)^3201 := by
    have hnat : (2112570503 : ℕ)^4225*100000000000000^3201 ≤ 32073606581421^3201*5000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112570503 5000000000 32073606581421 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1087180173/2500000000 : ℝ), (4475820409/10000000000 : ℝ), (2112570503/5000000000 : ℝ)] ![(6663514511249/20000000000000 : ℝ), (4326102606547/12500000000000 : ℝ), (32073606581421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1087180173/2500000000 : ℝ)|^4225 ≤ (6663514511249/20000000000000 : ℝ)^3201
        have hw : |(1087180173/2500000000 : ℝ)|=(1087180173/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4475820409/10000000000 : ℝ)|^4225 ≤ (4326102606547/12500000000000 : ℝ)^3201
        have hw : |(4475820409/10000000000 : ℝ)|=(4475820409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2112570503/5000000000 : ℝ)|^4225 ≤ (32073606581421/100000000000000 : ℝ)^3201
        have hw : |(2112570503/5000000000 : ℝ)|=(2112570503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1257_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75861189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1767/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11473/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11493/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3529/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1767/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11473/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1767/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11473/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1767/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11473/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1767/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11473/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1767/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11473/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1767/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11473/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11473/100000 : ℝ) ^ (8449/2048 : ℝ) ≤ (13204089409996413/100000000000000000000 : ℝ) := by
    have hpowers : (11473/100000 : ℝ)^8449 ≤ (13204089409996413/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11473 : ℕ)^8449*100000000000000000000^2048 ≤ 13204089409996413^2048*100000^8449 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11473 100000 13204089409996413 100000000000000000000 8449 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11473/100000 : ℝ)) (X := (13204089409996413/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8449 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1767/12500 : ℝ) ^ (8449/2048 : ℝ) ≤ (31237918208096639/100000000000000000000 : ℝ) := by
    have hpowers : (1767/12500 : ℝ)^8449 ≤ (31237918208096639/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1767 : ℕ)^8449*100000000000000000000^2048 ≤ 31237918208096639^2048*12500^8449 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1767 12500 31237918208096639 100000000000000000000 8449 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1767/12500 : ℝ)) (X := (31237918208096639/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8449 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013204089409996413/50000000000000000000 : ℝ) ≤ (10000640058477747/10000000000000000 : ℝ) ^ (8449/2048 : ℝ) := by
    have hpowers : (50013204089409996413/50000000000000000000 : ℝ)^2048 ≤ (10000640058477747/10000000000000000 : ℝ)^8449 := by
      have hnat : (50013204089409996413 : ℕ)^2048*10000000000000000^8449 ≤ 10000640058477747^8449*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013204089409996413 50000000000000000000 10000640058477747 10000000000000000 2048 8449 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000640058477747/10000000000000000 : ℝ)) (X := (50013204089409996413/50000000000000000000 : ℝ)) (by norm_num) 8449 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011110501904523263/25000000000000000000 : ℝ) ≤ (1600172331709/1600000000000 : ℝ) ^ (8449/2048 : ℝ) := by
    have hpowers : (25011110501904523263/25000000000000000000 : ℝ)^2048 ≤ (1600172331709/1600000000000 : ℝ)^8449 := by
      have hnat : (25011110501904523263 : ℕ)^2048*1600000000000^8449 ≤ 1600172331709^8449*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011110501904523263 25000000000000000000 1600172331709 1600000000000 2048 8449 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1600172331709/1600000000000 : ℝ)) (X := (25011110501904523263/25000000000000000000 : ℝ)) (by norm_num) 8449 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031237918208096639/50000000000000000000 : ℝ) ≤ (10001514087884753/10000000000000000 : ℝ) ^ (8449/2048 : ℝ) := by
    have hpowers : (50031237918208096639/50000000000000000000 : ℝ)^2048 ≤ (10001514087884753/10000000000000000 : ℝ)^8449 := by
      have hnat : (50031237918208096639 : ℕ)^2048*10000000000000000^8449 ≤ 10001514087884753^8449*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031237918208096639 50000000000000000000 10001514087884753 10000000000000000 2048 8449 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001514087884753/10000000000000000 : ℝ)) (X := (50031237918208096639/50000000000000000000 : ℝ)) (by norm_num) 8449 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13204089409996413/100000000000000000000 : ℝ) ≤ ((26621676736339660423/26630000000000000000 : ℝ)+2*(437014703503/266300000000000 : ℝ)*(11473/100000 : ℝ))^(8449/2048 : ℝ) := by
    rw [show (26621676736339660423/26630000000000000000 : ℝ)+2*(437014703503/266300000000000 : ℝ)*(11473/100000 : ℝ)=(10000640058477747/10000000000000000 : ℝ) by norm_num, show 1+2*(13204089409996413/100000000000000000000 : ℝ)=(50013204089409996413/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31237918208096639/100000000000000000000 : ℝ)+(13204089409996413/100000000000000000000 : ℝ) ≤ ((26621676736339660423/26630000000000000000 : ℝ)+(437014703503/266300000000000 : ℝ)*((1767/12500 : ℝ)+(11473/100000 : ℝ)))^(8449/2048 : ℝ) := by
    rw [show (26621676736339660423/26630000000000000000 : ℝ)+(437014703503/266300000000000 : ℝ)*((1767/12500 : ℝ)+(11473/100000 : ℝ))=(1600172331709/1600000000000 : ℝ) by norm_num, show 1+(31237918208096639/100000000000000000000 : ℝ)+(13204089409996413/100000000000000000000 : ℝ)=(25011110501904523263/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31237918208096639/100000000000000000000 : ℝ) ≤ ((26621676736339660423/26630000000000000000 : ℝ)+2*(437014703503/266300000000000 : ℝ)*(1767/12500 : ℝ))^(8449/2048 : ℝ) := by
    rw [show (26621676736339660423/26630000000000000000 : ℝ)+2*(437014703503/266300000000000 : ℝ)*(1767/12500 : ℝ)=(10001514087884753/10000000000000000 : ℝ) by norm_num, show 1+2*(31237918208096639/100000000000000000000 : ℝ)=(50031237918208096639/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26621676736339660423/26630000000000000000 : ℝ)*(X 1 0+X 2 0)+(437014703503/266300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8449/2048 : ℝ)) (lo := (11473/100000 : ℝ)) (hi := (1767/12500 : ℝ)) (c := (26621676736339660423/26630000000000000000 : ℝ)) (alpha := (437014703503/266300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26621676736339660423/26630000000000000000 : ℝ)*(X 0 1+X 2 1)+(437014703503/266300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8449/2048 : ℝ)) (lo := (11473/100000 : ℝ)) (hi := (1767/12500 : ℝ)) (c := (26621676736339660423/26630000000000000000 : ℝ)) (alpha := (437014703503/266300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26621676736339660423/26630000000000000000 : ℝ)*(X 0 2+X 1 2)+(437014703503/266300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8449/2048 : ℝ)) (lo := (11473/100000 : ℝ)) (hi := (1767/12500 : ℝ)) (c := (26621676736339660423/26630000000000000000 : ℝ)) (alpha := (437014703503/266300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1056531111/5000000000 : ℝ)*X 0 0+(2695545769/5000000000 : ℝ)*X 0 1+(1053449283/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534427189/1000000000 : ℝ)*X 1 0+(-543963457/2500000000 : ℝ)*X 1 1+(5267246409/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672135949/5000000000 : ℝ)*X 2 0+(658405801/1250000000 : ℝ)*X 2 1+(-1087926909/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4348711443/10000000000 : ℝ)*X 0 0+(2112250609/5000000000 : ℝ)*X 0 1+(4476457643/10000000000 : ℝ)*X 0 2+(4348711443/10000000000 : ℝ)*X 1 0+(2112250609/5000000000 : ℝ)*X 1 1+(4476457643/10000000000 : ℝ)*X 1 2+(4348711443/10000000000 : ℝ)*X 2 0+(2112250609/5000000000 : ℝ)*X 2 1+(4476457643/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1056533499/5000000000 : ℝ)*X 0 0+(2633779733/5000000000 : ℝ)*X 0 1+(269538863/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062528151/2000000000 : ℝ)*X 1 0+(-513080777/2500000000 : ℝ)*X 1 1+(5390776791/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((212505639/400000000 : ℝ)*X 2 0+(5390776527/10000000000 : ℝ)*X 2 1+(-2052323171/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1087180173/2500000000 : ℝ)*X 0 0+(4475820409/10000000000 : ℝ)*X 0 1+(2112570503/5000000000 : ℝ)*X 0 2+(1087180173/2500000000 : ℝ)*X 1 0+(4475820409/10000000000 : ℝ)*X 1 1+(2112570503/5000000000 : ℝ)*X 1 2+(1087180173/2500000000 : ℝ)*X 2 0+(4475820409/10000000000 : ℝ)*X 2 1+(2112570503/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3586107355466816604971827611/1331500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (268858647/50000000000000 : ℝ)*(base19) + (508581859/100000000000000 : ℝ)*(base23) + (11015237/50000000000000 : ℝ)*(lower2) + (8096387/12500000000000 : ℝ)*(upper3) + (52736011/100000000000000 : ℝ)*(upper5) + (6021793127221519/100000000000000 : ℝ)*(major0) + (6021793127221519/100000000000000 : ℝ)*(major1) + (75272414090269/1250000000000 : ℝ)*(major2) + (2018654013580057/25000000000000 : ℝ)*(sp0) + (4037315241148091/50000000000000 : ℝ)*(sp1) + (8074630511431617/100000000000000 : ℝ)*(sp2) + (1984473705774899/50000000000000 : ℝ)*(sp3) + (233838957/1562500000000 : ℝ)*(sp4) + (773310363/10000000000000 : ℝ)*(sp7) + (992238786163357/25000000000000 : ℝ)*(f.failure) + (2018657755003369/25000000000000 : ℝ)*(f.sum) + (86005733618597/26630000000000000000000000000 : ℝ)*base65 + (26793608171743757463/2663000000000000000000000000000000 : ℝ)*base68 + (576073468557729963/33287500000000000000000000000000 : ℝ)*base70 + (22634586934587757463/2663000000000000000000000000000000 : ℝ)*base72 + (161103612103323/26630000000000000000000000000 : ℝ)*base74 + (253950765428595037/33287500000000000000000000000000 : ℝ)*base75 + (2980049241043942537/2663000000000000000000000000000000 : ℝ)*base77 + (38323269379246057463/2663000000000000000000000000000000 : ℝ)*base80 + (38789985832163/13315000000000000000000000000 : ℝ)*base82 + (22751473/1250000000000000000000 : ℝ)*base89 + (22751473/1250000000000000000000 : ℝ)*base91 + (10251473/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (201781233851896322501776611/665750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (72170549/6250000000000 : ℝ)*(base19) + (1871956137/100000000000000 : ℝ)*(base23) + (45321377/25000000000000 : ℝ)*(upper2) + (24619797/100000000000000 : ℝ)*(upper5) + (3026223114792519/50000000000000 : ℝ)*(major0) + (3026223114792519/50000000000000 : ℝ)*(major1) + (3026223114792519/50000000000000 : ℝ)*(major2) + (1475046027/12500000000000 : ℝ)*(sp0) + (12036848379/50000000000000 : ℝ)*(sp1) + (6155580627/20000000000000 : ℝ)*(sp2) + (126808157634247/1562500000000 : ℝ)*(sp4) + (4057854330267241/50000000000000 : ℝ)*(sp5) + (8115701239100753/100000000000000 : ℝ)*(sp6) + (997289640026773/25000000000000 : ℝ)*(sp7) + (997289640026773/25000000000000 : ℝ)*(f.failure) + (1014466736120003/12500000000000 : ℝ)*(f.sum) + (23505928517897/6657500000000000000000000000 : ℝ)*base65 + (2654749753199524463/1331500000000000000000000000000000 : ℝ)*base68 + (3172699926798475537/1331500000000000000000000000000000 : ℝ)*base69 + (6839977581344524463/1331500000000000000000000000000000 : ℝ)*base72 + (28877367253/6657500000000000000000000000 : ℝ)*base74 + (20470236359667524463/1331500000000000000000000000000000 : ℝ)*base76 + (140146366907024463/1331500000000000000000000000000000 : ℝ)*base78 + (18570820669287975537/1331500000000000000000000000000000 : ℝ)*base79 + (22652063596971/13315000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (16613097/1250000000000000000000 : ℝ)*base89 + (16613097/1250000000000000000000 : ℝ)*base91 + (16613097/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1257_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75861189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1767/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11473/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11493/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3529/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1257_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1257_s7_0 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2113075599/10000000000 : ℝ)*x 0 + (2695453409/5000000000 : ℝ)*x 1 + (1316855631/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2113075599/10000000000 : ℝ)^4225 ≤ (3212886193201/25000000000000 : ℝ)^3201 := by
    have hnat : (2113075599 : ℕ)^4225*25000000000000^3201 ≤ 3212886193201^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113075599 10000000000 3212886193201 25000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695453409/5000000000 : ℝ)^4225 ≤ (44240541552301/100000000000000 : ℝ)^3201 := by
    have hnat : (2695453409 : ℕ)^4225*100000000000000^3201 ≤ 44240541552301^3201*5000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695453409 5000000000 44240541552301 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316855631/2500000000 : ℝ)^4225 ≤ (42907913660637/100000000000000 : ℝ)^3201 := by
    have hnat : (1316855631 : ℕ)^4225*100000000000000^3201 ≤ 42907913660637^3201*2500000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316855631 2500000000 42907913660637 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2113075599/10000000000 : ℝ), (2695453409/5000000000 : ℝ), (1316855631/2500000000 : ℝ)] ![(3212886193201/25000000000000 : ℝ), (44240541552301/100000000000000 : ℝ), (42907913660637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2113075599/10000000000 : ℝ)|^4225 ≤ (3212886193201/25000000000000 : ℝ)^3201
        have hw : |(-2113075599/10000000000 : ℝ)|=(2113075599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695453409/5000000000 : ℝ)|^4225 ≤ (44240541552301/100000000000000 : ℝ)^3201
        have hw : |(2695453409/5000000000 : ℝ)|=(2695453409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316855631/2500000000 : ℝ)|^4225 ≤ (42907913660637/100000000000000 : ℝ)^3201
        have hw : |(1316855631/2500000000 : ℝ)|=(1316855631/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s7_1 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344225737/10000000000 : ℝ)*x 0 + (-217568177/1000000000 : ℝ)*x 1 + (2633711223/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344225737/10000000000 : ℝ)^4225 ≤ (8747120855283/20000000000000 : ℝ)^3201 := by
    have hnat : (5344225737 : ℕ)^4225*20000000000000^3201 ≤ 8747120855283^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344225737 10000000000 8747120855283 20000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (217568177/1000000000 : ℝ)^4225 ≤ (1335648288193/10000000000000 : ℝ)^3201 := by
    have hnat : (217568177 : ℕ)^4225*10000000000000^3201 ≤ 1335648288193^3201*1000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217568177 1000000000 1335648288193 10000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633711223/5000000000 : ℝ)^4225 ≤ (21453956410999/50000000000000 : ℝ)^3201 := by
    have hnat : (2633711223 : ℕ)^4225*50000000000000^3201 ≤ 21453956410999^3201*5000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633711223 5000000000 21453956410999 50000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344225737/10000000000 : ℝ), (-217568177/1000000000 : ℝ), (2633711223/5000000000 : ℝ)] ![(8747120855283/20000000000000 : ℝ), (1335648288193/10000000000000 : ℝ), (21453956410999/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344225737/10000000000 : ℝ)|^4225 ≤ (8747120855283/20000000000000 : ℝ)^3201
        have hw : |(5344225737/10000000000 : ℝ)|=(5344225737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-217568177/1000000000 : ℝ)|^4225 ≤ (1335648288193/10000000000000 : ℝ)^3201
        have hw : |(-217568177/1000000000 : ℝ)|=(217568177/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633711223/5000000000 : ℝ)|^4225 ≤ (21453956410999/50000000000000 : ℝ)^3201
        have hw : |(2633711223/5000000000 : ℝ)|=(2633711223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s7_2 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344225827/10000000000 : ℝ)*x 0 + (1053484473/2000000000 : ℝ)*x 1 + (-1087840879/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344225827/10000000000 : ℝ)^4225 ≤ (43735605248567/100000000000000 : ℝ)^3201 := by
    have hnat : (5344225827 : ℕ)^4225*100000000000000^3201 ≤ 43735605248567^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344225827 10000000000 43735605248567 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053484473/2000000000 : ℝ)^4225 ≤ (167609031059/390625000000 : ℝ)^3201 := by
    have hnat : (1053484473 : ℕ)^4225*390625000000^3201 ≤ 167609031059^3201*2000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053484473 2000000000 167609031059 390625000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1087840879/5000000000 : ℝ)^4225 ≤ (1669560348087/12500000000000 : ℝ)^3201 := by
    have hnat : (1087840879 : ℕ)^4225*12500000000000^3201 ≤ 1669560348087^3201*5000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087840879 5000000000 1669560348087 12500000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344225827/10000000000 : ℝ), (1053484473/2000000000 : ℝ), (-1087840879/5000000000 : ℝ)] ![(43735605248567/100000000000000 : ℝ), (167609031059/390625000000 : ℝ), (1669560348087/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344225827/10000000000 : ℝ)|^4225 ≤ (43735605248567/100000000000000 : ℝ)^3201
        have hw : |(5344225827/10000000000 : ℝ)|=(5344225827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053484473/2000000000 : ℝ)|^4225 ≤ (167609031059/390625000000 : ℝ)^3201
        have hw : |(1053484473/2000000000 : ℝ)|=(1053484473/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1087840879/5000000000 : ℝ)|^4225 ≤ (1669560348087/12500000000000 : ℝ)^3201
        have hw : |(-1087840879/5000000000 : ℝ)|=(1087840879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s7_3 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (869744057/2000000000 : ℝ)*x 0 + (4224867363/10000000000 : ℝ)*x 1 + (4476089449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (869744057/2000000000 : ℝ)^4225 ≤ (33317568440511/100000000000000 : ℝ)^3201 := by
    have hnat : (869744057 : ℕ)^4225*100000000000000^3201 ≤ 33317568440511^3201*2000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869744057 2000000000 33317568440511 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4224867363/10000000000 : ℝ)^4225 ≤ (32070864833811/100000000000000 : ℝ)^3201 := by
    have hnat : (4224867363 : ℕ)^4225*100000000000000^3201 ≤ 32070864833811^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224867363 10000000000 32070864833811 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4476089449/10000000000 : ℝ)^4225 ≤ (34611566698649/100000000000000 : ℝ)^3201 := by
    have hnat : (4476089449 : ℕ)^4225*100000000000000^3201 ≤ 34611566698649^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4476089449 10000000000 34611566698649 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(869744057/2000000000 : ℝ), (4224867363/10000000000 : ℝ), (4476089449/10000000000 : ℝ)] ![(33317568440511/100000000000000 : ℝ), (32070864833811/100000000000000 : ℝ), (34611566698649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(869744057/2000000000 : ℝ)|^4225 ≤ (33317568440511/100000000000000 : ℝ)^3201
        have hw : |(869744057/2000000000 : ℝ)|=(869744057/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4224867363/10000000000 : ℝ)|^4225 ≤ (32070864833811/100000000000000 : ℝ)^3201
        have hw : |(4224867363/10000000000 : ℝ)|=(4224867363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4476089449/10000000000 : ℝ)|^4225 ≤ (34611566698649/100000000000000 : ℝ)^3201
        have hw : |(4476089449/10000000000 : ℝ)|=(4476089449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s7_4 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-42261599/200000000 : ℝ)*x 0 + (2633867061/5000000000 : ℝ)*x 1 + (5390594291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42261599/200000000 : ℝ)^4225 ≤ (257031594011/2000000000000 : ℝ)^3201 := by
    have hnat : (42261599 : ℕ)^4225*2000000000000^3201 ≤ 257031594011^3201*200000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42261599 200000000 257031594011 2000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633867061/5000000000 : ℝ)^4225 ≤ (42911263924797/100000000000000 : ℝ)^3201 := by
    have hnat : (2633867061 : ℕ)^4225*100000000000000^3201 ≤ 42911263924797^3201*5000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633867061 5000000000 42911263924797 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390594291/10000000000 : ℝ)^4225 ≤ (44237156361403/100000000000000 : ℝ)^3201 := by
    have hnat : (5390594291 : ℕ)^4225*100000000000000^3201 ≤ 44237156361403^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390594291 10000000000 44237156361403 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-42261599/200000000 : ℝ), (2633867061/5000000000 : ℝ), (5390594291/10000000000 : ℝ)] ![(257031594011/2000000000000 : ℝ), (42911263924797/100000000000000 : ℝ), (44237156361403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-42261599/200000000 : ℝ)|^4225 ≤ (257031594011/2000000000000 : ℝ)^3201
        have hw : |(-42261599/200000000 : ℝ)|=(42261599/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633867061/5000000000 : ℝ)|^4225 ≤ (42911263924797/100000000000000 : ℝ)^3201
        have hw : |(2633867061/5000000000 : ℝ)|=(2633867061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390594291/10000000000 : ℝ)|^4225 ≤ (44237156361403/100000000000000 : ℝ)^3201
        have hw : |(5390594291/10000000000 : ℝ)|=(5390594291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s7_5 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062537267/2000000000 : ℝ)*x 0 + (-102625489/500000000 : ℝ)*x 1 + (5390594361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062537267/2000000000 : ℝ)^4225 ≤ (43395247712167/100000000000000 : ℝ)^3201 := by
    have hnat : (1062537267 : ℕ)^4225*100000000000000^3201 ≤ 43395247712167^3201*2000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062537267 2000000000 43395247712167 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (102625489/500000000 : ℝ)^4225 ≤ (6183797576709/50000000000000 : ℝ)^3201 := by
    have hnat : (102625489 : ℕ)^4225*50000000000000^3201 ≤ 6183797576709^3201*500000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102625489 500000000 6183797576709 50000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390594361/10000000000 : ℝ)^4225 ≤ (44237157119613/100000000000000 : ℝ)^3201 := by
    have hnat : (5390594361 : ℕ)^4225*100000000000000^3201 ≤ 44237157119613^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390594361 10000000000 44237157119613 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062537267/2000000000 : ℝ), (-102625489/500000000 : ℝ), (5390594361/10000000000 : ℝ)] ![(43395247712167/100000000000000 : ℝ), (6183797576709/50000000000000 : ℝ), (44237157119613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062537267/2000000000 : ℝ)|^4225 ≤ (43395247712167/100000000000000 : ℝ)^3201
        have hw : |(1062537267/2000000000 : ℝ)|=(1062537267/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-102625489/500000000 : ℝ)|^4225 ≤ (6183797576709/50000000000000 : ℝ)^3201
        have hw : |(-102625489/500000000 : ℝ)|=(102625489/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390594361/10000000000 : ℝ)|^4225 ≤ (44237157119613/100000000000000 : ℝ)^3201
        have hw : |(5390594361/10000000000 : ℝ)|=(5390594361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s7_6 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312686297/10000000000 : ℝ)*x 0 + (2695297209/5000000000 : ℝ)*x 1 + (-1026254877/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312686297/10000000000 : ℝ)^4225 ≤ (542440591281/1250000000000 : ℝ)^3201 := by
    have hnat : (5312686297 : ℕ)^4225*1250000000000^3201 ≤ 542440591281^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312686297 10000000000 542440591281 1250000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695297209/5000000000 : ℝ)^4225 ≤ (11059289434253/25000000000000 : ℝ)^3201 := by
    have hnat : (2695297209 : ℕ)^4225*25000000000000^3201 ≤ 11059289434253^3201*5000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695297209 5000000000 11059289434253 25000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1026254877/5000000000 : ℝ)^4225 ≤ (2473518989327/20000000000000 : ℝ)^3201 := by
    have hnat : (1026254877 : ℕ)^4225*20000000000000^3201 ≤ 2473518989327^3201*5000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026254877 5000000000 2473518989327 20000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312686297/10000000000 : ℝ), (2695297209/5000000000 : ℝ), (-1026254877/5000000000 : ℝ)] ![(542440591281/1250000000000 : ℝ), (11059289434253/25000000000000 : ℝ), (2473518989327/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312686297/10000000000 : ℝ)|^4225 ≤ (542440591281/1250000000000 : ℝ)^3201
        have hw : |(5312686297/10000000000 : ℝ)|=(5312686297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695297209/5000000000 : ℝ)|^4225 ≤ (11059289434253/25000000000000 : ℝ)^3201
        have hw : |(2695297209/5000000000 : ℝ)|=(2695297209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1026254877/5000000000 : ℝ)|^4225 ≤ (2473518989327/20000000000000 : ℝ)^3201
        have hw : |(-1026254877/5000000000 : ℝ)|=(1026254877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s7_7 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (135897811/312500000 : ℝ)*x 0 + (2237727907/5000000000 : ℝ)*x 1 + (422550303/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135897811/312500000 : ℝ)^4225 ≤ (33317666196807/100000000000000 : ℝ)^3201 := by
    have hnat : (135897811 : ℕ)^4225*100000000000000^3201 ≤ 33317666196807^3201*312500000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135897811 312500000 33317666196807 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2237727907/5000000000 : ℝ)^4225 ≤ (34605099847497/100000000000000 : ℝ)^3201 := by
    have hnat : (2237727907 : ℕ)^4225*100000000000000^3201 ≤ 34605099847497^3201*5000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237727907 5000000000 34605099847497 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (422550303/1000000000 : ℝ)^4225 ≤ (16038616971899/50000000000000 : ℝ)^3201 := by
    have hnat : (422550303 : ℕ)^4225*50000000000000^3201 ≤ 16038616971899^3201*1000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422550303 1000000000 16038616971899 50000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(135897811/312500000 : ℝ), (2237727907/5000000000 : ℝ), (422550303/1000000000 : ℝ)] ![(33317666196807/100000000000000 : ℝ), (34605099847497/100000000000000 : ℝ), (16038616971899/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(135897811/312500000 : ℝ)|^4225 ≤ (33317666196807/100000000000000 : ℝ)^3201
        have hw : |(135897811/312500000 : ℝ)|=(135897811/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2237727907/5000000000 : ℝ)|^4225 ≤ (34605099847497/100000000000000 : ℝ)^3201
        have hw : |(2237727907/5000000000 : ℝ)|=(2237727907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(422550303/1000000000 : ℝ)|^4225 ≤ (16038616971899/50000000000000 : ℝ)^3201
        have hw : |(422550303/1000000000 : ℝ)|=(422550303/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1257_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75861189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3529/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11493/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1437/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (441/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3529/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11493/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3529/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11493/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3529/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11493/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3529/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11493/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3529/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11493/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3529/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11493/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11493/100000 : ℝ) ^ (8449/2048 : ℝ) ≤ (415603361500611/3125000000000000000 : ℝ) := by
    have hpowers : (11493/100000 : ℝ)^8449 ≤ (415603361500611/3125000000000000000 : ℝ)^2048 := by
      have hnat : (11493 : ℕ)^8449*3125000000000000000^2048 ≤ 415603361500611^2048*100000^8449 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11493 100000 415603361500611 3125000000000000000 8449 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11493/100000 : ℝ)) (X := (415603361500611/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 8449 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3529/25000 : ℝ) ^ (8449/2048 : ℝ) ≤ (1940999361155299/6250000000000000000 : ℝ) := by
    have hpowers : (3529/25000 : ℝ)^8449 ≤ (1940999361155299/6250000000000000000 : ℝ)^2048 := by
      have hnat : (3529 : ℕ)^8449*6250000000000000000^2048 ≤ 1940999361155299^2048*25000^8449 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3529 25000 1940999361155299 6250000000000000000 8449 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3529/25000 : ℝ)) (X := (1940999361155299/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8449 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562915603361500611/1562500000000000000 : ℝ) ≤ (5000322336821323/5000000000000000 : ℝ) ^ (8449/2048 : ℝ) := by
    have hpowers : (1562915603361500611/1562500000000000000 : ℝ)^2048 ≤ (5000322336821323/5000000000000000 : ℝ)^8449 := by
      have hnat : (1562915603361500611 : ℕ)^2048*5000000000000000^8449 ≤ 5000322336821323^8449*1562500000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562915603361500611 1562500000000000000 5000322336821323 5000000000000000 2048 8449 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000322336821323/5000000000000000 : ℝ)) (X := (1562915603361500611/1562500000000000000 : ℝ)) (by norm_num) 8449 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (6252772206084156521/6250000000000000000 : ℝ) ≤ (10001074972069559/10000000000000000 : ℝ) ^ (8449/2048 : ℝ) := by
    have hpowers : (6252772206084156521/6250000000000000000 : ℝ)^2048 ≤ (10001074972069559/10000000000000000 : ℝ)^8449 := by
      have hnat : (6252772206084156521 : ℕ)^2048*10000000000000000^8449 ≤ 10001074972069559^8449*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252772206084156521 6250000000000000000 10001074972069559 10000000000000000 2048 8449 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001074972069559/10000000000000000 : ℝ)) (X := (6252772206084156521/6250000000000000000 : ℝ)) (by norm_num) 8449 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (3126940999361155299/3125000000000000000 : ℝ) ≤ (1250188158812059/1250000000000000 : ℝ) ^ (8449/2048 : ℝ) := by
    have hpowers : (3126940999361155299/3125000000000000000 : ℝ)^2048 ≤ (1250188158812059/1250000000000000 : ℝ)^8449 := by
      have hnat : (3126940999361155299 : ℕ)^2048*1250000000000000^8449 ≤ 1250188158812059^8449*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126940999361155299 3125000000000000000 1250188158812059 1250000000000000 2048 8449 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250188158812059/1250000000000000 : ℝ)) (X := (3126940999361155299/3125000000000000000 : ℝ)) (by norm_num) 8449 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(415603361500611/3125000000000000000 : ℝ) ≤ ((163886250870772739/163937500000000000 : ℝ)+2*(430298426913/262300000000000 : ℝ)*(11493/100000 : ℝ))^(8449/2048 : ℝ) := by
    rw [show (163886250870772739/163937500000000000 : ℝ)+2*(430298426913/262300000000000 : ℝ)*(11493/100000 : ℝ)=(5000322336821323/5000000000000000 : ℝ) by norm_num, show 1+2*(415603361500611/3125000000000000000 : ℝ)=(1562915603361500611/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1940999361155299/6250000000000000000 : ℝ)+(415603361500611/3125000000000000000 : ℝ) ≤ ((163886250870772739/163937500000000000 : ℝ)+(430298426913/262300000000000 : ℝ)*((3529/25000 : ℝ)+(11493/100000 : ℝ)))^(8449/2048 : ℝ) := by
    rw [show (163886250870772739/163937500000000000 : ℝ)+(430298426913/262300000000000 : ℝ)*((3529/25000 : ℝ)+(11493/100000 : ℝ))=(10001074972069559/10000000000000000 : ℝ) by norm_num, show 1+(1940999361155299/6250000000000000000 : ℝ)+(415603361500611/3125000000000000000 : ℝ)=(6252772206084156521/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1940999361155299/6250000000000000000 : ℝ) ≤ ((163886250870772739/163937500000000000 : ℝ)+2*(430298426913/262300000000000 : ℝ)*(3529/25000 : ℝ))^(8449/2048 : ℝ) := by
    rw [show (163886250870772739/163937500000000000 : ℝ)+2*(430298426913/262300000000000 : ℝ)*(3529/25000 : ℝ)=(1250188158812059/1250000000000000 : ℝ) by norm_num, show 1+2*(1940999361155299/6250000000000000000 : ℝ)=(3126940999361155299/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (163886250870772739/163937500000000000 : ℝ)*(X 1 0+X 2 0)+(430298426913/262300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8449/2048 : ℝ)) (lo := (11493/100000 : ℝ)) (hi := (3529/25000 : ℝ)) (c := (163886250870772739/163937500000000000 : ℝ)) (alpha := (430298426913/262300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (163886250870772739/163937500000000000 : ℝ)*(X 0 1+X 2 1)+(430298426913/262300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8449/2048 : ℝ)) (lo := (11493/100000 : ℝ)) (hi := (3529/25000 : ℝ)) (c := (163886250870772739/163937500000000000 : ℝ)) (alpha := (430298426913/262300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (163886250870772739/163937500000000000 : ℝ)*(X 0 2+X 1 2)+(430298426913/262300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8449/2048 : ℝ)) (lo := (11493/100000 : ℝ)) (hi := (3529/25000 : ℝ)) (c := (163886250870772739/163937500000000000 : ℝ)) (alpha := (430298426913/262300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2113075599/10000000000 : ℝ)*X 0 0+(2695453409/5000000000 : ℝ)*X 0 1+(1316855631/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344225737/10000000000 : ℝ)*X 1 0+(-217568177/1000000000 : ℝ)*X 1 1+(2633711223/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344225827/10000000000 : ℝ)*X 2 0+(1053484473/2000000000 : ℝ)*X 2 1+(-1087840879/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((869744057/2000000000 : ℝ)*X 0 0+(4224867363/10000000000 : ℝ)*X 0 1+(4476089449/10000000000 : ℝ)*X 0 2+(869744057/2000000000 : ℝ)*X 1 0+(4224867363/10000000000 : ℝ)*X 1 1+(4476089449/10000000000 : ℝ)*X 1 2+(869744057/2000000000 : ℝ)*X 2 0+(4224867363/10000000000 : ℝ)*X 2 1+(4476089449/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-42261599/200000000 : ℝ)*X 0 0+(2633867061/5000000000 : ℝ)*X 0 1+(5390594291/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062537267/2000000000 : ℝ)*X 1 0+(-102625489/500000000 : ℝ)*X 1 1+(5390594361/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312686297/10000000000 : ℝ)*X 2 0+(2695297209/5000000000 : ℝ)*X 2 1+(-1026254877/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((135897811/312500000 : ℝ)*X 0 0+(2237727907/5000000000 : ℝ)*X 0 1+(422550303/1000000000 : ℝ)*X 0 2+(135897811/312500000 : ℝ)*X 1 0+(2237727907/5000000000 : ℝ)*X 1 1+(422550303/1000000000 : ℝ)*X 1 2+(135897811/312500000 : ℝ)*X 2 0+(2237727907/5000000000 : ℝ)*X 2 1+(422550303/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1236474322015332347048397/128076171875000000000000000000 : ℝ) := by norm_num
    linear_combination (15924023/781250000000 : ℝ)*(base19) + (172293791/10000000000000 : ℝ)*(base23) + (97156663/25000000000000 : ℝ)*(upper3) + (60351943/25000000000000 : ℝ)*(upper4) + (21918887/20000000000000 : ℝ)*(upper5) + (6039433010467959/100000000000000 : ℝ)*(major0) + (6039433010467959/100000000000000 : ℝ)*(major1) + (150985825261699/2500000000000 : ℝ)*(major2) + (8098242497076187/100000000000000 : ℝ)*(sp0) + (2024570523663541/25000000000000 : ℝ)*(sp1) + (4049141204995599/50000000000000 : ℝ)*(sp2) + (1990278605731169/50000000000000 : ℝ)*(sp3) + (1040896323/2500000000000 : ℝ)*(sp4) + (24354737449/100000000000000 : ℝ)*(sp7) + (1990290783099893/50000000000000 : ℝ)*(f.failure) + (2024571033232277/25000000000000 : ℝ)*(f.sum) + (149747933167903/26230000000000000000000000000 : ℝ)*base66 + (91853281093142799/16393750000000000000000000000000 : ℝ)*base68 + (29262510616984363/3278750000000000000000000000000 : ℝ)*base69 + (156628024449267799/16393750000000000000000000000000 : ℝ)*base72 + (73753198121047/26230000000000000000000000000 : ℝ)*base73 + (38949743278699363/3278750000000000000000000000000 : ℝ)*base75 + (2451738389737269/4098437500000000000000000000000 : ℝ)*base77 + (2354866886223857/512304687500000000000000000000 : ℝ)*base80 + (33325609900453/13115000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (13752777/2500000000000000000000 : ℝ)*base89 + (13752777/2500000000000000000000 : ℝ)*base91 + (11247223/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11146032539595110073351969/4098437500000000000000000000000 : ℝ) := by norm_num
    linear_combination (6647731/2500000000000 : ℝ)*(base19) + (9671539/3125000000000 : ℝ)*(base23) + (86713107/100000000000000 : ℝ)*(upper3) + (34283103/100000000000000 : ℝ)*(lower4) + (28379/195312500000 : ℝ)*(upper5) + (6070043047947339/100000000000000 : ℝ)*(major0) + (6070043047947339/100000000000000 : ℝ)*(major1) + (6070043047947339/100000000000000 : ℝ)*(major2) + (7536665523/100000000000000 : ℝ)*(sp1) + (6907083013/50000000000000 : ℝ)*(sp2) + (8139329407591399/100000000000000 : ℝ)*(sp4) + (4069660802508317/50000000000000 : ℝ)*(sp5) + (65114522271489/800000000000 : ℝ)*(sp6) + (1000189149412643/25000000000000 : ℝ)*(sp7) + (1000189149412643/25000000000000 : ℝ)*(f.failure) + (8139329407591399/100000000000000 : ℝ)*(f.sum) + (66826111074303/13115000000000000000000000000 : ℝ)*base66 + (22484259569781763/2049218750000000000000000000000 : ℝ)*base68 + (15017437916469823/8196875000000000000000000000000 : ℝ)*base69 + (54365486890617677/8196875000000000000000000000000 : ℝ)*base72 + (140329743457963/13115000000000000000000000000 : ℝ)*base74 + (4319482418841651/4098437500000000000000000000000 : ℝ)*base76 + (71163103364611427/8196875000000000000000000000000 : ℝ)*base78 + (31577567457895849/4098437500000000000000000000000 : ℝ)*base79 + (67297928845277/13115000000000000000000000000 : ℝ)*base81 + (1/50000000000000 : ℝ)*base86 + (12112527/1250000000000000000000 : ℝ)*base89 + (12112527/1250000000000000000000 : ℝ)*base91 + (12112527/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1257_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75861189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3529/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11493/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1437/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (441/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1257_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1257_s8_0 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2113080587/10000000000 : ℝ)*x 0 + (5390873529/10000000000 : ℝ)*x 1 + (5267452337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2113080587/10000000000 : ℝ)^4225 ≤ (12851584814083/100000000000000 : ℝ)^3201 := by
    have hnat : (2113080587 : ℕ)^4225*100000000000000^3201 ≤ 12851584814083^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113080587 10000000000 12851584814083 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390873529/10000000000 : ℝ)^4225 ≤ (11060045243421/25000000000000 : ℝ)^3201 := by
    have hnat : (5390873529 : ℕ)^4225*25000000000000^3201 ≤ 11060045243421^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390873529 10000000000 11060045243421 25000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267452337/10000000000 : ℝ)^4225 ≤ (42908234203679/100000000000000 : ℝ)^3201 := by
    have hnat : (5267452337 : ℕ)^4225*100000000000000^3201 ≤ 42908234203679^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267452337 10000000000 42908234203679 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2113080587/10000000000 : ℝ), (5390873529/10000000000 : ℝ), (5267452337/10000000000 : ℝ)] ![(12851584814083/100000000000000 : ℝ), (11060045243421/25000000000000 : ℝ), (42908234203679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2113080587/10000000000 : ℝ)|^4225 ≤ (12851584814083/100000000000000 : ℝ)^3201
        have hw : |(-2113080587/10000000000 : ℝ)|=(2113080587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390873529/10000000000 : ℝ)|^4225 ≤ (11060045243421/25000000000000 : ℝ)^3201
        have hw : |(5390873529/10000000000 : ℝ)|=(5390873529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267452337/10000000000 : ℝ)|^4225 ≤ (42908234203679/100000000000000 : ℝ)^3201
        have hw : |(5267452337/10000000000 : ℝ)|=(5267452337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s8_1 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167006769/312500000 : ℝ)*x 0 + (-2175654293/10000000000 : ℝ)*x 1 + (210698093/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167006769/312500000 : ℝ)^4225 ≤ (4373550566789/10000000000000 : ℝ)^3201 := by
    have hnat : (167006769 : ℕ)^4225*10000000000000^3201 ≤ 4373550566789^3201*312500000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167006769 312500000 4373550566789 10000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2175654293/10000000000 : ℝ)^4225 ≤ (13356260240381/100000000000000 : ℝ)^3201 := by
    have hnat : (2175654293 : ℕ)^4225*100000000000000^3201 ≤ 13356260240381^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175654293 10000000000 13356260240381 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210698093/400000000 : ℝ)^4225 ≤ (42908234074657/100000000000000 : ℝ)^3201 := by
    have hnat : (210698093 : ℕ)^4225*100000000000000^3201 ≤ 42908234074657^3201*400000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210698093 400000000 42908234074657 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167006769/312500000 : ℝ), (-2175654293/10000000000 : ℝ), (210698093/400000000 : ℝ)] ![(4373550566789/10000000000000 : ℝ), (13356260240381/100000000000000 : ℝ), (42908234074657/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167006769/312500000 : ℝ)|^4225 ≤ (4373550566789/10000000000000 : ℝ)^3201
        have hw : |(167006769/312500000 : ℝ)|=(167006769/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2175654293/10000000000 : ℝ)|^4225 ≤ (13356260240381/100000000000000 : ℝ)^3201
        have hw : |(-2175654293/10000000000 : ℝ)|=(2175654293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210698093/400000000 : ℝ)|^4225 ≤ (42908234074657/100000000000000 : ℝ)^3201
        have hw : |(210698093/400000000 : ℝ)|=(210698093/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s8_2 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344216597/10000000000 : ℝ)*x 0 + (2633726169/5000000000 : ℝ)*x 1 + (-2175654291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344216597/10000000000 : ℝ)^4225 ≤ (43735505549071/100000000000000 : ℝ)^3201 := by
    have hnat : (5344216597 : ℕ)^4225*100000000000000^3201 ≤ 43735505549071^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344216597 10000000000 43735505549071 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633726169/5000000000 : ℝ)^4225 ≤ (42908234214431/100000000000000 : ℝ)^3201 := by
    have hnat : (2633726169 : ℕ)^4225*100000000000000^3201 ≤ 42908234214431^3201*5000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633726169 5000000000 42908234214431 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2175654291/10000000000 : ℝ)^4225 ≤ (534250408967/4000000000000 : ℝ)^3201 := by
    have hnat : (2175654291 : ℕ)^4225*4000000000000^3201 ≤ 534250408967^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175654291 10000000000 534250408967 4000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344216597/10000000000 : ℝ), (2633726169/5000000000 : ℝ), (-2175654291/10000000000 : ℝ)] ![(43735505549071/100000000000000 : ℝ), (42908234214431/100000000000000 : ℝ), (534250408967/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344216597/10000000000 : ℝ)|^4225 ≤ (43735505549071/100000000000000 : ℝ)^3201
        have hw : |(5344216597/10000000000 : ℝ)|=(5344216597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633726169/5000000000 : ℝ)|^4225 ≤ (42908234214431/100000000000000 : ℝ)^3201
        have hw : |(2633726169/5000000000 : ℝ)|=(2633726169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2175654291/10000000000 : ℝ)|^4225 ≤ (534250408967/4000000000000 : ℝ)^3201
        have hw : |(-2175654291/10000000000 : ℝ)|=(2175654291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s8_3 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4348722123/10000000000 : ℝ)*x 0 + (1056232773/2500000000 : ℝ)*x 1 + (4476025067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4348722123/10000000000 : ℝ)^4225 ≤ (6663517405409/20000000000000 : ℝ)^3201 := by
    have hnat : (4348722123 : ℕ)^4225*20000000000000^3201 ≤ 6663517405409^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4348722123 10000000000 6663517405409 20000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056232773/2500000000 : ℝ)^4225 ≤ (801787583929/2500000000000 : ℝ)^3201 := by
    have hnat : (1056232773 : ℕ)^4225*2500000000000^3201 ≤ 801787583929^3201*2500000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056232773 2500000000 801787583929 2500000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4476025067/10000000000 : ℝ)^4225 ≤ (173054548027/500000000000 : ℝ)^3201 := by
    have hnat : (4476025067 : ℕ)^4225*500000000000^3201 ≤ 173054548027^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4476025067 10000000000 173054548027 500000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4348722123/10000000000 : ℝ), (1056232773/2500000000 : ℝ), (4476025067/10000000000 : ℝ)] ![(6663517405409/20000000000000 : ℝ), (801787583929/2500000000000 : ℝ), (173054548027/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4348722123/10000000000 : ℝ)|^4225 ≤ (6663517405409/20000000000000 : ℝ)^3201
        have hw : |(4348722123/10000000000 : ℝ)|=(4348722123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056232773/2500000000 : ℝ)|^4225 ≤ (801787583929/2500000000000 : ℝ)^3201
        have hw : |(1056232773/2500000000 : ℝ)|=(1056232773/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4476025067/10000000000 : ℝ)|^4225 ≤ (173054548027/500000000000 : ℝ)^3201
        have hw : |(4476025067/10000000000 : ℝ)|=(4476025067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s8_4 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-211308497/1000000000 : ℝ)*x 0 + (526776377/1000000000 : ℝ)*x 1 + (5390561141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211308497/1000000000 : ℝ)^4225 ≤ (12851619998737/100000000000000 : ℝ)^3201 := by
    have hnat : (211308497 : ℕ)^4225*100000000000000^3201 ≤ 12851619998737^3201*1000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211308497 1000000000 12851619998737 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526776377/1000000000 : ℝ)^4225 ≤ (2681973918739/6250000000000 : ℝ)^3201 := by
    have hnat : (526776377 : ℕ)^4225*6250000000000^3201 ≤ 2681973918739^3201*1000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526776377 1000000000 2681973918739 6250000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390561141/10000000000 : ℝ)^4225 ≤ (44236797295059/100000000000000 : ℝ)^3201 := by
    have hnat : (5390561141 : ℕ)^4225*100000000000000^3201 ≤ 44236797295059^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390561141 10000000000 44236797295059 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-211308497/1000000000 : ℝ), (526776377/1000000000 : ℝ), (5390561141/10000000000 : ℝ)] ![(12851619998737/100000000000000 : ℝ), (2681973918739/6250000000000 : ℝ), (44236797295059/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-211308497/1000000000 : ℝ)|^4225 ≤ (12851619998737/100000000000000 : ℝ)^3201
        have hw : |(-211308497/1000000000 : ℝ)|=(211308497/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526776377/1000000000 : ℝ)|^4225 ≤ (2681973918739/6250000000000 : ℝ)^3201
        have hw : |(526776377/1000000000 : ℝ)|=(526776377/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390561141/10000000000 : ℝ)|^4225 ≤ (44236797295059/100000000000000 : ℝ)^3201
        have hw : |(5390561141/10000000000 : ℝ)|=(5390561141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s8_5 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (8697463/20000000 : ℝ)*x 0 + (179015677/400000000 : ℝ)*x 1 + (2112783271/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8697463/20000000 : ℝ)^4225 ≤ (8329420462691/25000000000000 : ℝ)^3201 := by
    have hnat : (8697463 : ℕ)^4225*25000000000000^3201 ≤ 8329420462691^3201*20000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8697463 20000000 8329420462691 25000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (179015677/400000000 : ℝ)^4225 ≤ (17302223907703/50000000000000 : ℝ)^3201 := by
    have hnat : (179015677 : ℕ)^4225*50000000000000^3201 ≤ 17302223907703^3201*400000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179015677 400000000 17302223907703 50000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2112783271/5000000000 : ℝ)^4225 ≤ (32077870323569/100000000000000 : ℝ)^3201 := by
    have hnat : (2112783271 : ℕ)^4225*100000000000000^3201 ≤ 32077870323569^3201*5000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112783271 5000000000 32077870323569 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8697463/20000000 : ℝ), (179015677/400000000 : ℝ), (2112783271/5000000000 : ℝ)] ![(8329420462691/25000000000000 : ℝ), (17302223907703/50000000000000 : ℝ), (32077870323569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8697463/20000000 : ℝ)|^4225 ≤ (8329420462691/25000000000000 : ℝ)^3201
        have hw : |(8697463/20000000 : ℝ)|=(8697463/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(179015677/400000000 : ℝ)|^4225 ≤ (17302223907703/50000000000000 : ℝ)^3201
        have hw : |(179015677/400000000 : ℝ)|=(179015677/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2112783271/5000000000 : ℝ)|^4225 ≤ (32077870323569/100000000000000 : ℝ)^3201
        have hw : |(2112783271/5000000000 : ℝ)|=(2112783271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1257_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75861189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (441/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1437/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (11497/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (441/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (441/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1437/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (441/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1437/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (441/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1437/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (441/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1437/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (441/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1437/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (441/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1437/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1437/12500 : ℝ) ^ (8449/2048 : ℝ) ≤ (13313635034136063/100000000000000000000 : ℝ) := by
    have hpowers : (1437/12500 : ℝ)^8449 ≤ (13313635034136063/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1437 : ℕ)^8449*100000000000000000000^2048 ≤ 13313635034136063^2048*12500^8449 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1437 12500 13313635034136063 100000000000000000000 8449 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1437/12500 : ℝ)) (X := (13313635034136063/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8449 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (441/3125 : ℝ) ^ (8449/2048 : ℝ) ≤ (7754925158030569/25000000000000000000 : ℝ) := by
    have hpowers : (441/3125 : ℝ)^8449 ≤ (7754925158030569/25000000000000000000 : ℝ)^2048 := by
      have hnat : (441 : ℕ)^8449*25000000000000000000^2048 ≤ 7754925158030569^2048*3125^8449 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        441 3125 7754925158030569 25000000000000000000 8449 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (441/3125 : ℝ)) (X := (7754925158030569/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8449 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013313635034136063/50000000000000000000 : ℝ) ≤ (10000645368085441/10000000000000000 : ℝ) ^ (8449/2048 : ℝ) := by
    have hpowers : (50013313635034136063/50000000000000000000 : ℝ)^2048 ≤ (10000645368085441/10000000000000000 : ℝ)^8449 := by
      have hnat : (50013313635034136063 : ℕ)^2048*10000000000000000^8449 ≤ 10000645368085441^8449*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013313635034136063 50000000000000000000 10000645368085441 10000000000000000 2048 8449 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000645368085441/10000000000000000 : ℝ)) (X := (50013313635034136063/50000000000000000000 : ℝ)) (by norm_num) 8449 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044333335666258339/100000000000000000000 : ℝ) ≤ (312533576247093/312500000000000 : ℝ) ^ (8449/2048 : ℝ) := by
    have hpowers : (100044333335666258339/100000000000000000000 : ℝ)^2048 ≤ (312533576247093/312500000000000 : ℝ)^8449 := by
      have hnat : (100044333335666258339 : ℕ)^2048*312500000000000^8449 ≤ 312533576247093^8449*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044333335666258339 100000000000000000000 312533576247093 312500000000000 2048 8449 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312533576247093/312500000000000 : ℝ)) (X := (100044333335666258339/100000000000000000000 : ℝ)) (by norm_num) 8449 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507754925158030569/12500000000000000000 : ℝ) ≤ (10001503511728511/10000000000000000 : ℝ) ^ (8449/2048 : ℝ) := by
    have hpowers : (12507754925158030569/12500000000000000000 : ℝ)^2048 ≤ (10001503511728511/10000000000000000 : ℝ)^8449 := by
      have hnat : (12507754925158030569 : ℕ)^2048*10000000000000000^8449 ≤ 10001503511728511^8449*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507754925158030569 12500000000000000000 10001503511728511 10000000000000000 2048 8449 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001503511728511/10000000000000000 : ℝ)) (X := (12507754925158030569/12500000000000000000 : ℝ)) (by norm_num) 8449 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13313635034136063/100000000000000000000 : ℝ) ≤ ((1089659294316282539/1090000000000000000 : ℝ)+2*(85814364307/52320000000000 : ℝ)*(1437/12500 : ℝ))^(8449/2048 : ℝ) := by
    rw [show (1089659294316282539/1090000000000000000 : ℝ)+2*(85814364307/52320000000000 : ℝ)*(1437/12500 : ℝ)=(10000645368085441/10000000000000000 : ℝ) by norm_num, show 1+2*(13313635034136063/100000000000000000000 : ℝ)=(50013313635034136063/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7754925158030569/25000000000000000000 : ℝ)+(13313635034136063/100000000000000000000 : ℝ) ≤ ((1089659294316282539/1090000000000000000 : ℝ)+(85814364307/52320000000000 : ℝ)*((441/3125 : ℝ)+(1437/12500 : ℝ)))^(8449/2048 : ℝ) := by
    rw [show (1089659294316282539/1090000000000000000 : ℝ)+(85814364307/52320000000000 : ℝ)*((441/3125 : ℝ)+(1437/12500 : ℝ))=(312533576247093/312500000000000 : ℝ) by norm_num, show 1+(7754925158030569/25000000000000000000 : ℝ)+(13313635034136063/100000000000000000000 : ℝ)=(100044333335666258339/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7754925158030569/25000000000000000000 : ℝ) ≤ ((1089659294316282539/1090000000000000000 : ℝ)+2*(85814364307/52320000000000 : ℝ)*(441/3125 : ℝ))^(8449/2048 : ℝ) := by
    rw [show (1089659294316282539/1090000000000000000 : ℝ)+2*(85814364307/52320000000000 : ℝ)*(441/3125 : ℝ)=(10001503511728511/10000000000000000 : ℝ) by norm_num, show 1+2*(7754925158030569/25000000000000000000 : ℝ)=(12507754925158030569/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1089659294316282539/1090000000000000000 : ℝ)*(X 1 0+X 2 0)+(85814364307/52320000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8449/2048 : ℝ)) (lo := (1437/12500 : ℝ)) (hi := (441/3125 : ℝ)) (c := (1089659294316282539/1090000000000000000 : ℝ)) (alpha := (85814364307/52320000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1089659294316282539/1090000000000000000 : ℝ)*(X 0 1+X 2 1)+(85814364307/52320000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8449/2048 : ℝ)) (lo := (1437/12500 : ℝ)) (hi := (441/3125 : ℝ)) (c := (1089659294316282539/1090000000000000000 : ℝ)) (alpha := (85814364307/52320000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1089659294316282539/1090000000000000000 : ℝ)*(X 0 2+X 1 2)+(85814364307/52320000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8449/2048 : ℝ)) (lo := (1437/12500 : ℝ)) (hi := (441/3125 : ℝ)) (c := (1089659294316282539/1090000000000000000 : ℝ)) (alpha := (85814364307/52320000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2113080587/10000000000 : ℝ)*X 0 0+(5390873529/10000000000 : ℝ)*X 0 1+(5267452337/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167006769/312500000 : ℝ)*X 1 0+(-2175654293/10000000000 : ℝ)*X 1 1+(210698093/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344216597/10000000000 : ℝ)*X 2 0+(2633726169/5000000000 : ℝ)*X 2 1+(-2175654291/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4348722123/10000000000 : ℝ)*X 0 0+(1056232773/2500000000 : ℝ)*X 0 1+(4476025067/10000000000 : ℝ)*X 0 2+(4348722123/10000000000 : ℝ)*X 1 0+(1056232773/2500000000 : ℝ)*X 1 1+(4476025067/10000000000 : ℝ)*X 1 2+(4348722123/10000000000 : ℝ)*X 2 0+(1056232773/2500000000 : ℝ)*X 2 1+(4476025067/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-211308497/1000000000 : ℝ)*X 0 0+(526776377/1000000000 : ℝ)*X 0 1+(5390561141/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((8697463/20000000 : ℝ)*X 0 0+(179015677/400000000 : ℝ)*X 0 1+(2112783271/5000000000 : ℝ)*X 0 2+(8697463/20000000 : ℝ)*X 1 0+(179015677/400000000 : ℝ)*X 1 1+(2112783271/5000000000 : ℝ)*X 1 2+(8697463/20000000 : ℝ)*X 2 0+(179015677/400000000 : ℝ)*X 2 1+(2112783271/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s8_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (352774679641253070219160117/54500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (308081819/25000000000000 : ℝ)*(base19) + (71036259/6250000000000 : ℝ)*(base23) + (42256697/100000000000000 : ℝ)*(lower2) + (77684657/50000000000000 : ℝ)*(upper3) + (24540967/25000000000000 : ℝ)*(upper5) + (3776566726591/62500000000 : ℝ)*(major0) + (3776566726591/62500000000 : ℝ)*(major1) + (6042506762545601/100000000000000 : ℝ)*(major2) + (4051185937364273/50000000000000 : ℝ)*(sp0) + (1620480921049809/20000000000000 : ℝ)*(sp1) + (506400293812261/6250000000000 : ℝ)*(sp2) + (1991294631722071/50000000000000 : ℝ)*(sp3) + (1358513911/4000000000000 : ℝ)*(sp4) + (22760383/125000000000 : ℝ)*(sp5) + (1991303735875271/50000000000000 : ℝ)*(f.failure) + (12660009121213/156250000000 : ℝ)*(f.sum) + (4154458614353/1744000000000000000000000000 : ℝ)*base65 + (45671397759870227/3270000000000000000000000000000 : ℝ)*base67 + (274707862194317183/327000000000000000000000000000000 : ℝ)*base70 + (30334648352189773/3270000000000000000000000000000 : ℝ)*base72 + (5349957246593/1744000000000000000000000000 : ℝ)*base73 + (1846811487990317183/327000000000000000000000000000000 : ℝ)*base76 + (972692889492397/204375000000000000000000000000 : ℝ)*base77 + (2782013316631147/204375000000000000000000000000 : ℝ)*base79 + (227603119823/163500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (13757219/2500000000000000000000 : ℝ)*base89 + (13757219/2500000000000000000000 : ℝ)*base91 + (11242781/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1257_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75861189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (441/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1437/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11497/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (441/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1257_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1257_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75861189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1767/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11473/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11497/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (441/3125 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1257_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1257_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1257_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75861189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1767/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11473/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11497/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (441/3125 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1257_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
