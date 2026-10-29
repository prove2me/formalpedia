-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1351_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:07:59.260981+00:00
-- url     : https://prove2.me/submissions/076581f4-4b18-4c69-8a8e-923e54082596

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
theorem support_rectangle_w1351_s6_0 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1018108901/5000000000 : ℝ)*x 0 + (216490101/400000000 : ℝ)*x 1 + (131121823/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1018108901/5000000000 : ℝ)^4311 ≤ (6201147471879/50000000000000 : ℝ)^3287 := by
    have hnat : (1018108901 : ℕ)^4311*50000000000000^3287 ≤ 6201147471879^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1018108901 5000000000 6201147471879 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216490101/400000000 : ℝ)^4311 ≤ (22350500267477/50000000000000 : ℝ)^3287 := by
    have hnat : (216490101 : ℕ)^4311*50000000000000^3287 ≤ 22350500267477^3287*400000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216490101 400000000 22350500267477 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131121823/250000000 : ℝ)^4311 ≤ (42896704509067/100000000000000 : ℝ)^3287 := by
    have hnat : (131121823 : ℕ)^4311*100000000000000^3287 ≤ 42896704509067^3287*250000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131121823 250000000 42896704509067 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1018108901/5000000000 : ℝ), (216490101/400000000 : ℝ), (131121823/250000000 : ℝ)] ![(6201147471879/50000000000000 : ℝ), (22350500267477/50000000000000 : ℝ), (42896704509067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1018108901/5000000000 : ℝ)|^4311 ≤ (6201147471879/50000000000000 : ℝ)^3287
        have hw : |(-1018108901/5000000000 : ℝ)|=(1018108901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216490101/400000000 : ℝ)|^4311 ≤ (22350500267477/50000000000000 : ℝ)^3287
        have hw : |(216490101/400000000 : ℝ)|=(216490101/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131121823/250000000 : ℝ)|^4311 ≤ (42896704509067/100000000000000 : ℝ)^3287
        have hw : |(131121823/250000000 : ℝ)|=(131121823/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s6_1 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674421939/5000000000 : ℝ)*x 0 + (-2121491931/10000000000 : ℝ)*x 1 + (1311218227/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674421939/5000000000 : ℝ)^4311 ≤ (44015400894703/100000000000000 : ℝ)^3287 := by
    have hnat : (2674421939 : ℕ)^4311*100000000000000^3287 ≤ 44015400894703^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674421939 5000000000 44015400894703 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2121491931/10000000000 : ℝ)^4311 ≤ (13087894706969/100000000000000 : ℝ)^3287 := by
    have hnat : (2121491931 : ℕ)^4311*100000000000000^3287 ≤ 13087894706969^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121491931 10000000000 13087894706969 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311218227/2500000000 : ℝ)^4311 ≤ (42896704380347/100000000000000 : ℝ)^3287 := by
    have hnat : (1311218227 : ℕ)^4311*100000000000000^3287 ≤ 42896704380347^3287*2500000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311218227 2500000000 42896704380347 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674421939/5000000000 : ℝ), (-2121491931/10000000000 : ℝ), (1311218227/2500000000 : ℝ)] ![(44015400894703/100000000000000 : ℝ), (13087894706969/100000000000000 : ℝ), (42896704380347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674421939/5000000000 : ℝ)|^4311 ≤ (44015400894703/100000000000000 : ℝ)^3287
        have hw : |(2674421939/5000000000 : ℝ)|=(2674421939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2121491931/10000000000 : ℝ)|^4311 ≤ (13087894706969/100000000000000 : ℝ)^3287
        have hw : |(-2121491931/10000000000 : ℝ)|=(2121491931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311218227/2500000000 : ℝ)|^4311 ≤ (42896704380347/100000000000000 : ℝ)^3287
        have hw : |(1311218227/2500000000 : ℝ)|=(1311218227/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s6_2 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674421913/5000000000 : ℝ)*x 0 + (5244872929/10000000000 : ℝ)*x 1 + (-2121491973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674421913/5000000000 : ℝ)^4311 ≤ (11003850083373/25000000000000 : ℝ)^3287 := by
    have hnat : (2674421913 : ℕ)^4311*25000000000000^3287 ≤ 11003850083373^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674421913 5000000000 11003850083373 25000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244872929/10000000000 : ℝ)^4311 ≤ (5362088075701/12500000000000 : ℝ)^3287 := by
    have hnat : (5244872929 : ℕ)^4311*12500000000000^3287 ≤ 5362088075701^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244872929 10000000000 5362088075701 12500000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2121491973/10000000000 : ℝ)^4311 ≤ (6543947523397/50000000000000 : ℝ)^3287 := by
    have hnat : (2121491973 : ℕ)^4311*50000000000000^3287 ≤ 6543947523397^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121491973 10000000000 6543947523397 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674421913/5000000000 : ℝ), (5244872929/10000000000 : ℝ), (-2121491973/10000000000 : ℝ)] ![(11003850083373/25000000000000 : ℝ), (5362088075701/12500000000000 : ℝ), (6543947523397/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674421913/5000000000 : ℝ)|^4311 ≤ (11003850083373/25000000000000 : ℝ)^3287
        have hw : |(2674421913/5000000000 : ℝ)|=(2674421913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244872929/10000000000 : ℝ)|^4311 ≤ (5362088075701/12500000000000 : ℝ)^3287
        have hw : |(5244872929/10000000000 : ℝ)|=(5244872929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2121491973/10000000000 : ℝ)|^4311 ≤ (6543947523397/50000000000000 : ℝ)^3287
        have hw : |(-2121491973/10000000000 : ℝ)|=(2121491973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s6_3 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1081067581/2500000000 : ℝ)*x 0 + (415171203/1000000000 : ℝ)*x 1 + (562936037/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081067581/2500000000 : ℝ)^4311 ≤ (4162925849639/12500000000000 : ℝ)^3287 := by
    have hnat : (1081067581 : ℕ)^4311*12500000000000^3287 ≤ 4162925849639^3287*2500000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081067581 2500000000 4162925849639 12500000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (415171203/1000000000 : ℝ)^4311 ≤ (3157137128953/10000000000000 : ℝ)^3287 := by
    have hnat : (415171203 : ℕ)^4311*10000000000000^3287 ≤ 3157137128953^3287*1000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415171203 1000000000 3157137128953 10000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (562936037/1250000000 : ℝ)^4311 ≤ (878130547499/2500000000000 : ℝ)^3287 := by
    have hnat : (562936037 : ℕ)^4311*2500000000000^3287 ≤ 878130547499^3287*1250000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562936037 1250000000 878130547499 2500000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081067581/2500000000 : ℝ), (415171203/1000000000 : ℝ), (562936037/1250000000 : ℝ)] ![(4162925849639/12500000000000 : ℝ), (3157137128953/10000000000000 : ℝ), (878130547499/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081067581/2500000000 : ℝ)|^4311 ≤ (4162925849639/12500000000000 : ℝ)^3287
        have hw : |(1081067581/2500000000 : ℝ)|=(1081067581/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(415171203/1000000000 : ℝ)|^4311 ≤ (3157137128953/10000000000000 : ℝ)^3287
        have hw : |(415171203/1000000000 : ℝ)|=(415171203/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(562936037/1250000000 : ℝ)|^4311 ≤ (878130547499/2500000000000 : ℝ)^3287
        have hw : |(562936037/1250000000 : ℝ)|=(562936037/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s6_4 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2036229941/10000000000 : ℝ)*x 0 + (655684081/1250000000 : ℝ)*x 1 + (42278513/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2036229941/10000000000 : ℝ)^4311 ≤ (12402391914219/100000000000000 : ℝ)^3287 := by
    have hnat : (2036229941 : ℕ)^4311*100000000000000^3287 ≤ 12402391914219^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2036229941 10000000000 12402391914219 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655684081/1250000000 : ℝ)^4311 ≤ (1072578443573/2500000000000 : ℝ)^3287 := by
    have hnat : (655684081 : ℕ)^4311*2500000000000^3287 ≤ 1072578443573^3287*1250000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655684081 1250000000 1072578443573 2500000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42278513/78125000 : ℝ)^4311 ≤ (4469447032469/10000000000000 : ℝ)^3287 := by
    have hnat : (42278513 : ℕ)^4311*10000000000000^3287 ≤ 4469447032469^3287*78125000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42278513 78125000 4469447032469 10000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2036229941/10000000000 : ℝ), (655684081/1250000000 : ℝ), (42278513/78125000 : ℝ)] ![(12402391914219/100000000000000 : ℝ), (1072578443573/2500000000000 : ℝ), (4469447032469/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2036229941/10000000000 : ℝ)|^4311 ≤ (12402391914219/100000000000000 : ℝ)^3287
        have hw : |(-2036229941/10000000000 : ℝ)|=(2036229941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655684081/1250000000 : ℝ)|^4311 ≤ (1072578443573/2500000000000 : ℝ)^3287
        have hw : |(655684081/1250000000 : ℝ)|=(655684081/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42278513/78125000 : ℝ)|^4311 ≤ (4469447032469/10000000000000 : ℝ)^3287
        have hw : |(42278513/78125000 : ℝ)|=(42278513/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s6_5 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (663210777/1250000000 : ℝ)*x 0 + (-244339403/1250000000 : ℝ)*x 1 + (1082329933/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663210777/1250000000 : ℝ)^4311 ≤ (1742008289463/4000000000000 : ℝ)^3287 := by
    have hnat : (663210777 : ℕ)^4311*4000000000000^3287 ≤ 1742008289463^3287*1250000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663210777 1250000000 1742008289463 4000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (244339403/1250000000 : ℝ)^4311 ≤ (734707650439/6250000000000 : ℝ)^3287 := by
    have hnat : (244339403 : ℕ)^4311*6250000000000^3287 ≤ 734707650439^3287*1250000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      244339403 1250000000 734707650439 6250000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082329933/2000000000 : ℝ)^4311 ≤ (44694470335521/100000000000000 : ℝ)^3287 := by
    have hnat : (1082329933 : ℕ)^4311*100000000000000^3287 ≤ 44694470335521^3287*2000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082329933 2000000000 44694470335521 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663210777/1250000000 : ℝ), (-244339403/1250000000 : ℝ), (1082329933/2000000000 : ℝ)] ![(1742008289463/4000000000000 : ℝ), (734707650439/6250000000000 : ℝ), (44694470335521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663210777/1250000000 : ℝ)|^4311 ≤ (1742008289463/4000000000000 : ℝ)^3287
        have hw : |(663210777/1250000000 : ℝ)|=(663210777/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-244339403/1250000000 : ℝ)|^4311 ≤ (734707650439/6250000000000 : ℝ)^3287
        have hw : |(-244339403/1250000000 : ℝ)|=(244339403/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082329933/2000000000 : ℝ)|^4311 ≤ (44694470335521/100000000000000 : ℝ)^3287
        have hw : |(1082329933/2000000000 : ℝ)|=(1082329933/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s6_6 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (663210777/1250000000 : ℝ)*x 0 + (1082329933/2000000000 : ℝ)*x 1 + (-244339403/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663210777/1250000000 : ℝ)^4311 ≤ (1742008289463/4000000000000 : ℝ)^3287 := by
    have hnat : (663210777 : ℕ)^4311*4000000000000^3287 ≤ 1742008289463^3287*1250000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663210777 1250000000 1742008289463 4000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082329933/2000000000 : ℝ)^4311 ≤ (44694470335521/100000000000000 : ℝ)^3287 := by
    have hnat : (1082329933 : ℕ)^4311*100000000000000^3287 ≤ 44694470335521^3287*2000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082329933 2000000000 44694470335521 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (244339403/1250000000 : ℝ)^4311 ≤ (734707650439/6250000000000 : ℝ)^3287 := by
    have hnat : (244339403 : ℕ)^4311*6250000000000^3287 ≤ 734707650439^3287*1250000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      244339403 1250000000 734707650439 6250000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663210777/1250000000 : ℝ), (1082329933/2000000000 : ℝ), (-244339403/1250000000 : ℝ)] ![(1742008289463/4000000000000 : ℝ), (44694470335521/100000000000000 : ℝ), (734707650439/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663210777/1250000000 : ℝ)|^4311 ≤ (1742008289463/4000000000000 : ℝ)^3287
        have hw : |(663210777/1250000000 : ℝ)|=(663210777/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082329933/2000000000 : ℝ)|^4311 ≤ (44694470335521/100000000000000 : ℝ)^3287
        have hw : |(1082329933/2000000000 : ℝ)|=(1082329933/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-244339403/1250000000 : ℝ)|^4311 ≤ (734707650439/6250000000000 : ℝ)^3287
        have hw : |(-244339403/1250000000 : ℝ)|=(244339403/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s6_7 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1081073949/2500000000 : ℝ)*x 0 + (180089111/400000000 : ℝ)*x 1 + (4152978983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081073949/2500000000 : ℝ)^4311 ≤ (16651832041981/50000000000000 : ℝ)^3287 := by
    have hnat : (1081073949 : ℕ)^4311*50000000000000^3287 ≤ 16651832041981^3287*2500000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081073949 2500000000 16651832041981 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (180089111/400000000 : ℝ)^4311 ≤ (1755616407111/5000000000000 : ℝ)^3287 := by
    have hnat : (180089111 : ℕ)^4311*5000000000000^3287 ≤ 1755616407111^3287*400000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180089111 400000000 1755616407111 5000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4152978983/10000000000 : ℝ)^4311 ≤ (15792003878563/50000000000000 : ℝ)^3287 := by
    have hnat : (4152978983 : ℕ)^4311*50000000000000^3287 ≤ 15792003878563^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4152978983 10000000000 15792003878563 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081073949/2500000000 : ℝ), (180089111/400000000 : ℝ), (4152978983/10000000000 : ℝ)] ![(16651832041981/50000000000000 : ℝ), (1755616407111/5000000000000 : ℝ), (15792003878563/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081073949/2500000000 : ℝ)|^4311 ≤ (16651832041981/50000000000000 : ℝ)^3287
        have hw : |(1081073949/2500000000 : ℝ)|=(1081073949/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(180089111/400000000 : ℝ)|^4311 ≤ (1755616407111/5000000000000 : ℝ)^3287
        have hw : |(180089111/400000000 : ℝ)|=(180089111/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4152978983/10000000000 : ℝ)|^4311 ≤ (15792003878563/50000000000000 : ℝ)^3287
        have hw : |(4152978983/10000000000 : ℝ)|=(4152978983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1351_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77541681/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (92/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11163/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1117/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14713/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (92/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11163/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (92/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11163/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (92/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11163/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (92/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11163/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (92/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11163/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (92/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11163/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11163/100000 : ℝ) ^ (2155/512 : ℝ) ≤ (4910150400485433/50000000000000000000 : ℝ) := by
    have hpowers : (11163/100000 : ℝ)^2155 ≤ (4910150400485433/50000000000000000000 : ℝ)^512 := by
      have hnat : (11163 : ℕ)^2155*50000000000000000000^512 ≤ 4910150400485433^512*100000^2155 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11163 100000 4910150400485433 50000000000000000000 2155 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11163/100000 : ℝ)) (X := (4910150400485433/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2155 512 (by norm_num) hpowers
    exact h
  have hpowhi : (92/625 : ℝ) ^ (2155/512 : ℝ) ≤ (15729212439411349/50000000000000000000 : ℝ) := by
    have hpowers : (92/625 : ℝ)^2155 ≤ (15729212439411349/50000000000000000000 : ℝ)^512 := by
      have hnat : (92 : ℕ)^2155*50000000000000000000^512 ≤ 15729212439411349^512*625^2155 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        92 625 15729212439411349 50000000000000000000 2155 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (92/625 : ℝ)) (X := (15729212439411349/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2155 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004910150400485433/25000000000000000000 : ℝ) ≤ (625029162515089/625000000000000 : ℝ) ^ (2155/512 : ℝ) := by
    have hpowers : (25004910150400485433/25000000000000000000 : ℝ)^512 ≤ (625029162515089/625000000000000 : ℝ)^2155 := by
      have hnat : (25004910150400485433 : ℕ)^512*625000000000000^2155 ≤ 625029162515089^2155*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004910150400485433 25000000000000000000 625029162515089 625000000000000 512 2155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625029162515089/625000000000000 : ℝ)) (X := (25004910150400485433/25000000000000000000 : ℝ)) (by norm_num) 2155 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25010319681419948391/25000000000000000000 : ℝ) ≤ (5000490287300609/5000000000000000 : ℝ) ^ (2155/512 : ℝ) := by
    have hpowers : (25010319681419948391/25000000000000000000 : ℝ)^512 ≤ (5000490287300609/5000000000000000 : ℝ)^2155 := by
      have hnat : (25010319681419948391 : ℕ)^512*5000000000000000^2155 ≤ 5000490287300609^2155*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010319681419948391 25000000000000000000 5000490287300609 5000000000000000 512 2155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000490287300609/5000000000000000 : ℝ)) (X := (25010319681419948391/25000000000000000000 : ℝ)) (by norm_num) 2155 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015729212439411349/25000000000000000000 : ℝ) ≤ (2500373637240253/2500000000000000 : ℝ) ^ (2155/512 : ℝ) := by
    have hpowers : (25015729212439411349/25000000000000000000 : ℝ)^512 ≤ (2500373637240253/2500000000000000 : ℝ)^2155 := by
      have hnat : (25015729212439411349 : ℕ)^512*2500000000000000^2155 ≤ 2500373637240253^2155*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015729212439411349 25000000000000000000 2500373637240253 2500000000000000 512 2155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500373637240253/2500000000000000 : ℝ)) (X := (25015729212439411349/25000000000000000000 : ℝ)) (by norm_num) 2155 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4910150400485433/50000000000000000000 : ℝ) ≤ ((8890046176375496081/8892500000000000000 : ℝ)+2*(256987179897/177850000000000 : ℝ)*(11163/100000 : ℝ))^(2155/512 : ℝ) := by
    rw [show (8890046176375496081/8892500000000000000 : ℝ)+2*(256987179897/177850000000000 : ℝ)*(11163/100000 : ℝ)=(625029162515089/625000000000000 : ℝ) by norm_num, show 1+2*(4910150400485433/50000000000000000000 : ℝ)=(25004910150400485433/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15729212439411349/50000000000000000000 : ℝ)+(4910150400485433/50000000000000000000 : ℝ) ≤ ((8890046176375496081/8892500000000000000 : ℝ)+(256987179897/177850000000000 : ℝ)*((92/625 : ℝ)+(11163/100000 : ℝ)))^(2155/512 : ℝ) := by
    rw [show (8890046176375496081/8892500000000000000 : ℝ)+(256987179897/177850000000000 : ℝ)*((92/625 : ℝ)+(11163/100000 : ℝ))=(5000490287300609/5000000000000000 : ℝ) by norm_num, show 1+(15729212439411349/50000000000000000000 : ℝ)+(4910150400485433/50000000000000000000 : ℝ)=(25010319681419948391/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15729212439411349/50000000000000000000 : ℝ) ≤ ((8890046176375496081/8892500000000000000 : ℝ)+2*(256987179897/177850000000000 : ℝ)*(92/625 : ℝ))^(2155/512 : ℝ) := by
    rw [show (8890046176375496081/8892500000000000000 : ℝ)+2*(256987179897/177850000000000 : ℝ)*(92/625 : ℝ)=(2500373637240253/2500000000000000 : ℝ) by norm_num, show 1+2*(15729212439411349/50000000000000000000 : ℝ)=(25015729212439411349/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8890046176375496081/8892500000000000000 : ℝ)*(X 1 0+X 2 0)+(256987179897/177850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2155/512 : ℝ)) (lo := (11163/100000 : ℝ)) (hi := (92/625 : ℝ)) (c := (8890046176375496081/8892500000000000000 : ℝ)) (alpha := (256987179897/177850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8890046176375496081/8892500000000000000 : ℝ)*(X 0 1+X 2 1)+(256987179897/177850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2155/512 : ℝ)) (lo := (11163/100000 : ℝ)) (hi := (92/625 : ℝ)) (c := (8890046176375496081/8892500000000000000 : ℝ)) (alpha := (256987179897/177850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8890046176375496081/8892500000000000000 : ℝ)*(X 0 2+X 1 2)+(256987179897/177850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2155/512 : ℝ)) (lo := (11163/100000 : ℝ)) (hi := (92/625 : ℝ)) (c := (8890046176375496081/8892500000000000000 : ℝ)) (alpha := (256987179897/177850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1018108901/5000000000 : ℝ)*X 0 0+(216490101/400000000 : ℝ)*X 0 1+(131121823/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674421939/5000000000 : ℝ)*X 1 0+(-2121491931/10000000000 : ℝ)*X 1 1+(1311218227/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674421913/5000000000 : ℝ)*X 2 0+(5244872929/10000000000 : ℝ)*X 2 1+(-2121491973/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1081067581/2500000000 : ℝ)*X 0 0+(415171203/1000000000 : ℝ)*X 0 1+(562936037/1250000000 : ℝ)*X 0 2+(1081067581/2500000000 : ℝ)*X 1 0+(415171203/1000000000 : ℝ)*X 1 1+(562936037/1250000000 : ℝ)*X 1 2+(1081067581/2500000000 : ℝ)*X 2 0+(415171203/1000000000 : ℝ)*X 2 1+(562936037/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2036229941/10000000000 : ℝ)*X 0 0+(655684081/1250000000 : ℝ)*X 0 1+(42278513/78125000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((663210777/1250000000 : ℝ)*X 1 0+(-244339403/1250000000 : ℝ)*X 1 1+(1082329933/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((663210777/1250000000 : ℝ)*X 2 0+(1082329933/2000000000 : ℝ)*X 2 1+(-244339403/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1081073949/2500000000 : ℝ)*X 0 0+(180089111/400000000 : ℝ)*X 0 1+(4152978983/10000000000 : ℝ)*X 0 2+(1081073949/2500000000 : ℝ)*X 1 0+(180089111/400000000 : ℝ)*X 1 1+(4152978983/10000000000 : ℝ)*X 1 2+(1081073949/2500000000 : ℝ)*X 2 0+(180089111/400000000 : ℝ)*X 2 1+(4152978983/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6870295484886043623399/2223125000000000000000000000 : ℝ) := by norm_num
    linear_combination (65605139/12500000000000 : ℝ)*(base19) + (56091811/12500000000000 : ℝ)*(base23) + (21425779/100000000000000 : ℝ)*(lower2) + (37409579/50000000000000 : ℝ)*(upper3) + (11784759/100000000000000 : ℝ)*(lower4) + (2204298492990009/50000000000000 : ℝ)*(major0) + (2204298492990009/50000000000000 : ℝ)*(major1) + (2204298492990009/50000000000000 : ℝ)*(major2) + (1194891314904869/20000000000000 : ℝ)*(sp0) + (746808262231599/12500000000000 : ℝ)*(sp1) + (746808271744927/12500000000000 : ℝ)*(sp2) + (44417517119069/1562500000000 : ℝ)*(sp3) + (10048169559/100000000000000 : ℝ)*(sp4) + (615063313/10000000000000 : ℝ)*(sp7) + (1421363623126773/50000000000000 : ℝ)*(f.failure) + (373404163918369/6250000000000 : ℝ)*(f.sum) + (6983497225617/17785000000000000000000000000 : ℝ)*base65 + (340217662185429729/444625000000000000000000000000000 : ℝ)*base67 + (3095185339978554729/444625000000000000000000000000000 : ℝ)*base69 + (3566225449870304729/444625000000000000000000000000000 : ℝ)*base71 + (6466571550531/8892500000000000000000000000 : ℝ)*base73 + (899478415386445271/444625000000000000000000000000000 : ℝ)*base76 + (351702557589695271/444625000000000000000000000000000 : ℝ)*base78 + (1714886265639445271/444625000000000000000000000000000 : ℝ)*base80 + (4792813818131/8892500000000000000000000000 : ℝ)*base81 + (4525413/2500000000000000000000 : ℝ)*base89 + (4525413/2500000000000000000000 : ℝ)*base91 + (4525413/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1182323903588512346531022117/222312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (922858153/100000000000000 : ℝ)*(base19) + (100430419/10000000000000 : ℝ)*(base23) + (108661301/100000000000000 : ℝ)*(upper3) + (144237/390625000000 : ℝ)*(lower4) + (109329007/100000000000000 : ℝ)*(upper5) + (2220241723406019/50000000000000 : ℝ)*(major0) + (2220241723406019/50000000000000 : ℝ)*(major1) + (2220241723406019/50000000000000 : ℝ)*(major2) + (18910316187/100000000000000 : ℝ)*(sp1) + (4073466671/20000000000000 : ℝ)*(sp2) + (6017678617904009/100000000000000 : ℝ)*(sp4) + (6017658784729669/100000000000000 : ℝ)*(sp5) + (188051788945827/3125000000000 : ℝ)*(sp6) + (2863288098443493/100000000000000 : ℝ)*(sp7) + (2863288098443493/100000000000000 : ℝ)*(f.failure) + (6017678617904009/100000000000000 : ℝ)*(f.sum) + (26138057359357/17785000000000000000000000000 : ℝ)*base65 + (1589459294541413461/444625000000000000000000000000000 : ℝ)*base68 + (7592406640693413461/444625000000000000000000000000000 : ℝ)*base70 + (5690052133232288461/444625000000000000000000000000000 : ℝ)*base72 + (15573075009799/8892500000000000000000000000 : ℝ)*base74 + (2820502016720961539/444625000000000000000000000000000 : ℝ)*base75 + (5469820817925788461/444625000000000000000000000000000 : ℝ)*base78 + (3005501973544711539/444625000000000000000000000000000 : ℝ)*base79 + (680723552597/277890625000000000000000000 : ℝ)*base82 + (30731733/5000000000000000000000 : ℝ)*base89 + (30731733/5000000000000000000000 : ℝ)*base91 + (30731733/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1351_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77541681/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (92/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11163/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1117/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14713/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1351_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1351_s7_0 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2036223389/10000000000 : ℝ)*x 0 + (5412195481/10000000000 : ℝ)*x 1 + (1311231591/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2036223389/10000000000 : ℝ)^4311 ≤ (193786555853/1562500000000 : ℝ)^3287 := by
    have hnat : (2036223389 : ℕ)^4311*1562500000000^3287 ≤ 193786555853^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2036223389 10000000000 193786555853 1562500000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412195481/10000000000 : ℝ)^4311 ≤ (8940076524551/20000000000000 : ℝ)^3287 := by
    have hnat : (5412195481 : ℕ)^4311*20000000000000^3287 ≤ 8940076524551^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412195481 10000000000 8940076524551 20000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311231591/2500000000 : ℝ)^4311 ≤ (42897277789241/100000000000000 : ℝ)^3287 := by
    have hnat : (1311231591 : ℕ)^4311*100000000000000^3287 ≤ 42897277789241^3287*2500000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311231591 2500000000 42897277789241 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2036223389/10000000000 : ℝ), (5412195481/10000000000 : ℝ), (1311231591/2500000000 : ℝ)] ![(193786555853/1562500000000 : ℝ), (8940076524551/20000000000000 : ℝ), (42897277789241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2036223389/10000000000 : ℝ)|^4311 ≤ (193786555853/1562500000000 : ℝ)^3287
        have hw : |(-2036223389/10000000000 : ℝ)|=(2036223389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412195481/10000000000 : ℝ)|^4311 ≤ (8940076524551/20000000000000 : ℝ)^3287
        have hw : |(5412195481/10000000000 : ℝ)|=(5412195481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311231591/2500000000 : ℝ)|^4311 ≤ (42897277789241/100000000000000 : ℝ)^3287
        have hw : |(1311231591/2500000000 : ℝ)|=(1311231591/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s7_1 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674414771/5000000000 : ℝ)*x 0 + (-1060720083/5000000000 : ℝ)*x 1 + (2622463189/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674414771/5000000000 : ℝ)^4311 ≤ (44015246173131/100000000000000 : ℝ)^3287 := by
    have hnat : (2674414771 : ℕ)^4311*100000000000000^3287 ≤ 44015246173131^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674414771 5000000000 44015246173131 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1060720083/5000000000 : ℝ)^4311 ≤ (13087475873581/100000000000000 : ℝ)^3287 := by
    have hnat : (1060720083 : ℕ)^4311*100000000000000^3287 ≤ 13087475873581^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060720083 5000000000 13087475873581 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622463189/5000000000 : ℝ)^4311 ≤ (5362159742427/12500000000000 : ℝ)^3287 := by
    have hnat : (2622463189 : ℕ)^4311*12500000000000^3287 ≤ 5362159742427^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622463189 5000000000 5362159742427 12500000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674414771/5000000000 : ℝ), (-1060720083/5000000000 : ℝ), (2622463189/5000000000 : ℝ)] ![(44015246173131/100000000000000 : ℝ), (13087475873581/100000000000000 : ℝ), (5362159742427/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674414771/5000000000 : ℝ)|^4311 ≤ (44015246173131/100000000000000 : ℝ)^3287
        have hw : |(2674414771/5000000000 : ℝ)|=(2674414771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1060720083/5000000000 : ℝ)|^4311 ≤ (13087475873581/100000000000000 : ℝ)^3287
        have hw : |(-1060720083/5000000000 : ℝ)|=(1060720083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622463189/5000000000 : ℝ)|^4311 ≤ (5362159742427/12500000000000 : ℝ)^3287
        have hw : |(2622463189/5000000000 : ℝ)|=(2622463189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s7_2 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668603693/1250000000 : ℝ)*x 0 + (2622463183/5000000000 : ℝ)*x 1 + (-106072009/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668603693/1250000000 : ℝ)^4311 ≤ (11003811548679/25000000000000 : ℝ)^3287 := by
    have hnat : (668603693 : ℕ)^4311*25000000000000^3287 ≤ 11003811548679^3287*1250000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668603693 1250000000 11003811548679 25000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622463183/5000000000 : ℝ)^4311 ≤ (8579455562139/20000000000000 : ℝ)^3287 := by
    have hnat : (2622463183 : ℕ)^4311*20000000000000^3287 ≤ 8579455562139^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622463183 5000000000 8579455562139 20000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (106072009/500000000 : ℝ)^4311 ≤ (2617495197371/20000000000000 : ℝ)^3287 := by
    have hnat : (106072009 : ℕ)^4311*20000000000000^3287 ≤ 2617495197371^3287*500000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106072009 500000000 2617495197371 20000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668603693/1250000000 : ℝ), (2622463183/5000000000 : ℝ), (-106072009/500000000 : ℝ)] ![(11003811548679/25000000000000 : ℝ), (8579455562139/20000000000000 : ℝ), (2617495197371/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668603693/1250000000 : ℝ)|^4311 ≤ (11003811548679/25000000000000 : ℝ)^3287
        have hw : |(668603693/1250000000 : ℝ)|=(668603693/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622463183/5000000000 : ℝ)|^4311 ≤ (8579455562139/20000000000000 : ℝ)^3287
        have hw : |(2622463183/5000000000 : ℝ)|=(2622463183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-106072009/500000000 : ℝ)|^4311 ≤ (2617495197371/20000000000000 : ℝ)^3287
        have hw : |(-106072009/500000000 : ℝ)|=(106072009/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s7_3 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4324274307/10000000000 : ℝ)*x 0 + (415182763/1000000000 : ℝ)*x 1 + (2251685827/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4324274307/10000000000 : ℝ)^4311 ≤ (33303447028453/100000000000000 : ℝ)^3287 := by
    have hnat : (4324274307 : ℕ)^4311*100000000000000^3287 ≤ 33303447028453^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4324274307 10000000000 33303447028453 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (415182763/1000000000 : ℝ)^4311 ≤ (15786262111517/50000000000000 : ℝ)^3287 := by
    have hnat : (415182763 : ℕ)^4311*50000000000000^3287 ≤ 15786262111517^3287*1000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415182763 1000000000 15786262111517 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2251685827/5000000000 : ℝ)^4311 ≤ (7024805746411/20000000000000 : ℝ)^3287 := by
    have hnat : (2251685827 : ℕ)^4311*20000000000000^3287 ≤ 7024805746411^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251685827 5000000000 7024805746411 20000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4324274307/10000000000 : ℝ), (415182763/1000000000 : ℝ), (2251685827/5000000000 : ℝ)] ![(33303447028453/100000000000000 : ℝ), (15786262111517/50000000000000 : ℝ), (7024805746411/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4324274307/10000000000 : ℝ)|^4311 ≤ (33303447028453/100000000000000 : ℝ)^3287
        have hw : |(4324274307/10000000000 : ℝ)|=(4324274307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(415182763/1000000000 : ℝ)|^4311 ≤ (15786262111517/50000000000000 : ℝ)^3287
        have hw : |(415182763/1000000000 : ℝ)|=(415182763/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2251685827/5000000000 : ℝ)|^4311 ≤ (7024805746411/20000000000000 : ℝ)^3287
        have hw : |(2251685827/5000000000 : ℝ)|=(2251685827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s7_4 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-509058819/2500000000 : ℝ)*x 0 + (5245525411/10000000000 : ℝ)*x 1 + (5411593477/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (509058819/2500000000 : ℝ)^4311 ≤ (1240243453207/10000000000000 : ℝ)^3287 := by
    have hnat : (509058819 : ℕ)^4311*10000000000000^3287 ≤ 1240243453207^3287*2500000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      509058819 2500000000 1240243453207 10000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245525411/10000000000 : ℝ)^4311 ≤ (4290370373833/10000000000000 : ℝ)^3287 := by
    have hnat : (5245525411 : ℕ)^4311*10000000000000^3287 ≤ 4290370373833^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245525411 10000000000 4290370373833 10000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411593477/10000000000 : ℝ)^4311 ≤ (8938772343359/20000000000000 : ℝ)^3287 := by
    have hnat : (5411593477 : ℕ)^4311*20000000000000^3287 ≤ 8938772343359^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411593477 10000000000 8938772343359 20000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-509058819/2500000000 : ℝ), (5245525411/10000000000 : ℝ), (5411593477/10000000000 : ℝ)] ![(1240243453207/10000000000000 : ℝ), (4290370373833/10000000000000 : ℝ), (8938772343359/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-509058819/2500000000 : ℝ)|^4311 ≤ (1240243453207/10000000000000 : ℝ)^3287
        have hw : |(-509058819/2500000000 : ℝ)|=(509058819/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245525411/10000000000 : ℝ)|^4311 ≤ (4290370373833/10000000000000 : ℝ)^3287
        have hw : |(5245525411/10000000000 : ℝ)|=(5245525411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411593477/10000000000 : ℝ)|^4311 ≤ (8938772343359/20000000000000 : ℝ)^3287
        have hw : |(5411593477/10000000000 : ℝ)|=(5411593477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s7_5 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652850109/5000000000 : ℝ)*x 0 + (-977386593/5000000000 : ℝ)*x 1 + (676449193/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652850109/5000000000 : ℝ)^4311 ≤ (43550357972661/100000000000000 : ℝ)^3287 := by
    have hnat : (2652850109 : ℕ)^4311*100000000000000^3287 ≤ 43550357972661^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652850109 5000000000 43550357972661 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (977386593/5000000000 : ℝ)^4311 ≤ (293894489347/2500000000000 : ℝ)^3287 := by
    have hnat : (977386593 : ℕ)^4311*2500000000000^3287 ≤ 293894489347^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      977386593 5000000000 293894489347 2500000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676449193/1250000000 : ℝ)^4311 ≤ (22346931221263/50000000000000 : ℝ)^3287 := by
    have hnat : (676449193 : ℕ)^4311*50000000000000^3287 ≤ 22346931221263^3287*1250000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676449193 1250000000 22346931221263 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652850109/5000000000 : ℝ), (-977386593/5000000000 : ℝ), (676449193/1250000000 : ℝ)] ![(43550357972661/100000000000000 : ℝ), (293894489347/2500000000000 : ℝ), (22346931221263/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652850109/5000000000 : ℝ)|^4311 ≤ (43550357972661/100000000000000 : ℝ)^3287
        have hw : |(2652850109/5000000000 : ℝ)|=(2652850109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-977386593/5000000000 : ℝ)|^4311 ≤ (293894489347/2500000000000 : ℝ)^3287
        have hw : |(-977386593/5000000000 : ℝ)|=(977386593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676449193/1250000000 : ℝ)|^4311 ≤ (22346931221263/50000000000000 : ℝ)^3287
        have hw : |(676449193/1250000000 : ℝ)|=(676449193/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s7_6 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326425049/2500000000 : ℝ)*x 0 + (270579681/500000000 : ℝ)*x 1 + (-244346639/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326425049/2500000000 : ℝ)^4311 ≤ (2721897358489/6250000000000 : ℝ)^3287 := by
    have hnat : (1326425049 : ℕ)^4311*6250000000000^3287 ≤ 2721897358489^3287*2500000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326425049 2500000000 2721897358489 6250000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270579681/500000000 : ℝ)^4311 ≤ (44693863265743/100000000000000 : ℝ)^3287 := by
    have hnat : (270579681 : ℕ)^4311*100000000000000^3287 ≤ 44693863265743^3287*500000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270579681 500000000 44693863265743 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (244346639/1250000000 : ℝ)^4311 ≤ (11755778990213/100000000000000 : ℝ)^3287 := by
    have hnat : (244346639 : ℕ)^4311*100000000000000^3287 ≤ 11755778990213^3287*1250000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      244346639 1250000000 11755778990213 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326425049/2500000000 : ℝ), (270579681/500000000 : ℝ), (-244346639/1250000000 : ℝ)] ![(2721897358489/6250000000000 : ℝ), (44693863265743/100000000000000 : ℝ), (11755778990213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326425049/2500000000 : ℝ)|^4311 ≤ (2721897358489/6250000000000 : ℝ)^3287
        have hw : |(1326425049/2500000000 : ℝ)|=(1326425049/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270579681/500000000 : ℝ)|^4311 ≤ (44693863265743/100000000000000 : ℝ)^3287
        have hw : |(270579681/500000000 : ℝ)|=(270579681/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-244346639/1250000000 : ℝ)|^4311 ≤ (11755778990213/100000000000000 : ℝ)^3287
        have hw : |(-244346639/1250000000 : ℝ)|=(244346639/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s7_7 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4324299637/10000000000 : ℝ)*x 0 + (1125528207/2500000000 : ℝ)*x 1 + (519136621/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4324299637/10000000000 : ℝ)^4311 ≤ (16651851440533/50000000000000 : ℝ)^3287 := by
    have hnat : (4324299637 : ℕ)^4311*50000000000000^3287 ≤ 16651851440533^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4324299637 10000000000 16651851440533 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1125528207/2500000000 : ℝ)^4311 ≤ (17555576207739/50000000000000 : ℝ)^3287 := by
    have hnat : (1125528207 : ℕ)^4311*50000000000000^3287 ≤ 17555576207739^3287*2500000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125528207 2500000000 17555576207739 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (519136621/1250000000 : ℝ)^4311 ≤ (3948143086433/12500000000000 : ℝ)^3287 := by
    have hnat : (519136621 : ℕ)^4311*12500000000000^3287 ≤ 3948143086433^3287*1250000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519136621 1250000000 3948143086433 12500000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4324299637/10000000000 : ℝ), (1125528207/2500000000 : ℝ), (519136621/1250000000 : ℝ)] ![(16651851440533/50000000000000 : ℝ), (17555576207739/50000000000000 : ℝ), (3948143086433/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4324299637/10000000000 : ℝ)|^4311 ≤ (16651851440533/50000000000000 : ℝ)^3287
        have hw : |(4324299637/10000000000 : ℝ)|=(4324299637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1125528207/2500000000 : ℝ)|^4311 ≤ (17555576207739/50000000000000 : ℝ)^3287
        have hw : |(1125528207/2500000000 : ℝ)|=(1125528207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(519136621/1250000000 : ℝ)|^4311 ≤ (3948143086433/12500000000000 : ℝ)^3287
        have hw : |(519136621/1250000000 : ℝ)|=(519136621/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1351_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77541681/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14713/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1117/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (11171/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1839/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14713/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1117/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14713/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1117/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14713/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1117/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14713/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1117/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14713/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1117/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14713/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1117/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1117/10000 : ℝ) ^ (2155/512 : ℝ) ≤ (9846245949347573/100000000000000000000 : ℝ) := by
    have hpowers : (1117/10000 : ℝ)^2155 ≤ (9846245949347573/100000000000000000000 : ℝ)^512 := by
      have hnat : (1117 : ℕ)^2155*100000000000000000000^512 ≤ 9846245949347573^512*10000^2155 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1117 10000 9846245949347573 100000000000000000000 2155 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1117/10000 : ℝ)) (X := (9846245949347573/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2155 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14713/100000 : ℝ) ^ (2155/512 : ℝ) ≤ (3924438391931361/12500000000000000000 : ℝ) := by
    have hpowers : (14713/100000 : ℝ)^2155 ≤ (3924438391931361/12500000000000000000 : ℝ)^512 := by
      have hnat : (14713 : ℕ)^2155*12500000000000000000^512 ≤ 3924438391931361^512*100000^2155 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14713 100000 3924438391931361 12500000000000000000 2155 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14713/100000 : ℝ)) (X := (3924438391931361/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2155 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009846245949347573/50000000000000000000 : ℝ) ≤ (1250058479112829/1250000000000000 : ℝ) ^ (2155/512 : ℝ) := by
    have hpowers : (50009846245949347573/50000000000000000000 : ℝ)^512 ≤ (1250058479112829/1250000000000000 : ℝ)^2155 := by
      have hnat : (50009846245949347573 : ℕ)^512*1250000000000000^2155 ≤ 1250058479112829^2155*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009846245949347573 50000000000000000000 1250058479112829 1250000000000000 512 2155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250058479112829/1250000000000000 : ℝ)) (X := (50009846245949347573/50000000000000000000 : ℝ)) (by norm_num) 2155 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100041241753084798461/100000000000000000000 : ℝ) ≤ (10000979696456627/10000000000000000 : ℝ) ^ (2155/512 : ℝ) := by
    have hpowers : (100041241753084798461/100000000000000000000 : ℝ)^512 ≤ (10000979696456627/10000000000000000 : ℝ)^2155 := by
      have hnat : (100041241753084798461 : ℕ)^512*10000000000000000^2155 ≤ 10000979696456627^2155*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100041241753084798461 100000000000000000000 10000979696456627 10000000000000000 512 2155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000979696456627/10000000000000000 : ℝ)) (X := (100041241753084798461/100000000000000000000 : ℝ)) (by norm_num) 2155 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253924438391931361/6250000000000000000 : ℝ) ≤ (5000745780005311/5000000000000000 : ℝ) ^ (2155/512 : ℝ) := by
    have hpowers : (6253924438391931361/6250000000000000000 : ℝ)^512 ≤ (5000745780005311/5000000000000000 : ℝ)^2155 := by
      have hnat : (6253924438391931361 : ℕ)^512*5000000000000000^2155 ≤ 5000745780005311^2155*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253924438391931361 6250000000000000000 5000745780005311 5000000000000000 512 2155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000745780005311/5000000000000000 : ℝ)) (X := (6253924438391931361/6250000000000000000 : ℝ)) (by norm_num) 2155 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9846245949347573/100000000000000000000 : ℝ) ≤ ((2951685208348148073/2952500000000000000 : ℝ)+2*(34124236933/23620000000000 : ℝ)*(1117/10000 : ℝ))^(2155/512 : ℝ) := by
    rw [show (2951685208348148073/2952500000000000000 : ℝ)+2*(34124236933/23620000000000 : ℝ)*(1117/10000 : ℝ)=(1250058479112829/1250000000000000 : ℝ) by norm_num, show 1+2*(9846245949347573/100000000000000000000 : ℝ)=(50009846245949347573/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3924438391931361/12500000000000000000 : ℝ)+(9846245949347573/100000000000000000000 : ℝ) ≤ ((2951685208348148073/2952500000000000000 : ℝ)+(34124236933/23620000000000 : ℝ)*((14713/100000 : ℝ)+(1117/10000 : ℝ)))^(2155/512 : ℝ) := by
    rw [show (2951685208348148073/2952500000000000000 : ℝ)+(34124236933/23620000000000 : ℝ)*((14713/100000 : ℝ)+(1117/10000 : ℝ))=(10000979696456627/10000000000000000 : ℝ) by norm_num, show 1+(3924438391931361/12500000000000000000 : ℝ)+(9846245949347573/100000000000000000000 : ℝ)=(100041241753084798461/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3924438391931361/12500000000000000000 : ℝ) ≤ ((2951685208348148073/2952500000000000000 : ℝ)+2*(34124236933/23620000000000 : ℝ)*(14713/100000 : ℝ))^(2155/512 : ℝ) := by
    rw [show (2951685208348148073/2952500000000000000 : ℝ)+2*(34124236933/23620000000000 : ℝ)*(14713/100000 : ℝ)=(5000745780005311/5000000000000000 : ℝ) by norm_num, show 1+2*(3924438391931361/12500000000000000000 : ℝ)=(6253924438391931361/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2951685208348148073/2952500000000000000 : ℝ)*(X 1 0+X 2 0)+(34124236933/23620000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2155/512 : ℝ)) (lo := (1117/10000 : ℝ)) (hi := (14713/100000 : ℝ)) (c := (2951685208348148073/2952500000000000000 : ℝ)) (alpha := (34124236933/23620000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2951685208348148073/2952500000000000000 : ℝ)*(X 0 1+X 2 1)+(34124236933/23620000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2155/512 : ℝ)) (lo := (1117/10000 : ℝ)) (hi := (14713/100000 : ℝ)) (c := (2951685208348148073/2952500000000000000 : ℝ)) (alpha := (34124236933/23620000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2951685208348148073/2952500000000000000 : ℝ)*(X 0 2+X 1 2)+(34124236933/23620000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2155/512 : ℝ)) (lo := (1117/10000 : ℝ)) (hi := (14713/100000 : ℝ)) (c := (2951685208348148073/2952500000000000000 : ℝ)) (alpha := (34124236933/23620000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2036223389/10000000000 : ℝ)*X 0 0+(5412195481/10000000000 : ℝ)*X 0 1+(1311231591/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674414771/5000000000 : ℝ)*X 1 0+(-1060720083/5000000000 : ℝ)*X 1 1+(2622463189/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668603693/1250000000 : ℝ)*X 2 0+(2622463183/5000000000 : ℝ)*X 2 1+(-106072009/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4324274307/10000000000 : ℝ)*X 0 0+(415182763/1000000000 : ℝ)*X 0 1+(2251685827/5000000000 : ℝ)*X 0 2+(4324274307/10000000000 : ℝ)*X 1 0+(415182763/1000000000 : ℝ)*X 1 1+(2251685827/5000000000 : ℝ)*X 1 2+(4324274307/10000000000 : ℝ)*X 2 0+(415182763/1000000000 : ℝ)*X 2 1+(2251685827/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-509058819/2500000000 : ℝ)*X 0 0+(5245525411/10000000000 : ℝ)*X 0 1+(5411593477/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652850109/5000000000 : ℝ)*X 1 0+(-977386593/5000000000 : ℝ)*X 1 1+(676449193/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326425049/2500000000 : ℝ)*X 2 0+(270579681/500000000 : ℝ)*X 2 1+(-244346639/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4324299637/10000000000 : ℝ)*X 0 0+(1125528207/2500000000 : ℝ)*X 0 1+(519136621/1250000000 : ℝ)*X 0 2+(4324299637/10000000000 : ℝ)*X 1 0+(1125528207/2500000000 : ℝ)*X 1 1+(519136621/1250000000 : ℝ)*X 1 2+(4324299637/10000000000 : ℝ)*X 2 0+(1125528207/2500000000 : ℝ)*X 2 1+(519136621/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (38910626434456034239928811/9226562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (808935223/100000000000000 : ℝ)*(base19) + (770933987/100000000000000 : ℝ)*(base23) + (21521897/100000000000000 : ℝ)*(lower2) + (28830201/25000000000000 : ℝ)*(upper3) + (13854901/20000000000000 : ℝ)*(upper5) + (551439680768613/12500000000000 : ℝ)*(major0) + (551439680768613/12500000000000 : ℝ)*(major1) + (551439680768613/12500000000000 : ℝ)*(major2) + (2989203844120979/50000000000000 : ℝ)*(sp0) + (1494605885370179/25000000000000 : ℝ)*(sp1) + (186825736858811/3125000000000 : ℝ)*(sp2) + (711150429455721/25000000000000 : ℝ)*(sp3) + (16662173981/100000000000000 : ℝ)*(sp4) + (8683484321/100000000000000 : ℝ)*(sp7) + (711152600326801/25000000000000 : ℝ)*(f.failure) + (5978424350415939/100000000000000 : ℝ)*(f.sum) + (284345376779/47240000000000000000000000 : ℝ)*base66 + (91355596636051499/36906250000000000000000000000000 : ℝ)*base67 + (7771262510698501/36906250000000000000000000000000 : ℝ)*base70 + (228481977559801499/36906250000000000000000000000000 : ℝ)*base71 + (366686202489/59050000000000000000000000 : ℝ)*base74 + (302387360723792251/36906250000000000000000000000000 : ℝ)*base76 + (174101650586948501/36906250000000000000000000000000 : ℝ)*base78 + (89677806057167251/36906250000000000000000000000000 : ℝ)*base80 + (711847089599/147625000000000000000000000 : ℝ)*base82 + (1107519/1250000000000000000000 : ℝ)*base90 + (1107519/1250000000000000000000 : ℝ)*base92 + (1107519/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (40046426152976886981739809/4613281250000000000000000000000 : ℝ) := by norm_num
    linear_combination (369081761/50000000000000 : ℝ)*(base19) + (1069355111/100000000000000 : ℝ)*(base23) + (62929081/25000000000000 : ℝ)*(lower1) + (31831969/25000000000000 : ℝ)*(upper3) + (15132291/10000000000000 : ℝ)*(lower4) + (15795631/12500000000000 : ℝ)*(upper5) + (138855741819861/3125000000000 : ℝ)*(major0) + (138855741819861/3125000000000 : ℝ)*(major1) + (138855741819861/3125000000000 : ℝ)*(major2) + (218209699/2500000000000 : ℝ)*(sp2) + (6021608938717257/100000000000000 : ℝ)*(sp4) + (1204321640110747/20000000000000 : ℝ)*(sp5) + (6021599140974187/100000000000000 : ℝ)*(sp6) + (1432579124198879/50000000000000 : ℝ)*(sp7) + (1432579124198879/50000000000000 : ℝ)*(f.failure) + (6021608938717257/100000000000000 : ℝ)*(f.sum) + (442039796209/590500000000000000000000000 : ℝ)*base66 + (389472930421446331/18453125000000000000000000000000 : ℝ)*base67 + (274391916732334919/18453125000000000000000000000000 : ℝ)*base70 + (1043099780489434103/9226562500000000000000000000000 : ℝ)*base71 + (3601471073209/590500000000000000000000000 : ℝ)*base74 + (772191556572659647/9226562500000000000000000000000 : ℝ)*base76 + (8635208142175017/576660156250000000000000000000 : ℝ)*base78 + (282250268201878397/9226562500000000000000000000000 : ℝ)*base80 + (546478621373/147625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (55975599/2500000000000000000000 : ℝ)*base89 + (55975599/2500000000000000000000 : ℝ)*base91 + (55975599/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1351_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77541681/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14713/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1117/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11171/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1839/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1351_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1351_box_0 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-74787249/400000000 : ℝ)*x 0 + (336847707/625000000 : ℝ)*x 1 + (2694781827/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (74787249/400000000 : ℝ)^4311 ≤ (1386152884089/12500000000000 : ℝ)^3287 := by
    have hnat : (74787249 : ℕ)^4311*12500000000000^3287 ≤ 1386152884089^3287*400000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74787249 400000000 1386152884089 12500000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (336847707/625000000 : ℝ)^4311 ≤ (44455386610839/100000000000000 : ℝ)^3287 := by
    have hnat : (336847707 : ℕ)^4311*100000000000000^3287 ≤ 44455386610839^3287*625000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336847707 625000000 44455386610839 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2694781827/5000000000 : ℝ)^4311 ≤ (44455390310613/100000000000000 : ℝ)^3287 := by
    have hnat : (2694781827 : ℕ)^4311*100000000000000^3287 ≤ 44455390310613^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2694781827 5000000000 44455390310613 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-74787249/400000000 : ℝ), (336847707/625000000 : ℝ), (2694781827/5000000000 : ℝ)] ![(1386152884089/12500000000000 : ℝ), (44455386610839/100000000000000 : ℝ), (44455390310613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-74787249/400000000 : ℝ)|^4311 ≤ (1386152884089/12500000000000 : ℝ)^3287
        have hw : |(-74787249/400000000 : ℝ)|=(74787249/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(336847707/625000000 : ℝ)|^4311 ≤ (44455386610839/100000000000000 : ℝ)^3287
        have hw : |(336847707/625000000 : ℝ)|=(336847707/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2694781827/5000000000 : ℝ)|^4311 ≤ (44455390310613/100000000000000 : ℝ)^3287
        have hw : |(2694781827/5000000000 : ℝ)|=(2694781827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_box_1 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (264264243/500000000 : ℝ)*x 0 + (-503147433/2500000000 : ℝ)*x 1 + (67369557/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264264243/500000000 : ℝ)^4311 ≤ (4333071175207/10000000000000 : ℝ)^3287 := by
    have hnat : (264264243 : ℕ)^4311*10000000000000^3287 ≤ 4333071175207^3287*500000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264264243 500000000 4333071175207 10000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (503147433/2500000000 : ℝ)^4311 ≤ (3053472033259/25000000000000 : ℝ)^3287 := by
    have hnat : (503147433 : ℕ)^4311*25000000000000^3287 ≤ 3053472033259^3287*2500000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503147433 2500000000 3053472033259 25000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67369557/125000000 : ℝ)^4311 ≤ (4445540011177/10000000000000 : ℝ)^3287 := by
    have hnat : (67369557 : ℕ)^4311*10000000000000^3287 ≤ 4445540011177^3287*125000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67369557 125000000 4445540011177 10000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264264243/500000000 : ℝ), (-503147433/2500000000 : ℝ), (67369557/125000000 : ℝ)] ![(4333071175207/10000000000000 : ℝ), (3053472033259/25000000000000 : ℝ), (4445540011177/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264264243/500000000 : ℝ)|^4311 ≤ (4333071175207/10000000000000 : ℝ)^3287
        have hw : |(264264243/500000000 : ℝ)|=(264264243/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-503147433/2500000000 : ℝ)|^4311 ≤ (3053472033259/25000000000000 : ℝ)^3287
        have hw : |(-503147433/2500000000 : ℝ)|=(503147433/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(67369557/125000000 : ℝ)|^4311 ≤ (4445540011177/10000000000000 : ℝ)^3287
        have hw : |(67369557/125000000 : ℝ)|=(67369557/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_box_2 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5285285459/10000000000 : ℝ)*x 0 + (5389563733/10000000000 : ℝ)*x 1 + (-402518009/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285285459/10000000000 : ℝ)^4311 ≤ (43330718192763/100000000000000 : ℝ)^3287 := by
    have hnat : (5285285459 : ℕ)^4311*100000000000000^3287 ≤ 43330718192763^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285285459 10000000000 43330718192763 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5389563733/10000000000 : ℝ)^4311 ≤ (44455391165239/100000000000000 : ℝ)^3287 := by
    have hnat : (5389563733 : ℕ)^4311*100000000000000^3287 ≤ 44455391165239^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389563733 10000000000 44455391165239 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (402518009/2000000000 : ℝ)^4311 ≤ (12213890624309/100000000000000 : ℝ)^3287 := by
    have hnat : (402518009 : ℕ)^4311*100000000000000^3287 ≤ 12213890624309^3287*2000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402518009 2000000000 12213890624309 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285285459/10000000000 : ℝ), (5389563733/10000000000 : ℝ), (-402518009/2000000000 : ℝ)] ![(43330718192763/100000000000000 : ℝ), (44455391165239/100000000000000 : ℝ), (12213890624309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285285459/10000000000 : ℝ)|^4311 ≤ (43330718192763/100000000000000 : ℝ)^3287
        have hw : |(5285285459/10000000000 : ℝ)|=(5285285459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5389563733/10000000000 : ℝ)|^4311 ≤ (44455391165239/100000000000000 : ℝ)^3287
        have hw : |(5389563733/10000000000 : ℝ)|=(5389563733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-402518009/2000000000 : ℝ)|^4311 ≤ (12213890624309/100000000000000 : ℝ)^3287
        have hw : |(-402518009/2000000000 : ℝ)|=(402518009/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_box_3 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (894450467/2000000000 : ℝ)*x 0 + (1063538669/2500000000 : ℝ)*x 1 + (4254154147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (894450467/2000000000 : ℝ)^4311 ≤ (17403021922911/50000000000000 : ℝ)^3287 := by
    have hnat : (894450467 : ℕ)^4311*50000000000000^3287 ≤ 17403021922911^3287*2000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      894450467 2000000000 17403021922911 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1063538669/2500000000 : ℝ)^4311 ≤ (16298490364967/50000000000000 : ℝ)^3287 := by
    have hnat : (1063538669 : ℕ)^4311*50000000000000^3287 ≤ 16298490364967^3287*2500000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063538669 2500000000 16298490364967 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4254154147/10000000000 : ℝ)^4311 ≤ (32596975413773/100000000000000 : ℝ)^3287 := by
    have hnat : (4254154147 : ℕ)^4311*100000000000000^3287 ≤ 32596975413773^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4254154147 10000000000 32596975413773 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(894450467/2000000000 : ℝ), (1063538669/2500000000 : ℝ), (4254154147/10000000000 : ℝ)] ![(17403021922911/50000000000000 : ℝ), (16298490364967/50000000000000 : ℝ), (32596975413773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(894450467/2000000000 : ℝ)|^4311 ≤ (17403021922911/50000000000000 : ℝ)^3287
        have hw : |(894450467/2000000000 : ℝ)|=(894450467/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1063538669/2500000000 : ℝ)|^4311 ≤ (16298490364967/50000000000000 : ℝ)^3287
        have hw : |(1063538669/2500000000 : ℝ)|=(1063538669/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4254154147/10000000000 : ℝ)|^4311 ≤ (32596975413773/100000000000000 : ℝ)^3287
        have hw : |(4254154147/10000000000 : ℝ)|=(4254154147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_box_4 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-551378763/2500000000 : ℝ)*x 0 + (658140407/1250000000 : ℝ)*x 1 + (5265123331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (551378763/2500000000 : ℝ)^4311 ≤ (6885944706827/50000000000000 : ℝ)^3287 := by
    have hnat : (551378763 : ℕ)^4311*50000000000000^3287 ≤ 6885944706827^3287*2500000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551378763 2500000000 6885944706827 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658140407/1250000000 : ℝ)^4311 ≤ (43114054881847/100000000000000 : ℝ)^3287 := by
    have hnat : (658140407 : ℕ)^4311*100000000000000^3287 ≤ 43114054881847^3287*1250000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658140407 1250000000 43114054881847 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265123331/10000000000 : ℝ)^4311 ≤ (21557027843659/50000000000000 : ℝ)^3287 := by
    have hnat : (5265123331 : ℕ)^4311*50000000000000^3287 ≤ 21557027843659^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265123331 10000000000 21557027843659 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-551378763/2500000000 : ℝ), (658140407/1250000000 : ℝ), (5265123331/10000000000 : ℝ)] ![(6885944706827/50000000000000 : ℝ), (43114054881847/100000000000000 : ℝ), (21557027843659/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-551378763/2500000000 : ℝ)|^4311 ≤ (6885944706827/50000000000000 : ℝ)^3287
        have hw : |(-551378763/2500000000 : ℝ)|=(551378763/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658140407/1250000000 : ℝ)|^4311 ≤ (43114054881847/100000000000000 : ℝ)^3287
        have hw : |(658140407/1250000000 : ℝ)|=(658140407/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265123331/10000000000 : ℝ)|^4311 ≤ (21557027843659/50000000000000 : ℝ)^3287
        have hw : |(5265123331/10000000000 : ℝ)|=(5265123331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_box_5 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1343164191/2500000000 : ℝ)*x 0 + (-2062586927/10000000000 : ℝ)*x 1 + (1053024671/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1343164191/2500000000 : ℝ)^4311 ≤ (4427258009809/10000000000000 : ℝ)^3287 := by
    have hnat : (1343164191 : ℕ)^4311*10000000000000^3287 ≤ 4427258009809^3287*2500000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343164191 2500000000 4427258009809 10000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2062586927/10000000000 : ℝ)^4311 ≤ (2522672787597/20000000000000 : ℝ)^3287 := by
    have hnat : (2062586927 : ℕ)^4311*20000000000000^3287 ≤ 2522672787597^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2062586927 10000000000 2522672787597 20000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053024671/2000000000 : ℝ)^4311 ≤ (43114055945069/100000000000000 : ℝ)^3287 := by
    have hnat : (1053024671 : ℕ)^4311*100000000000000^3287 ≤ 43114055945069^3287*2000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053024671 2000000000 43114055945069 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1343164191/2500000000 : ℝ), (-2062586927/10000000000 : ℝ), (1053024671/2000000000 : ℝ)] ![(4427258009809/10000000000000 : ℝ), (2522672787597/20000000000000 : ℝ), (43114055945069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1343164191/2500000000 : ℝ)|^4311 ≤ (4427258009809/10000000000000 : ℝ)^3287
        have hw : |(1343164191/2500000000 : ℝ)|=(1343164191/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2062586927/10000000000 : ℝ)|^4311 ≤ (2522672787597/20000000000000 : ℝ)^3287
        have hw : |(-2062586927/10000000000 : ℝ)|=(2062586927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053024671/2000000000 : ℝ)|^4311 ≤ (43114055945069/100000000000000 : ℝ)^3287
        have hw : |(1053024671/2000000000 : ℝ)|=(1053024671/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_box_6 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2686328423/5000000000 : ℝ)*x 0 + (329070207/625000000 : ℝ)*x 1 + (-3300139/16000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686328423/5000000000 : ℝ)^4311 ≤ (22136290492151/50000000000000 : ℝ)^3287 := by
    have hnat : (2686328423 : ℕ)^4311*50000000000000^3287 ≤ 22136290492151^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686328423 5000000000 22136290492151 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329070207/625000000 : ℝ)^4311 ≤ (8622811096653/20000000000000 : ℝ)^3287 := by
    have hnat : (329070207 : ℕ)^4311*20000000000000^3287 ≤ 8622811096653^3287*625000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329070207 625000000 8622811096653 20000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3300139/16000000 : ℝ)^4311 ≤ (12613363520923/100000000000000 : ℝ)^3287 := by
    have hnat : (3300139 : ℕ)^4311*100000000000000^3287 ≤ 12613363520923^3287*16000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3300139 16000000 12613363520923 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686328423/5000000000 : ℝ), (329070207/625000000 : ℝ), (-3300139/16000000 : ℝ)] ![(22136290492151/50000000000000 : ℝ), (8622811096653/20000000000000 : ℝ), (12613363520923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686328423/5000000000 : ℝ)|^4311 ≤ (22136290492151/50000000000000 : ℝ)^3287
        have hw : |(2686328423/5000000000 : ℝ)|=(2686328423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329070207/625000000 : ℝ)|^4311 ≤ (8622811096653/20000000000000 : ℝ)^3287
        have hw : |(329070207/625000000 : ℝ)|=(329070207/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3300139/16000000 : ℝ)|^4311 ≤ (12613363520923/100000000000000 : ℝ)^3287
        have hw : |(-3300139/16000000 : ℝ)|=(3300139/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_box_7 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2087678471/5000000000 : ℝ)*x 0 + (2201274453/5000000000 : ℝ)*x 1 + (4402548719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2087678471/5000000000 : ℝ)^4311 ≤ (7951850272769/25000000000000 : ℝ)^3287 := by
    have hnat : (2087678471 : ℕ)^4311*25000000000000^3287 ≤ 7951850272769^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087678471 5000000000 7951850272769 25000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2201274453/5000000000 : ℝ)^4311 ≤ (34096300394481/100000000000000 : ℝ)^3287 := by
    have hnat : (2201274453 : ℕ)^4311*100000000000000^3287 ≤ 34096300394481^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2201274453 5000000000 34096300394481 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4402548719/10000000000 : ℝ)^4311 ≤ (34096298495053/100000000000000 : ℝ)^3287 := by
    have hnat : (4402548719 : ℕ)^4311*100000000000000^3287 ≤ 34096298495053^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4402548719 10000000000 34096298495053 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2087678471/5000000000 : ℝ), (2201274453/5000000000 : ℝ), (4402548719/10000000000 : ℝ)] ![(7951850272769/25000000000000 : ℝ), (34096300394481/100000000000000 : ℝ), (34096298495053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2087678471/5000000000 : ℝ)|^4311 ≤ (7951850272769/25000000000000 : ℝ)^3287
        have hw : |(2087678471/5000000000 : ℝ)|=(2087678471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2201274453/5000000000 : ℝ)|^4311 ≤ (34096300394481/100000000000000 : ℝ)^3287
        have hw : |(2201274453/5000000000 : ℝ)|=(2201274453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4402548719/10000000000 : ℝ)|^4311 ≤ (34096298495053/100000000000000 : ℝ)^3287
        have hw : |(4402548719/10000000000 : ℝ)|=(4402548719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_box_8 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-213496697/1000000000 : ℝ)*x 0 + (5179412421/10000000000 : ℝ)*x 1 + (2701789633/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213496697/1000000000 : ℝ)^4311 ≤ (6598515047807/50000000000000 : ℝ)^3287 := by
    have hnat : (213496697 : ℕ)^4311*50000000000000^3287 ≤ 6598515047807^3287*1000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213496697 1000000000 6598515047807 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5179412421/10000000000 : ℝ)^4311 ≤ (10548974136509/25000000000000 : ℝ)^3287 := by
    have hnat : (5179412421 : ℕ)^4311*25000000000000^3287 ≤ 10548974136509^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179412421 10000000000 10548974136509 25000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2701789633/5000000000 : ℝ)^4311 ≤ (8921414667441/20000000000000 : ℝ)^3287 := by
    have hnat : (2701789633 : ℕ)^4311*20000000000000^3287 ≤ 8921414667441^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701789633 5000000000 8921414667441 20000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-213496697/1000000000 : ℝ), (5179412421/10000000000 : ℝ), (2701789633/5000000000 : ℝ)] ![(6598515047807/50000000000000 : ℝ), (10548974136509/25000000000000 : ℝ), (8921414667441/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-213496697/1000000000 : ℝ)|^4311 ≤ (6598515047807/50000000000000 : ℝ)^3287
        have hw : |(-213496697/1000000000 : ℝ)|=(213496697/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5179412421/10000000000 : ℝ)|^4311 ≤ (10548974136509/25000000000000 : ℝ)^3287
        have hw : |(5179412421/10000000000 : ℝ)|=(5179412421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2701789633/5000000000 : ℝ)|^4311 ≤ (8921414667441/20000000000000 : ℝ)^3287
        have hw : |(2701789633/5000000000 : ℝ)|=(2701789633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_box_9 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5275439397/10000000000 : ℝ)*x 0 + (-250853419/1250000000 : ℝ)*x 1 + (5403579519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275439397/10000000000 : ℝ)^4311 ≤ (43224880045477/100000000000000 : ℝ)^3287 := by
    have hnat : (5275439397 : ℕ)^4311*100000000000000^3287 ≤ 43224880045477^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275439397 10000000000 43224880045477 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (250853419/1250000000 : ℝ)^4311 ≤ (2433608773053/20000000000000 : ℝ)^3287 := by
    have hnat : (250853419 : ℕ)^4311*20000000000000^3287 ≤ 2433608773053^3287*1250000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250853419 1250000000 2433608773053 20000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5403579519/10000000000 : ℝ)^4311 ≤ (11151769019097/25000000000000 : ℝ)^3287 := by
    have hnat : (5403579519 : ℕ)^4311*25000000000000^3287 ≤ 11151769019097^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403579519 10000000000 11151769019097 25000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275439397/10000000000 : ℝ), (-250853419/1250000000 : ℝ), (5403579519/10000000000 : ℝ)] ![(43224880045477/100000000000000 : ℝ), (2433608773053/20000000000000 : ℝ), (11151769019097/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275439397/10000000000 : ℝ)|^4311 ≤ (43224880045477/100000000000000 : ℝ)^3287
        have hw : |(5275439397/10000000000 : ℝ)|=(5275439397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-250853419/1250000000 : ℝ)|^4311 ≤ (2433608773053/20000000000000 : ℝ)^3287
        have hw : |(-250853419/1250000000 : ℝ)|=(250853419/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5403579519/10000000000 : ℝ)|^4311 ≤ (11151769019097/25000000000000 : ℝ)^3287
        have hw : |(5403579519/10000000000 : ℝ)|=(5403579519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_box_10 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5275440083/10000000000 : ℝ)*x 0 + (1080715841/2000000000 : ℝ)*x 1 + (-2006826851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275440083/10000000000 : ℝ)^4311 ≤ (21612443708673/50000000000000 : ℝ)^3287 := by
    have hnat : (5275440083 : ℕ)^4311*50000000000000^3287 ≤ 21612443708673^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275440083 10000000000 21612443708673 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1080715841/2000000000 : ℝ)^4311 ≤ (44607072676769/100000000000000 : ℝ)^3287 := by
    have hnat : (1080715841 : ℕ)^4311*100000000000000^3287 ≤ 44607072676769^3287*2000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080715841 2000000000 44607072676769 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2006826851/10000000000 : ℝ)^4311 ≤ (12168039881197/100000000000000 : ℝ)^3287 := by
    have hnat : (2006826851 : ℕ)^4311*100000000000000^3287 ≤ 12168039881197^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2006826851 10000000000 12168039881197 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275440083/10000000000 : ℝ), (1080715841/2000000000 : ℝ), (-2006826851/10000000000 : ℝ)] ![(21612443708673/50000000000000 : ℝ), (44607072676769/100000000000000 : ℝ), (12168039881197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275440083/10000000000 : ℝ)|^4311 ≤ (21612443708673/50000000000000 : ℝ)^3287
        have hw : |(5275440083/10000000000 : ℝ)|=(5275440083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1080715841/2000000000 : ℝ)|^4311 ≤ (44607072676769/100000000000000 : ℝ)^3287
        have hw : |(1080715841/2000000000 : ℝ)|=(1080715841/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2006826851/10000000000 : ℝ)|^4311 ≤ (12168039881197/100000000000000 : ℝ)^3287
        have hw : |(-2006826851/10000000000 : ℝ)|=(2006826851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_box_11 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (35196351/78125000 : ℝ)*x 0 + (1059356701/2500000000 : ℝ)*x 1 + (21187133/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (35196351/78125000 : ℝ)^4311 ≤ (35142046385557/100000000000000 : ℝ)^3287 := by
    have hnat : (35196351 : ℕ)^4311*100000000000000^3287 ≤ 35142046385557^3287*78125000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35196351 78125000 35142046385557 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1059356701/2500000000 : ℝ)^4311 ≤ (32428977824451/100000000000000 : ℝ)^3287 := by
    have hnat : (1059356701 : ℕ)^4311*100000000000000^3287 ≤ 32428977824451^3287*2500000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059356701 2500000000 32428977824451 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21187133/50000000 : ℝ)^4311 ≤ (16214487888439/50000000000000 : ℝ)^3287 := by
    have hnat : (21187133 : ℕ)^4311*50000000000000^3287 ≤ 16214487888439^3287*50000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21187133 50000000 16214487888439 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(35196351/78125000 : ℝ), (1059356701/2500000000 : ℝ), (21187133/50000000 : ℝ)] ![(35142046385557/100000000000000 : ℝ), (32428977824451/100000000000000 : ℝ), (16214487888439/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(35196351/78125000 : ℝ)|^4311 ≤ (35142046385557/100000000000000 : ℝ)^3287
        have hw : |(35196351/78125000 : ℝ)|=(35196351/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1059356701/2500000000 : ℝ)|^4311 ≤ (32428977824451/100000000000000 : ℝ)^3287
        have hw : |(1059356701/2500000000 : ℝ)|=(1059356701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(21187133/50000000 : ℝ)|^4311 ≤ (16214487888439/50000000000000 : ℝ)^3287
        have hw : |(21187133/50000000 : ℝ)|=(21187133/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_box_12 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1940549161/10000000000 : ℝ)*x 0 + (68413613/125000000 : ℝ)*x 1 + (2627023423/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1940549161/10000000000 : ℝ)^4311 ≤ (58218582491/500000000000 : ℝ)^3287 := by
    have hnat : (1940549161 : ℕ)^4311*500000000000^3287 ≤ 58218582491^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1940549161 10000000000 58218582491 500000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (68413613/125000000 : ℝ)^4311 ≤ (45361145967393/100000000000000 : ℝ)^3287 := by
    have hnat : (68413613 : ℕ)^4311*100000000000000^3287 ≤ 45361145967393^3287*125000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68413613 125000000 45361145967393 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627023423/5000000000 : ℝ)^4311 ≤ (21497568760217/50000000000000 : ℝ)^3287 := by
    have hnat : (2627023423 : ℕ)^4311*50000000000000^3287 ≤ 21497568760217^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627023423 5000000000 21497568760217 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1940549161/10000000000 : ℝ), (68413613/125000000 : ℝ), (2627023423/5000000000 : ℝ)] ![(58218582491/500000000000 : ℝ), (45361145967393/100000000000000 : ℝ), (21497568760217/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1940549161/10000000000 : ℝ)|^4311 ≤ (58218582491/500000000000 : ℝ)^3287
        have hw : |(-1940549161/10000000000 : ℝ)|=(1940549161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(68413613/125000000 : ℝ)|^4311 ≤ (45361145967393/100000000000000 : ℝ)^3287
        have hw : |(68413613/125000000 : ℝ)|=(68413613/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627023423/5000000000 : ℝ)|^4311 ≤ (21497568760217/50000000000000 : ℝ)^3287
        have hw : |(2627023423/5000000000 : ℝ)|=(2627023423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_box_13 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1345107911/2500000000 : ℝ)*x 0 + (-206693389/1000000000 : ℝ)*x 1 + (5254046549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1345107911/2500000000 : ℝ)^4311 ≤ (44356625817843/100000000000000 : ℝ)^3287 := by
    have hnat : (1345107911 : ℕ)^4311*100000000000000^3287 ≤ 44356625817843^3287*2500000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345107911 2500000000 44356625817843 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (206693389/1000000000 : ℝ)^4311 ≤ (3162059959143/25000000000000 : ℝ)^3287 := by
    have hnat : (206693389 : ℕ)^4311*25000000000000^3287 ≤ 3162059959143^3287*1000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206693389 1000000000 3162059959143 25000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254046549/10000000000 : ℝ)^4311 ≤ (2149756716643/5000000000000 : ℝ)^3287 := by
    have hnat : (5254046549 : ℕ)^4311*5000000000000^3287 ≤ 2149756716643^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254046549 10000000000 2149756716643 5000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1345107911/2500000000 : ℝ), (-206693389/1000000000 : ℝ), (5254046549/10000000000 : ℝ)] ![(44356625817843/100000000000000 : ℝ), (3162059959143/25000000000000 : ℝ), (2149756716643/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1345107911/2500000000 : ℝ)|^4311 ≤ (44356625817843/100000000000000 : ℝ)^3287
        have hw : |(1345107911/2500000000 : ℝ)|=(1345107911/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-206693389/1000000000 : ℝ)|^4311 ≤ (3162059959143/25000000000000 : ℝ)^3287
        have hw : |(-206693389/1000000000 : ℝ)|=(206693389/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254046549/10000000000 : ℝ)|^4311 ≤ (2149756716643/5000000000000 : ℝ)^3287
        have hw : |(5254046549/10000000000 : ℝ)|=(5254046549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_box_14 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5380431661/10000000000 : ℝ)*x 0 + (5254046867/10000000000 : ℝ)*x 1 + (-1033466721/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5380431661/10000000000 : ℝ)^4311 ≤ (11089156500413/25000000000000 : ℝ)^3287 := by
    have hnat : (5380431661 : ℕ)^4311*25000000000000^3287 ≤ 11089156500413^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5380431661 10000000000 11089156500413 25000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5254046867/10000000000 : ℝ)^4311 ≤ (21497568872909/50000000000000 : ℝ)^3287 := by
    have hnat : (5254046867 : ℕ)^4311*50000000000000^3287 ≤ 21497568872909^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254046867 10000000000 21497568872909 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1033466721/5000000000 : ℝ)^4311 ≤ (12648236241067/100000000000000 : ℝ)^3287 := by
    have hnat : (1033466721 : ℕ)^4311*100000000000000^3287 ≤ 12648236241067^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033466721 5000000000 12648236241067 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5380431661/10000000000 : ℝ), (5254046867/10000000000 : ℝ), (-1033466721/5000000000 : ℝ)] ![(11089156500413/25000000000000 : ℝ), (21497568872909/50000000000000 : ℝ), (12648236241067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5380431661/10000000000 : ℝ)|^4311 ≤ (11089156500413/25000000000000 : ℝ)^3287
        have hw : |(5380431661/10000000000 : ℝ)|=(5380431661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5254046867/10000000000 : ℝ)|^4311 ≤ (21497568872909/50000000000000 : ℝ)^3287
        have hw : |(5254046867/10000000000 : ℝ)|=(5254046867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1033466721/5000000000 : ℝ)|^4311 ≤ (12648236241067/100000000000000 : ℝ)^3287
        have hw : |(-1033466721/5000000000 : ℝ)|=(1033466721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_box_15 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (829696313/2000000000 : ℝ)*x 0 + (1103936797/2500000000 : ℝ)*x 1 + (1103936747/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (829696313/2000000000 : ℝ)^4311 ≤ (31539156378789/100000000000000 : ℝ)^3287 := by
    have hnat : (829696313 : ℕ)^4311*100000000000000^3287 ≤ 31539156378789^3287*2000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      829696313 2000000000 31539156378789 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1103936797/2500000000 : ℝ)^4311 ≤ (6846084564389/20000000000000 : ℝ)^3287 := by
    have hnat : (1103936797 : ℕ)^4311*20000000000000^3287 ≤ 6846084564389^3287*2500000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103936797 2500000000 6846084564389 20000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1103936747/2500000000 : ℝ)^4311 ≤ (1369216831543/4000000000000 : ℝ)^3287 := by
    have hnat : (1103936747 : ℕ)^4311*4000000000000^3287 ≤ 1369216831543^3287*2500000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103936747 2500000000 1369216831543 4000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(829696313/2000000000 : ℝ), (1103936797/2500000000 : ℝ), (1103936747/2500000000 : ℝ)] ![(31539156378789/100000000000000 : ℝ), (6846084564389/20000000000000 : ℝ), (1369216831543/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(829696313/2000000000 : ℝ)|^4311 ≤ (31539156378789/100000000000000 : ℝ)^3287
        have hw : |(829696313/2000000000 : ℝ)|=(829696313/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1103936797/2500000000 : ℝ)|^4311 ≤ (6846084564389/20000000000000 : ℝ)^3287
        have hw : |(1103936797/2500000000 : ℝ)|=(1103936797/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1103936747/2500000000 : ℝ)|^4311 ≤ (1369216831543/4000000000000 : ℝ)^3287
        have hw : |(1103936747/2500000000 : ℝ)|=(1103936747/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1351_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77541681/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1839/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11171/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62859/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58959/100000 : ℝ) ∧ (80007/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84387/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1839/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11171/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1839/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11171/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1839/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11171/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1839/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11171/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1839/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11171/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1839/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11171/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11171/100000 : ℝ) ^ (2155/512 : ℝ) ≤ (4924978330479439/50000000000000000000 : ℝ) := by
    have hpowers : (11171/100000 : ℝ)^2155 ≤ (4924978330479439/50000000000000000000 : ℝ)^512 := by
      have hnat : (11171 : ℕ)^2155*50000000000000000000^512 ≤ 4924978330479439^512*100000^2155 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11171 100000 4924978330479439 50000000000000000000 2155 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11171/100000 : ℝ)) (X := (4924978330479439/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2155 512 (by norm_num) hpowers
    exact h
  have hpowhi : (1839/12500 : ℝ) ^ (2155/512 : ℝ) ≤ (31386526724309139/100000000000000000000 : ℝ) := by
    have hpowers : (1839/12500 : ℝ)^2155 ≤ (31386526724309139/100000000000000000000 : ℝ)^512 := by
      have hnat : (1839 : ℕ)^2155*100000000000000000000^512 ≤ 31386526724309139^512*12500^2155 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1839 12500 31386526724309139 100000000000000000000 2155 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1839/12500 : ℝ)) (X := (31386526724309139/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2155 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004924978330479439/25000000000000000000 : ℝ) ≤ (2500117002299883/2500000000000000 : ℝ) ^ (2155/512 : ℝ) := by
    have hpowers : (25004924978330479439/25000000000000000000 : ℝ)^512 ≤ (2500117002299883/2500000000000000 : ℝ)^2155 := by
      have hnat : (25004924978330479439 : ℕ)^512*2500000000000000^2155 ≤ 2500117002299883^2155*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004924978330479439 25000000000000000000 2500117002299883 2500000000000000 512 2155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500117002299883/2500000000000000 : ℝ)) (X := (25004924978330479439/25000000000000000000 : ℝ)) (by norm_num) 2155 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100041236483385268017/100000000000000000000 : ℝ) ≤ (2500244892823691/2500000000000000 : ℝ) ^ (2155/512 : ℝ) := by
    have hpowers : (100041236483385268017/100000000000000000000 : ℝ)^512 ≤ (2500244892823691/2500000000000000 : ℝ)^2155 := by
      have hnat : (100041236483385268017 : ℕ)^512*2500000000000000^2155 ≤ 2500244892823691^2155*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100041236483385268017 100000000000000000000 2500244892823691 2500000000000000 512 2155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500244892823691/2500000000000000 : ℝ)) (X := (100041236483385268017/100000000000000000000 : ℝ)) (by norm_num) 2155 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031386526724309139/50000000000000000000 : ℝ) ≤ (2500372783347499/2500000000000000 : ℝ) ^ (2155/512 : ℝ) := by
    have hpowers : (50031386526724309139/50000000000000000000 : ℝ)^512 ≤ (2500372783347499/2500000000000000 : ℝ)^2155 := by
      have hnat : (50031386526724309139 : ℕ)^512*2500000000000000^2155 ≤ 2500372783347499^2155*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031386526724309139 50000000000000000000 2500372783347499 2500000000000000 512 2155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500372783347499/2500000000000000 : ℝ)) (X := (50031386526724309139/50000000000000000000 : ℝ)) (by norm_num) 2155 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4924978330479439/50000000000000000000 : ℝ) ≤ ((8850056975060967367/8852500000000000000 : ℝ)+2*(3996578869/2766406250000 : ℝ)*(11171/100000 : ℝ))^(2155/512 : ℝ) := by
    rw [show (8850056975060967367/8852500000000000000 : ℝ)+2*(3996578869/2766406250000 : ℝ)*(11171/100000 : ℝ)=(2500117002299883/2500000000000000 : ℝ) by norm_num, show 1+2*(4924978330479439/50000000000000000000 : ℝ)=(25004924978330479439/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31386526724309139/100000000000000000000 : ℝ)+(4924978330479439/50000000000000000000 : ℝ) ≤ ((8850056975060967367/8852500000000000000 : ℝ)+(3996578869/2766406250000 : ℝ)*((1839/12500 : ℝ)+(11171/100000 : ℝ)))^(2155/512 : ℝ) := by
    rw [show (8850056975060967367/8852500000000000000 : ℝ)+(3996578869/2766406250000 : ℝ)*((1839/12500 : ℝ)+(11171/100000 : ℝ))=(2500244892823691/2500000000000000 : ℝ) by norm_num, show 1+(31386526724309139/100000000000000000000 : ℝ)+(4924978330479439/50000000000000000000 : ℝ)=(100041236483385268017/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31386526724309139/100000000000000000000 : ℝ) ≤ ((8850056975060967367/8852500000000000000 : ℝ)+2*(3996578869/2766406250000 : ℝ)*(1839/12500 : ℝ))^(2155/512 : ℝ) := by
    rw [show (8850056975060967367/8852500000000000000 : ℝ)+2*(3996578869/2766406250000 : ℝ)*(1839/12500 : ℝ)=(2500372783347499/2500000000000000 : ℝ) by norm_num, show 1+2*(31386526724309139/100000000000000000000 : ℝ)=(50031386526724309139/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8850056975060967367/8852500000000000000 : ℝ)*(X 1 0+X 2 0)+(3996578869/2766406250000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2155/512 : ℝ)) (lo := (11171/100000 : ℝ)) (hi := (1839/12500 : ℝ)) (c := (8850056975060967367/8852500000000000000 : ℝ)) (alpha := (3996578869/2766406250000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8850056975060967367/8852500000000000000 : ℝ)*(X 0 1+X 2 1)+(3996578869/2766406250000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2155/512 : ℝ)) (lo := (11171/100000 : ℝ)) (hi := (1839/12500 : ℝ)) (c := (8850056975060967367/8852500000000000000 : ℝ)) (alpha := (3996578869/2766406250000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8850056975060967367/8852500000000000000 : ℝ)*(X 0 2+X 1 2)+(3996578869/2766406250000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2155/512 : ℝ)) (lo := (11171/100000 : ℝ)) (hi := (1839/12500 : ℝ)) (c := (8850056975060967367/8852500000000000000 : ℝ)) (alpha := (3996578869/2766406250000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-74787249/400000000 : ℝ)*X 0 0+(336847707/625000000 : ℝ)*X 0 1+(2694781827/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((264264243/500000000 : ℝ)*X 1 0+(-503147433/2500000000 : ℝ)*X 1 1+(67369557/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5285285459/10000000000 : ℝ)*X 2 0+(5389563733/10000000000 : ℝ)*X 2 1+(-402518009/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((894450467/2000000000 : ℝ)*X 0 0+(1063538669/2500000000 : ℝ)*X 0 1+(4254154147/10000000000 : ℝ)*X 0 2+(894450467/2000000000 : ℝ)*X 1 0+(1063538669/2500000000 : ℝ)*X 1 1+(4254154147/10000000000 : ℝ)*X 1 2+(894450467/2000000000 : ℝ)*X 2 0+(1063538669/2500000000 : ℝ)*X 2 1+(4254154147/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-551378763/2500000000 : ℝ)*X 0 0+(658140407/1250000000 : ℝ)*X 0 1+(5265123331/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1343164191/2500000000 : ℝ)*X 1 0+(-2062586927/10000000000 : ℝ)*X 1 1+(1053024671/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2686328423/5000000000 : ℝ)*X 2 0+(329070207/625000000 : ℝ)*X 2 1+(-3300139/16000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2087678471/5000000000 : ℝ)*X 0 0+(2201274453/5000000000 : ℝ)*X 0 1+(4402548719/10000000000 : ℝ)*X 0 2+(2087678471/5000000000 : ℝ)*X 1 0+(2201274453/5000000000 : ℝ)*X 1 1+(4402548719/10000000000 : ℝ)*X 1 2+(2087678471/5000000000 : ℝ)*X 2 0+(2201274453/5000000000 : ℝ)*X 2 1+(4402548719/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-213496697/1000000000 : ℝ)*X 0 0+(5179412421/10000000000 : ℝ)*X 0 1+(2701789633/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5275439397/10000000000 : ℝ)*X 1 0+(-250853419/1250000000 : ℝ)*X 1 1+(5403579519/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5275440083/10000000000 : ℝ)*X 2 0+(1080715841/2000000000 : ℝ)*X 2 1+(-2006826851/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((35196351/78125000 : ℝ)*X 0 0+(1059356701/2500000000 : ℝ)*X 0 1+(21187133/50000000 : ℝ)*X 0 2+(35196351/78125000 : ℝ)*X 1 0+(1059356701/2500000000 : ℝ)*X 1 1+(21187133/50000000 : ℝ)*X 1 2+(35196351/78125000 : ℝ)*X 2 0+(1059356701/2500000000 : ℝ)*X 2 1+(21187133/50000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1940549161/10000000000 : ℝ)*X 0 0+(68413613/125000000 : ℝ)*X 0 1+(2627023423/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1345107911/2500000000 : ℝ)*X 1 0+(-206693389/1000000000 : ℝ)*X 1 1+(5254046549/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5380431661/10000000000 : ℝ)*X 2 0+(5254046867/10000000000 : ℝ)*X 2 1+(-1033466721/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((829696313/2000000000 : ℝ)*X 0 0+(1103936797/2500000000 : ℝ)*X 0 1+(1103936747/2500000000 : ℝ)*X 0 2+(829696313/2000000000 : ℝ)*X 1 0+(1103936797/2500000000 : ℝ)*X 1 1+(1103936747/2500000000 : ℝ)*X 1 2+(829696313/2000000000 : ℝ)*X 2 0+(1103936797/2500000000 : ℝ)*X 2 1+(1103936747/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62859/100000 : ℝ) ≤ (-278218227284336774102860635965079/442625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10160469/100000000000000 : ℝ)*(lower0) + (659539/1562500000000 : ℝ)*(lower2) + (571393/25000000000000 : ℝ)*(lower3) + (1346573/100000000000000 : ℝ)*(lower4) + (2248763/20000000000000 : ℝ)*(lower5) + (2930723552335821/100000000000000 : ℝ)*(major0) + (2930723552335821/100000000000000 : ℝ)*(major1) + (2930723552335821/100000000000000 : ℝ)*(major2) + (3992626212449703/100000000000000 : ℝ)*(sp4) + (1996307749141463/50000000000000 : ℝ)*(sp5) + (3992605048572131/100000000000000 : ℝ)*(sp6) + (377954606418169/20000000000000 : ℝ)*(sp7) + (5357083389/50000000000000 : ℝ)*(sp13) + (21163877571/100000000000000 : ℝ)*(sp14) + (377954606418169/20000000000000 : ℝ)*(f.failure) + (3992626212449703/100000000000000 : ℝ)*(f.sum) + (72331705595751/8852500000000000000000000000 : ℝ)*base65 + (823869296421546693/885250000000000000000000000000000 : ℝ)*base68 + (4192015124699046693/885250000000000000000000000000000 : ℝ)*base70 + (4775511938388546693/885250000000000000000000000000000 : ℝ)*base72 + (22063004478033/4426250000000000000000000000 : ℝ)*base73 + (10842336381703796693/885250000000000000000000000000000 : ℝ)*base76 + (12510056823186203307/885250000000000000000000000000000 : ℝ)*base77 + (2070769876853203307/885250000000000000000000000000000 : ℝ)*base79 + (422108617033/4426250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (3202089/1000000000000000000000 : ℝ)*base89 + (3202089/1000000000000000000000 : ℝ)*base91 + (3202089/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (58959/100000 : ℝ) ≤ (130488479529746153506158969964059/221312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (53141687/100000000000000 : ℝ)*(lower0) + (22068033/50000000000000 : ℝ)*(upper1) + (12229519/100000000000000 : ℝ)*(upper4) + (1499860195532341/50000000000000 : ℝ)*(major0) + (1499860195532341/50000000000000 : ℝ)*(major1) + (1499860195532341/50000000000000 : ℝ)*(major2) + (252845143492119/6250000000000 : ℝ)*(sp0) + (2022744578200807/50000000000000 : ℝ)*(sp1) + (2022757745873543/50000000000000 : ℝ)*(sp2) + (967131229611431/50000000000000 : ℝ)*(sp3) + (34702420407/100000000000000 : ℝ)*(sp5) + (1045884367/12500000000000 : ℝ)*(sp6) + (734700341/100000000000000 : ℝ)*(sp7) + (781474059/50000000000000 : ℝ)*(sp12) + (1934263193923203/100000000000000 : ℝ)*(f.failure) + (2022761929411011/50000000000000 : ℝ)*(f.sum) + (36938094955273/8852500000000000000000000000 : ℝ)*base66 + (1082358861111333853/442625000000000000000000000000000 : ℝ)*base68 + (1731263741957291147/442625000000000000000000000000000 : ℝ)*base69 + (382893414924416147/442625000000000000000000000000000 : ℝ)*base71 + (643731993429919/17705000000000000000000000000 : ℝ)*base73 + (2235641887079666147/442625000000000000000000000000000 : ℝ)*base75 + (1672164594828333853/442625000000000000000000000000000 : ℝ)*base78 + (13255369989840916147/442625000000000000000000000000000 : ℝ)*base79 + (42275941700991/17705000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (45524243/5000000000000000000000 : ℝ)*base89 + (45524243/5000000000000000000000 : ℝ)*base91 + (45524243/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (80007/100000 : ℝ) ≤ (17707081263325216265358562383879/22131250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (49353919/25000000000000 : ℝ)*(lower3) + (28261863/10000000000000 : ℝ)*(upper4) + (3803661/100000000000000 : ℝ)*(lower5) + (165573516359521/5000000000000 : ℝ)*(major0) + (165573516359521/5000000000000 : ℝ)*(major1) + (165573516359521/5000000000000 : ℝ)*(major2) + (10387081539/100000000000000 : ℝ)*(sp0) + (231778610861/100000000000000 : ℝ)*(sp1) + (208008013813/100000000000000 : ℝ)*(sp2) + (5189372759/4000000000000 : ℝ)*(sp3) + (2230488196925883/50000000000000 : ℝ)*(sp8) + (1115188750580611/25000000000000 : ℝ)*(sp9) + (1115194693229873/25000000000000 : ℝ)*(sp10) + (1067577168867053/50000000000000 : ℝ)*(sp11) + (2135284072053081/100000000000000 : ℝ)*(f.failure) + (2230493390466653/50000000000000 : ℝ)*(f.sum) + (1291437704013/354100000000000000000000000 : ℝ)*base66 + (148687847278826207/44262500000000000000000000000000 : ℝ)*base67 + (90276060084536293/44262500000000000000000000000000 : ℝ)*base70 + (146175828991788707/44262500000000000000000000000000 : ℝ)*base71 + (435536256667/110656250000000000000000000 : ℝ)*base73 + (266247606844288707/44262500000000000000000000000000 : ℝ)*base75 + (88676527669601207/44262500000000000000000000000000 : ℝ)*base77 + (197361916509111293/44262500000000000000000000000000 : ℝ)*base80 + (76427213413/22131250000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (21969161/5000000000000000000000 : ℝ)*base89 + (21969161/5000000000000000000000 : ℝ)*base91 + (21969161/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-84387/100000 : ℝ) ≤ (-373507247193995860429982070446943/442625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9696127/10000000000000 : ℝ)*(lower0) + (153610603/100000000000000 : ℝ)*(lower1) + (195021091/100000000000000 : ℝ)*(lower2) + (3348031518546643/100000000000000 : ℝ)*(major0) + (3348031518546643/100000000000000 : ℝ)*(major1) + (3348031518546643/100000000000000 : ℝ)*(major2) + (2239637699/50000000000000 : ℝ)*(sp0) + (78971924063/25000000000000 : ℝ)*(sp5) + (75035697521/100000000000000 : ℝ)*(sp6) + (33149476231/50000000000000 : ℝ)*(sp7) + (2282663746448059/50000000000000 : ℝ)*(sp12) + (913003216895053/20000000000000 : ℝ)*(sp13) + (913051387294799/20000000000000 : ℝ)*(sp14) + (1079396479650149/50000000000000 : ℝ)*(sp15) + (53971481456319/2500000000000 : ℝ)*(f.failure) + (1141332993042879/25000000000000 : ℝ)*(f.sum) + (11525700672077/8852500000000000000000000000 : ℝ)*base66 + (397598129351798981/885250000000000000000000000000000 : ℝ)*base67 + (3680890142494298981/885250000000000000000000000000000 : ℝ)*base69 + (3794873519165701019/885250000000000000000000000000000 : ℝ)*base72 + (273968704903967/8852500000000000000000000000 : ℝ)*base74 + (390859569586951019/885250000000000000000000000000000 : ℝ)*base76 + (2082743614161048981/885250000000000000000000000000000 : ℝ)*base77 + (8572803693186548981/885250000000000000000000000000000 : ℝ)*base79 + (76346541716591/17705000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (417761/125000000000000000000 : ℝ)*base90 + (417761/125000000000000000000 : ℝ)*base92 + (417761/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1351_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77541681/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1839/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11171/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62859/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58959/100000 : ℝ) else (80007/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84387/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1351_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1351_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77541681/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (92/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11163/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62859/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58959/100000 : ℝ) else (80007/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84387/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1351_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1351_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1351_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77541681/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (92/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11163/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62859/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58959/100000 : ℝ) else (80007/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84387/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1351_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
