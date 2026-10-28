-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1205_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:04:46.5556+00:00
-- url     : https://prove2.me/submissions/45bb01e3-894e-46b3-accf-997c84a4decb

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
theorem support_rectangle_w1205_box_0 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2012264849/10000000000 : ℝ)*x 0 + (2687697441/5000000000 : ℝ)*x 1 + (2687697381/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2012264849/10000000000 : ℝ)^4199 ≤ (19196845713/160000000000 : ℝ)^3175 := by
    have hnat : (2012264849 : ℕ)^4199*160000000000^3175 ≤ 19196845713^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2012264849 10000000000 19196845713 160000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2687697441/5000000000 : ℝ)^4199 ≤ (44000986356409/100000000000000 : ℝ)^3175 := by
    have hnat : (2687697441 : ℕ)^4199*100000000000000^3175 ≤ 44000986356409^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687697441 5000000000 44000986356409 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2687697381/5000000000 : ℝ)^4199 ≤ (4400098505733/10000000000000 : ℝ)^3175 := by
    have hnat : (2687697381 : ℕ)^4199*10000000000000^3175 ≤ 4400098505733^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687697381 5000000000 4400098505733 10000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2012264849/10000000000 : ℝ), (2687697441/5000000000 : ℝ), (2687697381/5000000000 : ℝ)] ![(19196845713/160000000000 : ℝ), (44000986356409/100000000000000 : ℝ), (4400098505733/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2012264849/10000000000 : ℝ)|^4199 ≤ (19196845713/160000000000 : ℝ)^3175
        have hw : |(-2012264849/10000000000 : ℝ)|=(2012264849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2687697441/5000000000 : ℝ)|^4199 ≤ (44000986356409/100000000000000 : ℝ)^3175
        have hw : |(2687697441/5000000000 : ℝ)|=(2687697441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2687697381/5000000000 : ℝ)|^4199 ≤ (4400098505733/10000000000000 : ℝ)^3175
        have hw : |(2687697381/5000000000 : ℝ)|=(2687697381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_box_1 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (132413069/250000000 : ℝ)*x 0 + (-2119379913/10000000000 : ℝ)*x 1 + (1343848663/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132413069/250000000 : ℝ)^4199 ≤ (43149171014061/100000000000000 : ℝ)^3175 := by
    have hnat : (132413069 : ℕ)^4199*100000000000000^3175 ≤ 43149171014061^3175*250000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132413069 250000000 43149171014061 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2119379913/10000000000 : ℝ)^4199 ≤ (12849845108861/100000000000000 : ℝ)^3175 := by
    have hnat : (2119379913 : ℕ)^4199*100000000000000^3175 ≤ 12849845108861^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119379913 10000000000 12849845108861 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1343848663/2500000000 : ℝ)^4199 ≤ (11000245966627/25000000000000 : ℝ)^3175 := by
    have hnat : (1343848663 : ℕ)^4199*25000000000000^3175 ≤ 11000245966627^3175*2500000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343848663 2500000000 11000245966627 25000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132413069/250000000 : ℝ), (-2119379913/10000000000 : ℝ), (1343848663/2500000000 : ℝ)] ![(43149171014061/100000000000000 : ℝ), (12849845108861/100000000000000 : ℝ), (11000245966627/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132413069/250000000 : ℝ)|^4199 ≤ (43149171014061/100000000000000 : ℝ)^3175
        have hw : |(132413069/250000000 : ℝ)|=(132413069/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2119379913/10000000000 : ℝ)|^4199 ≤ (12849845108861/100000000000000 : ℝ)^3175
        have hw : |(-2119379913/10000000000 : ℝ)|=(2119379913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1343848663/2500000000 : ℝ)|^4199 ≤ (11000245966627/25000000000000 : ℝ)^3175
        have hw : |(1343848663/2500000000 : ℝ)|=(1343848663/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_box_2 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5296522903/10000000000 : ℝ)*x 0 + (5375394789/10000000000 : ℝ)*x 1 + (-423875907/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296522903/10000000000 : ℝ)^4199 ≤ (43149172554767/100000000000000 : ℝ)^3175 := by
    have hnat : (5296522903 : ℕ)^4199*100000000000000^3175 ≤ 43149172554767^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296522903 10000000000 43149172554767 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5375394789/10000000000 : ℝ)^4199 ≤ (44000985349623/100000000000000 : ℝ)^3175 := by
    have hnat : (5375394789 : ℕ)^4199*100000000000000^3175 ≤ 44000985349623^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375394789 10000000000 44000985349623 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (423875907/2000000000 : ℝ)^4199 ≤ (12849842077881/100000000000000 : ℝ)^3175 := by
    have hnat : (423875907 : ℕ)^4199*100000000000000^3175 ≤ 12849842077881^3175*2000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423875907 2000000000 12849842077881 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296522903/10000000000 : ℝ), (5375394789/10000000000 : ℝ), (-423875907/2000000000 : ℝ)] ![(43149172554767/100000000000000 : ℝ), (44000985349623/100000000000000 : ℝ), (12849842077881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296522903/10000000000 : ℝ)|^4199 ≤ (43149172554767/100000000000000 : ℝ)^3175
        have hw : |(5296522903/10000000000 : ℝ)|=(5296522903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5375394789/10000000000 : ℝ)|^4199 ≤ (44000985349623/100000000000000 : ℝ)^3175
        have hw : |(5375394789/10000000000 : ℝ)|=(5375394789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-423875907/2000000000 : ℝ)|^4199 ≤ (12849842077881/100000000000000 : ℝ)^3175
        have hw : |(-423875907/2000000000 : ℝ)|=(423875907/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_box_3 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4462766497/10000000000 : ℝ)*x 0 + (1076123487/2500000000 : ℝ)*x 1 + (269030969/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4462766497/10000000000 : ℝ)^4199 ≤ (17201432428633/50000000000000 : ℝ)^3175 := by
    have hnat : (4462766497 : ℕ)^4199*50000000000000^3175 ≤ 17201432428633^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4462766497 10000000000 17201432428633 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1076123487/2500000000 : ℝ)^4199 ≤ (6559711944621/20000000000000 : ℝ)^3175 := by
    have hnat : (1076123487 : ℕ)^4199*20000000000000^3175 ≤ 6559711944621^3175*2500000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076123487 2500000000 6559711944621 20000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269030969/625000000 : ℝ)^4199 ≤ (32798575403047/100000000000000 : ℝ)^3175 := by
    have hnat : (269030969 : ℕ)^4199*100000000000000^3175 ≤ 32798575403047^3175*625000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269030969 625000000 32798575403047 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4462766497/10000000000 : ℝ), (1076123487/2500000000 : ℝ), (269030969/625000000 : ℝ)] ![(17201432428633/50000000000000 : ℝ), (6559711944621/20000000000000 : ℝ), (32798575403047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4462766497/10000000000 : ℝ)|^4199 ≤ (17201432428633/50000000000000 : ℝ)^3175
        have hw : |(4462766497/10000000000 : ℝ)|=(4462766497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1076123487/2500000000 : ℝ)|^4199 ≤ (6559711944621/20000000000000 : ℝ)^3175
        have hw : |(1076123487/2500000000 : ℝ)|=(1076123487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269030969/625000000 : ℝ)|^4199 ≤ (32798575403047/100000000000000 : ℝ)^3175
        have hw : |(269030969/625000000 : ℝ)|=(269030969/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_box_4 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-7072991/31250000 : ℝ)*x 0 + (2640946169/5000000000 : ℝ)*x 1 + (5281892233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7072991/31250000 : ℝ)^4199 ≤ (14016779827641/100000000000000 : ℝ)^3175 := by
    have hnat : (7072991 : ℕ)^4199*100000000000000^3175 ≤ 14016779827641^3175*31250000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7072991 31250000 14016779827641 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640946169/5000000000 : ℝ)^4199 ≤ (42991610643251/100000000000000 : ℝ)^3175 := by
    have hnat : (2640946169 : ℕ)^4199*100000000000000^3175 ≤ 42991610643251^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640946169 5000000000 42991610643251 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5281892233/10000000000 : ℝ)^4199 ≤ (10747902378243/25000000000000 : ℝ)^3175 := by
    have hnat : (5281892233 : ℕ)^4199*25000000000000^3175 ≤ 10747902378243^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281892233 10000000000 10747902378243 25000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-7072991/31250000 : ℝ), (2640946169/5000000000 : ℝ), (5281892233/10000000000 : ℝ)] ![(14016779827641/100000000000000 : ℝ), (42991610643251/100000000000000 : ℝ), (10747902378243/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-7072991/31250000 : ℝ)|^4199 ≤ (14016779827641/100000000000000 : ℝ)^3175
        have hw : |(-7072991/31250000 : ℝ)|=(7072991/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640946169/5000000000 : ℝ)|^4199 ≤ (42991610643251/100000000000000 : ℝ)^3175
        have hw : |(2640946169/5000000000 : ℝ)|=(2640946169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5281892233/10000000000 : ℝ)|^4199 ≤ (10747902378243/25000000000000 : ℝ)^3175
        have hw : |(5281892233/10000000000 : ℝ)|=(5281892233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_box_5 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1072497921/2000000000 : ℝ)*x 0 + (-2156342779/10000000000 : ℝ)*x 1 + (211275679/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072497921/2000000000 : ℝ)^4199 ≤ (1754453295897/4000000000000 : ℝ)^3175 := by
    have hnat : (1072497921 : ℕ)^4199*4000000000000^3175 ≤ 1754453295897^3175*2000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072497921 2000000000 1754453295897 4000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2156342779/10000000000 : ℝ)^4199 ≤ (6573530426631/50000000000000 : ℝ)^3175 := by
    have hnat : (2156342779 : ℕ)^4199*50000000000000^3175 ≤ 6573530426631^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156342779 10000000000 6573530426631 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (211275679/400000000 : ℝ)^4199 ≤ (8598321347143/20000000000000 : ℝ)^3175 := by
    have hnat : (211275679 : ℕ)^4199*20000000000000^3175 ≤ 8598321347143^3175*400000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211275679 400000000 8598321347143 20000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072497921/2000000000 : ℝ), (-2156342779/10000000000 : ℝ), (211275679/400000000 : ℝ)] ![(1754453295897/4000000000000 : ℝ), (6573530426631/50000000000000 : ℝ), (8598321347143/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072497921/2000000000 : ℝ)|^4199 ≤ (1754453295897/4000000000000 : ℝ)^3175
        have hw : |(1072497921/2000000000 : ℝ)|=(1072497921/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2156342779/10000000000 : ℝ)|^4199 ≤ (6573530426631/50000000000000 : ℝ)^3175
        have hw : |(-2156342779/10000000000 : ℝ)|=(2156342779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(211275679/400000000 : ℝ)|^4199 ≤ (8598321347143/20000000000000 : ℝ)^3175
        have hw : |(211275679/400000000 : ℝ)|=(211275679/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_box_6 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5362489221/10000000000 : ℝ)*x 0 + (132047311/250000000 : ℝ)*x 1 + (-2156342673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362489221/10000000000 : ℝ)^4199 ≤ (8772265648719/20000000000000 : ℝ)^3175 := by
    have hnat : (5362489221 : ℕ)^4199*20000000000000^3175 ≤ 8772265648719^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362489221 10000000000 8772265648719 20000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (132047311/250000000 : ℝ)^4199 ≤ (10747902935309/25000000000000 : ℝ)^3175 := by
    have hnat : (132047311 : ℕ)^4199*25000000000000^3175 ≤ 10747902935309^3175*250000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132047311 250000000 10747902935309 25000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2156342673/10000000000 : ℝ)^4199 ≤ (1643382499819/12500000000000 : ℝ)^3175 := by
    have hnat : (2156342673 : ℕ)^4199*12500000000000^3175 ≤ 1643382499819^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156342673 10000000000 1643382499819 12500000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362489221/10000000000 : ℝ), (132047311/250000000 : ℝ), (-2156342673/10000000000 : ℝ)] ![(8772265648719/20000000000000 : ℝ), (10747902935309/25000000000000 : ℝ), (1643382499819/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362489221/10000000000 : ℝ)|^4199 ≤ (8772265648719/20000000000000 : ℝ)^3175
        have hw : |(5362489221/10000000000 : ℝ)|=(5362489221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(132047311/250000000 : ℝ)|^4199 ≤ (10747902935309/25000000000000 : ℝ)^3175
        have hw : |(132047311/250000000 : ℝ)|=(132047311/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2156342673/10000000000 : ℝ)|^4199 ≤ (1643382499819/12500000000000 : ℝ)^3175
        have hw : |(-2156342673/10000000000 : ℝ)|=(2156342673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_box_7 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4248595133/10000000000 : ℝ)*x 0 + (2205779969/5000000000 : ℝ)*x 1 + (4411560141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4248595133/10000000000 : ℝ)^4199 ≤ (32236445853439/100000000000000 : ℝ)^3175 := by
    have hnat : (4248595133 : ℕ)^4199*100000000000000^3175 ≤ 32236445853439^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4248595133 10000000000 32236445853439 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2205779969/5000000000 : ℝ)^4199 ≤ (16940888017437/50000000000000 : ℝ)^3175 := by
    have hnat : (2205779969 : ℕ)^4199*50000000000000^3175 ≤ 16940888017437^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205779969 5000000000 16940888017437 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4411560141/10000000000 : ℝ)^4199 ≤ (6776355619359/20000000000000 : ℝ)^3175 := by
    have hnat : (4411560141 : ℕ)^4199*20000000000000^3175 ≤ 6776355619359^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4411560141 10000000000 6776355619359 20000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4248595133/10000000000 : ℝ), (2205779969/5000000000 : ℝ), (4411560141/10000000000 : ℝ)] ![(32236445853439/100000000000000 : ℝ), (16940888017437/50000000000000 : ℝ), (6776355619359/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4248595133/10000000000 : ℝ)|^4199 ≤ (32236445853439/100000000000000 : ℝ)^3175
        have hw : |(4248595133/10000000000 : ℝ)|=(4248595133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2205779969/5000000000 : ℝ)|^4199 ≤ (16940888017437/50000000000000 : ℝ)^3175
        have hw : |(2205779969/5000000000 : ℝ)|=(2205779969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4411560141/10000000000 : ℝ)|^4199 ≤ (6776355619359/20000000000000 : ℝ)^3175
        have hw : |(4411560141/10000000000 : ℝ)|=(4411560141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_box_8 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2210780327/10000000000 : ℝ)*x 0 + (5218182697/10000000000 : ℝ)*x 1 + (2692503499/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2210780327/10000000000 : ℝ)^4199 ≤ (3396946057839/25000000000000 : ℝ)^3175 := by
    have hnat : (2210780327 : ℕ)^4199*25000000000000^3175 ≤ 3396946057839^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210780327 10000000000 3396946057839 25000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218182697/10000000000 : ℝ)^4199 ≤ (42307141950929/100000000000000 : ℝ)^3175 := by
    have hnat : (5218182697 : ℕ)^4199*100000000000000^3175 ≤ 42307141950929^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218182697 10000000000 42307141950929 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2692503499/5000000000 : ℝ)^4199 ≤ (689141778159/1562500000000 : ℝ)^3175 := by
    have hnat : (2692503499 : ℕ)^4199*1562500000000^3175 ≤ 689141778159^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692503499 5000000000 689141778159 1562500000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2210780327/10000000000 : ℝ), (5218182697/10000000000 : ℝ), (2692503499/5000000000 : ℝ)] ![(3396946057839/25000000000000 : ℝ), (42307141950929/100000000000000 : ℝ), (689141778159/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2210780327/10000000000 : ℝ)|^4199 ≤ (3396946057839/25000000000000 : ℝ)^3175
        have hw : |(-2210780327/10000000000 : ℝ)|=(2210780327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218182697/10000000000 : ℝ)|^4199 ≤ (42307141950929/100000000000000 : ℝ)^3175
        have hw : |(5218182697/10000000000 : ℝ)|=(5218182697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2692503499/5000000000 : ℝ)|^4199 ≤ (689141778159/1562500000000 : ℝ)^3175
        have hw : |(2692503499/5000000000 : ℝ)|=(2692503499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_box_9 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1322434571/2500000000 : ℝ)*x 0 + (-2115511739/10000000000 : ℝ)*x 1 + (5385006973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322434571/2500000000 : ℝ)^4199 ≤ (43076089030743/100000000000000 : ℝ)^3175 := by
    have hnat : (1322434571 : ℕ)^4199*100000000000000^3175 ≤ 43076089030743^3175*2500000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322434571 2500000000 43076089030743 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2115511739/10000000000 : ℝ)^4199 ≤ (12818837424739/100000000000000 : ℝ)^3175 := by
    have hnat : (2115511739 : ℕ)^4199*100000000000000^3175 ≤ 12818837424739^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115511739 10000000000 12818837424739 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5385006973/10000000000 : ℝ)^4199 ≤ (44105073531379/100000000000000 : ℝ)^3175 := by
    have hnat : (5385006973 : ℕ)^4199*100000000000000^3175 ≤ 44105073531379^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385006973 10000000000 44105073531379 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322434571/2500000000 : ℝ), (-2115511739/10000000000 : ℝ), (5385006973/10000000000 : ℝ)] ![(43076089030743/100000000000000 : ℝ), (12818837424739/100000000000000 : ℝ), (44105073531379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322434571/2500000000 : ℝ)|^4199 ≤ (43076089030743/100000000000000 : ℝ)^3175
        have hw : |(1322434571/2500000000 : ℝ)|=(1322434571/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2115511739/10000000000 : ℝ)|^4199 ≤ (12818837424739/100000000000000 : ℝ)^3175
        have hw : |(-2115511739/10000000000 : ℝ)|=(2115511739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5385006973/10000000000 : ℝ)|^4199 ≤ (44105073531379/100000000000000 : ℝ)^3175
        have hw : |(5385006973/10000000000 : ℝ)|=(5385006973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_box_10 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165304323/312500000 : ℝ)*x 0 + (1346251751/2500000000 : ℝ)*x 1 + (-528877907/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165304323/312500000 : ℝ)^4199 ≤ (2692255599423/6250000000000 : ℝ)^3175 := by
    have hnat : (165304323 : ℕ)^4199*6250000000000^3175 ≤ 2692255599423^3175*312500000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165304323 312500000 2692255599423 6250000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1346251751/2500000000 : ℝ)^4199 ≤ (1378283558349/3125000000000 : ℝ)^3175 := by
    have hnat : (1346251751 : ℕ)^4199*3125000000000^3175 ≤ 1378283558349^3175*2500000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346251751 2500000000 1378283558349 3125000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (528877907/2500000000 : ℝ)^4199 ≤ (6409418267607/50000000000000 : ℝ)^3175 := by
    have hnat : (528877907 : ℕ)^4199*50000000000000^3175 ≤ 6409418267607^3175*2500000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528877907 2500000000 6409418267607 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165304323/312500000 : ℝ), (1346251751/2500000000 : ℝ), (-528877907/2500000000 : ℝ)] ![(2692255599423/6250000000000 : ℝ), (1378283558349/3125000000000 : ℝ), (6409418267607/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165304323/312500000 : ℝ)|^4199 ≤ (2692255599423/6250000000000 : ℝ)^3175
        have hw : |(165304323/312500000 : ℝ)|=(165304323/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1346251751/2500000000 : ℝ)|^4199 ≤ (1378283558349/3125000000000 : ℝ)^3175
        have hw : |(1346251751/2500000000 : ℝ)|=(1346251751/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-528877907/2500000000 : ℝ)|^4199 ≤ (6409418267607/50000000000000 : ℝ)^3175
        have hw : |(-528877907/2500000000 : ℝ)|=(528877907/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_box_11 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (280281959/625000000 : ℝ)*x 0 + (4293481697/10000000000 : ℝ)*x 1 + (429348183/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (280281959/625000000 : ℝ)^4199 ≤ (34624730309013/100000000000000 : ℝ)^3175 := by
    have hnat : (280281959 : ℕ)^4199*100000000000000^3175 ≤ 34624730309013^3175*625000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280281959 625000000 34624730309013 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4293481697/10000000000 : ℝ)^4199 ≤ (32687634168751/100000000000000 : ℝ)^3175 := by
    have hnat : (4293481697 : ℕ)^4199*100000000000000^3175 ≤ 32687634168751^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4293481697 10000000000 32687634168751 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (429348183/1000000000 : ℝ)^4199 ≤ (4085954438487/12500000000000 : ℝ)^3175 := by
    have hnat : (429348183 : ℕ)^4199*12500000000000^3175 ≤ 4085954438487^3175*1000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429348183 1000000000 4085954438487 12500000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(280281959/625000000 : ℝ), (4293481697/10000000000 : ℝ), (429348183/1000000000 : ℝ)] ![(34624730309013/100000000000000 : ℝ), (32687634168751/100000000000000 : ℝ), (4085954438487/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(280281959/625000000 : ℝ)|^4199 ≤ (34624730309013/100000000000000 : ℝ)^3175
        have hw : |(280281959/625000000 : ℝ)|=(280281959/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4293481697/10000000000 : ℝ)|^4199 ≤ (32687634168751/100000000000000 : ℝ)^3175
        have hw : |(4293481697/10000000000 : ℝ)|=(4293481697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(429348183/1000000000 : ℝ)|^4199 ≤ (4085954438487/12500000000000 : ℝ)^3175
        have hw : |(429348183/1000000000 : ℝ)|=(429348183/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_box_12 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-206512299/1000000000 : ℝ)*x 0 + (339866921/625000000 : ℝ)*x 1 + (5273827057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (206512299/1000000000 : ℝ)^4199 ≤ (12416594433493/100000000000000 : ℝ)^3175 := by
    have hnat : (206512299 : ℕ)^4199*100000000000000^3175 ≤ 12416594433493^3175*1000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206512299 1000000000 12416594433493 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339866921/625000000 : ℝ)^4199 ≤ (44678592723847/100000000000000 : ℝ)^3175 := by
    have hnat : (339866921 : ℕ)^4199*100000000000000^3175 ≤ 44678592723847^3175*625000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339866921 625000000 44678592723847 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5273827057/10000000000 : ℝ)^4199 ≤ (42904812820939/100000000000000 : ℝ)^3175 := by
    have hnat : (5273827057 : ℕ)^4199*100000000000000^3175 ≤ 42904812820939^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273827057 10000000000 42904812820939 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-206512299/1000000000 : ℝ), (339866921/625000000 : ℝ), (5273827057/10000000000 : ℝ)] ![(12416594433493/100000000000000 : ℝ), (44678592723847/100000000000000 : ℝ), (42904812820939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-206512299/1000000000 : ℝ)|^4199 ≤ (12416594433493/100000000000000 : ℝ)^3175
        have hw : |(-206512299/1000000000 : ℝ)|=(206512299/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(339866921/625000000 : ℝ)|^4199 ≤ (44678592723847/100000000000000 : ℝ)^3175
        have hw : |(339866921/625000000 : ℝ)|=(339866921/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5273827057/10000000000 : ℝ)|^4199 ≤ (42904812820939/100000000000000 : ℝ)^3175
        have hw : |(5273827057/10000000000 : ℝ)|=(5273827057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_box_13 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2684088699/5000000000 : ℝ)*x 0 + (-1079737239/5000000000 : ℝ)*x 1 + (527382699/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684088699/5000000000 : ℝ)^4199 ≤ (43922869287321/100000000000000 : ℝ)^3175 := by
    have hnat : (2684088699 : ℕ)^4199*100000000000000^3175 ≤ 43922869287321^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684088699 5000000000 43922869287321 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1079737239/5000000000 : ℝ)^4199 ≤ (6586159302781/50000000000000 : ℝ)^3175 := by
    have hnat : (1079737239 : ℕ)^4199*50000000000000^3175 ≤ 6586159302781^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079737239 5000000000 6586159302781 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (527382699/1000000000 : ℝ)^4199 ≤ (42904812100069/100000000000000 : ℝ)^3175 := by
    have hnat : (527382699 : ℕ)^4199*100000000000000^3175 ≤ 42904812100069^3175*1000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527382699 1000000000 42904812100069 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684088699/5000000000 : ℝ), (-1079737239/5000000000 : ℝ), (527382699/1000000000 : ℝ)] ![(43922869287321/100000000000000 : ℝ), (6586159302781/50000000000000 : ℝ), (42904812100069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684088699/5000000000 : ℝ)|^4199 ≤ (43922869287321/100000000000000 : ℝ)^3175
        have hw : |(2684088699/5000000000 : ℝ)|=(2684088699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1079737239/5000000000 : ℝ)|^4199 ≤ (6586159302781/50000000000000 : ℝ)^3175
        have hw : |(-1079737239/5000000000 : ℝ)|=(1079737239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(527382699/1000000000 : ℝ)|^4199 ≤ (42904812100069/100000000000000 : ℝ)^3175
        have hw : |(527382699/1000000000 : ℝ)|=(527382699/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_box_14 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5368177673/10000000000 : ℝ)*x 0 + (8438123/16000000 : ℝ)*x 1 + (-2159474261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368177673/10000000000 : ℝ)^4199 ≤ (43922872263087/100000000000000 : ℝ)^3175 := by
    have hnat : (5368177673 : ℕ)^4199*100000000000000^3175 ≤ 43922872263087^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368177673 10000000000 43922872263087 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8438123/16000000 : ℝ)^4199 ≤ (21452405431377/50000000000000 : ℝ)^3175 := by
    have hnat : (8438123 : ℕ)^4199*50000000000000^3175 ≤ 21452405431377^3175*16000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8438123 16000000 21452405431377 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2159474261/10000000000 : ℝ)^4199 ≤ (6586158427503/50000000000000 : ℝ)^3175 := by
    have hnat : (2159474261 : ℕ)^4199*50000000000000^3175 ≤ 6586158427503^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159474261 10000000000 6586158427503 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368177673/10000000000 : ℝ), (8438123/16000000 : ℝ), (-2159474261/10000000000 : ℝ)] ![(43922872263087/100000000000000 : ℝ), (21452405431377/50000000000000 : ℝ), (6586158427503/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368177673/10000000000 : ℝ)|^4199 ≤ (43922872263087/100000000000000 : ℝ)^3175
        have hw : |(5368177673/10000000000 : ℝ)|=(5368177673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8438123/16000000 : ℝ)|^4199 ≤ (21452405431377/50000000000000 : ℝ)^3175
        have hw : |(8438123/16000000 : ℝ)|=(8438123/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2159474261/10000000000 : ℝ)|^4199 ≤ (6586158427503/50000000000000 : ℝ)^3175
        have hw : |(-2159474261/10000000000 : ℝ)|=(2159474261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_box_15 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1057472373/2500000000 : ℝ)*x 0 + (884158131/2000000000 : ℝ)*x 1 + (4420789999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057472373/2500000000 : ℝ)^4199 ≤ (16024436975321/50000000000000 : ℝ)^3175 := by
    have hnat : (1057472373 : ℕ)^4199*50000000000000^3175 ≤ 16024436975321^3175*2500000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057472373 2500000000 16024436975321 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (884158131/2000000000 : ℝ)^4199 ≤ (16987783176599/50000000000000 : ℝ)^3175 := by
    have hnat : (884158131 : ℕ)^4199*50000000000000^3175 ≤ 16987783176599^3175*2000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      884158131 2000000000 16987783176599 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4420789999/10000000000 : ℝ)^4199 ≤ (33975559685549/100000000000000 : ℝ)^3175 := by
    have hnat : (4420789999 : ℕ)^4199*100000000000000^3175 ≤ 33975559685549^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4420789999 10000000000 33975559685549 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057472373/2500000000 : ℝ), (884158131/2000000000 : ℝ), (4420789999/10000000000 : ℝ)] ![(16024436975321/50000000000000 : ℝ), (16987783176599/50000000000000 : ℝ), (33975559685549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057472373/2500000000 : ℝ)|^4199 ≤ (16024436975321/50000000000000 : ℝ)^3175
        have hw : |(1057472373/2500000000 : ℝ)|=(1057472373/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(884158131/2000000000 : ℝ)|^4199 ≤ (16987783176599/50000000000000 : ℝ)^3175
        have hw : |(884158131/2000000000 : ℝ)|=(884158131/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4420789999/10000000000 : ℝ)|^4199 ≤ (33975559685549/100000000000000 : ℝ)^3175
        have hw : |(4420789999/10000000000 : ℝ)|=(4420789999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1205_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15070439/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3521/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5717/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(389/625 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(14837/25000 : ℝ) ∧ (79999/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (16653/20000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3521/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5717/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3521/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5717/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3521/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5717/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3521/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5717/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3521/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5717/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3521/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5717/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5717/50000 : ℝ) ^ (8397/2048 : ℝ) ≤ (13756900541607333/100000000000000000000 : ℝ) := by
    have hpowers : (5717/50000 : ℝ)^8397 ≤ (13756900541607333/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5717 : ℕ)^8397*100000000000000000000^2048 ≤ 13756900541607333^2048*50000^8397 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5717 50000 13756900541607333 100000000000000000000 8397 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5717/50000 : ℝ)) (X := (13756900541607333/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3521/25000 : ℝ) ^ (8397/2048 : ℝ) ≤ (32336538982115309/100000000000000000000 : ℝ) := by
    have hpowers : (3521/25000 : ℝ)^8397 ≤ (32336538982115309/100000000000000000000 : ℝ)^2048 := by
      have hnat : (3521 : ℕ)^8397*100000000000000000000^2048 ≤ 32336538982115309^2048*25000^8397 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3521 25000 32336538982115309 100000000000000000000 8397 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3521/25000 : ℝ)) (X := (32336538982115309/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013756900541607333/50000000000000000000 : ℝ) ≤ (10000670982546377/10000000000000000 : ℝ) ^ (8397/2048 : ℝ) := by
    have hpowers : (50013756900541607333/50000000000000000000 : ℝ)^2048 ≤ (10000670982546377/10000000000000000 : ℝ)^8397 := by
      have hnat : (50013756900541607333 : ℕ)^2048*10000000000000000^8397 ≤ 10000670982546377^8397*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013756900541607333 50000000000000000000 10000670982546377 10000000000000000 2048 8397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000670982546377/10000000000000000 : ℝ)) (X := (50013756900541607333/50000000000000000000 : ℝ)) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023046719761861321/50000000000000000000 : ℝ) ≤ (2500281001901957/2500000000000000 : ℝ) ^ (8397/2048 : ℝ) := by
    have hpowers : (50023046719761861321/50000000000000000000 : ℝ)^2048 ≤ (2500281001901957/2500000000000000 : ℝ)^8397 := by
      have hnat : (50023046719761861321 : ℕ)^2048*2500000000000000^8397 ≤ 2500281001901957^8397*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023046719761861321 50000000000000000000 2500281001901957 2500000000000000 2048 8397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500281001901957/2500000000000000 : ℝ)) (X := (50023046719761861321/50000000000000000000 : ℝ)) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032336538982115309/50000000000000000000 : ℝ) ≤ (10001577032669279/10000000000000000 : ℝ) ^ (8397/2048 : ℝ) := by
    have hpowers : (50032336538982115309/50000000000000000000 : ℝ)^2048 ≤ (10001577032669279/10000000000000000 : ℝ)^8397 := by
      have hnat : (50032336538982115309 : ℕ)^2048*10000000000000000^8397 ≤ 10001577032669279^8397*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032336538982115309 50000000000000000000 10001577032669279 10000000000000000 2048 8397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001577032669279/10000000000000000 : ℝ)) (X := (50032336538982115309/50000000000000000000 : ℝ)) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13756900541607333/100000000000000000000 : ℝ) ≤ ((13245709163321318791/13250000000000000000 : ℝ)+2*(453025061451/265000000000000 : ℝ)*(5717/50000 : ℝ))^(8397/2048 : ℝ) := by
    rw [show (13245709163321318791/13250000000000000000 : ℝ)+2*(453025061451/265000000000000 : ℝ)*(5717/50000 : ℝ)=(10000670982546377/10000000000000000 : ℝ) by norm_num, show 1+2*(13756900541607333/100000000000000000000 : ℝ)=(50013756900541607333/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32336538982115309/100000000000000000000 : ℝ)+(13756900541607333/100000000000000000000 : ℝ) ≤ ((13245709163321318791/13250000000000000000 : ℝ)+(453025061451/265000000000000 : ℝ)*((3521/25000 : ℝ)+(5717/50000 : ℝ)))^(8397/2048 : ℝ) := by
    rw [show (13245709163321318791/13250000000000000000 : ℝ)+(453025061451/265000000000000 : ℝ)*((3521/25000 : ℝ)+(5717/50000 : ℝ))=(2500281001901957/2500000000000000 : ℝ) by norm_num, show 1+(32336538982115309/100000000000000000000 : ℝ)+(13756900541607333/100000000000000000000 : ℝ)=(50023046719761861321/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32336538982115309/100000000000000000000 : ℝ) ≤ ((13245709163321318791/13250000000000000000 : ℝ)+2*(453025061451/265000000000000 : ℝ)*(3521/25000 : ℝ))^(8397/2048 : ℝ) := by
    rw [show (13245709163321318791/13250000000000000000 : ℝ)+2*(453025061451/265000000000000 : ℝ)*(3521/25000 : ℝ)=(10001577032669279/10000000000000000 : ℝ) by norm_num, show 1+2*(32336538982115309/100000000000000000000 : ℝ)=(50032336538982115309/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13245709163321318791/13250000000000000000 : ℝ)*(X 1 0+X 2 0)+(453025061451/265000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8397/2048 : ℝ)) (lo := (5717/50000 : ℝ)) (hi := (3521/25000 : ℝ)) (c := (13245709163321318791/13250000000000000000 : ℝ)) (alpha := (453025061451/265000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13245709163321318791/13250000000000000000 : ℝ)*(X 0 1+X 2 1)+(453025061451/265000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8397/2048 : ℝ)) (lo := (5717/50000 : ℝ)) (hi := (3521/25000 : ℝ)) (c := (13245709163321318791/13250000000000000000 : ℝ)) (alpha := (453025061451/265000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13245709163321318791/13250000000000000000 : ℝ)*(X 0 2+X 1 2)+(453025061451/265000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8397/2048 : ℝ)) (lo := (5717/50000 : ℝ)) (hi := (3521/25000 : ℝ)) (c := (13245709163321318791/13250000000000000000 : ℝ)) (alpha := (453025061451/265000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2012264849/10000000000 : ℝ)*X 0 0+(2687697441/5000000000 : ℝ)*X 0 1+(2687697381/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((132413069/250000000 : ℝ)*X 1 0+(-2119379913/10000000000 : ℝ)*X 1 1+(1343848663/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5296522903/10000000000 : ℝ)*X 2 0+(5375394789/10000000000 : ℝ)*X 2 1+(-423875907/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4462766497/10000000000 : ℝ)*X 0 0+(1076123487/2500000000 : ℝ)*X 0 1+(269030969/625000000 : ℝ)*X 0 2+(4462766497/10000000000 : ℝ)*X 1 0+(1076123487/2500000000 : ℝ)*X 1 1+(269030969/625000000 : ℝ)*X 1 2+(4462766497/10000000000 : ℝ)*X 2 0+(1076123487/2500000000 : ℝ)*X 2 1+(269030969/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-7072991/31250000 : ℝ)*X 0 0+(2640946169/5000000000 : ℝ)*X 0 1+(5281892233/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1072497921/2000000000 : ℝ)*X 1 0+(-2156342779/10000000000 : ℝ)*X 1 1+(211275679/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5362489221/10000000000 : ℝ)*X 2 0+(132047311/250000000 : ℝ)*X 2 1+(-2156342673/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4248595133/10000000000 : ℝ)*X 0 0+(2205779969/5000000000 : ℝ)*X 0 1+(4411560141/10000000000 : ℝ)*X 0 2+(4248595133/10000000000 : ℝ)*X 1 0+(2205779969/5000000000 : ℝ)*X 1 1+(4411560141/10000000000 : ℝ)*X 1 2+(4248595133/10000000000 : ℝ)*X 2 0+(2205779969/5000000000 : ℝ)*X 2 1+(4411560141/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2210780327/10000000000 : ℝ)*X 0 0+(5218182697/10000000000 : ℝ)*X 0 1+(2692503499/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1322434571/2500000000 : ℝ)*X 1 0+(-2115511739/10000000000 : ℝ)*X 1 1+(5385006973/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((165304323/312500000 : ℝ)*X 2 0+(1346251751/2500000000 : ℝ)*X 2 1+(-528877907/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((280281959/625000000 : ℝ)*X 0 0+(4293481697/10000000000 : ℝ)*X 0 1+(429348183/1000000000 : ℝ)*X 0 2+(280281959/625000000 : ℝ)*X 1 0+(4293481697/10000000000 : ℝ)*X 1 1+(429348183/1000000000 : ℝ)*X 1 2+(280281959/625000000 : ℝ)*X 2 0+(4293481697/10000000000 : ℝ)*X 2 1+(429348183/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-206512299/1000000000 : ℝ)*X 0 0+(339866921/625000000 : ℝ)*X 0 1+(5273827057/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2684088699/5000000000 : ℝ)*X 1 0+(-1079737239/5000000000 : ℝ)*X 1 1+(527382699/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5368177673/10000000000 : ℝ)*X 2 0+(8438123/16000000 : ℝ)*X 2 1+(-2159474261/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1057472373/2500000000 : ℝ)*X 0 0+(884158131/2000000000 : ℝ)*X 0 1+(4420789999/10000000000 : ℝ)*X 0 2+(1057472373/2500000000 : ℝ)*X 1 0+(884158131/2000000000 : ℝ)*X 1 1+(4420789999/10000000000 : ℝ)*X 1 2+(1057472373/2500000000 : ℝ)*X 2 0+(884158131/2000000000 : ℝ)*X 2 1+(4420789999/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-389/625 : ℝ) ≤ (-515404385869006344493234347/828125000000000000000000000 : ℝ) := by norm_num
    linear_combination (43778851/100000000000000 : ℝ)*(upper0) + (2141357/10000000000000 : ℝ)*(upper1) + (14242051/25000000000000 : ℝ)*(upper2) + (23315617/25000000000000 : ℝ)*(upper3) + (98146521/100000000000000 : ℝ)*(upper5) + (1986389678984933/50000000000000 : ℝ)*(major0) + (1986389678984933/50000000000000 : ℝ)*(major1) + (1986389678984933/50000000000000 : ℝ)*(major2) + (22391566271/100000000000000 : ℝ)*(sp1) + (11796607569/100000000000000 : ℝ)*(sp3) + (2665082060301223/50000000000000 : ℝ)*(sp4) + (213205669161447/4000000000000 : ℝ)*(sp5) + (2665082060301223/50000000000000 : ℝ)*(sp6) + (1318064317822589/50000000000000 : ℝ)*(sp7) + (2636140432252747/100000000000000 : ℝ)*(f.failure) + (2665082060301223/50000000000000 : ℝ)*(f.sum) + (3807874351523/1656250000000000000000000000 : ℝ)*base66 + (14021566344517926003/662500000000000000000000000000000 : ℝ)*base67 + (1986084385532073997/662500000000000000000000000000000 : ℝ)*base70 + (4905835864092926003/662500000000000000000000000000000 : ℝ)*base71 + (369877051707283/6625000000000000000000000000 : ℝ)*base73 + (45344043749869573997/662500000000000000000000000000000 : ℝ)*base76 + (5439184317305426003/662500000000000000000000000000000 : ℝ)*base77 + (12678143943932073997/662500000000000000000000000000000 : ℝ)*base80 + (39124710750717/6625000000000000000000000000 : ℝ)*base82 + (3754067/1000000000000000000000 : ℝ)*base90 + (3754067/1000000000000000000000 : ℝ)*base92 + (3754067/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (14837/25000 : ℝ) ≤ (3709391242704059909151095581299/6250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (263942371/100000000000000 : ℝ)*(upper0) + (11970157/25000000000000 : ℝ)*(lower1) + (53512313/50000000000000 : ℝ)*(lower3) + (11455251/12500000000000 : ℝ)*(upper4) + (48256239/25000000000000 : ℝ)*(upper5) + (2018972832366287/50000000000000 : ℝ)*(major0) + (2018972832366287/50000000000000 : ℝ)*(major1) + (2018972832366287/50000000000000 : ℝ)*(major2) + (537672633028619/10000000000000 : ℝ)*(sp0) + (537672633028619/10000000000000 : ℝ)*(sp1) + (2688362046782803/50000000000000 : ℝ)*(sp2) + (1339649333133607/50000000000000 : ℝ)*(sp3) + (279590073/12500000000000 : ℝ)*(sp6) + (414564753/500000000000 : ℝ)*(sp11) + (1339690789608907/50000000000000 : ℝ)*(f.failure) + (537672633028619/10000000000000 : ℝ)*(f.sum) + (714386089329/125000000000000000000000000 : ℝ)*base65 + (8900912550563189/12500000000000000000000000000000 : ℝ)*base67 + (1720977512750563189/12500000000000000000000000000000 : ℝ)*base69 + (136161518725563189/12500000000000000000000000000000 : ℝ)*base71 + (402075195079/125000000000000000000000000 : ℝ)*base73 + (675121024000563189/12500000000000000000000000000000 : ℝ)*base75 + (54258832700563189/12500000000000000000000000000000 : ℝ)*base77 + (351116756125563189/12500000000000000000000000000000 : ℝ)*base79 + (35018995056421/125000000000000000000000000 : ℝ)*base82 + (3199827/500000000000000000000 : ℝ)*base90 + (3199827/500000000000000000000 : ℝ)*base92 + (3199827/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (79999/100000 : ℝ) ≤ (530009023310507959140133851945891/662500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18448907/100000000000000 : ℝ)*(upper0) + (2553783/50000000000000 : ℝ)*(lower1) + (75848263/100000000000000 : ℝ)*(lower3) + (43270507/100000000000000 : ℝ)*(upper4) + (4505221852490633/100000000000000 : ℝ)*(major0) + (4505221852490633/100000000000000 : ℝ)*(major1) + (4505221852490633/100000000000000 : ℝ)*(major2) + (29001768861/50000000000000 : ℝ)*(sp1) + (75837312193/100000000000000 : ℝ)*(sp2) + (3891755059/12500000000000 : ℝ)*(sp3) + (5994333574396153/100000000000000 : ℝ)*(sp8) + (5994275570858431/100000000000000 : ℝ)*(sp9) + (5994257737083961/100000000000000 : ℝ)*(sp10) + (2989411875874921/100000000000000 : ℝ)*(sp11) + (1494721504957697/50000000000000 : ℝ)*(f.failure) + (5994333574396153/100000000000000 : ℝ)*(f.sum) + (17789919106767/13250000000000000000000000000 : ℝ)*base66 + (9773454376091465297/1325000000000000000000000000000000 : ℝ)*base68 + (19632730428058534703/1325000000000000000000000000000000 : ℝ)*base69 + (2062444014058534703/1325000000000000000000000000000000 : ℝ)*base71 + (11660904639983/13250000000000000000000000000 : ℝ)*base73 + (10462904405833534703/1325000000000000000000000000000000 : ℝ)*base75 + (5717244446483534703/1325000000000000000000000000000000 : ℝ)*base77 + (5442639512091465297/1325000000000000000000000000000000 : ℝ)*base80 + (84104354034733/13250000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (5218983/500000000000000000000 : ℝ)*base89 + (5218983/500000000000000000000 : ℝ)*base91 + (5218983/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-16653/20000 : ℝ) ≤ (-137902742380785062272922752899129/165625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19723399/100000000000000 : ℝ)*(lower0) + (70151681/50000000000000 : ℝ)*(upper1) + (10477381/6250000000000 : ℝ)*(lower2) + (44415431/50000000000000 : ℝ)*(upper3) + (183511977/100000000000000 : ℝ)*(upper5) + (1135130355414373/25000000000000 : ℝ)*(major0) + (1135130355414373/25000000000000 : ℝ)*(major1) + (1135130355414373/25000000000000 : ℝ)*(major2) + (2635965811/20000000000000 : ℝ)*(sp4) + (194063204283/100000000000000 : ℝ)*(sp7) + (6095917611599899/100000000000000 : ℝ)*(sp12) + (3047965395714477/50000000000000 : ℝ)*(sp13) + (3047965395714477/50000000000000 : ℝ)*(sp14) + (753167999931731/25000000000000 : ℝ)*(sp15) + (376608257866401/12500000000000 : ℝ)*(f.failure) + (3047965395714477/50000000000000 : ℝ)*(f.sum) + (21993799574679/6625000000000000000000000000 : ℝ)*base66 + (2877050913747533043/331250000000000000000000000000000 : ℝ)*base67 + (463176477641283043/331250000000000000000000000000000 : ℝ)*base69 + (1671111103853783043/331250000000000000000000000000000 : ℝ)*base71 + (307004641231/414062500000000000000000000 : ℝ)*base73 + (1789577200728783043/331250000000000000000000000000000 : ℝ)*base75 + (860620174583716957/331250000000000000000000000000000 : ℝ)*base78 + (20506351163052466957/331250000000000000000000000000000 : ℝ)*base80 + (26554624130179/6625000000000000000000000000 : ℝ)*base82 + (1420039/125000000000000000000 : ℝ)*base89 + (1420039/125000000000000000000 : ℝ)*base91 + (1420039/125000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1205_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15070439/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3521/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5717/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(389/625 : ℝ) ≤ X j i ∧ X j i ≤ -(14837/25000 : ℝ) else (79999/100000 : ℝ) ≤ X j i ∧ X j i ≤ (16653/20000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1205_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1205_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15070439/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3521/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5717/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(389/625 : ℝ) ≤ X j i ∧ X j i ≤ -(14837/25000 : ℝ) else (79999/100000 : ℝ) ≤ X j i ∧ X j i ≤ (16653/20000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1205_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15070439/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3521/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5717/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(389/625 : ℝ) ≤ X j i ∧ X j i ≤ -(14837/25000 : ℝ) else (79999/100000 : ℝ) ≤ X j i ∧ X j i ≤ (16653/20000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1205_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
