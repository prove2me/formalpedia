-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1054_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:58:04.226994+00:00
-- url     : https://prove2.me/submissions/33d3a505-de98-44ef-9b1d-6b681f69f78b

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
theorem support_rectangle_w1054_s0_0 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-959989829/5000000000 : ℝ)*x 0 + (1214978567/2000000000 : ℝ)*x 1 + (2384621247/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (959989829/5000000000 : ℝ)^8247 ≤ (1113051166851/10000000000000 : ℝ)^6199 := by
    have hnat : (959989829 : ℕ)^8247*10000000000000^6199 ≤ 1113051166851^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      959989829 5000000000 1113051166851 10000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1214978567/2000000000 : ℝ)^8247 ≤ (12881457768621/25000000000000 : ℝ)^6199 := by
    have hnat : (1214978567 : ℕ)^8247*25000000000000^6199 ≤ 12881457768621^6199*2000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1214978567 2000000000 12881457768621 25000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2384621247/5000000000 : ℝ)^8247 ≤ (37343657239617/100000000000000 : ℝ)^6199 := by
    have hnat : (2384621247 : ℕ)^8247*100000000000000^6199 ≤ 37343657239617^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2384621247 5000000000 37343657239617 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-959989829/5000000000 : ℝ), (1214978567/2000000000 : ℝ), (2384621247/5000000000 : ℝ)] ![(1113051166851/10000000000000 : ℝ), (12881457768621/25000000000000 : ℝ), (37343657239617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-959989829/5000000000 : ℝ)|^8247 ≤ (1113051166851/10000000000000 : ℝ)^6199
        have hw : |(-959989829/5000000000 : ℝ)|=(959989829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1214978567/2000000000 : ℝ)|^8247 ≤ (12881457768621/25000000000000 : ℝ)^6199
        have hw : |(1214978567/2000000000 : ℝ)|=(1214978567/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2384621247/5000000000 : ℝ)|^8247 ≤ (37343657239617/100000000000000 : ℝ)^6199
        have hw : |(2384621247/5000000000 : ℝ)|=(2384621247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s0_1 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1380436621/2500000000 : ℝ)*x 0 + (-1335938799/5000000000 : ℝ)*x 1 + (4769244583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1380436621/2500000000 : ℝ)^8247 ≤ (2269001356749/5000000000000 : ℝ)^6199 := by
    have hnat : (1380436621 : ℕ)^8247*5000000000000^6199 ≤ 2269001356749^6199*2500000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1380436621 2500000000 2269001356749 5000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1335938799/5000000000 : ℝ)^8247 ≤ (8638146924791/50000000000000 : ℝ)^6199 := by
    have hnat : (1335938799 : ℕ)^8247*50000000000000^6199 ≤ 8638146924791^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1335938799 5000000000 8638146924791 50000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4769244583/10000000000 : ℝ)^8247 ≤ (2333979937543/6250000000000 : ℝ)^6199 := by
    have hnat : (4769244583 : ℕ)^8247*6250000000000^6199 ≤ 2333979937543^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4769244583 10000000000 2333979937543 6250000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1380436621/2500000000 : ℝ), (-1335938799/5000000000 : ℝ), (4769244583/10000000000 : ℝ)] ![(2269001356749/5000000000000 : ℝ), (8638146924791/50000000000000 : ℝ), (2333979937543/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1380436621/2500000000 : ℝ)|^8247 ≤ (2269001356749/5000000000000 : ℝ)^6199
        have hw : |(1380436621/2500000000 : ℝ)|=(1380436621/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1335938799/5000000000 : ℝ)|^8247 ≤ (8638146924791/50000000000000 : ℝ)^6199
        have hw : |(-1335938799/5000000000 : ℝ)|=(1335938799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4769244583/10000000000 : ℝ)|^8247 ≤ (2333979937543/6250000000000 : ℝ)^6199
        have hw : |(4769244583/10000000000 : ℝ)|=(4769244583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s0_2 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5521748681/10000000000 : ℝ)*x 0 + (4769243049/10000000000 : ℝ)*x 1 + (-333984583/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5521748681/10000000000 : ℝ)^8247 ≤ (45380051156071/100000000000000 : ℝ)^6199 := by
    have hnat : (5521748681 : ℕ)^8247*100000000000000^6199 ≤ 45380051156071^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5521748681 10000000000 45380051156071 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4769243049/10000000000 : ℝ)^8247 ≤ (466795787763/1250000000000 : ℝ)^6199 := by
    have hnat : (4769243049 : ℕ)^8247*1250000000000^6199 ≤ 466795787763^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4769243049 10000000000 466795787763 1250000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (333984583/1250000000 : ℝ)^8247 ≤ (17276285815149/100000000000000 : ℝ)^6199 := by
    have hnat : (333984583 : ℕ)^8247*100000000000000^6199 ≤ 17276285815149^6199*1250000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      333984583 1250000000 17276285815149 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5521748681/10000000000 : ℝ), (4769243049/10000000000 : ℝ), (-333984583/1250000000 : ℝ)] ![(45380051156071/100000000000000 : ℝ), (466795787763/1250000000000 : ℝ), (17276285815149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5521748681/10000000000 : ℝ)|^8247 ≤ (45380051156071/100000000000000 : ℝ)^6199
        have hw : |(5521748681/10000000000 : ℝ)|=(5521748681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4769243049/10000000000 : ℝ)|^8247 ≤ (466795787763/1250000000000 : ℝ)^6199
        have hw : |(4769243049/10000000000 : ℝ)|=(4769243049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-333984583/1250000000 : ℝ)|^8247 ≤ (17276285815149/100000000000000 : ℝ)^6199
        have hw : |(-333984583/1250000000 : ℝ)|=(333984583/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s0_3 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4208204397/10000000000 : ℝ)*x 0 + (781378331/2500000000 : ℝ)*x 1 + (1419578639/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4208204397/10000000000 : ℝ)^8247 ≤ (123500160893/390625000000 : ℝ)^6199 := by
    have hnat : (4208204397 : ℕ)^8247*390625000000^6199 ≤ 123500160893^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4208204397 10000000000 123500160893 390625000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (781378331/2500000000 : ℝ)^8247 ≤ (10642056579499/50000000000000 : ℝ)^6199 := by
    have hnat : (781378331 : ℕ)^8247*50000000000000^6199 ≤ 10642056579499^6199*2500000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      781378331 2500000000 10642056579499 50000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1419578639/2500000000 : ℝ)^8247 ≤ (4709984563183/10000000000000 : ℝ)^6199 := by
    have hnat : (1419578639 : ℕ)^8247*10000000000000^6199 ≤ 4709984563183^6199*2500000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1419578639 2500000000 4709984563183 10000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4208204397/10000000000 : ℝ), (781378331/2500000000 : ℝ), (1419578639/2500000000 : ℝ)] ![(123500160893/390625000000 : ℝ), (10642056579499/50000000000000 : ℝ), (4709984563183/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4208204397/10000000000 : ℝ)|^8247 ≤ (123500160893/390625000000 : ℝ)^6199
        have hw : |(4208204397/10000000000 : ℝ)|=(4208204397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(781378331/2500000000 : ℝ)|^8247 ≤ (10642056579499/50000000000000 : ℝ)^6199
        have hw : |(781378331/2500000000 : ℝ)|=(781378331/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1419578639/2500000000 : ℝ)|^8247 ≤ (4709984563183/10000000000000 : ℝ)^6199
        have hw : |(1419578639/2500000000 : ℝ)|=(1419578639/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s0_4 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1925387203/10000000000 : ℝ)*x 0 + (4802960139/10000000000 : ℝ)*x 1 + (3019999297/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1925387203/10000000000 : ℝ)^8247 ≤ (349132391497/3125000000000 : ℝ)^6199 := by
    have hnat : (1925387203 : ℕ)^8247*3125000000000^6199 ≤ 349132391497^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1925387203 10000000000 349132391497 3125000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4802960139/10000000000 : ℝ)^8247 ≤ (37695302794649/100000000000000 : ℝ)^6199 := by
    have hnat : (4802960139 : ℕ)^8247*100000000000000^6199 ≤ 37695302794649^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4802960139 10000000000 37695302794649 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3019999297/5000000000 : ℝ)^8247 ≤ (25566230328561/50000000000000 : ℝ)^6199 := by
    have hnat : (3019999297 : ℕ)^8247*50000000000000^6199 ≤ 25566230328561^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3019999297 5000000000 25566230328561 50000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1925387203/10000000000 : ℝ), (4802960139/10000000000 : ℝ), (3019999297/5000000000 : ℝ)] ![(349132391497/3125000000000 : ℝ), (37695302794649/100000000000000 : ℝ), (25566230328561/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1925387203/10000000000 : ℝ)|^8247 ≤ (349132391497/3125000000000 : ℝ)^6199
        have hw : |(-1925387203/10000000000 : ℝ)|=(1925387203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4802960139/10000000000 : ℝ)|^8247 ≤ (37695302794649/100000000000000 : ℝ)^6199
        have hw : |(4802960139/10000000000 : ℝ)|=(4802960139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3019999297/5000000000 : ℝ)|^8247 ≤ (25566230328561/50000000000000 : ℝ)^6199
        have hw : |(3019999297/5000000000 : ℝ)|=(3019999297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s0_5 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (32296501/62500000 : ℝ)*x 0 + (-1401124139/10000000000 : ℝ)*x 1 + (754999709/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (32296501/62500000 : ℝ)^8247 ≤ (41547852993541/100000000000000 : ℝ)^6199 := by
    have hnat : (32296501 : ℕ)^8247*100000000000000^6199 ≤ 41547852993541^6199*62500000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32296501 62500000 41547852993541 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1401124139/10000000000 : ℝ)^8247 ≤ (3659848358953/50000000000000 : ℝ)^6199 := by
    have hnat : (1401124139 : ℕ)^8247*50000000000000^6199 ≤ 3659848358953^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1401124139 10000000000 3659848358953 50000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (754999709/1250000000 : ℝ)^8247 ≤ (6391556284139/12500000000000 : ℝ)^6199 := by
    have hnat : (754999709 : ℕ)^8247*12500000000000^6199 ≤ 6391556284139^6199*1250000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      754999709 1250000000 6391556284139 12500000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(32296501/62500000 : ℝ), (-1401124139/10000000000 : ℝ), (754999709/1250000000 : ℝ)] ![(41547852993541/100000000000000 : ℝ), (3659848358953/50000000000000 : ℝ), (6391556284139/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(32296501/62500000 : ℝ)|^8247 ≤ (41547852993541/100000000000000 : ℝ)^6199
        have hw : |(32296501/62500000 : ℝ)|=(32296501/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1401124139/10000000000 : ℝ)|^8247 ≤ (3659848358953/50000000000000 : ℝ)^6199
        have hw : |(-1401124139/10000000000 : ℝ)|=(1401124139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(754999709/1250000000 : ℝ)|^8247 ≤ (6391556284139/12500000000000 : ℝ)^6199
        have hw : |(754999709/1250000000 : ℝ)|=(754999709/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s0_6 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (41339533/80000000 : ℝ)*x 0 + (3019998431/5000000000 : ℝ)*x 1 + (-1401123197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41339533/80000000 : ℝ)^8247 ≤ (10386967166031/25000000000000 : ℝ)^6199 := by
    have hnat : (41339533 : ℕ)^8247*25000000000000^6199 ≤ 10386967166031^6199*80000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41339533 80000000 10386967166031 25000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3019998431/5000000000 : ℝ)^8247 ≤ (102264882301/200000000000 : ℝ)^6199 := by
    have hnat : (3019998431 : ℕ)^8247*200000000000^6199 ≤ 102264882301^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3019998431 5000000000 102264882301 200000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1401123197/10000000000 : ℝ)^8247 ≤ (1829922542729/25000000000000 : ℝ)^6199 := by
    have hnat : (1401123197 : ℕ)^8247*25000000000000^6199 ≤ 1829922542729^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1401123197 10000000000 1829922542729 25000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41339533/80000000 : ℝ), (3019998431/5000000000 : ℝ), (-1401123197/10000000000 : ℝ)] ![(10386967166031/25000000000000 : ℝ), (102264882301/200000000000 : ℝ), (1829922542729/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41339533/80000000 : ℝ)|^8247 ≤ (10386967166031/25000000000000 : ℝ)^6199
        have hw : |(41339533/80000000 : ℝ)|=(41339533/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3019998431/5000000000 : ℝ)|^8247 ≤ (102264882301/200000000000 : ℝ)^6199
        have hw : |(3019998431/5000000000 : ℝ)|=(3019998431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1401123197/10000000000 : ℝ)|^8247 ≤ (1829922542729/25000000000000 : ℝ)^6199
        have hw : |(-1401123197/10000000000 : ℝ)|=(1401123197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s0_7 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2109391077/5000000000 : ℝ)*x 0 + (14030969/25000000 : ℝ)*x 1 + (3193741711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2109391077/5000000000 : ℝ)^8247 ≤ (31721810285207/100000000000000 : ℝ)^6199 := by
    have hnat : (2109391077 : ℕ)^8247*100000000000000^6199 ≤ 31721810285207^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109391077 5000000000 31721810285207 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (14030969/25000000 : ℝ)^8247 ≤ (23186868566401/50000000000000 : ℝ)^6199 := by
    have hnat : (14030969 : ℕ)^8247*50000000000000^6199 ≤ 23186868566401^6199*25000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14030969 25000000 23186868566401 50000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3193741711/10000000000 : ℝ)^8247 ≤ (21904452562509/100000000000000 : ℝ)^6199 := by
    have hnat : (3193741711 : ℕ)^8247*100000000000000^6199 ≤ 21904452562509^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3193741711 10000000000 21904452562509 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2109391077/5000000000 : ℝ), (14030969/25000000 : ℝ), (3193741711/10000000000 : ℝ)] ![(31721810285207/100000000000000 : ℝ), (23186868566401/50000000000000 : ℝ), (21904452562509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2109391077/5000000000 : ℝ)|^8247 ≤ (31721810285207/100000000000000 : ℝ)^6199
        have hw : |(2109391077/5000000000 : ℝ)|=(2109391077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(14030969/25000000 : ℝ)|^8247 ≤ (23186868566401/50000000000000 : ℝ)^6199
        have hw : |(14030969/25000000 : ℝ)|=(14030969/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3193741711/10000000000 : ℝ)|^8247 ≤ (21904452562509/100000000000000 : ℝ)^6199
        have hw : |(3193741711/10000000000 : ℝ)|=(3193741711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1054_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36939913/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (23/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7039/25000 : ℝ)*pair X 0 0 := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base34 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1, f.sum]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
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
  have hpowlo : (0 : ℝ) ^ (4123/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4123 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4123*1^1024 ≤ 0^1024*1^4123 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4123 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4123/1024 : ℝ) ≤ (499778307704745081/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4123 ≤ (499778307704745081/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4123*20000000000000000000^1024 ≤ 499778307704745081^1024*5^4123 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 499778307704745081 20000000000000000000 4123 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (499778307704745081/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4123/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4123 := by
      have hnat : (1 : ℕ)^1024*1^4123 ≤ 1^4123*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20499778307704745081/20000000000000000000 : ℝ) ≤ (5030744343675547/5000000000000000 : ℝ) ^ (4123/1024 : ℝ) := by
    have hpowers : (20499778307704745081/20000000000000000000 : ℝ)^1024 ≤ (5030744343675547/5000000000000000 : ℝ)^4123 := by
      have hnat : (20499778307704745081 : ℕ)^1024*5000000000000000^4123 ≤ 5030744343675547^4123*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20499778307704745081 20000000000000000000 5030744343675547 5000000000000000 1024 4123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5030744343675547/5000000000000000 : ℝ)) (X := (20499778307704745081/20000000000000000000 : ℝ)) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10499778307704745081/10000000000000000000 : ℝ) ≤ (2530744343675547/2500000000000000 : ℝ) ^ (4123/1024 : ℝ) := by
    have hpowers : (10499778307704745081/10000000000000000000 : ℝ)^1024 ≤ (2530744343675547/2500000000000000 : ℝ)^4123 := by
      have hnat : (10499778307704745081 : ℕ)^1024*2500000000000000^4123 ≤ 2530744343675547^4123*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10499778307704745081 10000000000000000000 2530744343675547 2500000000000000 1024 4123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2530744343675547/2500000000000000 : ℝ)) (X := (10499778307704745081/10000000000000000000 : ℝ)) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(30744343675547/2000000000000000 : ℝ)*(0 : ℝ))^(4123/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(30744343675547/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(499778307704745081/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(30744343675547/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4123/1024 : ℝ) := by
    rw [show (1 : ℝ)+(30744343675547/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5030744343675547/5000000000000000 : ℝ) by norm_num, show 1+(499778307704745081/20000000000000000000 : ℝ)+(0 : ℝ)=(20499778307704745081/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(499778307704745081/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(30744343675547/2000000000000000 : ℝ)*(2/5 : ℝ))^(4123/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(30744343675547/2000000000000000 : ℝ)*(2/5 : ℝ)=(2530744343675547/2500000000000000 : ℝ) by norm_num, show 1+2*(499778307704745081/20000000000000000000 : ℝ)=(10499778307704745081/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(30744343675547/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4123/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30744343675547/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(30744343675547/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4123/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30744343675547/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(30744343675547/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4123/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30744343675547/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-959989829/5000000000 : ℝ)*X 0 0+(1214978567/2000000000 : ℝ)*X 0 1+(2384621247/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1380436621/2500000000 : ℝ)*X 1 0+(-1335938799/5000000000 : ℝ)*X 1 1+(4769244583/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5521748681/10000000000 : ℝ)*X 2 0+(4769243049/10000000000 : ℝ)*X 2 1+(-333984583/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4208204397/10000000000 : ℝ)*X 0 0+(781378331/2500000000 : ℝ)*X 0 1+(1419578639/2500000000 : ℝ)*X 0 2+(4208204397/10000000000 : ℝ)*X 1 0+(781378331/2500000000 : ℝ)*X 1 1+(1419578639/2500000000 : ℝ)*X 1 2+(4208204397/10000000000 : ℝ)*X 2 0+(781378331/2500000000 : ℝ)*X 2 1+(1419578639/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1925387203/10000000000 : ℝ)*X 0 0+(4802960139/10000000000 : ℝ)*X 0 1+(3019999297/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((32296501/62500000 : ℝ)*X 1 0+(-1401124139/10000000000 : ℝ)*X 1 1+(754999709/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((41339533/80000000 : ℝ)*X 2 0+(3019998431/5000000000 : ℝ)*X 2 1+(-1401123197/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2109391077/5000000000 : ℝ)*X 0 0+(14030969/25000000 : ℝ)*X 0 1+(3193741711/10000000000 : ℝ)*X 0 2+(2109391077/5000000000 : ℝ)*X 1 0+(14030969/25000000 : ℝ)*X 1 1+(3193741711/10000000000 : ℝ)*X 1 2+(2109391077/5000000000 : ℝ)*X 2 0+(14030969/25000000 : ℝ)*X 2 1+(3193741711/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (85723822302727172298243/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (341971649/100000000000000 : ℝ)*(base23) + (10669281/6250000000000 : ℝ)*(base24) + (236615647/100000000000000 : ℝ)*(base34) + (450511367/100000000000000 : ℝ)*(base39) + (128784117/50000000000000 : ℝ)*(upper3) + (289408513249067/50000000000000 : ℝ)*(major0) + (72352098735311/12500000000000 : ℝ)*(major1) + (578816575986767/100000000000000 : ℝ)*(major2) + (382952251667859/50000000000000 : ℝ)*(sp0) + (765904831548239/100000000000000 : ℝ)*(sp1) + (95738066595477/12500000000000 : ℝ)*(sp2) + (391727140112509/100000000000000 : ℝ)*(sp3) + (45798437/50000000000000 : ℝ)*(sp4) + (1602249537/100000000000000 : ℝ)*(sp7) + (78345748472409/20000000000000 : ℝ)*(f.failure) + (765905282059607/100000000000000 : ℝ)*(f.sum) + (183128007678503/40000000000000000000000000000 : ℝ)*base66 + (357587787086549/200000000000000000000000000000 : ℝ)*base67 + (3637149665117/25000000000000000000000000000 : ℝ)*base69 + (1345134075913451/200000000000000000000000000000 : ℝ)*base72 + (1016609328384153/200000000000000000000000000000 : ℝ)*base74 + (130187966335351/100000000000000000000000000000 : ℝ)*base76 + (256194770534883/25000000000000000000000000000 : ℝ)*base78 + (738804761535351/100000000000000000000000000000 : ℝ)*base80 + (112034985674883/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (1360417/500000000000000000000 : ℝ)*base89 + (3639583/500000000000000000000 : ℝ)*base92 + (1360417/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (499532103985081861711119/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4034487/3125000000000 : ℝ)*(base1) + (258335067/25000000000000 : ℝ)*(base19) + (641891471/50000000000000 : ℝ)*(base23) + (149023359/100000000000000 : ℝ)*(base45) + (10766827/10000000000000 : ℝ)*(upper3) + (8715029/4000000000000 : ℝ)*(upper5) + (610917959977547/100000000000000 : ℝ)*(major0) + (610917959977547/100000000000000 : ℝ)*(major1) + (610917959977547/100000000000000 : ℝ)*(major2) + (31009801/10000000000000 : ℝ)*(sp2) + (404191019645359/50000000000000 : ℝ)*(sp4) + (404190438423433/50000000000000 : ℝ)*(sp5) + (404190158153091/50000000000000 : ℝ)*(sp6) + (51681714269209/12500000000000 : ℝ)*(sp7) + (51681730407157/12500000000000 : ℝ)*(f.failure) + (404190955093567/50000000000000 : ℝ)*(f.sum) + (71046799543209/100000000000000000000000000000 : ℝ)*base65 + (1049584172543209/200000000000000000000000000000 : ℝ)*base67 + (789117083856791/200000000000000000000000000000 : ℝ)*base70 + (135233963343209/200000000000000000000000000000 : ℝ)*base71 + (465558690343209/100000000000000000000000000000 : ℝ)*base73 + (1238233824143209/200000000000000000000000000000 : ℝ)*base75 + (280971563343209/200000000000000000000000000000 : ℝ)*base77 + (44435458143209/200000000000000000000000000000 : ℝ)*base79 + (17991456856791/100000000000000000000000000000 : ℝ)*base82 + (217659/312500000000000000000 : ℝ)*base90 + (217659/312500000000000000000 : ℝ)*base92 + (217659/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1054_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36939913/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (23/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7039/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1054_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1054_s1_0 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1065484059/5000000000 : ℝ)*x 0 + (2862847097/5000000000 : ℝ)*x 1 + (2491656703/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1065484059/5000000000 : ℝ)^8247 ≤ (12786597088057/100000000000000 : ℝ)^6199 := by
    have hnat : (1065484059 : ℕ)^8247*100000000000000^6199 ≤ 12786597088057^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065484059 5000000000 12786597088057 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2862847097/5000000000 : ℝ)^8247 ≤ (9524680342771/20000000000000 : ℝ)^6199 := by
    have hnat : (2862847097 : ℕ)^8247*20000000000000^6199 ≤ 9524680342771^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2862847097 5000000000 9524680342771 20000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2491656703/5000000000 : ℝ)^8247 ≤ (7918000237091/20000000000000 : ℝ)^6199 := by
    have hnat : (2491656703 : ℕ)^8247*20000000000000^6199 ≤ 7918000237091^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2491656703 5000000000 7918000237091 20000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1065484059/5000000000 : ℝ), (2862847097/5000000000 : ℝ), (2491656703/5000000000 : ℝ)] ![(12786597088057/100000000000000 : ℝ), (9524680342771/20000000000000 : ℝ), (7918000237091/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1065484059/5000000000 : ℝ)|^8247 ≤ (12786597088057/100000000000000 : ℝ)^6199
        have hw : |(-1065484059/5000000000 : ℝ)|=(1065484059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2862847097/5000000000 : ℝ)|^8247 ≤ (9524680342771/20000000000000 : ℝ)^6199
        have hw : |(2862847097/5000000000 : ℝ)|=(2862847097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2491656703/5000000000 : ℝ)|^8247 ≤ (7918000237091/20000000000000 : ℝ)^6199
        have hw : |(2491656703/5000000000 : ℝ)|=(2491656703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s1_1 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (338998457/625000000 : ℝ)*x 0 + (-2533449061/10000000000 : ℝ)*x 1 + (1245828433/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (338998457/625000000 : ℝ)^8247 ≤ (44314176715551/100000000000000 : ℝ)^6199 := by
    have hnat : (338998457 : ℕ)^8247*100000000000000^6199 ≤ 44314176715551^6199*625000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338998457 625000000 44314176715551 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2533449061/10000000000 : ℝ)^8247 ≤ (4023954658643/25000000000000 : ℝ)^6199 := by
    have hnat : (2533449061 : ℕ)^8247*25000000000000^6199 ≤ 4023954658643^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2533449061 10000000000 4023954658643 25000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1245828433/2500000000 : ℝ)^8247 ≤ (39590004631011/100000000000000 : ℝ)^6199 := by
    have hnat : (1245828433 : ℕ)^8247*100000000000000^6199 ≤ 39590004631011^6199*2500000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1245828433 2500000000 39590004631011 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(338998457/625000000 : ℝ), (-2533449061/10000000000 : ℝ), (1245828433/2500000000 : ℝ)] ![(44314176715551/100000000000000 : ℝ), (4023954658643/25000000000000 : ℝ), (39590004631011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(338998457/625000000 : ℝ)|^8247 ≤ (44314176715551/100000000000000 : ℝ)^6199
        have hw : |(338998457/625000000 : ℝ)|=(338998457/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2533449061/10000000000 : ℝ)|^8247 ≤ (4023954658643/25000000000000 : ℝ)^6199
        have hw : |(-2533449061/10000000000 : ℝ)|=(2533449061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1245828433/2500000000 : ℝ)|^8247 ≤ (39590004631011/100000000000000 : ℝ)^6199
        have hw : |(1245828433/2500000000 : ℝ)|=(1245828433/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s1_2 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (271198789/500000000 : ℝ)*x 0 + (2491656587/5000000000 : ℝ)*x 1 + (-1266724579/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (271198789/500000000 : ℝ)^8247 ≤ (44314181802357/100000000000000 : ℝ)^6199 := by
    have hnat : (271198789 : ℕ)^8247*100000000000000^6199 ≤ 44314181802357^6199*500000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271198789 500000000 44314181802357 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2491656587/5000000000 : ℝ)^8247 ≤ (39589998733403/100000000000000 : ℝ)^6199 := by
    have hnat : (2491656587 : ℕ)^8247*100000000000000^6199 ≤ 39589998733403^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2491656587 5000000000 39589998733403 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1266724579/5000000000 : ℝ)^8247 ≤ (8047909727223/50000000000000 : ℝ)^6199 := by
    have hnat : (1266724579 : ℕ)^8247*50000000000000^6199 ≤ 8047909727223^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1266724579 5000000000 8047909727223 50000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(271198789/500000000 : ℝ), (2491656587/5000000000 : ℝ), (-1266724579/5000000000 : ℝ)] ![(44314181802357/100000000000000 : ℝ), (39589998733403/100000000000000 : ℝ), (8047909727223/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(271198789/500000000 : ℝ)|^8247 ≤ (44314181802357/100000000000000 : ℝ)^6199
        have hw : |(271198789/500000000 : ℝ)|=(271198789/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2491656587/5000000000 : ℝ)|^8247 ≤ (39589998733403/100000000000000 : ℝ)^6199
        have hw : |(2491656587/5000000000 : ℝ)|=(2491656587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1266724579/5000000000 : ℝ)|^8247 ≤ (8047909727223/50000000000000 : ℝ)^6199
        have hw : |(-1266724579/5000000000 : ℝ)|=(1266724579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s1_3 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4324795103/10000000000 : ℝ)*x 0 + (1830112933/5000000000 : ℝ)*x 1 + (5111722269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4324795103/10000000000 : ℝ)^8247 ≤ (32786671933261/100000000000000 : ℝ)^6199 := by
    have hnat : (4324795103 : ℕ)^8247*100000000000000^6199 ≤ 32786671933261^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4324795103 10000000000 32786671933261 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1830112933/5000000000 : ℝ)^8247 ≤ (6565101330877/25000000000000 : ℝ)^6199 := by
    have hnat : (1830112933 : ℕ)^8247*25000000000000^6199 ≤ 6565101330877^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1830112933 5000000000 6565101330877 25000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5111722269/10000000000 : ℝ)^8247 ≤ (40952922737313/100000000000000 : ℝ)^6199 := by
    have hnat : (5111722269 : ℕ)^8247*100000000000000^6199 ≤ 40952922737313^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5111722269 10000000000 40952922737313 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4324795103/10000000000 : ℝ), (1830112933/5000000000 : ℝ), (5111722269/10000000000 : ℝ)] ![(32786671933261/100000000000000 : ℝ), (6565101330877/25000000000000 : ℝ), (40952922737313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4324795103/10000000000 : ℝ)|^8247 ≤ (32786671933261/100000000000000 : ℝ)^6199
        have hw : |(4324795103/10000000000 : ℝ)|=(4324795103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1830112933/5000000000 : ℝ)|^8247 ≤ (6565101330877/25000000000000 : ℝ)^6199
        have hw : |(1830112933/5000000000 : ℝ)|=(1830112933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5111722269/10000000000 : ℝ)|^8247 ≤ (40952922737313/100000000000000 : ℝ)^6199
        have hw : |(5111722269/10000000000 : ℝ)|=(5111722269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s1_4 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-6662207/31250000 : ℝ)*x 0 + (249689711/500000000 : ℝ)*x 1 + (2857499881/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6662207/31250000 : ℝ)^8247 ≤ (6397043211773/50000000000000 : ℝ)^6199 := by
    have hnat : (6662207 : ℕ)^8247*50000000000000^6199 ≤ 6397043211773^6199*31250000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6662207 31250000 6397043211773 50000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (249689711/500000000 : ℝ)^8247 ≤ (39700813358409/100000000000000 : ℝ)^6199 := by
    have hnat : (249689711 : ℕ)^8247*100000000000000^6199 ≤ 39700813358409^6199*500000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249689711 500000000 39700813358409 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2857499881/5000000000 : ℝ)^8247 ≤ (2375255010389/5000000000000 : ℝ)^6199 := by
    have hnat : (2857499881 : ℕ)^8247*5000000000000^6199 ≤ 2375255010389^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2857499881 5000000000 2375255010389 5000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-6662207/31250000 : ℝ), (249689711/500000000 : ℝ), (2857499881/5000000000 : ℝ)] ![(6397043211773/50000000000000 : ℝ), (39700813358409/100000000000000 : ℝ), (2375255010389/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-6662207/31250000 : ℝ)|^8247 ≤ (6397043211773/50000000000000 : ℝ)^6199
        have hw : |(-6662207/31250000 : ℝ)|=(6662207/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(249689711/500000000 : ℝ)|^8247 ≤ (39700813358409/100000000000000 : ℝ)^6199
        have hw : |(249689711/500000000 : ℝ)|=(249689711/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2857499881/5000000000 : ℝ)|^8247 ≤ (2375255010389/5000000000000 : ℝ)^6199
        have hw : |(2857499881/5000000000 : ℝ)|=(2857499881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s1_5 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2617251181/5000000000 : ℝ)*x 0 + (-1801762959/10000000000 : ℝ)*x 1 + (142874991/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2617251181/5000000000 : ℝ)^8247 ≤ (8453345359291/20000000000000 : ℝ)^6199 := by
    have hnat : (2617251181 : ℕ)^8247*20000000000000^6199 ≤ 8453345359291^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617251181 5000000000 8453345359291 20000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1801762959/10000000000 : ℝ)^8247 ≤ (255704358239/2500000000000 : ℝ)^6199 := by
    have hnat : (1801762959 : ℕ)^8247*2500000000000^6199 ≤ 255704358239^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1801762959 10000000000 255704358239 2500000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (142874991/250000000 : ℝ)^8247 ≤ (47505098858637/100000000000000 : ℝ)^6199 := by
    have hnat : (142874991 : ℕ)^8247*100000000000000^6199 ≤ 47505098858637^6199*250000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142874991 250000000 47505098858637 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2617251181/5000000000 : ℝ), (-1801762959/10000000000 : ℝ), (142874991/250000000 : ℝ)] ![(8453345359291/20000000000000 : ℝ), (255704358239/2500000000000 : ℝ), (47505098858637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2617251181/5000000000 : ℝ)|^8247 ≤ (8453345359291/20000000000000 : ℝ)^6199
        have hw : |(2617251181/5000000000 : ℝ)|=(2617251181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1801762959/10000000000 : ℝ)|^8247 ≤ (255704358239/2500000000000 : ℝ)^6199
        have hw : |(-1801762959/10000000000 : ℝ)|=(1801762959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(142874991/250000000 : ℝ)|^8247 ≤ (47505098858637/100000000000000 : ℝ)^6199
        have hw : |(142874991/250000000 : ℝ)|=(142874991/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s1_6 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5234502377/10000000000 : ℝ)*x 0 + (2857499867/5000000000 : ℝ)*x 1 + (-1801762801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5234502377/10000000000 : ℝ)^8247 ≤ (4226672695759/10000000000000 : ℝ)^6199 := by
    have hnat : (5234502377 : ℕ)^8247*10000000000000^6199 ≤ 4226672695759^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234502377 10000000000 4226672695759 10000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2857499867/5000000000 : ℝ)^8247 ≤ (47505099898141/100000000000000 : ℝ)^6199 := by
    have hnat : (2857499867 : ℕ)^8247*100000000000000^6199 ≤ 47505099898141^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2857499867 5000000000 47505099898141 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1801762801/10000000000 : ℝ)^8247 ≤ (2557043284077/25000000000000 : ℝ)^6199 := by
    have hnat : (1801762801 : ℕ)^8247*25000000000000^6199 ≤ 2557043284077^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1801762801 10000000000 2557043284077 25000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5234502377/10000000000 : ℝ), (2857499867/5000000000 : ℝ), (-1801762801/10000000000 : ℝ)] ![(4226672695759/10000000000000 : ℝ), (47505099898141/100000000000000 : ℝ), (2557043284077/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5234502377/10000000000 : ℝ)|^8247 ≤ (4226672695759/10000000000000 : ℝ)^6199
        have hw : |(5234502377/10000000000 : ℝ)|=(5234502377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2857499867/5000000000 : ℝ)|^8247 ≤ (47505099898141/100000000000000 : ℝ)^6199
        have hw : |(2857499867/5000000000 : ℝ)|=(2857499867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1801762801/10000000000 : ℝ)|^8247 ≤ (2557043284077/25000000000000 : ℝ)^6199
        have hw : |(-1801762801/10000000000 : ℝ)|=(1801762801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s1_7 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (540828623/1250000000 : ℝ)*x 0 + (101824621/200000000 : ℝ)*x 1 + (3681134947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540828623/1250000000 : ℝ)^8247 ≤ (32805169207031/100000000000000 : ℝ)^6199 := by
    have hnat : (540828623 : ℕ)^8247*100000000000000^6199 ≤ 32805169207031^6199*1250000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540828623 1250000000 32805169207031 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (101824621/200000000 : ℝ)^8247 ≤ (5091832985491/12500000000000 : ℝ)^6199 := by
    have hnat : (101824621 : ℕ)^8247*12500000000000^6199 ≤ 5091832985491^6199*200000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101824621 200000000 5091832985491 12500000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3681134947/10000000000 : ℝ)^8247 ≤ (26460166894697/100000000000000 : ℝ)^6199 := by
    have hnat : (3681134947 : ℕ)^8247*100000000000000^6199 ≤ 26460166894697^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3681134947 10000000000 26460166894697 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540828623/1250000000 : ℝ), (101824621/200000000 : ℝ), (3681134947/10000000000 : ℝ)] ![(32805169207031/100000000000000 : ℝ), (5091832985491/12500000000000 : ℝ), (26460166894697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540828623/1250000000 : ℝ)|^8247 ≤ (32805169207031/100000000000000 : ℝ)^6199
        have hw : |(540828623/1250000000 : ℝ)|=(540828623/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(101824621/200000000 : ℝ)|^8247 ≤ (5091832985491/12500000000000 : ℝ)^6199
        have hw : |(101824621/200000000 : ℝ)|=(101824621/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3681134947/10000000000 : ℝ)|^8247 ≤ (26460166894697/100000000000000 : ℝ)^6199
        have hw : |(3681134947/10000000000 : ℝ)|=(3681134947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1054_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36939913/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7039/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (23/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2571/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1303/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7039/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (23/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7039/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (23/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7039/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (23/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7039/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (23/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7039/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (23/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7039/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (23/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (23/50000 : ℝ) ^ (4123/1024 : ℝ) ≤ (731253/20000000000000000000 : ℝ) := by
    have hpowers : (23/50000 : ℝ)^4123 ≤ (731253/20000000000000000000 : ℝ)^1024 := by
      have hnat : (23 : ℕ)^4123*20000000000000000000^1024 ≤ 731253^1024*50000^4123 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        23 50000 731253 20000000000000000000 4123 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (23/50000 : ℝ)) (X := (731253/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7039/25000 : ℝ) ^ (4123/1024 : ℝ) ≤ (607813805756037711/100000000000000000000 : ℝ) := by
    have hpowers : (7039/25000 : ℝ)^4123 ≤ (607813805756037711/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7039 : ℕ)^4123*100000000000000000000^1024 ≤ 607813805756037711^1024*25000^4123 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7039 25000 607813805756037711 100000000000000000000 4123 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7039/25000 : ℝ)) (X := (607813805756037711/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000000000000731253/10000000000000000000 : ℝ) ≤ (5000000000000091/5000000000000000 : ℝ) ^ (4123/1024 : ℝ) := by
    have hpowers : (10000000000000731253/10000000000000000000 : ℝ)^1024 ≤ (5000000000000091/5000000000000000 : ℝ)^4123 := by
      have hnat : (10000000000000731253 : ℕ)^1024*5000000000000000^4123 ≤ 5000000000000091^4123*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000000000000731253 10000000000000000000 5000000000000091 5000000000000000 1024 4123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000000000091/5000000000000000 : ℝ)) (X := (10000000000000731253/10000000000000000000 : ℝ)) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12575976725719961747/12500000000000000000 : ℝ) ≤ (10015061475248829/10000000000000000 : ℝ) ^ (4123/1024 : ℝ) := by
    have hpowers : (12575976725719961747/12500000000000000000 : ℝ)^1024 ≤ (10015061475248829/10000000000000000 : ℝ)^4123 := by
      have hnat : (12575976725719961747 : ℕ)^1024*10000000000000000^4123 ≤ 10015061475248829^4123*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12575976725719961747 12500000000000000000 10015061475248829 10000000000000000 1024 4123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10015061475248829/10000000000000000 : ℝ)) (X := (12575976725719961747/12500000000000000000 : ℝ)) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50607813805756037711/50000000000000000000 : ℝ) ≤ (2507530737624369/2500000000000000 : ℝ) ^ (4123/1024 : ℝ) := by
    have hpowers : (50607813805756037711/50000000000000000000 : ℝ)^1024 ≤ (2507530737624369/2500000000000000 : ℝ)^4123 := by
      have hnat : (50607813805756037711 : ℕ)^1024*2500000000000000^4123 ≤ 2507530737624369^4123*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50607813805756037711 50000000000000000000 2507530737624369 2500000000000000 1024 4123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2507530737624369/2500000000000000 : ℝ)) (X := (50607813805756037711/50000000000000000000 : ℝ)) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(731253/20000000000000000000 : ℝ) ≤ ((5856221132172546677/5856250000000000000 : ℝ)+2*(5020491749549/937000000000000 : ℝ)*(23/50000 : ℝ))^(4123/1024 : ℝ) := by
    rw [show (5856221132172546677/5856250000000000000 : ℝ)+2*(5020491749549/937000000000000 : ℝ)*(23/50000 : ℝ)=(5000000000000091/5000000000000000 : ℝ) by norm_num, show 1+2*(731253/20000000000000000000 : ℝ)=(10000000000000731253/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(607813805756037711/100000000000000000000 : ℝ)+(731253/20000000000000000000 : ℝ) ≤ ((5856221132172546677/5856250000000000000 : ℝ)+(5020491749549/937000000000000 : ℝ)*((7039/25000 : ℝ)+(23/50000 : ℝ)))^(4123/1024 : ℝ) := by
    rw [show (5856221132172546677/5856250000000000000 : ℝ)+(5020491749549/937000000000000 : ℝ)*((7039/25000 : ℝ)+(23/50000 : ℝ))=(10015061475248829/10000000000000000 : ℝ) by norm_num, show 1+(607813805756037711/100000000000000000000 : ℝ)+(731253/20000000000000000000 : ℝ)=(12575976725719961747/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(607813805756037711/100000000000000000000 : ℝ) ≤ ((5856221132172546677/5856250000000000000 : ℝ)+2*(5020491749549/937000000000000 : ℝ)*(7039/25000 : ℝ))^(4123/1024 : ℝ) := by
    rw [show (5856221132172546677/5856250000000000000 : ℝ)+2*(5020491749549/937000000000000 : ℝ)*(7039/25000 : ℝ)=(2507530737624369/2500000000000000 : ℝ) by norm_num, show 1+2*(607813805756037711/100000000000000000000 : ℝ)=(50607813805756037711/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5856221132172546677/5856250000000000000 : ℝ)*(X 1 0+X 2 0)+(5020491749549/937000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4123/1024 : ℝ)) (lo := (23/50000 : ℝ)) (hi := (7039/25000 : ℝ)) (c := (5856221132172546677/5856250000000000000 : ℝ)) (alpha := (5020491749549/937000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5856221132172546677/5856250000000000000 : ℝ)*(X 0 1+X 2 1)+(5020491749549/937000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4123/1024 : ℝ)) (lo := (23/50000 : ℝ)) (hi := (7039/25000 : ℝ)) (c := (5856221132172546677/5856250000000000000 : ℝ)) (alpha := (5020491749549/937000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5856221132172546677/5856250000000000000 : ℝ)*(X 0 2+X 1 2)+(5020491749549/937000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4123/1024 : ℝ)) (lo := (23/50000 : ℝ)) (hi := (7039/25000 : ℝ)) (c := (5856221132172546677/5856250000000000000 : ℝ)) (alpha := (5020491749549/937000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1065484059/5000000000 : ℝ)*X 0 0+(2862847097/5000000000 : ℝ)*X 0 1+(2491656703/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((338998457/625000000 : ℝ)*X 1 0+(-2533449061/10000000000 : ℝ)*X 1 1+(1245828433/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((271198789/500000000 : ℝ)*X 2 0+(2491656587/5000000000 : ℝ)*X 2 1+(-1266724579/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4324795103/10000000000 : ℝ)*X 0 0+(1830112933/5000000000 : ℝ)*X 0 1+(5111722269/10000000000 : ℝ)*X 0 2+(4324795103/10000000000 : ℝ)*X 1 0+(1830112933/5000000000 : ℝ)*X 1 1+(5111722269/10000000000 : ℝ)*X 1 2+(4324795103/10000000000 : ℝ)*X 2 0+(1830112933/5000000000 : ℝ)*X 2 1+(5111722269/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-6662207/31250000 : ℝ)*X 0 0+(249689711/500000000 : ℝ)*X 0 1+(2857499881/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2617251181/5000000000 : ℝ)*X 1 0+(-1801762959/10000000000 : ℝ)*X 1 1+(142874991/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5234502377/10000000000 : ℝ)*X 2 0+(2857499867/5000000000 : ℝ)*X 2 1+(-1801762801/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((540828623/1250000000 : ℝ)*X 0 0+(101824621/200000000 : ℝ)*X 0 1+(3681134947/10000000000 : ℝ)*X 0 2+(540828623/1250000000 : ℝ)*X 1 0+(101824621/200000000 : ℝ)*X 1 1+(3681134947/10000000000 : ℝ)*X 1 2+(540828623/1250000000 : ℝ)*X 2 0+(101824621/200000000 : ℝ)*X 2 1+(3681134947/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1120803113700533489279938281/146406250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (125139157/100000000000000 : ℝ)*(base1) + (339020537/20000000000000 : ℝ)*(base19) + (226416189/12500000000000 : ℝ)*(base23) + (180980431/100000000000000 : ℝ)*(upper3) + (45078833/25000000000000 : ℝ)*(upper5) + (508996883863251/50000000000000 : ℝ)*(major0) + (508996883863251/50000000000000 : ℝ)*(major1) + (508996883863251/50000000000000 : ℝ)*(major2) + (1347026041784201/100000000000000 : ℝ)*(sp0) + (42094784941903/3125000000000 : ℝ)*(sp1) + (1347033001914069/100000000000000 : ℝ)*(sp2) + (688948142642059/100000000000000 : ℝ)*(sp3) + (8896598537/100000000000000 : ℝ)*(sp4) + (1049811783/25000000000000 : ℝ)*(sp7) + (172238116757087/25000000000000 : ℝ)*(f.failure) + (1347034813243581/100000000000000 : ℝ)*(f.sum) + (4280576878353/2928125000000000000000000000 : ℝ)*base65 + (1066170622980039323/292812500000000000000000000000000 : ℝ)*base68 + (978751113492226823/292812500000000000000000000000000 : ℝ)*base70 + (248721860897148177/292812500000000000000000000000000 : ℝ)*base71 + (1603946633649/23425000000000000000000000000 : ℝ)*base73 + (621735687387226823/292812500000000000000000000000000 : ℝ)*base76 + (1114522152889101823/292812500000000000000000000000000 : ℝ)*base78 + (554265501999960677/292812500000000000000000000000000 : ℝ)*base79 + (27408299903137/11712500000000000000000000000 : ℝ)*base81 + (1586569/625000000000000000000 : ℝ)*base90 + (1586569/625000000000000000000 : ℝ)*base92 + (1586569/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (929630007282788244501431367/292812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20521507/50000000000000 : ℝ)*(base1) + (22725081/3125000000000 : ℝ)*(base19) + (185603943/25000000000000 : ℝ)*(base23) + (35993989/50000000000000 : ℝ)*(upper3) + (14052877/20000000000000 : ℝ)*(upper5) + (1047869472401657/100000000000000 : ℝ)*(major0) + (1047869472401657/100000000000000 : ℝ)*(major1) + (1047869472401657/100000000000000 : ℝ)*(major2) + (34038881/1250000000000 : ℝ)*(sp1) + (30336221/1000000000000 : ℝ)*(sp2) + (277313458147911/20000000000000 : ℝ)*(sp4) + (1386563799383469/100000000000000 : ℝ)*(sp5) + (1386563473658669/100000000000000 : ℝ)*(sp6) + (709171548236079/100000000000000 : ℝ)*(sp7) + (709171589279093/100000000000000 : ℝ)*(f.failure) + (1386567249696541/100000000000000 : ℝ)*(f.sum) + (26143490008907/46850000000000000000000000000 : ℝ)*base66 + (1283138431985225039/585625000000000000000000000000000 : ℝ)*base67 + (1708586987234600039/585625000000000000000000000000000 : ℝ)*base69 + (1589944976694774961/585625000000000000000000000000000 : ℝ)*base72 + (154600138684543/46850000000000000000000000000 : ℝ)*base73 + (1023398502496649961/585625000000000000000000000000000 : ℝ)*base76 + (329194303241649961/585625000000000000000000000000000 : ℝ)*base78 + (2186670570016024961/585625000000000000000000000000000 : ℝ)*base80 + (135676475206293/46850000000000000000000000000 : ℝ)*base81 + (3138909/2500000000000000000000 : ℝ)*base89 + (3138909/2500000000000000000000 : ℝ)*base91 + (3138909/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1054_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36939913/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7039/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (23/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2571/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1303/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1054_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1054_s2_0 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-109453629/500000000 : ℝ)*x 0 + (5528399621/10000000000 : ℝ)*x 1 + (5143756449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (109453629/500000000 : ℝ)^8247 ≤ (828281682699/6250000000000 : ℝ)^6199 := by
    have hnat : (109453629 : ℕ)^8247*6250000000000^6199 ≤ 828281682699^6199*500000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109453629 500000000 828281682699 6250000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5528399621/10000000000 : ℝ)^8247 ≤ (45452784258431/100000000000000 : ℝ)^6199 := by
    have hnat : (5528399621 : ℕ)^8247*100000000000000^6199 ≤ 45452784258431^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5528399621 10000000000 45452784258431 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5143756449/10000000000 : ℝ)^8247 ≤ (1290459649901/3125000000000 : ℝ)^6199 := by
    have hnat : (5143756449 : ℕ)^8247*3125000000000^6199 ≤ 1290459649901^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5143756449 10000000000 1290459649901 3125000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-109453629/500000000 : ℝ), (5528399621/10000000000 : ℝ), (5143756449/10000000000 : ℝ)] ![(828281682699/6250000000000 : ℝ), (45452784258431/100000000000000 : ℝ), (1290459649901/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-109453629/500000000 : ℝ)|^8247 ≤ (828281682699/6250000000000 : ℝ)^6199
        have hw : |(-109453629/500000000 : ℝ)|=(109453629/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5528399621/10000000000 : ℝ)|^8247 ≤ (45452784258431/100000000000000 : ℝ)^6199
        have hw : |(5528399621/10000000000 : ℝ)|=(5528399621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5143756449/10000000000 : ℝ)|^8247 ≤ (1290459649901/3125000000000 : ℝ)^6199
        have hw : |(5143756449/10000000000 : ℝ)|=(5143756449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s2_1 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (537774037/1000000000 : ℝ)*x 0 + (-1194886137/5000000000 : ℝ)*x 1 + (257187831/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537774037/1000000000 : ℝ)^8247 ≤ (21906173410139/50000000000000 : ℝ)^6199 := by
    have hnat : (537774037 : ℕ)^8247*50000000000000^6199 ≤ 21906173410139^6199*1000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537774037 1000000000 21906173410139 50000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1194886137/5000000000 : ℝ)^8247 ≤ (58175556787/390625000000 : ℝ)^6199 := by
    have hnat : (1194886137 : ℕ)^8247*390625000000^6199 ≤ 58175556787^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1194886137 5000000000 58175556787 390625000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (257187831/500000000 : ℝ)^8247 ≤ (2580919413949/6250000000000 : ℝ)^6199 := by
    have hnat : (257187831 : ℕ)^8247*6250000000000^6199 ≤ 2580919413949^6199*500000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257187831 500000000 2580919413949 6250000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537774037/1000000000 : ℝ), (-1194886137/5000000000 : ℝ), (257187831/500000000 : ℝ)] ![(21906173410139/50000000000000 : ℝ), (58175556787/390625000000 : ℝ), (2580919413949/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537774037/1000000000 : ℝ)|^8247 ≤ (21906173410139/50000000000000 : ℝ)^6199
        have hw : |(537774037/1000000000 : ℝ)|=(537774037/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1194886137/5000000000 : ℝ)|^8247 ≤ (58175556787/390625000000 : ℝ)^6199
        have hw : |(-1194886137/5000000000 : ℝ)|=(1194886137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(257187831/500000000 : ℝ)|^8247 ≤ (2580919413949/6250000000000 : ℝ)^6199
        have hw : |(257187831/500000000 : ℝ)|=(257187831/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s2_2 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (336108777/625000000 : ℝ)*x 0 + (5143756521/10000000000 : ℝ)*x 1 + (-2389772321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (336108777/625000000 : ℝ)^8247 ≤ (10953086873067/25000000000000 : ℝ)^6199 := by
    have hnat : (336108777 : ℕ)^8247*25000000000000^6199 ≤ 10953086873067^6199*625000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336108777 625000000 10953086873067 25000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5143756521/10000000000 : ℝ)^8247 ≤ (41294709565823/100000000000000 : ℝ)^6199 := by
    have hnat : (5143756521 : ℕ)^8247*100000000000000^6199 ≤ 41294709565823^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5143756521 10000000000 41294709565823 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2389772321/10000000000 : ℝ)^8247 ≤ (14892942927141/100000000000000 : ℝ)^6199 := by
    have hnat : (2389772321 : ℕ)^8247*100000000000000^6199 ≤ 14892942927141^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2389772321 10000000000 14892942927141 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(336108777/625000000 : ℝ), (5143756521/10000000000 : ℝ), (-2389772321/10000000000 : ℝ)] ![(10953086873067/25000000000000 : ℝ), (41294709565823/100000000000000 : ℝ), (14892942927141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(336108777/625000000 : ℝ)|^8247 ≤ (10953086873067/25000000000000 : ℝ)^6199
        have hw : |(336108777/625000000 : ℝ)|=(336108777/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5143756521/10000000000 : ℝ)|^8247 ≤ (41294709565823/100000000000000 : ℝ)^6199
        have hw : |(5143756521/10000000000 : ℝ)|=(5143756521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2389772321/10000000000 : ℝ)|^8247 ≤ (14892942927141/100000000000000 : ℝ)^6199
        have hw : |(-2389772321/10000000000 : ℝ)|=(2389772321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s2_3 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (872880867/2000000000 : ℝ)*x 0 + (4004759723/10000000000 : ℝ)*x 1 + (190272457/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (872880867/2000000000 : ℝ)^8247 ≤ (3318676201793/10000000000000 : ℝ)^6199 := by
    have hnat : (872880867 : ℕ)^8247*10000000000000^6199 ≤ 3318676201793^6199*2000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872880867 2000000000 3318676201793 10000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4004759723/10000000000 : ℝ)^8247 ≤ (739975478127/2500000000000 : ℝ)^6199 := by
    have hnat : (4004759723 : ℕ)^8247*2500000000000^6199 ≤ 739975478127^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4004759723 10000000000 739975478127 2500000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (190272457/400000000 : ℝ)^8247 ≤ (18607109419511/50000000000000 : ℝ)^6199 := by
    have hnat : (190272457 : ℕ)^8247*50000000000000^6199 ≤ 18607109419511^6199*400000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190272457 400000000 18607109419511 50000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(872880867/2000000000 : ℝ), (4004759723/10000000000 : ℝ), (190272457/400000000 : ℝ)] ![(3318676201793/10000000000000 : ℝ), (739975478127/2500000000000 : ℝ), (18607109419511/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(872880867/2000000000 : ℝ)|^8247 ≤ (3318676201793/10000000000000 : ℝ)^6199
        have hw : |(872880867/2000000000 : ℝ)|=(872880867/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4004759723/10000000000 : ℝ)|^8247 ≤ (739975478127/2500000000000 : ℝ)^6199
        have hw : |(4004759723/10000000000 : ℝ)|=(4004759723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(190272457/400000000 : ℝ)|^8247 ≤ (18607109419511/50000000000000 : ℝ)^6199
        have hw : |(190272457/400000000 : ℝ)|=(190272457/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s2_4 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2189202803/10000000000 : ℝ)*x 0 + (5146577957/10000000000 : ℝ)*x 1 + (8633669/15625000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2189202803/10000000000 : ℝ)^8247 ≤ (13253555751009/100000000000000 : ℝ)^6199 := by
    have hnat : (2189202803 : ℕ)^8247*100000000000000^6199 ≤ 13253555751009^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189202803 10000000000 13253555751009 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5146577957/10000000000 : ℝ)^8247 ≤ (41324846420129/100000000000000 : ℝ)^6199 := by
    have hnat : (5146577957 : ℕ)^8247*100000000000000^6199 ≤ 41324846420129^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5146577957 10000000000 41324846420129 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8633669/15625000 : ℝ)^8247 ≤ (22710798907527/50000000000000 : ℝ)^6199 := by
    have hnat : (8633669 : ℕ)^8247*50000000000000^6199 ≤ 22710798907527^6199*15625000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8633669 15625000 22710798907527 50000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2189202803/10000000000 : ℝ), (5146577957/10000000000 : ℝ), (8633669/15625000 : ℝ)] ![(13253555751009/100000000000000 : ℝ), (41324846420129/100000000000000 : ℝ), (22710798907527/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2189202803/10000000000 : ℝ)|^8247 ≤ (13253555751009/100000000000000 : ℝ)^6199
        have hw : |(-2189202803/10000000000 : ℝ)|=(2189202803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5146577957/10000000000 : ℝ)|^8247 ≤ (41324846420129/100000000000000 : ℝ)^6199
        have hw : |(5146577957/10000000000 : ℝ)|=(5146577957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8633669/15625000 : ℝ)|^8247 ≤ (22710798907527/50000000000000 : ℝ)^6199
        have hw : |(8633669/15625000 : ℝ)|=(8633669/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s2_5 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (211229409/400000000 : ℝ)*x 0 + (-2007980779/10000000000 : ℝ)*x 1 + (5525548233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211229409/400000000 : ℝ)^8247 ≤ (8552819520887/20000000000000 : ℝ)^6199 := by
    have hnat : (211229409 : ℕ)^8247*20000000000000^6199 ≤ 8552819520887^6199*400000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211229409 400000000 8552819520887 20000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2007980779/10000000000 : ℝ)^8247 ≤ (590715188807/5000000000000 : ℝ)^6199 := by
    have hnat : (2007980779 : ℕ)^8247*5000000000000^6199 ≤ 590715188807^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2007980779 10000000000 590715188807 5000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5525548233/10000000000 : ℝ)^8247 ≤ (45421598613387/100000000000000 : ℝ)^6199 := by
    have hnat : (5525548233 : ℕ)^8247*100000000000000^6199 ≤ 45421598613387^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5525548233 10000000000 45421598613387 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211229409/400000000 : ℝ), (-2007980779/10000000000 : ℝ), (5525548233/10000000000 : ℝ)] ![(8552819520887/20000000000000 : ℝ), (590715188807/5000000000000 : ℝ), (45421598613387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211229409/400000000 : ℝ)|^8247 ≤ (8552819520887/20000000000000 : ℝ)^6199
        have hw : |(211229409/400000000 : ℝ)|=(211229409/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2007980779/10000000000 : ℝ)|^8247 ≤ (590715188807/5000000000000 : ℝ)^6199
        have hw : |(-2007980779/10000000000 : ℝ)|=(2007980779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5525548233/10000000000 : ℝ)|^8247 ≤ (45421598613387/100000000000000 : ℝ)^6199
        have hw : |(5525548233/10000000000 : ℝ)|=(5525548233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s2_6 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5280735461/10000000000 : ℝ)*x 0 + (5525548069/10000000000 : ℝ)*x 1 + (-1003990341/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5280735461/10000000000 : ℝ)^8247 ≤ (8552820029399/20000000000000 : ℝ)^6199 := by
    have hnat : (5280735461 : ℕ)^8247*20000000000000^6199 ≤ 8552820029399^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280735461 10000000000 8552820029399 20000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5525548069/10000000000 : ℝ)^8247 ≤ (45421596819871/100000000000000 : ℝ)^6199 := by
    have hnat : (5525548069 : ℕ)^8247*100000000000000^6199 ≤ 45421596819871^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5525548069 10000000000 45421596819871 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1003990341/5000000000 : ℝ)^8247 ≤ (1476787877109/12500000000000 : ℝ)^6199 := by
    have hnat : (1003990341 : ℕ)^8247*12500000000000^6199 ≤ 1476787877109^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003990341 5000000000 1476787877109 12500000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5280735461/10000000000 : ℝ), (5525548069/10000000000 : ℝ), (-1003990341/5000000000 : ℝ)] ![(8552820029399/20000000000000 : ℝ), (45421596819871/100000000000000 : ℝ), (1476787877109/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5280735461/10000000000 : ℝ)|^8247 ≤ (8552820029399/20000000000000 : ℝ)^6199
        have hw : |(5280735461/10000000000 : ℝ)|=(5280735461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5525548069/10000000000 : ℝ)|^8247 ≤ (45421596819871/100000000000000 : ℝ)^6199
        have hw : |(5525548069/10000000000 : ℝ)|=(5525548069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1003990341/5000000000 : ℝ)|^8247 ≤ (1476787877109/12500000000000 : ℝ)^6199
        have hw : |(-1003990341/5000000000 : ℝ)|=(1003990341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s2_7 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4364659013/10000000000 : ℝ)*x 0 + (593911849/1250000000 : ℝ)*x 1 + (160413387/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4364659013/10000000000 : ℝ)^8247 ≤ (8297334599421/25000000000000 : ℝ)^6199 := by
    have hnat : (4364659013 : ℕ)^8247*25000000000000^6199 ≤ 8297334599421^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364659013 10000000000 8297334599421 25000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (593911849/1250000000 : ℝ)^8247 ≤ (7431362543807/20000000000000 : ℝ)^6199 := by
    have hnat : (593911849 : ℕ)^8247*20000000000000^6199 ≤ 7431362543807^6199*1250000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      593911849 1250000000 7431362543807 20000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (160413387/400000000 : ℝ)^8247 ≤ (741346221579/2500000000000 : ℝ)^6199 := by
    have hnat : (160413387 : ℕ)^8247*2500000000000^6199 ≤ 741346221579^6199*400000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160413387 400000000 741346221579 2500000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4364659013/10000000000 : ℝ), (593911849/1250000000 : ℝ), (160413387/400000000 : ℝ)] ![(8297334599421/25000000000000 : ℝ), (7431362543807/20000000000000 : ℝ), (741346221579/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4364659013/10000000000 : ℝ)|^8247 ≤ (8297334599421/25000000000000 : ℝ)^6199
        have hw : |(4364659013/10000000000 : ℝ)|=(4364659013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(593911849/1250000000 : ℝ)|^8247 ≤ (7431362543807/20000000000000 : ℝ)^6199
        have hw : |(593911849/1250000000 : ℝ)|=(593911849/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(160413387/400000000 : ℝ)|^8247 ≤ (741346221579/2500000000000 : ℝ)^6199
        have hw : |(160413387/400000000 : ℝ)|=(160413387/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1054_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36939913/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1303/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2571/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (8653/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16781/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1303/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2571/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1303/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2571/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1303/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2571/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1303/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2571/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1303/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2571/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1303/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2571/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2571/50000 : ℝ) ^ (4123/1024 : ℝ) ≤ (64646418133899/10000000000000000000 : ℝ) := by
    have hpowers : (2571/50000 : ℝ)^4123 ≤ (64646418133899/10000000000000000000 : ℝ)^1024 := by
      have hnat : (2571 : ℕ)^4123*10000000000000000000^1024 ≤ 64646418133899^1024*50000^4123 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2571 50000 64646418133899 10000000000000000000 4123 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2571/50000 : ℝ)) (X := (64646418133899/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1303/6250 : ℝ) ^ (4123/1024 : ℝ) ≤ (181260526355720323/100000000000000000000 : ℝ) := by
    have hpowers : (1303/6250 : ℝ)^4123 ≤ (181260526355720323/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1303 : ℕ)^4123*100000000000000000000^1024 ≤ 181260526355720323^1024*6250^4123 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1303 6250 181260526355720323 100000000000000000000 4123 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1303/6250 : ℝ)) (X := (181260526355720323/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000064646418133899/5000000000000000000 : ℝ) ≤ (1250004013922539/1250000000000000 : ℝ) ^ (4123/1024 : ℝ) := by
    have hpowers : (5000064646418133899/5000000000000000000 : ℝ)^1024 ≤ (1250004013922539/1250000000000000 : ℝ)^4123 := by
      have hnat : (5000064646418133899 : ℕ)^1024*1250000000000000^4123 ≤ 1250004013922539^4123*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000064646418133899 5000000000000000000 1250004013922539 1250000000000000 1024 4123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250004013922539/1250000000000000 : ℝ)) (X := (5000064646418133899/5000000000000000000 : ℝ)) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100181906990537059313/100000000000000000000 : ℝ) ≤ (625282175524249/625000000000000 : ℝ) ^ (4123/1024 : ℝ) := by
    have hpowers : (100181906990537059313/100000000000000000000 : ℝ)^1024 ≤ (625282175524249/625000000000000 : ℝ)^4123 := by
      have hnat : (100181906990537059313 : ℕ)^1024*625000000000000^4123 ≤ 625282175524249^4123*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100181906990537059313 100000000000000000000 625282175524249 625000000000000 1024 4123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625282175524249/625000000000000 : ℝ)) (X := (100181906990537059313/100000000000000000000 : ℝ)) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50181260526355720323/50000000000000000000 : ℝ) ≤ (1251124688174457/1250000000000000 : ℝ) ^ (4123/1024 : ℝ) := by
    have hpowers : (50181260526355720323/50000000000000000000 : ℝ)^1024 ≤ (1251124688174457/1250000000000000 : ℝ)^4123 := by
      have hnat : (50181260526355720323 : ℕ)^1024*1250000000000000^4123 ≤ 1251124688174457^4123*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50181260526355720323 50000000000000000000 1251124688174457 1250000000000000 1024 4123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1251124688174457/1250000000000000 : ℝ)) (X := (50181260526355720323/50000000000000000000 : ℝ)) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(64646418133899/10000000000000000000 : ℝ) ≤ ((9813400267832017589/9816250000000000000 : ℝ)+2*(560337125959/196325000000000 : ℝ)*(2571/50000 : ℝ))^(4123/1024 : ℝ) := by
    rw [show (9813400267832017589/9816250000000000000 : ℝ)+2*(560337125959/196325000000000 : ℝ)*(2571/50000 : ℝ)=(1250004013922539/1250000000000000 : ℝ) by norm_num, show 1+2*(64646418133899/10000000000000000000 : ℝ)=(5000064646418133899/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(181260526355720323/100000000000000000000 : ℝ)+(64646418133899/10000000000000000000 : ℝ) ≤ ((9813400267832017589/9816250000000000000 : ℝ)+(560337125959/196325000000000 : ℝ)*((1303/6250 : ℝ)+(2571/50000 : ℝ)))^(4123/1024 : ℝ) := by
    rw [show (9813400267832017589/9816250000000000000 : ℝ)+(560337125959/196325000000000 : ℝ)*((1303/6250 : ℝ)+(2571/50000 : ℝ))=(625282175524249/625000000000000 : ℝ) by norm_num, show 1+(181260526355720323/100000000000000000000 : ℝ)+(64646418133899/10000000000000000000 : ℝ)=(100181906990537059313/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(181260526355720323/100000000000000000000 : ℝ) ≤ ((9813400267832017589/9816250000000000000 : ℝ)+2*(560337125959/196325000000000 : ℝ)*(1303/6250 : ℝ))^(4123/1024 : ℝ) := by
    rw [show (9813400267832017589/9816250000000000000 : ℝ)+2*(560337125959/196325000000000 : ℝ)*(1303/6250 : ℝ)=(1251124688174457/1250000000000000 : ℝ) by norm_num, show 1+2*(181260526355720323/100000000000000000000 : ℝ)=(50181260526355720323/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9813400267832017589/9816250000000000000 : ℝ)*(X 1 0+X 2 0)+(560337125959/196325000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4123/1024 : ℝ)) (lo := (2571/50000 : ℝ)) (hi := (1303/6250 : ℝ)) (c := (9813400267832017589/9816250000000000000 : ℝ)) (alpha := (560337125959/196325000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9813400267832017589/9816250000000000000 : ℝ)*(X 0 1+X 2 1)+(560337125959/196325000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4123/1024 : ℝ)) (lo := (2571/50000 : ℝ)) (hi := (1303/6250 : ℝ)) (c := (9813400267832017589/9816250000000000000 : ℝ)) (alpha := (560337125959/196325000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9813400267832017589/9816250000000000000 : ℝ)*(X 0 2+X 1 2)+(560337125959/196325000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4123/1024 : ℝ)) (lo := (2571/50000 : ℝ)) (hi := (1303/6250 : ℝ)) (c := (9813400267832017589/9816250000000000000 : ℝ)) (alpha := (560337125959/196325000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-109453629/500000000 : ℝ)*X 0 0+(5528399621/10000000000 : ℝ)*X 0 1+(5143756449/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((537774037/1000000000 : ℝ)*X 1 0+(-1194886137/5000000000 : ℝ)*X 1 1+(257187831/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((336108777/625000000 : ℝ)*X 2 0+(5143756521/10000000000 : ℝ)*X 2 1+(-2389772321/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((872880867/2000000000 : ℝ)*X 0 0+(4004759723/10000000000 : ℝ)*X 0 1+(190272457/400000000 : ℝ)*X 0 2+(872880867/2000000000 : ℝ)*X 1 0+(4004759723/10000000000 : ℝ)*X 1 1+(190272457/400000000 : ℝ)*X 1 2+(872880867/2000000000 : ℝ)*X 2 0+(4004759723/10000000000 : ℝ)*X 2 1+(190272457/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2189202803/10000000000 : ℝ)*X 0 0+(5146577957/10000000000 : ℝ)*X 0 1+(8633669/15625000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((211229409/400000000 : ℝ)*X 1 0+(-2007980779/10000000000 : ℝ)*X 1 1+(5525548233/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5280735461/10000000000 : ℝ)*X 2 0+(5525548069/10000000000 : ℝ)*X 2 1+(-1003990341/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4364659013/10000000000 : ℝ)*X 0 0+(593911849/1250000000 : ℝ)*X 0 1+(160413387/400000000 : ℝ)*X 0 2+(4364659013/10000000000 : ℝ)*X 1 0+(593911849/1250000000 : ℝ)*X 1 1+(160413387/400000000 : ℝ)*X 1 2+(4364659013/10000000000 : ℝ)*X 2 0+(593911849/1250000000 : ℝ)*X 2 1+(160413387/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (601042064145427173800953461/245406250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (207008741/50000000000000 : ℝ)*(base19) + (428609809/100000000000000 : ℝ)*(base23) + (31580177/50000000000000 : ℝ)*(upper3) + (8271519/100000000000000 : ℝ)*(upper4) + (3842821/12500000000000 : ℝ)*(upper5) + (1964761533942267/100000000000000 : ℝ)*(major0) + (1964761533942267/100000000000000 : ℝ)*(major1) + (1964761533942267/100000000000000 : ℝ)*(major2) + (324977154319161/12500000000000 : ℝ)*(sp0) + (2599821596793729/100000000000000 : ℝ)*(sp1) + (2599821582201401/100000000000000 : ℝ)*(sp2) + (1329698216859327/100000000000000 : ℝ)*(sp3) + (2388128961/50000000000000 : ℝ)*(sp4) + (689643733/25000000000000 : ℝ)*(sp7) + (1329700975434259/100000000000000 : ℝ)*(f.failure) + (259982201081121/10000000000000 : ℝ)*(f.sum) + (67404073166363/39265000000000000000000000000 : ℝ)*base66 + (6015340203575809263/981625000000000000000000000000000 : ℝ)*base67 + (1480344471398309263/981625000000000000000000000000000 : ℝ)*base69 + (1821771826708190737/981625000000000000000000000000000 : ℝ)*base72 + (152954068828177/39265000000000000000000000000 : ℝ)*base73 + (556087454367809263/981625000000000000000000000000000 : ℝ)*base75 + (1399327047391059263/981625000000000000000000000000000 : ℝ)*base77 + (5884041264287434263/981625000000000000000000000000000 : ℝ)*base79 + (4035564101799/19632500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (10320533/2500000000000000000000 : ℝ)*base90 + (10320533/2500000000000000000000 : ℝ)*base92 + (10320533/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1221729931886571991588473927/122703125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (971405761/50000000000000 : ℝ)*(base19) + (441520231/20000000000000 : ℝ)*(base23) + (124743929/50000000000000 : ℝ)*(upper3) + (55144219/100000000000000 : ℝ)*(lower4) + (108778891/50000000000000 : ℝ)*(upper5) + (498541290696423/25000000000000 : ℝ)*(major0) + (498541290696423/25000000000000 : ℝ)*(major1) + (498541290696423/25000000000000 : ℝ)*(major2) + (8369441469/50000000000000 : ℝ)*(sp1) + (9524562941/50000000000000 : ℝ)*(sp2) + (1319364692495629/50000000000000 : ℝ)*(sp4) + (1319355351648399/50000000000000 : ℝ)*(sp5) + (131935406413211/5000000000000 : ℝ)*(sp6) + (1349600608686931/100000000000000 : ℝ)*(sp7) + (1349600608686931/100000000000000 : ℝ)*(f.failure) + (1319364692495629/50000000000000 : ℝ)*(f.sum) + (16179242492673/39265000000000000000000000000 : ℝ)*base66 + (1215424365319671647/245406250000000000000000000000000 : ℝ)*base67 + (616153481810577897/245406250000000000000000000000000 : ℝ)*base69 + (42698461909827897/245406250000000000000000000000000 : ℝ)*base71 + (19433302833771/19632500000000000000000000000 : ℝ)*base73 + (1610534155356140397/245406250000000000000000000000000 : ℝ)*base75 + (1611961038584765397/245406250000000000000000000000000 : ℝ)*base77 + (2449899327757546647/245406250000000000000000000000000 : ℝ)*base79 + (26708518742183/39265000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (24622997/2500000000000000000000 : ℝ)*base90 + (24622997/2500000000000000000000 : ℝ)*base92 + (24622997/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1054_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36939913/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1303/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2571/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8653/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16781/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1054_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1054_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36939913/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8653/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16781/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1054_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1054_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1054_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36939913/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8653/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16781/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1054_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
