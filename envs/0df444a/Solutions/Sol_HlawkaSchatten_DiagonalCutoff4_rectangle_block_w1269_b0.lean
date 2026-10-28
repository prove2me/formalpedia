-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1269_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:20:05.329037+00:00
-- url     : https://prove2.me/submissions/0b12c3d5-87da-4404-b570-b7427649f35f

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
theorem support_rectangle_w1269_s0_0 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-115723029/625000000 : ℝ)*x 0 + (3013963119/5000000000 : ℝ)*x 1 + (191752487/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (115723029/625000000 : ℝ)^8463 ≤ (540344292271/5000000000000 : ℝ)^6415 := by
    have hnat : (115723029 : ℕ)^8463*5000000000000^6415 ≤ 540344292271^6415*625000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      115723029 625000000 540344292271 5000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3013963119/5000000000 : ℝ)^8463 ≤ (10256900698031/20000000000000 : ℝ)^6415 := by
    have hnat : (3013963119 : ℕ)^8463*20000000000000^6415 ≤ 10256900698031^6415*5000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3013963119 5000000000 10256900698031 20000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (191752487/400000000 : ℝ)^8463 ≤ (37908610648113/100000000000000 : ℝ)^6415 := by
    have hnat : (191752487 : ℕ)^8463*100000000000000^6415 ≤ 37908610648113^6415*400000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191752487 400000000 37908610648113 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-115723029/625000000 : ℝ), (3013963119/5000000000 : ℝ), (191752487/400000000 : ℝ)] ![(540344292271/5000000000000 : ℝ), (10256900698031/20000000000000 : ℝ), (37908610648113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-115723029/625000000 : ℝ)|^8463 ≤ (540344292271/5000000000000 : ℝ)^6415
        have hw : |(-115723029/625000000 : ℝ)|=(115723029/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3013963119/5000000000 : ℝ)|^8463 ≤ (10256900698031/20000000000000 : ℝ)^6415
        have hw : |(3013963119/5000000000 : ℝ)|=(3013963119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(191752487/400000000 : ℝ)|^8463 ≤ (37908610648113/100000000000000 : ℝ)^6415
        have hw : |(191752487/400000000 : ℝ)|=(191752487/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s0_1 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (550971999/1000000000 : ℝ)*x 0 + (-1278353799/5000000000 : ℝ)*x 1 + (119845303/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (550971999/1000000000 : ℝ)^8463 ≤ (9109922274751/20000000000000 : ℝ)^6415 := by
    have hnat : (550971999 : ℕ)^8463*20000000000000^6415 ≤ 9109922274751^6415*1000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550971999 1000000000 9109922274751 20000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1278353799/5000000000 : ℝ)^8463 ≤ (16541778546217/100000000000000 : ℝ)^6415 := by
    have hnat : (1278353799 : ℕ)^8463*100000000000000^6415 ≤ 16541778546217^6415*5000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1278353799 5000000000 16541778546217 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (119845303/250000000 : ℝ)^8463 ≤ (3790861007433/10000000000000 : ℝ)^6415 := by
    have hnat : (119845303 : ℕ)^8463*10000000000000^6415 ≤ 3790861007433^6415*250000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119845303 250000000 3790861007433 10000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(550971999/1000000000 : ℝ), (-1278353799/5000000000 : ℝ), (119845303/250000000 : ℝ)] ![(9109922274751/20000000000000 : ℝ), (16541778546217/100000000000000 : ℝ), (3790861007433/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(550971999/1000000000 : ℝ)|^8463 ≤ (9109922274751/20000000000000 : ℝ)^6415
        have hw : |(550971999/1000000000 : ℝ)|=(550971999/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1278353799/5000000000 : ℝ)|^8463 ≤ (16541778546217/100000000000000 : ℝ)^6415
        have hw : |(-1278353799/5000000000 : ℝ)|=(1278353799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(119845303/250000000 : ℝ)|^8463 ≤ (3790861007433/10000000000000 : ℝ)^6415
        have hw : |(119845303/250000000 : ℝ)|=(119845303/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s0_2 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2754860007/5000000000 : ℝ)*x 0 + (239690607/500000000 : ℝ)*x 1 + (-1278353771/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2754860007/5000000000 : ℝ)^8463 ≤ (4554961163551/10000000000000 : ℝ)^6415 := by
    have hnat : (2754860007 : ℕ)^8463*10000000000000^6415 ≤ 4554961163551^6415*5000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2754860007 5000000000 4554961163551 10000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (239690607/500000000 : ℝ)^8463 ≤ (37908610282979/100000000000000 : ℝ)^6415 := by
    have hnat : (239690607 : ℕ)^8463*100000000000000^6415 ≤ 37908610282979^6415*500000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239690607 500000000 37908610282979 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1278353771/5000000000 : ℝ)^8463 ≤ (16541778068229/100000000000000 : ℝ)^6415 := by
    have hnat : (1278353771 : ℕ)^8463*100000000000000^6415 ≤ 16541778068229^6415*5000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1278353771 5000000000 16541778068229 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2754860007/5000000000 : ℝ), (239690607/500000000 : ℝ), (-1278353771/5000000000 : ℝ)] ![(4554961163551/10000000000000 : ℝ), (37908610282979/100000000000000 : ℝ), (16541778068229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2754860007/5000000000 : ℝ)|^8463 ≤ (4554961163551/10000000000000 : ℝ)^6415
        have hw : |(2754860007/5000000000 : ℝ)|=(2754860007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(239690607/500000000 : ℝ)|^8463 ≤ (37908610282979/100000000000000 : ℝ)^6415
        have hw : |(239690607/500000000 : ℝ)|=(239690607/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1278353771/5000000000 : ℝ)|^8463 ≤ (16541778068229/100000000000000 : ℝ)^6415
        have hw : |(-1278353771/5000000000 : ℝ)|=(1278353771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s0_3 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1047375273/2500000000 : ℝ)*x 0 + (3110841763/10000000000 : ℝ)*x 1 + (2813692771/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1047375273/2500000000 : ℝ)^8463 ≤ (31734887432429/100000000000000 : ℝ)^6415 := by
    have hnat : (1047375273 : ℕ)^8463*100000000000000^6415 ≤ 31734887432429^6415*2500000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047375273 2500000000 31734887432429 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3110841763/10000000000 : ℝ)^8463 ≤ (5356958923127/25000000000000 : ℝ)^6415 := by
    have hnat : (3110841763 : ℕ)^8463*25000000000000^6415 ≤ 5356958923127^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3110841763 10000000000 5356958923127 25000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2813692771/5000000000 : ℝ)^8463 ≤ (2927329803999/6250000000000 : ℝ)^6415 := by
    have hnat : (2813692771 : ℕ)^8463*6250000000000^6415 ≤ 2927329803999^6415*5000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2813692771 5000000000 2927329803999 6250000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1047375273/2500000000 : ℝ), (3110841763/10000000000 : ℝ), (2813692771/5000000000 : ℝ)] ![(31734887432429/100000000000000 : ℝ), (5356958923127/25000000000000 : ℝ), (2927329803999/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1047375273/2500000000 : ℝ)|^8463 ≤ (31734887432429/100000000000000 : ℝ)^6415
        have hw : |(1047375273/2500000000 : ℝ)|=(1047375273/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3110841763/10000000000 : ℝ)|^8463 ≤ (5356958923127/25000000000000 : ℝ)^6415
        have hw : |(3110841763/10000000000 : ℝ)|=(3110841763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2813692771/5000000000 : ℝ)|^8463 ≤ (2927329803999/6250000000000 : ℝ)^6415
        have hw : |(2813692771/5000000000 : ℝ)|=(2813692771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s0_4 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1856406603/10000000000 : ℝ)*x 0 + (965138663/2000000000 : ℝ)*x 1 + (5994912657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1856406603/10000000000 : ℝ)^8463 ≤ (542207742573/5000000000000 : ℝ)^6415 := by
    have hnat : (1856406603 : ℕ)^8463*5000000000000^6415 ≤ 542207742573^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1856406603 10000000000 542207742573 5000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (965138663/2000000000 : ℝ)^8463 ≤ (38241560235213/100000000000000 : ℝ)^6415 := by
    have hnat : (965138663 : ℕ)^8463*100000000000000^6415 ≤ 38241560235213^6415*2000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      965138663 2000000000 38241560235213 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5994912657/10000000000 : ℝ)^8463 ≤ (12728571224189/25000000000000 : ℝ)^6415 := by
    have hnat : (5994912657 : ℕ)^8463*25000000000000^6415 ≤ 12728571224189^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5994912657 10000000000 12728571224189 25000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1856406603/10000000000 : ℝ), (965138663/2000000000 : ℝ), (5994912657/10000000000 : ℝ)] ![(542207742573/5000000000000 : ℝ), (38241560235213/100000000000000 : ℝ), (12728571224189/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1856406603/10000000000 : ℝ)|^8463 ≤ (542207742573/5000000000000 : ℝ)^6415
        have hw : |(-1856406603/10000000000 : ℝ)|=(1856406603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(965138663/2000000000 : ℝ)|^8463 ≤ (38241560235213/100000000000000 : ℝ)^6415
        have hw : |(965138663/2000000000 : ℝ)|=(965138663/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5994912657/10000000000 : ℝ)|^8463 ≤ (12728571224189/25000000000000 : ℝ)^6415
        have hw : |(5994912657/10000000000 : ℝ)|=(5994912657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s0_5 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2586951321/5000000000 : ℝ)*x 0 + (-677802429/5000000000 : ℝ)*x 1 + (5994915033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2586951321/5000000000 : ℝ)^8463 ≤ (131009940417/312500000000 : ℝ)^6415 := by
    have hnat : (2586951321 : ℕ)^8463*312500000000^6415 ≤ 131009940417^6415*5000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586951321 5000000000 131009940417 312500000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (677802429/5000000000 : ℝ)^8463 ≤ (7162507537263/100000000000000 : ℝ)^6415 := by
    have hnat : (677802429 : ℕ)^8463*100000000000000^6415 ≤ 7162507537263^6415*5000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677802429 5000000000 7162507537263 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5994915033/10000000000 : ℝ)^8463 ≤ (25457155759079/50000000000000 : ℝ)^6415 := by
    have hnat : (5994915033 : ℕ)^8463*50000000000000^6415 ≤ 25457155759079^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5994915033 10000000000 25457155759079 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2586951321/5000000000 : ℝ), (-677802429/5000000000 : ℝ), (5994915033/10000000000 : ℝ)] ![(131009940417/312500000000 : ℝ), (7162507537263/100000000000000 : ℝ), (25457155759079/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2586951321/5000000000 : ℝ)|^8463 ≤ (131009940417/312500000000 : ℝ)^6415
        have hw : |(2586951321/5000000000 : ℝ)|=(2586951321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-677802429/5000000000 : ℝ)|^8463 ≤ (7162507537263/100000000000000 : ℝ)^6415
        have hw : |(-677802429/5000000000 : ℝ)|=(677802429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5994915033/10000000000 : ℝ)|^8463 ≤ (25457155759079/50000000000000 : ℝ)^6415
        have hw : |(5994915033/10000000000 : ℝ)|=(5994915033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s0_6 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5173903739/10000000000 : ℝ)*x 0 + (2997456537/5000000000 : ℝ)*x 1 + (-54224253/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5173903739/10000000000 : ℝ)^8463 ≤ (41923192659991/100000000000000 : ℝ)^6415 := by
    have hnat : (5173903739 : ℕ)^8463*100000000000000^6415 ≤ 41923192659991^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5173903739 10000000000 41923192659991 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2997456537/5000000000 : ℝ)^8463 ≤ (25457144784473/50000000000000 : ℝ)^6415 := by
    have hnat : (2997456537 : ℕ)^8463*50000000000000^6415 ≤ 25457144784473^6415*5000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2997456537 5000000000 25457144784473 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54224253/400000000 : ℝ)^8463 ≤ (7162517762887/100000000000000 : ℝ)^6415 := by
    have hnat : (54224253 : ℕ)^8463*100000000000000^6415 ≤ 7162517762887^6415*400000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54224253 400000000 7162517762887 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5173903739/10000000000 : ℝ), (2997456537/5000000000 : ℝ), (-54224253/400000000 : ℝ)] ![(41923192659991/100000000000000 : ℝ), (25457144784473/50000000000000 : ℝ), (7162517762887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5173903739/10000000000 : ℝ)|^8463 ≤ (41923192659991/100000000000000 : ℝ)^6415
        have hw : |(5173903739/10000000000 : ℝ)|=(5173903739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2997456537/5000000000 : ℝ)|^8463 ≤ (25457144784473/50000000000000 : ℝ)^6415
        have hw : |(2997456537/5000000000 : ℝ)|=(2997456537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-54224253/400000000 : ℝ)|^8463 ≤ (7162517762887/100000000000000 : ℝ)^6415
        have hw : |(-54224253/400000000 : ℝ)|=(54224253/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s0_7 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4199369623/10000000000 : ℝ)*x 0 + (5562380851/10000000000 : ℝ)*x 1 + (317815561/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4199369623/10000000000 : ℝ)^8463 ≤ (15916771093791/50000000000000 : ℝ)^6415 := by
    have hnat : (4199369623 : ℕ)^8463*50000000000000^6415 ≤ 15916771093791^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4199369623 10000000000 15916771093791 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5562380851/10000000000 : ℝ)^8463 ≤ (576560350177/1250000000000 : ℝ)^6415 := by
    have hnat : (5562380851 : ℕ)^8463*1250000000000^6415 ≤ 576560350177^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5562380851 10000000000 576560350177 1250000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (317815561/1000000000 : ℝ)^8463 ≤ (4408325955287/20000000000000 : ℝ)^6415 := by
    have hnat : (317815561 : ℕ)^8463*20000000000000^6415 ≤ 4408325955287^6415*1000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317815561 1000000000 4408325955287 20000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4199369623/10000000000 : ℝ), (5562380851/10000000000 : ℝ), (317815561/1000000000 : ℝ)] ![(15916771093791/50000000000000 : ℝ), (576560350177/1250000000000 : ℝ), (4408325955287/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4199369623/10000000000 : ℝ)|^8463 ≤ (15916771093791/50000000000000 : ℝ)^6415
        have hw : |(4199369623/10000000000 : ℝ)|=(4199369623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5562380851/10000000000 : ℝ)|^8463 ≤ (576560350177/1250000000000 : ℝ)^6415
        have hw : |(5562380851/10000000000 : ℝ)|=(5562380851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(317815561/1000000000 : ℝ)|^8463 ≤ (4408325955287/20000000000000 : ℝ)^6415
        have hw : |(317815561/1000000000 : ℝ)|=(317815561/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1269_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75978749/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (109/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27387/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8461/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8461 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8461*1^2048 ≤ 0^2048*1^8461 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8461 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8461 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8461/2048 : ℝ) ≤ (226971578410911013/10000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8461 ≤ (226971578410911013/10000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8461*10000000000000000000^2048 ≤ 226971578410911013^2048*5^8461 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 226971578410911013 10000000000000000000 8461 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (226971578410911013/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8461 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8461/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8461 := by
      have hnat : (1 : ℕ)^2048*1^8461 ≤ 1^8461*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8461 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10226971578410911013/10000000000000000000 : ℝ) ≤ (2513618123979393/2500000000000000 : ℝ) ^ (8461/2048 : ℝ) := by
    have hpowers : (10226971578410911013/10000000000000000000 : ℝ)^2048 ≤ (2513618123979393/2500000000000000 : ℝ)^8461 := by
      have hnat : (10226971578410911013 : ℕ)^2048*2500000000000000^8461 ≤ 2513618123979393^8461*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10226971578410911013 10000000000000000000 2513618123979393 2500000000000000 2048 8461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2513618123979393/2500000000000000 : ℝ)) (X := (10226971578410911013/10000000000000000000 : ℝ)) (by norm_num) 8461 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (5226971578410911013/5000000000000000000 : ℝ) ≤ (1263618123979393/1250000000000000 : ℝ) ^ (8461/2048 : ℝ) := by
    have hpowers : (5226971578410911013/5000000000000000000 : ℝ)^2048 ≤ (1263618123979393/1250000000000000 : ℝ)^8461 := by
      have hnat : (5226971578410911013 : ℕ)^2048*1250000000000000^8461 ≤ 1263618123979393^8461*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5226971578410911013 5000000000000000000 1263618123979393 1250000000000000 2048 8461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1263618123979393/1250000000000000 : ℝ)) (X := (5226971578410911013/5000000000000000000 : ℝ)) (by norm_num) 8461 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(13618123979393/1000000000000000 : ℝ)*(0 : ℝ))^(8461/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(13618123979393/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(226971578410911013/10000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(13618123979393/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8461/2048 : ℝ) := by
    rw [show (1 : ℝ)+(13618123979393/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2513618123979393/2500000000000000 : ℝ) by norm_num, show 1+(226971578410911013/10000000000000000000 : ℝ)+(0 : ℝ)=(10226971578410911013/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(226971578410911013/10000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(13618123979393/1000000000000000 : ℝ)*(2/5 : ℝ))^(8461/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(13618123979393/1000000000000000 : ℝ)*(2/5 : ℝ)=(1263618123979393/1250000000000000 : ℝ) by norm_num, show 1+2*(226971578410911013/10000000000000000000 : ℝ)=(5226971578410911013/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(13618123979393/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8461/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (13618123979393/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(13618123979393/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8461/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (13618123979393/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(13618123979393/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8461/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (13618123979393/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-115723029/625000000 : ℝ)*X 0 0+(3013963119/5000000000 : ℝ)*X 0 1+(191752487/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((550971999/1000000000 : ℝ)*X 1 0+(-1278353799/5000000000 : ℝ)*X 1 1+(119845303/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2754860007/5000000000 : ℝ)*X 2 0+(239690607/500000000 : ℝ)*X 2 1+(-1278353771/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1047375273/2500000000 : ℝ)*X 0 0+(3110841763/10000000000 : ℝ)*X 0 1+(2813692771/5000000000 : ℝ)*X 0 2+(1047375273/2500000000 : ℝ)*X 1 0+(3110841763/10000000000 : ℝ)*X 1 1+(2813692771/5000000000 : ℝ)*X 1 2+(1047375273/2500000000 : ℝ)*X 2 0+(3110841763/10000000000 : ℝ)*X 2 1+(2813692771/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1856406603/10000000000 : ℝ)*X 0 0+(965138663/2000000000 : ℝ)*X 0 1+(5994912657/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2586951321/5000000000 : ℝ)*X 1 0+(-677802429/5000000000 : ℝ)*X 1 1+(5994915033/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5173903739/10000000000 : ℝ)*X 2 0+(2997456537/5000000000 : ℝ)*X 2 1+(-54224253/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4199369623/10000000000 : ℝ)*X 0 0+(5562380851/10000000000 : ℝ)*X 0 1+(317815561/1000000000 : ℝ)*X 0 2+(4199369623/10000000000 : ℝ)*X 1 0+(5562380851/10000000000 : ℝ)*X 1 1+(317815561/1000000000 : ℝ)*X 1 2+(4199369623/10000000000 : ℝ)*X 2 0+(5562380851/10000000000 : ℝ)*X 2 1+(317815561/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (36499705946427692830137/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (46370393/100000000000000 : ℝ)*(base1) + (229505529/25000000000000 : ℝ)*(base19) + (855127821/100000000000000 : ℝ)*(base23) + (66423921/100000000000000 : ℝ)*(base24) + (206582559/100000000000000 : ℝ)*(upper3) + (120767605021199/20000000000000 : ℝ)*(major0) + (120767605021199/20000000000000 : ℝ)*(major1) + (120767605021199/20000000000000 : ℝ)*(major2) + (810300966432601/100000000000000 : ℝ)*(sp0) + (405151019549489/50000000000000 : ℝ)*(sp1) + (810302035569353/100000000000000 : ℝ)*(sp2) + (397371329697593/100000000000000 : ℝ)*(sp3) + (1018529443/50000000000000 : ℝ)*(sp4) + (797678609/50000000000000 : ℝ)*(sp7) + (99343242856301/25000000000000 : ℝ)*(f.failure) + (162060591424219/20000000000000 : ℝ)*(f.sum) + (15144591672207/10000000000000000000000000000 : ℝ)*base65 + (59957182052207/20000000000000000000000000000 : ℝ)*base67 + (49623390892207/20000000000000000000000000000 : ℝ)*base69 + (98945392352207/20000000000000000000000000000 : ℝ)*base71 + (10112262822207/10000000000000000000000000000 : ℝ)*base73 + (111831869232207/20000000000000000000000000000 : ℝ)*base75 + (30266177912207/20000000000000000000000000000 : ℝ)*base77 + (39349083787793/20000000000000000000000000000 : ℝ)*base80 + (845326447793/10000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (752551/1250000000000000000000 : ℝ)*base90 + (752551/1250000000000000000000 : ℝ)*base92 + (752551/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (44043073100545464808707/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (120244239/50000000000000 : ℝ)*(base1) + (335077169/50000000000000 : ℝ)*(base19) + (163102701/20000000000000 : ℝ)*(base23) + (27309887/20000000000000 : ℝ)*(upper3) + (318673912497233/50000000000000 : ℝ)*(major0) + (318673912497233/50000000000000 : ℝ)*(major1) + (318673912497233/50000000000000 : ℝ)*(major2) + (1589327543/100000000000000 : ℝ)*(sp1) + (1034991903/100000000000000 : ℝ)*(sp2) + (46203013/10000000000000 : ℝ)*(sp3) + (10690883930687/1250000000000 : ℝ)*(sp4) + (427634107242301/50000000000000 : ℝ)*(sp5) + (427634311730537/50000000000000 : ℝ)*(sp6) + (419424356055643/100000000000000 : ℝ)*(sp7) + (419425058574251/100000000000000 : ℝ)*(f.failure) + (427635236983241/50000000000000 : ℝ)*(f.sum) + (492719794569/25000000000000000000000000000 : ℝ)*base65 + (95794127630431/50000000000000000000000000000 : ℝ)*base68 + (212834758980431/50000000000000000000000000000 : ℝ)*base70 + (282895818630431/50000000000000000000000000000 : ℝ)*base72 + (21689982694569/25000000000000000000000000000 : ℝ)*base73 + (442815474280431/50000000000000000000000000000 : ℝ)*base76 + (127685782330431/50000000000000000000000000000 : ℝ)*base78 + (131553702430431/50000000000000000000000000000 : ℝ)*base80 + (24370493830431/25000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (14591999/5000000000000000000000 : ℝ)*base89 + (14591999/5000000000000000000000 : ℝ)*base91 + (14591999/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1269_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75978749/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (109/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27387/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1269_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1269_s1_0 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-204658213/1000000000 : ℝ)*x 0 + (5675251649/10000000000 : ℝ)*x 1 + (2510821619/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (204658213/1000000000 : ℝ)^8463 ≤ (2466630118543/20000000000000 : ℝ)^6415 := by
    have hnat : (204658213 : ℕ)^8463*20000000000000^6415 ≤ 2466630118543^6415*1000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204658213 1000000000 2466630118543 20000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5675251649/10000000000 : ℝ)^8463 ≤ (740055803701/1562500000000 : ℝ)^6415 := by
    have hnat : (5675251649 : ℕ)^8463*1562500000000^6415 ≤ 740055803701^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5675251649 10000000000 740055803701 1562500000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2510821619/5000000000 : ℝ)^8463 ≤ (20151638976199/50000000000000 : ℝ)^6415 := by
    have hnat : (2510821619 : ℕ)^8463*50000000000000^6415 ≤ 20151638976199^6415*5000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2510821619 5000000000 20151638976199 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-204658213/1000000000 : ℝ), (5675251649/10000000000 : ℝ), (2510821619/5000000000 : ℝ)] ![(2466630118543/20000000000000 : ℝ), (740055803701/1562500000000 : ℝ), (20151638976199/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-204658213/1000000000 : ℝ)|^8463 ≤ (2466630118543/20000000000000 : ℝ)^6415
        have hw : |(-204658213/1000000000 : ℝ)|=(204658213/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5675251649/10000000000 : ℝ)|^8463 ≤ (740055803701/1562500000000 : ℝ)^6415
        have hw : |(5675251649/10000000000 : ℝ)|=(5675251649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2510821619/5000000000 : ℝ)|^8463 ≤ (20151638976199/50000000000000 : ℝ)^6415
        have hw : |(2510821619/5000000000 : ℝ)|=(2510821619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s1_1 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5413171041/10000000000 : ℝ)*x 0 + (-599392617/2500000000 : ℝ)*x 1 + (313852719/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5413171041/10000000000 : ℝ)^8463 ≤ (22249781878009/50000000000000 : ℝ)^6415 := by
    have hnat : (5413171041 : ℕ)^8463*50000000000000^6415 ≤ 22249781878009^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413171041 10000000000 22249781878009 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (599392617/2500000000 : ℝ)^8463 ≤ (15197155459403/100000000000000 : ℝ)^6415 := by
    have hnat : (599392617 : ℕ)^8463*100000000000000^6415 ≤ 15197155459403^6415*2500000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      599392617 2500000000 15197155459403 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (313852719/625000000 : ℝ)^8463 ≤ (40303280768859/100000000000000 : ℝ)^6415 := by
    have hnat : (313852719 : ℕ)^8463*100000000000000^6415 ≤ 40303280768859^6415*625000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      313852719 625000000 40303280768859 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5413171041/10000000000 : ℝ), (-599392617/2500000000 : ℝ), (313852719/625000000 : ℝ)] ![(22249781878009/50000000000000 : ℝ), (15197155459403/100000000000000 : ℝ), (40303280768859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5413171041/10000000000 : ℝ)|^8463 ≤ (22249781878009/50000000000000 : ℝ)^6415
        have hw : |(5413171041/10000000000 : ℝ)|=(5413171041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-599392617/2500000000 : ℝ)|^8463 ≤ (15197155459403/100000000000000 : ℝ)^6415
        have hw : |(-599392617/2500000000 : ℝ)|=(599392617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(313852719/625000000 : ℝ)|^8463 ≤ (40303280768859/100000000000000 : ℝ)^6415
        have hw : |(313852719/625000000 : ℝ)|=(313852719/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s1_2 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5413171287/10000000000 : ℝ)*x 0 + (5021643331/10000000000 : ℝ)*x 1 + (-37462037/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5413171287/10000000000 : ℝ)^8463 ≤ (44499566423901/100000000000000 : ℝ)^6415 := by
    have hnat : (5413171287 : ℕ)^8463*100000000000000^6415 ≤ 44499566423901^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413171287 10000000000 44499566423901 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5021643331/10000000000 : ℝ)^8463 ≤ (403032789371/1000000000000 : ℝ)^6415 := by
    have hnat : (5021643331 : ℕ)^8463*1000000000000^6415 ≤ 403032789371^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5021643331 10000000000 403032789371 1000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (37462037/156250000 : ℝ)^8463 ≤ (15197154623187/100000000000000 : ℝ)^6415 := by
    have hnat : (37462037 : ℕ)^8463*100000000000000^6415 ≤ 15197154623187^6415*156250000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37462037 156250000 15197154623187 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5413171287/10000000000 : ℝ), (5021643331/10000000000 : ℝ), (-37462037/156250000 : ℝ)] ![(44499566423901/100000000000000 : ℝ), (403032789371/1000000000000 : ℝ), (15197154623187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5413171287/10000000000 : ℝ)|^8463 ≤ (44499566423901/100000000000000 : ℝ)^6415
        have hw : |(5413171287/10000000000 : ℝ)|=(5413171287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5021643331/10000000000 : ℝ)|^8463 ≤ (403032789371/1000000000000 : ℝ)^6415
        have hw : |(5021643331/10000000000 : ℝ)|=(5021643331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-37462037/156250000 : ℝ)|^8463 ≤ (15197154623187/100000000000000 : ℝ)^6415
        have hw : |(-37462037/156250000 : ℝ)|=(37462037/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s1_3 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4304716219/10000000000 : ℝ)*x 0 + (147505133/400000000 : ℝ)*x 1 + (2510217211/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4304716219/10000000000 : ℝ)^8463 ≤ (32891272421491/100000000000000 : ℝ)^6415 := by
    have hnat : (4304716219 : ℕ)^8463*100000000000000^6415 ≤ 32891272421491^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4304716219 10000000000 32891272421491 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (147505133/400000000 : ℝ)^8463 ≤ (26818248305287/100000000000000 : ℝ)^6415 := by
    have hnat : (147505133 : ℕ)^8463*100000000000000^6415 ≤ 26818248305287^6415*400000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147505133 400000000 26818248305287 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2510217211/5000000000 : ℝ)^8463 ≤ (5036309907117/12500000000000 : ℝ)^6415 := by
    have hnat : (2510217211 : ℕ)^8463*12500000000000^6415 ≤ 5036309907117^6415*5000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2510217211 5000000000 5036309907117 12500000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4304716219/10000000000 : ℝ), (147505133/400000000 : ℝ), (2510217211/5000000000 : ℝ)] ![(32891272421491/100000000000000 : ℝ), (26818248305287/100000000000000 : ℝ), (5036309907117/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4304716219/10000000000 : ℝ)|^8463 ≤ (32891272421491/100000000000000 : ℝ)^6415
        have hw : |(4304716219/10000000000 : ℝ)|=(4304716219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(147505133/400000000 : ℝ)|^8463 ≤ (26818248305287/100000000000000 : ℝ)^6415
        have hw : |(147505133/400000000 : ℝ)|=(147505133/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2510217211/5000000000 : ℝ)|^8463 ≤ (5036309907117/12500000000000 : ℝ)^6415
        have hw : |(2510217211/5000000000 : ℝ)|=(2510217211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s1_4 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2047265511/10000000000 : ℝ)*x 0 + (503029849/1000000000 : ℝ)*x 1 + (5666430017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2047265511/10000000000 : ℝ)^8463 ≤ (12338583828881/100000000000000 : ℝ)^6415 := by
    have hnat : (2047265511 : ℕ)^8463*100000000000000^6415 ≤ 12338583828881^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2047265511 10000000000 12338583828881 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (503029849/1000000000 : ℝ)^8463 ≤ (10098736677/25000000000 : ℝ)^6415 := by
    have hnat : (503029849 : ℕ)^8463*25000000000^6415 ≤ 10098736677^6415*1000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503029849 1000000000 10098736677 25000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5666430017/10000000000 : ℝ)^8463 ≤ (23633234723869/50000000000000 : ℝ)^6415 := by
    have hnat : (5666430017 : ℕ)^8463*50000000000000^6415 ≤ 23633234723869^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5666430017 10000000000 23633234723869 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2047265511/10000000000 : ℝ), (503029849/1000000000 : ℝ), (5666430017/10000000000 : ℝ)] ![(12338583828881/100000000000000 : ℝ), (10098736677/25000000000 : ℝ), (23633234723869/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2047265511/10000000000 : ℝ)|^8463 ≤ (12338583828881/100000000000000 : ℝ)^6415
        have hw : |(-2047265511/10000000000 : ℝ)|=(2047265511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(503029849/1000000000 : ℝ)|^8463 ≤ (10098736677/25000000000 : ℝ)^6415
        have hw : |(503029849/1000000000 : ℝ)|=(503029849/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5666430017/10000000000 : ℝ)|^8463 ≤ (23633234723869/50000000000000 : ℝ)^6415
        have hw : |(5666430017/10000000000 : ℝ)|=(5666430017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s1_5 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5244616011/10000000000 : ℝ)*x 0 + (-438195851/2500000000 : ℝ)*x 1 + (141660753/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5244616011/10000000000 : ℝ)^8463 ≤ (10670181606559/25000000000000 : ℝ)^6415 := by
    have hnat : (5244616011 : ℕ)^8463*25000000000000^6415 ≤ 10670181606559^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244616011 10000000000 10670181606559 25000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (438195851/2500000000 : ℝ)^8463 ≤ (10052802973953/100000000000000 : ℝ)^6415 := by
    have hnat : (438195851 : ℕ)^8463*100000000000000^6415 ≤ 10052802973953^6415*2500000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438195851 2500000000 10052802973953 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (141660753/250000000 : ℝ)^8463 ≤ (11816617645301/25000000000000 : ℝ)^6415 := by
    have hnat : (141660753 : ℕ)^8463*25000000000000^6415 ≤ 11816617645301^6415*250000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141660753 250000000 11816617645301 25000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5244616011/10000000000 : ℝ), (-438195851/2500000000 : ℝ), (141660753/250000000 : ℝ)] ![(10670181606559/25000000000000 : ℝ), (10052802973953/100000000000000 : ℝ), (11816617645301/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5244616011/10000000000 : ℝ)|^8463 ≤ (10670181606559/25000000000000 : ℝ)^6415
        have hw : |(5244616011/10000000000 : ℝ)|=(5244616011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-438195851/2500000000 : ℝ)|^8463 ≤ (10052802973953/100000000000000 : ℝ)^6415
        have hw : |(-438195851/2500000000 : ℝ)|=(438195851/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(141660753/250000000 : ℝ)|^8463 ≤ (11816617645301/25000000000000 : ℝ)^6415
        have hw : |(141660753/250000000 : ℝ)|=(141660753/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s1_6 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5244616417/10000000000 : ℝ)*x 0 + (5666430771/10000000000 : ℝ)*x 1 + (-1752781883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5244616417/10000000000 : ℝ)^8463 ≤ (8536146157017/20000000000000 : ℝ)^6415 := by
    have hnat : (5244616417 : ℕ)^8463*20000000000000^6415 ≤ 8536146157017^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244616417 10000000000 8536146157017 20000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5666430771/10000000000 : ℝ)^8463 ≤ (945329554903/2000000000000 : ℝ)^6415 := by
    have hnat : (5666430771 : ℕ)^8463*2000000000000^6415 ≤ 945329554903^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5666430771 10000000000 945329554903 2000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1752781883/10000000000 : ℝ)^8463 ≤ (2513197866383/25000000000000 : ℝ)^6415 := by
    have hnat : (1752781883 : ℕ)^8463*25000000000000^6415 ≤ 2513197866383^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1752781883 10000000000 2513197866383 25000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5244616417/10000000000 : ℝ), (5666430771/10000000000 : ℝ), (-1752781883/10000000000 : ℝ)] ![(8536146157017/20000000000000 : ℝ), (945329554903/2000000000000 : ℝ), (2513197866383/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5244616417/10000000000 : ℝ)|^8463 ≤ (8536146157017/20000000000000 : ℝ)^6415
        have hw : |(5244616417/10000000000 : ℝ)|=(5244616417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5666430771/10000000000 : ℝ)|^8463 ≤ (945329554903/2000000000000 : ℝ)^6415
        have hw : |(5666430771/10000000000 : ℝ)|=(5666430771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1752781883/10000000000 : ℝ)|^8463 ≤ (2513197866383/25000000000000 : ℝ)^6415
        have hw : |(-1752781883/10000000000 : ℝ)|=(1752781883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s1_7 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (13456589/31250000 : ℝ)*x 0 + (2501392937/5000000000 : ℝ)*x 1 + (3705615981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13456589/31250000 : ℝ)^8463 ≤ (32905307243377/100000000000000 : ℝ)^6415 := by
    have hnat : (13456589 : ℕ)^8463*100000000000000^6415 ≤ 32905307243377^6415*31250000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13456589 31250000 32905307243377 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2501392937/5000000000 : ℝ)^8463 ≤ (40103732171573/100000000000000 : ℝ)^6415 := by
    have hnat : (2501392937 : ℕ)^8463*100000000000000^6415 ≤ 40103732171573^6415*5000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2501392937 5000000000 40103732171573 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3705615981/10000000000 : ℝ)^8463 ≤ (3373870070731/12500000000000 : ℝ)^6415 := by
    have hnat : (3705615981 : ℕ)^8463*12500000000000^6415 ≤ 3373870070731^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3705615981 10000000000 3373870070731 12500000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(13456589/31250000 : ℝ), (2501392937/5000000000 : ℝ), (3705615981/10000000000 : ℝ)] ![(32905307243377/100000000000000 : ℝ), (40103732171573/100000000000000 : ℝ), (3373870070731/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(13456589/31250000 : ℝ)|^8463 ≤ (32905307243377/100000000000000 : ℝ)^6415
        have hw : |(13456589/31250000 : ℝ)|=(13456589/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2501392937/5000000000 : ℝ)|^8463 ≤ (40103732171573/100000000000000 : ℝ)^6415
        have hw : |(2501392937/5000000000 : ℝ)|=(2501392937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3705615981/10000000000 : ℝ)|^8463 ≤ (3373870070731/12500000000000 : ℝ)^6415
        have hw : |(3705615981/10000000000 : ℝ)|=(3705615981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1269_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75978749/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27387/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (109/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (3101/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20017/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27387/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (109/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27387/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (109/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27387/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (109/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27387/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (109/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27387/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (109/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27387/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (109/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (109/12500 : ℝ) ^ (8461/2048 : ℝ) ≤ (310139874593/100000000000000000000 : ℝ) := by
    have hpowers : (109/12500 : ℝ)^8461 ≤ (310139874593/100000000000000000000 : ℝ)^2048 := by
      have hnat : (109 : ℕ)^8461*100000000000000000000^2048 ≤ 310139874593^2048*12500^8461 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        109 12500 310139874593 100000000000000000000 8461 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (109/12500 : ℝ)) (X := (310139874593/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8461 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (27387/100000 : ℝ) ^ (8461/2048 : ℝ) ≤ (474570382164928633/100000000000000000000 : ℝ) := by
    have hpowers : (27387/100000 : ℝ)^8461 ≤ (474570382164928633/100000000000000000000 : ℝ)^2048 := by
      have hnat : (27387 : ℕ)^8461*100000000000000000000^2048 ≤ 474570382164928633^2048*100000^8461 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27387 100000 474570382164928633 100000000000000000000 8461 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27387/100000 : ℝ)) (X := (474570382164928633/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8461 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000310139874593/50000000000000000000 : ℝ) ≤ (10000000015013981/10000000000000000 : ℝ) ^ (8461/2048 : ℝ) := by
    have hpowers : (50000000310139874593/50000000000000000000 : ℝ)^2048 ≤ (10000000015013981/10000000000000000 : ℝ)^8461 := by
      have hnat : (50000000310139874593 : ℕ)^2048*10000000000000000^8461 ≤ 10000000015013981^8461*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000310139874593 50000000000000000000 10000000015013981 10000000000000000 2048 8461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000015013981/10000000000000000 : ℝ)) (X := (50000000310139874593/50000000000000000000 : ℝ)) (by norm_num) 8461 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50237285346152401613/50000000000000000000 : ℝ) ≤ (2502866616308363/2500000000000000 : ℝ) ^ (8461/2048 : ℝ) := by
    have hpowers : (50237285346152401613/50000000000000000000 : ℝ)^2048 ≤ (2502866616308363/2500000000000000 : ℝ)^8461 := by
      have hnat : (50237285346152401613 : ℕ)^2048*2500000000000000^8461 ≤ 2502866616308363^8461*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50237285346152401613 50000000000000000000 2502866616308363 2500000000000000 2048 8461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2502866616308363/2500000000000000 : ℝ)) (X := (50237285346152401613/50000000000000000000 : ℝ)) (by norm_num) 8461 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50474570382164928633/50000000000000000000 : ℝ) ≤ (10022932915452923/10000000000000000 : ℝ) ^ (8461/2048 : ℝ) := by
    have hpowers : (50474570382164928633/50000000000000000000 : ℝ)^2048 ≤ (10022932915452923/10000000000000000 : ℝ)^8461 := by
      have hnat : (50474570382164928633 : ℕ)^2048*10000000000000000^8461 ≤ 10022932915452923^8461*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50474570382164928633 50000000000000000000 10022932915452923 10000000000000000 2048 8461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10022932915452923/10000000000000000 : ℝ)) (X := (50474570382164928633/50000000000000000000 : ℝ)) (by norm_num) 8461 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(310139874593/100000000000000000000 : ℝ) ≤ ((265130002908912948791/265150000000000000000 : ℝ)+2*(11466450219471/2651500000000000 : ℝ)*(109/12500 : ℝ))^(8461/2048 : ℝ) := by
    rw [show (265130002908912948791/265150000000000000000 : ℝ)+2*(11466450219471/2651500000000000 : ℝ)*(109/12500 : ℝ)=(10000000015013981/10000000000000000 : ℝ) by norm_num, show 1+2*(310139874593/100000000000000000000 : ℝ)=(50000000310139874593/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(474570382164928633/100000000000000000000 : ℝ)+(310139874593/100000000000000000000 : ℝ) ≤ ((265130002908912948791/265150000000000000000 : ℝ)+(11466450219471/2651500000000000 : ℝ)*((27387/100000 : ℝ)+(109/12500 : ℝ)))^(8461/2048 : ℝ) := by
    rw [show (265130002908912948791/265150000000000000000 : ℝ)+(11466450219471/2651500000000000 : ℝ)*((27387/100000 : ℝ)+(109/12500 : ℝ))=(2502866616308363/2500000000000000 : ℝ) by norm_num, show 1+(474570382164928633/100000000000000000000 : ℝ)+(310139874593/100000000000000000000 : ℝ)=(50237285346152401613/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(474570382164928633/100000000000000000000 : ℝ) ≤ ((265130002908912948791/265150000000000000000 : ℝ)+2*(11466450219471/2651500000000000 : ℝ)*(27387/100000 : ℝ))^(8461/2048 : ℝ) := by
    rw [show (265130002908912948791/265150000000000000000 : ℝ)+2*(11466450219471/2651500000000000 : ℝ)*(27387/100000 : ℝ)=(10022932915452923/10000000000000000 : ℝ) by norm_num, show 1+2*(474570382164928633/100000000000000000000 : ℝ)=(50474570382164928633/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (265130002908912948791/265150000000000000000 : ℝ)*(X 1 0+X 2 0)+(11466450219471/2651500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8461/2048 : ℝ)) (lo := (109/12500 : ℝ)) (hi := (27387/100000 : ℝ)) (c := (265130002908912948791/265150000000000000000 : ℝ)) (alpha := (11466450219471/2651500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (265130002908912948791/265150000000000000000 : ℝ)*(X 0 1+X 2 1)+(11466450219471/2651500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8461/2048 : ℝ)) (lo := (109/12500 : ℝ)) (hi := (27387/100000 : ℝ)) (c := (265130002908912948791/265150000000000000000 : ℝ)) (alpha := (11466450219471/2651500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (265130002908912948791/265150000000000000000 : ℝ)*(X 0 2+X 1 2)+(11466450219471/2651500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8461/2048 : ℝ)) (lo := (109/12500 : ℝ)) (hi := (27387/100000 : ℝ)) (c := (265130002908912948791/265150000000000000000 : ℝ)) (alpha := (11466450219471/2651500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-204658213/1000000000 : ℝ)*X 0 0+(5675251649/10000000000 : ℝ)*X 0 1+(2510821619/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5413171041/10000000000 : ℝ)*X 1 0+(-599392617/2500000000 : ℝ)*X 1 1+(313852719/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5413171287/10000000000 : ℝ)*X 2 0+(5021643331/10000000000 : ℝ)*X 2 1+(-37462037/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4304716219/10000000000 : ℝ)*X 0 0+(147505133/400000000 : ℝ)*X 0 1+(2510217211/5000000000 : ℝ)*X 0 2+(4304716219/10000000000 : ℝ)*X 1 0+(147505133/400000000 : ℝ)*X 1 1+(2510217211/5000000000 : ℝ)*X 1 2+(4304716219/10000000000 : ℝ)*X 2 0+(147505133/400000000 : ℝ)*X 2 1+(2510217211/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2047265511/10000000000 : ℝ)*X 0 0+(503029849/1000000000 : ℝ)*X 0 1+(5666430017/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5244616011/10000000000 : ℝ)*X 1 0+(-438195851/2500000000 : ℝ)*X 1 1+(141660753/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5244616417/10000000000 : ℝ)*X 2 0+(5666430771/10000000000 : ℝ)*X 2 1+(-1752781883/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((13456589/31250000 : ℝ)*X 0 0+(2501392937/5000000000 : ℝ)*X 0 1+(3705615981/10000000000 : ℝ)*X 0 2+(13456589/31250000 : ℝ)*X 1 0+(2501392937/5000000000 : ℝ)*X 1 1+(3705615981/10000000000 : ℝ)*X 1 2+(13456589/31250000 : ℝ)*X 2 0+(2501392937/5000000000 : ℝ)*X 2 1+(3705615981/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7460437046453478331038680049/2651500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (461999/3125000000000 : ℝ)*(base1) + (33472929/5000000000000 : ℝ)*(base19) + (184746973/25000000000000 : ℝ)*(base23) + (64542221/100000000000000 : ℝ)*(upper3) + (119787823/100000000000000 : ℝ)*(upper5) + (228027787736413/20000000000000 : ℝ)*(major0) + (228027787736413/20000000000000 : ℝ)*(major1) + (228027787736413/20000000000000 : ℝ)*(major2) + (191246488674463/12500000000000 : ℝ)*(sp0) + (1529975909050707/100000000000000 : ℝ)*(sp1) + (382493959880349/25000000000000 : ℝ)*(sp2) + (375149498507943/50000000000000 : ℝ)*(sp3) + (4683897551/100000000000000 : ℝ)*(sp4) + (438653219/20000000000000 : ℝ)*(sp7) + (750301205065949/100000000000000 : ℝ)*(f.failure) + (191247072313661/12500000000000 : ℝ)*(f.sum) + (3260649749071/828593750000000000000000000 : ℝ)*base66 + (2181676226229326683/5303000000000000000000000000000000 : ℝ)*base67 + (3466565725190673317/5303000000000000000000000000000000 : ℝ)*base70 + (3670282655464326683/5303000000000000000000000000000000 : ℝ)*base71 + (187703542340037/26515000000000000000000000000 : ℝ)*base74 + (16279246951117673317/5303000000000000000000000000000000 : ℝ)*base76 + (16037684011030673317/5303000000000000000000000000000000 : ℝ)*base78 + (43560390669340673317/5303000000000000000000000000000000 : ℝ)*base80 + (74775637345681/13257500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (17517801/5000000000000000000000 : ℝ)*base89 + (17517801/5000000000000000000000 : ℝ)*base91 + (17517801/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3711802404633444171/26515000000000000000000000 : ℝ) := by norm_num
    linear_combination (16897249/3125000000000 : ℝ)*(base19) + (519339497/50000000000000 : ℝ)*(base23) + (52940077/50000000000000 : ℝ)*(upper2) + (57998707/50000000000000 : ℝ)*(upper3) + (11714551998697/1000000000000 : ℝ)*(major0) + (11714551998697/1000000000000 : ℝ)*(major1) + (11714551998697/1000000000000 : ℝ)*(major2) + (521550461/25000000000000 : ℝ)*(sp1) + (1878101007/25000000000000 : ℝ)*(sp2) + (7650293/100000000000000 : ℝ)*(sp3) + (98250039003723/6250000000000 : ℝ)*(sp4) + (392999499286439/25000000000000 : ℝ)*(sp5) + (785996036488273/50000000000000 : ℝ)*(sp6) + (192727440840811/25000000000000 : ℝ)*(sp7) + (770909771013537/100000000000000 : ℝ)*(f.failure) + (98250039003723/6250000000000 : ℝ)*(f.sum) + (17832191545669/5303000000000000000000000000 : ℝ)*base66 + (959752211203275327/265150000000000000000000000000000 : ℝ)*base67 + (108013166601474673/265150000000000000000000000000000 : ℝ)*base70 + (745584780397624673/265150000000000000000000000000000 : ℝ)*base72 + (533996591547/5303000000000000000000000000 : ℝ)*base74 + (1145419970882525327/265150000000000000000000000000000 : ℝ)*base75 + (1827503051987324673/265150000000000000000000000000000 : ℝ)*base78 + (371389156706175327/265150000000000000000000000000000 : ℝ)*base79 + (322600911751/331437500000000000000000000 : ℝ)*base82 + (3325213/5000000000000000000000 : ℝ)*base89 + (3325213/5000000000000000000000 : ℝ)*base91 + (3325213/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1269_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75978749/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27387/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (109/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3101/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20017/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1269_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1269_s2_0 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-261655927/1250000000 : ℝ)*x 0 + (1100138557/2000000000 : ℝ)*x 1 + (5166430979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (261655927/1250000000 : ℝ)^8463 ≤ (3176371907279/25000000000000 : ℝ)^6415 := by
    have hnat : (261655927 : ℕ)^8463*25000000000000^6415 ≤ 3176371907279^6415*1250000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261655927 1250000000 3176371907279 25000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1100138557/2000000000 : ℝ)^8463 ≤ (22725591252539/50000000000000 : ℝ)^6415 := by
    have hnat : (1100138557 : ℕ)^8463*50000000000000^6415 ≤ 22725591252539^6415*2000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100138557 2000000000 22725591252539 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5166430979/10000000000 : ℝ)^8463 ≤ (1046083246429/2500000000000 : ℝ)^6415 := by
    have hnat : (5166430979 : ℕ)^8463*2500000000000^6415 ≤ 1046083246429^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5166430979 10000000000 1046083246429 2500000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-261655927/1250000000 : ℝ), (1100138557/2000000000 : ℝ), (5166430979/10000000000 : ℝ)] ![(3176371907279/25000000000000 : ℝ), (22725591252539/50000000000000 : ℝ), (1046083246429/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-261655927/1250000000 : ℝ)|^8463 ≤ (3176371907279/25000000000000 : ℝ)^6415
        have hw : |(-261655927/1250000000 : ℝ)|=(261655927/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1100138557/2000000000 : ℝ)|^8463 ≤ (22725591252539/50000000000000 : ℝ)^6415
        have hw : |(1100138557/2000000000 : ℝ)|=(1100138557/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5166430979/10000000000 : ℝ)|^8463 ≤ (1046083246429/2500000000000 : ℝ)^6415
        have hw : |(5166430979/10000000000 : ℝ)|=(5166430979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s2_1 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (335696007/625000000 : ℝ)*x 0 + (-1133346677/5000000000 : ℝ)*x 1 + (5166432327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335696007/625000000 : ℝ)^8463 ≤ (22022129394447/50000000000000 : ℝ)^6415 := by
    have hnat : (335696007 : ℕ)^8463*50000000000000^6415 ≤ 22022129394447^6415*625000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335696007 625000000 22022129394447 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1133346677/5000000000 : ℝ)^8463 ≤ (2822479385793/20000000000000 : ℝ)^6415 := by
    have hnat : (1133346677 : ℕ)^8463*20000000000000^6415 ≤ 2822479385793^6415*5000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133346677 5000000000 2822479385793 20000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5166432327/10000000000 : ℝ)^8463 ≤ (5230418032521/12500000000000 : ℝ)^6415 := by
    have hnat : (5166432327 : ℕ)^8463*12500000000000^6415 ≤ 5230418032521^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5166432327 10000000000 5230418032521 12500000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335696007/625000000 : ℝ), (-1133346677/5000000000 : ℝ), (5166432327/10000000000 : ℝ)] ![(22022129394447/50000000000000 : ℝ), (2822479385793/20000000000000 : ℝ), (5230418032521/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335696007/625000000 : ℝ)|^8463 ≤ (22022129394447/50000000000000 : ℝ)^6415
        have hw : |(335696007/625000000 : ℝ)|=(335696007/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1133346677/5000000000 : ℝ)|^8463 ≤ (2822479385793/20000000000000 : ℝ)^6415
        have hw : |(-1133346677/5000000000 : ℝ)|=(1133346677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5166432327/10000000000 : ℝ)|^8463 ≤ (5230418032521/12500000000000 : ℝ)^6415
        have hw : |(5166432327/10000000000 : ℝ)|=(5166432327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s2_2 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1342784219/2500000000 : ℝ)*x 0 + (80725489/156250000 : ℝ)*x 1 + (-2266693689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342784219/2500000000 : ℝ)^8463 ≤ (275276669087/625000000000 : ℝ)^6415 := by
    have hnat : (1342784219 : ℕ)^8463*625000000000^6415 ≤ 275276669087^6415*2500000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342784219 2500000000 275276669087 625000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (80725489/156250000 : ℝ)^8463 ≤ (41843333244217/100000000000000 : ℝ)^6415 := by
    have hnat : (80725489 : ℕ)^8463*100000000000000^6415 ≤ 41843333244217^6415*156250000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80725489 156250000 41843333244217 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2266693689/10000000000 : ℝ)^8463 ≤ (2822479936107/20000000000000 : ℝ)^6415 := by
    have hnat : (2266693689 : ℕ)^8463*20000000000000^6415 ≤ 2822479936107^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2266693689 10000000000 2822479936107 20000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342784219/2500000000 : ℝ), (80725489/156250000 : ℝ), (-2266693689/10000000000 : ℝ)] ![(275276669087/625000000000 : ℝ), (41843333244217/100000000000000 : ℝ), (2822479936107/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342784219/2500000000 : ℝ)|^8463 ≤ (275276669087/625000000000 : ℝ)^6415
        have hw : |(1342784219/2500000000 : ℝ)|=(1342784219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(80725489/156250000 : ℝ)|^8463 ≤ (41843333244217/100000000000000 : ℝ)^6415
        have hw : |(80725489/156250000 : ℝ)|=(80725489/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2266693689/10000000000 : ℝ)|^8463 ≤ (2822479936107/20000000000000 : ℝ)^6415
        have hw : |(-2266693689/10000000000 : ℝ)|=(2266693689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s2_3 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2168534871/5000000000 : ℝ)*x 0 + (4009140617/10000000000 : ℝ)*x 1 + (58634437/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2168534871/5000000000 : ℝ)^8463 ≤ (16608894501829/50000000000000 : ℝ)^6415 := by
    have hnat : (2168534871 : ℕ)^8463*50000000000000^6415 ≤ 16608894501829^6415*5000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2168534871 5000000000 16608894501829 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4009140617/10000000000 : ℝ)^8463 ≤ (3743128442987/12500000000000 : ℝ)^6415 := by
    have hnat : (4009140617 : ℕ)^8463*12500000000000^6415 ≤ 3743128442987^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4009140617 10000000000 3743128442987 12500000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (58634437/125000000 : ℝ)^8463 ≤ (575580991197/1562500000000 : ℝ)^6415 := by
    have hnat : (58634437 : ℕ)^8463*1562500000000^6415 ≤ 575580991197^6415*125000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58634437 125000000 575580991197 1562500000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2168534871/5000000000 : ℝ), (4009140617/10000000000 : ℝ), (58634437/125000000 : ℝ)] ![(16608894501829/50000000000000 : ℝ), (3743128442987/12500000000000 : ℝ), (575580991197/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2168534871/5000000000 : ℝ)|^8463 ≤ (16608894501829/50000000000000 : ℝ)^6415
        have hw : |(2168534871/5000000000 : ℝ)|=(2168534871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4009140617/10000000000 : ℝ)|^8463 ≤ (3743128442987/12500000000000 : ℝ)^6415
        have hw : |(4009140617/10000000000 : ℝ)|=(4009140617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(58634437/125000000 : ℝ)|^8463 ≤ (575580991197/1562500000000 : ℝ)^6415
        have hw : |(58634437/125000000 : ℝ)|=(58634437/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s2_4 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-523334447/2500000000 : ℝ)*x 0 + (2584352339/5000000000 : ℝ)*x 1 + (1374599361/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (523334447/2500000000 : ℝ)^8463 ≤ (3176552822601/25000000000000 : ℝ)^6415 := by
    have hnat : (523334447 : ℕ)^8463*25000000000000^6415 ≤ 3176552822601^6415*2500000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523334447 2500000000 3176552822601 25000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2584352339/5000000000 : ℝ)^8463 ≤ (1046690635217/2500000000000 : ℝ)^6415 := by
    have hnat : (2584352339 : ℕ)^8463*2500000000000^6415 ≤ 1046690635217^6415*5000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2584352339 5000000000 1046690635217 2500000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1374599361/2500000000 : ℝ)^8463 ≤ (45426163285461/100000000000000 : ℝ)^6415 := by
    have hnat : (1374599361 : ℕ)^8463*100000000000000^6415 ≤ 45426163285461^6415*2500000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1374599361 2500000000 45426163285461 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-523334447/2500000000 : ℝ), (2584352339/5000000000 : ℝ), (1374599361/2500000000 : ℝ)] ![(3176552822601/25000000000000 : ℝ), (1046690635217/2500000000000 : ℝ), (45426163285461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-523334447/2500000000 : ℝ)|^8463 ≤ (3176552822601/25000000000000 : ℝ)^6415
        have hw : |(-523334447/2500000000 : ℝ)|=(523334447/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2584352339/5000000000 : ℝ)|^8463 ≤ (1046690635217/2500000000000 : ℝ)^6415
        have hw : |(2584352339/5000000000 : ℝ)|=(2584352339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1374599361/2500000000 : ℝ)|^8463 ≤ (45426163285461/100000000000000 : ℝ)^6415
        have hw : |(1374599361/2500000000 : ℝ)|=(1374599361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s2_5 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (41294331/78125000 : ℝ)*x 0 + (-48368189/250000000 : ℝ)*x 1 + (5498397653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41294331/78125000 : ℝ)^8463 ≤ (8624416432157/20000000000000 : ℝ)^6415 := by
    have hnat : (41294331 : ℕ)^8463*20000000000000^6415 ≤ 8624416432157^6415*78125000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41294331 78125000 8624416432157 20000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (48368189/250000000 : ℝ)^8463 ≤ (5725876128457/50000000000000 : ℝ)^6415 := by
    have hnat : (48368189 : ℕ)^8463*50000000000000^6415 ≤ 5725876128457^6415*250000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48368189 250000000 5725876128457 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5498397653/10000000000 : ℝ)^8463 ≤ (45426165563409/100000000000000 : ℝ)^6415 := by
    have hnat : (5498397653 : ℕ)^8463*100000000000000^6415 ≤ 45426165563409^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5498397653 10000000000 45426165563409 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41294331/78125000 : ℝ), (-48368189/250000000 : ℝ), (5498397653/10000000000 : ℝ)] ![(8624416432157/20000000000000 : ℝ), (5725876128457/50000000000000 : ℝ), (45426165563409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41294331/78125000 : ℝ)|^8463 ≤ (8624416432157/20000000000000 : ℝ)^6415
        have hw : |(41294331/78125000 : ℝ)|=(41294331/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-48368189/250000000 : ℝ)|^8463 ≤ (5725876128457/50000000000000 : ℝ)^6415
        have hw : |(-48368189/250000000 : ℝ)|=(48368189/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5498397653/10000000000 : ℝ)|^8463 ≤ (45426165563409/100000000000000 : ℝ)^6415
        have hw : |(5498397653/10000000000 : ℝ)|=(5498397653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s2_6 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5285674721/10000000000 : ℝ)*x 0 + (2749198739/5000000000 : ℝ)*x 1 + (-1934727317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285674721/10000000000 : ℝ)^8463 ≤ (43122085960069/100000000000000 : ℝ)^6415 := by
    have hnat : (5285674721 : ℕ)^8463*100000000000000^6415 ≤ 43122085960069^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285674721 10000000000 43122085960069 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2749198739/5000000000 : ℝ)^8463 ≤ (11356540914009/25000000000000 : ℝ)^6415 := by
    have hnat : (2749198739 : ℕ)^8463*25000000000000^6415 ≤ 11356540914009^6415*5000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2749198739 5000000000 11356540914009 25000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1934727317/10000000000 : ℝ)^8463 ≤ (2290350071879/20000000000000 : ℝ)^6415 := by
    have hnat : (1934727317 : ℕ)^8463*20000000000000^6415 ≤ 2290350071879^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1934727317 10000000000 2290350071879 20000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285674721/10000000000 : ℝ), (2749198739/5000000000 : ℝ), (-1934727317/10000000000 : ℝ)] ![(43122085960069/100000000000000 : ℝ), (11356540914009/25000000000000 : ℝ), (2290350071879/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285674721/10000000000 : ℝ)|^8463 ≤ (43122085960069/100000000000000 : ℝ)^6415
        have hw : |(5285674721/10000000000 : ℝ)|=(5285674721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2749198739/5000000000 : ℝ)|^8463 ≤ (11356540914009/25000000000000 : ℝ)^6415
        have hw : |(2749198739/5000000000 : ℝ)|=(2749198739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1934727317/10000000000 : ℝ)|^8463 ≤ (2290350071879/20000000000000 : ℝ)^6415
        have hw : |(-1934727317/10000000000 : ℝ)|=(1934727317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s2_7 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1084313729/2500000000 : ℝ)*x 0 + (4686118331/10000000000 : ℝ)*x 1 + (401382407/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1084313729/2500000000 : ℝ)^8463 ≤ (3321966005181/10000000000000 : ℝ)^6415 := by
    have hnat : (1084313729 : ℕ)^8463*10000000000000^6415 ≤ 3321966005181^6415*2500000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084313729 2500000000 3321966005181 10000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4686118331/10000000000 : ℝ)^8463 ≤ (18394577129403/50000000000000 : ℝ)^6415 := by
    have hnat : (4686118331 : ℕ)^8463*50000000000000^6415 ≤ 18394577129403^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4686118331 10000000000 18394577129403 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (401382407/1000000000 : ℝ)^8463 ≤ (5998237135289/20000000000000 : ℝ)^6415 := by
    have hnat : (401382407 : ℕ)^8463*20000000000000^6415 ≤ 5998237135289^6415*1000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      401382407 1000000000 5998237135289 20000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1084313729/2500000000 : ℝ), (4686118331/10000000000 : ℝ), (401382407/1000000000 : ℝ)] ![(3321966005181/10000000000000 : ℝ), (18394577129403/50000000000000 : ℝ), (5998237135289/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1084313729/2500000000 : ℝ)|^8463 ≤ (3321966005181/10000000000000 : ℝ)^6415
        have hw : |(1084313729/2500000000 : ℝ)|=(1084313729/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4686118331/10000000000 : ℝ)|^8463 ≤ (18394577129403/50000000000000 : ℝ)^6415
        have hw : |(4686118331/10000000000 : ℝ)|=(4686118331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(401382407/1000000000 : ℝ)|^8463 ≤ (5998237135289/20000000000000 : ℝ)^6415
        have hw : |(401382407/1000000000 : ℝ)|=(401382407/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1269_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75978749/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20017/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3101/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (9351/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8207/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20017/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3101/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20017/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3101/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20017/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3101/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20017/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3101/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20017/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3101/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20017/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3101/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3101/50000 : ℝ) ^ (8461/2048 : ℝ) ≤ (1026901822286629/100000000000000000000 : ℝ) := by
    have hpowers : (3101/50000 : ℝ)^8461 ≤ (1026901822286629/100000000000000000000 : ℝ)^2048 := by
      have hnat : (3101 : ℕ)^8461*100000000000000000000^2048 ≤ 1026901822286629^2048*50000^8461 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3101 50000 1026901822286629 100000000000000000000 8461 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3101/50000 : ℝ)) (X := (1026901822286629/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8461 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (20017/100000 : ℝ) ^ (8461/2048 : ℝ) ≤ (64983987337918953/50000000000000000000 : ℝ) := by
    have hpowers : (20017/100000 : ℝ)^8461 ≤ (64983987337918953/50000000000000000000 : ℝ)^2048 := by
      have hnat : (20017 : ℕ)^8461*50000000000000000000^2048 ≤ 64983987337918953^2048*100000^8461 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20017 100000 64983987337918953 50000000000000000000 8461 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20017/100000 : ℝ)) (X := (64983987337918953/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8461 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001026901822286629/50000000000000000000 : ℝ) ≤ (5000024856146591/5000000000000000 : ℝ) ^ (8461/2048 : ℝ) := by
    have hpowers : (50001026901822286629/50000000000000000000 : ℝ)^2048 ≤ (5000024856146591/5000000000000000 : ℝ)^8461 := by
      have hnat : (50001026901822286629 : ℕ)^2048*5000000000000000^8461 ≤ 5000024856146591^8461*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001026901822286629 50000000000000000000 5000024856146591 5000000000000000 2048 8461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000024856146591/5000000000000000 : ℝ)) (X := (50001026901822286629/50000000000000000000 : ℝ)) (by norm_num) 8461 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20026198975299624907/20000000000000000000 : ℝ) ≤ (5001584590630033/5000000000000000 : ℝ) ^ (8461/2048 : ℝ) := by
    have hpowers : (20026198975299624907/20000000000000000000 : ℝ)^2048 ≤ (5001584590630033/5000000000000000 : ℝ)^8461 := by
      have hnat : (20026198975299624907 : ℕ)^2048*5000000000000000^8461 ≤ 5001584590630033^8461*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20026198975299624907 20000000000000000000 5001584590630033 5000000000000000 2048 8461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001584590630033/5000000000000000 : ℝ)) (X := (20026198975299624907/20000000000000000000 : ℝ)) (by norm_num) 8461 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25064983987337918953/25000000000000000000 : ℝ) ≤ (200125773004539/200000000000000 : ℝ) ^ (8461/2048 : ℝ) := by
    have hpowers : (25064983987337918953/25000000000000000000 : ℝ)^2048 ≤ (200125773004539/200000000000000 : ℝ)^8461 := by
      have hnat : (25064983987337918953 : ℕ)^2048*200000000000000^8461 ≤ 200125773004539^8461*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25064983987337918953 25000000000000000000 200125773004539 200000000000000 2048 8461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200125773004539/200000000000000 : ℝ)) (X := (25064983987337918953/25000000000000000000 : ℝ)) (by norm_num) 8461 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1026901822286629/100000000000000000000 : ℝ) ≤ ((69055996441132540097/69075000000000000000 : ℝ)+2*(779867241721/345375000000000 : ℝ)*(3101/50000 : ℝ))^(8461/2048 : ℝ) := by
    rw [show (69055996441132540097/69075000000000000000 : ℝ)+2*(779867241721/345375000000000 : ℝ)*(3101/50000 : ℝ)=(5000024856146591/5000000000000000 : ℝ) by norm_num, show 1+2*(1026901822286629/100000000000000000000 : ℝ)=(50001026901822286629/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(64983987337918953/50000000000000000000 : ℝ)+(1026901822286629/100000000000000000000 : ℝ) ≤ ((69055996441132540097/69075000000000000000 : ℝ)+(779867241721/345375000000000 : ℝ)*((20017/100000 : ℝ)+(3101/50000 : ℝ)))^(8461/2048 : ℝ) := by
    rw [show (69055996441132540097/69075000000000000000 : ℝ)+(779867241721/345375000000000 : ℝ)*((20017/100000 : ℝ)+(3101/50000 : ℝ))=(5001584590630033/5000000000000000 : ℝ) by norm_num, show 1+(64983987337918953/50000000000000000000 : ℝ)+(1026901822286629/100000000000000000000 : ℝ)=(20026198975299624907/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(64983987337918953/50000000000000000000 : ℝ) ≤ ((69055996441132540097/69075000000000000000 : ℝ)+2*(779867241721/345375000000000 : ℝ)*(20017/100000 : ℝ))^(8461/2048 : ℝ) := by
    rw [show (69055996441132540097/69075000000000000000 : ℝ)+2*(779867241721/345375000000000 : ℝ)*(20017/100000 : ℝ)=(200125773004539/200000000000000 : ℝ) by norm_num, show 1+2*(64983987337918953/50000000000000000000 : ℝ)=(25064983987337918953/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (69055996441132540097/69075000000000000000 : ℝ)*(X 1 0+X 2 0)+(779867241721/345375000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8461/2048 : ℝ)) (lo := (3101/50000 : ℝ)) (hi := (20017/100000 : ℝ)) (c := (69055996441132540097/69075000000000000000 : ℝ)) (alpha := (779867241721/345375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (69055996441132540097/69075000000000000000 : ℝ)*(X 0 1+X 2 1)+(779867241721/345375000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8461/2048 : ℝ)) (lo := (3101/50000 : ℝ)) (hi := (20017/100000 : ℝ)) (c := (69055996441132540097/69075000000000000000 : ℝ)) (alpha := (779867241721/345375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (69055996441132540097/69075000000000000000 : ℝ)*(X 0 2+X 1 2)+(779867241721/345375000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8461/2048 : ℝ)) (lo := (3101/50000 : ℝ)) (hi := (20017/100000 : ℝ)) (c := (69055996441132540097/69075000000000000000 : ℝ)) (alpha := (779867241721/345375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-261655927/1250000000 : ℝ)*X 0 0+(1100138557/2000000000 : ℝ)*X 0 1+(5166430979/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((335696007/625000000 : ℝ)*X 1 0+(-1133346677/5000000000 : ℝ)*X 1 1+(5166432327/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1342784219/2500000000 : ℝ)*X 2 0+(80725489/156250000 : ℝ)*X 2 1+(-2266693689/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2168534871/5000000000 : ℝ)*X 0 0+(4009140617/10000000000 : ℝ)*X 0 1+(58634437/125000000 : ℝ)*X 0 2+(2168534871/5000000000 : ℝ)*X 1 0+(4009140617/10000000000 : ℝ)*X 1 1+(58634437/125000000 : ℝ)*X 1 2+(2168534871/5000000000 : ℝ)*X 2 0+(4009140617/10000000000 : ℝ)*X 2 1+(58634437/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-523334447/2500000000 : ℝ)*X 0 0+(2584352339/5000000000 : ℝ)*X 0 1+(1374599361/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((41294331/78125000 : ℝ)*X 1 0+(-48368189/250000000 : ℝ)*X 1 1+(5498397653/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5285674721/10000000000 : ℝ)*X 2 0+(2749198739/5000000000 : ℝ)*X 2 1+(-1934727317/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1084313729/2500000000 : ℝ)*X 0 0+(4686118331/10000000000 : ℝ)*X 0 1+(401382407/1000000000 : ℝ)*X 0 2+(1084313729/2500000000 : ℝ)*X 1 0+(4686118331/10000000000 : ℝ)*X 1 1+(401382407/1000000000 : ℝ)*X 1 2+(1084313729/2500000000 : ℝ)*X 2 0+(4686118331/10000000000 : ℝ)*X 2 1+(401382407/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2590154563558482662072267/3070000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (129970739/12500000000000 : ℝ)*(base19) + (264056679/20000000000000 : ℝ)*(base23) + (203363259/50000000000000 : ℝ)*(upper3) + (38947969/50000000000000 : ℝ)*(upper4) + (164301597/100000000000000 : ℝ)*(upper5) + (17835317398833/800000000000 : ℝ)*(major0) + (17835317398833/800000000000 : ℝ)*(major1) + (17835317398833/800000000000 : ℝ)*(major2) + (1495841934221163/50000000000000 : ℝ)*(sp0) + (93490558259473/3125000000000 : ℝ)*(sp1) + (1495848791892827/50000000000000 : ℝ)*(sp2) + (36677906028671/2500000000000 : ℝ)*(sp3) + (15035626723/100000000000000 : ℝ)*(sp4) + (14176369067/100000000000000 : ℝ)*(sp7) + (733565208757953/50000000000000 : ℝ)*(f.failure) + (2991698904069049/100000000000000 : ℝ)*(f.sum) + (1480661009183/230250000000000000000000000 : ℝ)*base66 + (68164985422917733/18420000000000000000000000000000 : ℝ)*base68 + (200346660344817733/18420000000000000000000000000000 : ℝ)*base70 + (181264712372577733/18420000000000000000000000000000 : ℝ)*base72 + (4934179866653/921000000000000000000000000 : ℝ)*base74 + (76775529138662267/18420000000000000000000000000000 : ℝ)*base75 + (114855632930817733/18420000000000000000000000000000 : ℝ)*base78 + (54646690155482267/18420000000000000000000000000000 : ℝ)*base79 + (122911418317/28781250000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (12259203/2500000000000000000000 : ℝ)*base90 + (12259203/2500000000000000000000 : ℝ)*base92 + (12259203/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7464559509582203713409/921000000000000000000000000 : ℝ) := by norm_num
    linear_combination (75092379/5000000000000 : ℝ)*(base19) + (1008336097/50000000000000 : ℝ)*(base23) + (13303487/5000000000000 : ℝ)*(upper3) + (52076871/50000000000000 : ℝ)*(lower4) + (53291047/50000000000000 : ℝ)*(upper5) + (45205694315717/2000000000000 : ℝ)*(major0) + (45205694315717/2000000000000 : ℝ)*(major1) + (45205694315717/2000000000000 : ℝ)*(major2) + (1426036303/10000000000000 : ℝ)*(sp1) + (21385856059/100000000000000 : ℝ)*(sp2) + (758280956503511/25000000000000 : ℝ)*(sp4) + (1516554031901717/50000000000000 : ℝ)*(sp5) + (94784388233931/3125000000000 : ℝ)*(sp6) + (1189956268317/80000000000 : ℝ)*(sp7) + (1189956268317/80000000000 : ℝ)*(f.failure) + (758280956503511/25000000000000 : ℝ)*(f.sum) + (280403237981/86343750000000000000000000 : ℝ)*base65 + (335753991532095451/138150000000000000000000000000000 : ℝ)*base68 + (1643675171147804549/138150000000000000000000000000000 : ℝ)*base69 + (294869330724404549/138150000000000000000000000000000 : ℝ)*base71 + (993053481007/1381500000000000000000000000 : ℝ)*base74 + (473695575708404549/138150000000000000000000000000000 : ℝ)*base75 + (872923207644195451/138150000000000000000000000000000 : ℝ)*base78 + (108353179817295451/138150000000000000000000000000000 : ℝ)*base80 + (9250100327701/2763000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (4567/4000000000000000000 : ℝ)*base90 + (4567/4000000000000000000 : ℝ)*base92 + (4567/4000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1269_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75978749/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20017/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3101/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9351/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8207/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1269_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1269_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75978749/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9351/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8207/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1269_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1269_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1269_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75978749/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9351/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8207/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1269_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
