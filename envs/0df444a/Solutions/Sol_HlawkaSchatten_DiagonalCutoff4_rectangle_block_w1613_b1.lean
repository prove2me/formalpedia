-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1613_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:51:50.325452+00:00
-- url     : https://prove2.me/submissions/c67e4448-10ed-4944-a331-f46513b6df32

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
theorem support_rectangle_w1613_s3_0 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1696653561/10000000000 : ℝ)*x 0 + (2729525177/5000000000 : ℝ)*x 1 + (647580247/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1696653561/10000000000 : ℝ)^4771 ≤ (10448460760113/100000000000000 : ℝ)^3747 := by
    have hnat : (1696653561 : ℕ)^4771*100000000000000^3747 ≤ 10448460760113^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1696653561 10000000000 10448460760113 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2729525177/5000000000 : ℝ)^4771 ≤ (11566849320107/25000000000000 : ℝ)^3747 := by
    have hnat : (2729525177 : ℕ)^4771*25000000000000^3747 ≤ 11566849320107^3747*5000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729525177 5000000000 11566849320107 25000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (647580247/1250000000 : ℝ)^4771 ≤ (8656828388119/20000000000000 : ℝ)^3747 := by
    have hnat : (647580247 : ℕ)^4771*20000000000000^3747 ≤ 8656828388119^3747*1250000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647580247 1250000000 8656828388119 20000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1696653561/10000000000 : ℝ), (2729525177/5000000000 : ℝ), (647580247/1250000000 : ℝ)] ![(10448460760113/100000000000000 : ℝ), (11566849320107/25000000000000 : ℝ), (8656828388119/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1696653561/10000000000 : ℝ)|^4771 ≤ (10448460760113/100000000000000 : ℝ)^3747
        have hw : |(-1696653561/10000000000 : ℝ)|=(1696653561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2729525177/5000000000 : ℝ)|^4771 ≤ (11566849320107/25000000000000 : ℝ)^3747
        have hw : |(2729525177/5000000000 : ℝ)|=(2729525177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(647580247/1250000000 : ℝ)|^4771 ≤ (8656828388119/20000000000000 : ℝ)^3747
        have hw : |(647580247/1250000000 : ℝ)|=(647580247/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_s3_1 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676638713/5000000000 : ℝ)*x 0 + (-920104999/5000000000 : ℝ)*x 1 + (8094753/15625000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676638713/5000000000 : ℝ)^4771 ≤ (22564490074447/50000000000000 : ℝ)^3747 := by
    have hnat : (2676638713 : ℕ)^4771*50000000000000^3747 ≤ 22564490074447^3747*5000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676638713 5000000000 22564490074447 50000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (920104999/5000000000 : ℝ)^4771 ≤ (5793439246277/50000000000000 : ℝ)^3747 := by
    have hnat : (920104999 : ℕ)^4771*50000000000000^3747 ≤ 5793439246277^3747*5000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      920104999 5000000000 5793439246277 50000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8094753/15625000 : ℝ)^4771 ≤ (10821035336213/25000000000000 : ℝ)^3747 := by
    have hnat : (8094753 : ℕ)^4771*25000000000000^3747 ≤ 10821035336213^3747*15625000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8094753 15625000 10821035336213 25000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676638713/5000000000 : ℝ), (-920104999/5000000000 : ℝ), (8094753/15625000 : ℝ)] ![(22564490074447/50000000000000 : ℝ), (5793439246277/50000000000000 : ℝ), (10821035336213/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676638713/5000000000 : ℝ)|^4771 ≤ (22564490074447/50000000000000 : ℝ)^3747
        have hw : |(2676638713/5000000000 : ℝ)|=(2676638713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-920104999/5000000000 : ℝ)|^4771 ≤ (5793439246277/50000000000000 : ℝ)^3747
        have hw : |(-920104999/5000000000 : ℝ)|=(920104999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8094753/15625000 : ℝ)|^4771 ≤ (10821035336213/25000000000000 : ℝ)^3747
        have hw : |(8094753/15625000 : ℝ)|=(8094753/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_s3_2 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334579849/625000000 : ℝ)*x 0 + (2590320889/5000000000 : ℝ)*x 1 + (-73608399/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334579849/625000000 : ℝ)^4771 ≤ (9025796368973/20000000000000 : ℝ)^3747 := by
    have hnat : (334579849 : ℕ)^4771*20000000000000^3747 ≤ 9025796368973^3747*625000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334579849 625000000 9025796368973 20000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2590320889/5000000000 : ℝ)^4771 ≤ (21642069917109/50000000000000 : ℝ)^3747 := by
    have hnat : (2590320889 : ℕ)^4771*50000000000000^3747 ≤ 21642069917109^3747*5000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590320889 5000000000 21642069917109 50000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (73608399/400000000 : ℝ)^4771 ≤ (5793439154079/50000000000000 : ℝ)^3747 := by
    have hnat : (73608399 : ℕ)^4771*50000000000000^3747 ≤ 5793439154079^3747*400000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73608399 400000000 5793439154079 50000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334579849/625000000 : ℝ), (2590320889/5000000000 : ℝ), (-73608399/400000000 : ℝ)] ![(9025796368973/20000000000000 : ℝ), (21642069917109/50000000000000 : ℝ), (5793439154079/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334579849/625000000 : ℝ)|^4771 ≤ (9025796368973/20000000000000 : ℝ)^3747
        have hw : |(334579849/625000000 : ℝ)|=(334579849/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2590320889/5000000000 : ℝ)|^4771 ≤ (21642069917109/50000000000000 : ℝ)^3747
        have hw : |(2590320889/5000000000 : ℝ)|=(2590320889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-73608399/400000000 : ℝ)|^4771 ≤ (5793439154079/50000000000000 : ℝ)^3747
        have hw : |(-73608399/400000000 : ℝ)|=(73608399/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_s3_3 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2105005217/5000000000 : ℝ)*x 0 + (3877323283/10000000000 : ℝ)*x 1 + (142630357/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2105005217/5000000000 : ℝ)^4771 ≤ (33235735043067/100000000000000 : ℝ)^3747 := by
    have hnat : (2105005217 : ℕ)^4771*100000000000000^3747 ≤ 33235735043067^3747*5000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105005217 5000000000 33235735043067 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3877323283/10000000000 : ℝ)^4771 ≤ (3741053129019/12500000000000 : ℝ)^3747 := by
    have hnat : (3877323283 : ℕ)^4771*12500000000000^3747 ≤ 3741053129019^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3877323283 10000000000 3741053129019 12500000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (142630357/312500000 : ℝ)^4771 ≤ (36835839918267/100000000000000 : ℝ)^3747 := by
    have hnat : (142630357 : ℕ)^4771*100000000000000^3747 ≤ 36835839918267^3747*312500000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142630357 312500000 36835839918267 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2105005217/5000000000 : ℝ), (3877323283/10000000000 : ℝ), (142630357/312500000 : ℝ)] ![(33235735043067/100000000000000 : ℝ), (3741053129019/12500000000000 : ℝ), (36835839918267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2105005217/5000000000 : ℝ)|^4771 ≤ (33235735043067/100000000000000 : ℝ)^3747
        have hw : |(2105005217/5000000000 : ℝ)|=(2105005217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3877323283/10000000000 : ℝ)|^4771 ≤ (3741053129019/12500000000000 : ℝ)^3747
        have hw : |(3877323283/10000000000 : ℝ)|=(3877323283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(142630357/312500000 : ℝ)|^4771 ≤ (36835839918267/100000000000000 : ℝ)^3747
        have hw : |(142630357/312500000 : ℝ)|=(142630357/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_s3_4 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-212090513/1250000000 : ℝ)*x 0 + (5182720647/10000000000 : ℝ)*x 1 + (170529679/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212090513/1250000000 : ℝ)^4771 ≤ (10449013908001/100000000000000 : ℝ)^3747 := by
    have hnat : (212090513 : ℕ)^4771*100000000000000^3747 ≤ 10449013908001^3747*1250000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212090513 1250000000 10449013908001 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5182720647/10000000000 : ℝ)^4771 ≤ (8661251322707/20000000000000 : ℝ)^3747 := by
    have hnat : (5182720647 : ℕ)^4771*20000000000000^3747 ≤ 8661251322707^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182720647 10000000000 8661251322707 20000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (170529679/312500000 : ℝ)^4771 ≤ (46244729468983/100000000000000 : ℝ)^3747 := by
    have hnat : (170529679 : ℕ)^4771*100000000000000^3747 ≤ 46244729468983^3747*312500000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170529679 312500000 46244729468983 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-212090513/1250000000 : ℝ), (5182720647/10000000000 : ℝ), (170529679/312500000 : ℝ)] ![(10449013908001/100000000000000 : ℝ), (8661251322707/20000000000000 : ℝ), (46244729468983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-212090513/1250000000 : ℝ)|^4771 ≤ (10449013908001/100000000000000 : ℝ)^3747
        have hw : |(-212090513/1250000000 : ℝ)|=(212090513/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5182720647/10000000000 : ℝ)|^4771 ≤ (8661251322707/20000000000000 : ℝ)^3747
        have hw : |(5182720647/10000000000 : ℝ)|=(5182720647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(170529679/312500000 : ℝ)|^4771 ≤ (46244729468983/100000000000000 : ℝ)^3747
        have hw : |(170529679/312500000 : ℝ)|=(170529679/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_s3_5 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319824709/2500000000 : ℝ)*x 0 + (-1563902167/10000000000 : ℝ)*x 1 + (1364237421/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319824709/2500000000 : ℝ)^4771 ≤ (44336398672579/100000000000000 : ℝ)^3747 := by
    have hnat : (1319824709 : ℕ)^4771*100000000000000^3747 ≤ 44336398672579^3747*2500000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319824709 2500000000 44336398672579 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1563902167/10000000000 : ℝ)^4771 ≤ (9418872309291/100000000000000 : ℝ)^3747 := by
    have hnat : (1563902167 : ℕ)^4771*100000000000000^3747 ≤ 9418872309291^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1563902167 10000000000 9418872309291 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1364237421/2500000000 : ℝ)^4771 ≤ (9248945798841/20000000000000 : ℝ)^3747 := by
    have hnat : (1364237421 : ℕ)^4771*20000000000000^3747 ≤ 9248945798841^3747*2500000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364237421 2500000000 9248945798841 20000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319824709/2500000000 : ℝ), (-1563902167/10000000000 : ℝ), (1364237421/2500000000 : ℝ)] ![(44336398672579/100000000000000 : ℝ), (9418872309291/100000000000000 : ℝ), (9248945798841/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319824709/2500000000 : ℝ)|^4771 ≤ (44336398672579/100000000000000 : ℝ)^3747
        have hw : |(1319824709/2500000000 : ℝ)|=(1319824709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1563902167/10000000000 : ℝ)|^4771 ≤ (9418872309291/100000000000000 : ℝ)^3747
        have hw : |(-1563902167/10000000000 : ℝ)|=(1563902167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1364237421/2500000000 : ℝ)|^4771 ≤ (9248945798841/20000000000000 : ℝ)^3747
        have hw : |(1364237421/2500000000 : ℝ)|=(1364237421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_s3_6 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42234391/80000000 : ℝ)*x 0 + (2728474797/5000000000 : ℝ)*x 1 + (-1563902241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42234391/80000000 : ℝ)^4771 ≤ (2771024943101/6250000000000 : ℝ)^3747 := by
    have hnat : (42234391 : ℕ)^4771*6250000000000^3747 ≤ 2771024943101^3747*80000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42234391 80000000 2771024943101 6250000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2728474797/5000000000 : ℝ)^4771 ≤ (11561182005767/25000000000000 : ℝ)^3747 := by
    have hnat : (2728474797 : ℕ)^4771*25000000000000^3747 ≤ 11561182005767^3747*5000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728474797 5000000000 11561182005767 25000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1563902241/10000000000 : ℝ)^4771 ≤ (4709436438383/50000000000000 : ℝ)^3747 := by
    have hnat : (1563902241 : ℕ)^4771*50000000000000^3747 ≤ 4709436438383^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1563902241 10000000000 4709436438383 50000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42234391/80000000 : ℝ), (2728474797/5000000000 : ℝ), (-1563902241/10000000000 : ℝ)] ![(2771024943101/6250000000000 : ℝ), (11561182005767/25000000000000 : ℝ), (4709436438383/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42234391/80000000 : ℝ)|^4771 ≤ (2771024943101/6250000000000 : ℝ)^3747
        have hw : |(42234391/80000000 : ℝ)|=(42234391/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2728474797/5000000000 : ℝ)|^4771 ≤ (11561182005767/25000000000000 : ℝ)^3747
        have hw : |(2728474797/5000000000 : ℝ)|=(2728474797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1563902241/10000000000 : ℝ)|^4771 ≤ (4709436438383/50000000000000 : ℝ)^3747
        have hw : |(-1563902241/10000000000 : ℝ)|=(1563902241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_s3_7 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2105092297/5000000000 : ℝ)*x 0 + (4559042543/10000000000 : ℝ)*x 1 + (1941253019/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2105092297/5000000000 : ℝ)^4771 ≤ (2077342855661/6250000000000 : ℝ)^3747 := by
    have hnat : (2105092297 : ℕ)^4771*6250000000000^3747 ≤ 2077342855661^3747*5000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105092297 5000000000 2077342855661 6250000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4559042543/10000000000 : ℝ)^4771 ≤ (36783142387413/100000000000000 : ℝ)^3747 := by
    have hnat : (4559042543 : ℕ)^4771*100000000000000^3747 ≤ 36783142387413^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4559042543 10000000000 36783142387413 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1941253019/5000000000 : ℝ)^4771 ≤ (2997937190627/10000000000000 : ℝ)^3747 := by
    have hnat : (1941253019 : ℕ)^4771*10000000000000^3747 ≤ 2997937190627^3747*5000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1941253019 5000000000 2997937190627 10000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2105092297/5000000000 : ℝ), (4559042543/10000000000 : ℝ), (1941253019/5000000000 : ℝ)] ![(2077342855661/6250000000000 : ℝ), (36783142387413/100000000000000 : ℝ), (2997937190627/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2105092297/5000000000 : ℝ)|^4771 ≤ (2077342855661/6250000000000 : ℝ)^3747
        have hw : |(2105092297/5000000000 : ℝ)|=(2105092297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4559042543/10000000000 : ℝ)|^4771 ≤ (36783142387413/100000000000000 : ℝ)^3747
        have hw : |(4559042543/10000000000 : ℝ)|=(4559042543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1941253019/5000000000 : ℝ)|^4771 ≤ (2997937190627/10000000000000 : ℝ)^3747
        have hw : |(1941253019/5000000000 : ℝ)|=(1941253019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1613_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3467051/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (413/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (2611/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4087/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16481/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (413/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16481/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (413/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16481/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (413/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16481/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (413/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16481/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (413/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16481/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (413/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (413/4000 : ℝ) ^ (4767/1024 : ℝ) ≤ (1283389836651143/50000000000000000000 : ℝ) := by
    have hpowers : (413/4000 : ℝ)^4767 ≤ (1283389836651143/50000000000000000000 : ℝ)^1024 := by
      have hnat : (413 : ℕ)^4767*50000000000000000000^1024 ≤ 1283389836651143^1024*4000^4767 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        413 4000 1283389836651143 50000000000000000000 4767 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (413/4000 : ℝ)) (X := (1283389836651143/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4767 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16481/100000 : ℝ) ^ (4767/1024 : ℝ) ≤ (22638328775221983/100000000000000000000 : ℝ) := by
    have hpowers : (16481/100000 : ℝ)^4767 ≤ (22638328775221983/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16481 : ℕ)^4767*100000000000000000000^1024 ≤ 22638328775221983^1024*100000^4767 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16481 100000 22638328775221983 100000000000000000000 4767 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16481/100000 : ℝ)) (X := (22638328775221983/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4767 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001283389836651143/25000000000000000000 : ℝ) ≤ (2500027567961133/2500000000000000 : ℝ) ^ (4767/1024 : ℝ) := by
    have hpowers : (25001283389836651143/25000000000000000000 : ℝ)^1024 ≤ (2500027567961133/2500000000000000 : ℝ)^4767 := by
      have hnat : (25001283389836651143 : ℕ)^1024*2500000000000000^4767 ≤ 2500027567961133^4767*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001283389836651143 25000000000000000000 2500027567961133 2500000000000000 1024 4767 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500027567961133/2500000000000000 : ℝ)) (X := (25001283389836651143/25000000000000000000 : ℝ)) (by norm_num) 4767 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100025205108448524269/100000000000000000000 : ℝ) ≤ (10000541377751817/10000000000000000 : ℝ) ^ (4767/1024 : ℝ) := by
    have hpowers : (100025205108448524269/100000000000000000000 : ℝ)^1024 ≤ (10000541377751817/10000000000000000 : ℝ)^4767 := by
      have hnat : (100025205108448524269 : ℕ)^1024*10000000000000000^4767 ≤ 10000541377751817^4767*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100025205108448524269 100000000000000000000 10000541377751817 10000000000000000 1024 4767 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000541377751817/10000000000000000 : ℝ)) (X := (100025205108448524269/100000000000000000000 : ℝ)) (by norm_num) 4767 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50022638328775221983/50000000000000000000 : ℝ) ≤ (5000486241829551/5000000000000000 : ℝ) ^ (4767/1024 : ℝ) := by
    have hpowers : (50022638328775221983/50000000000000000000 : ℝ)^1024 ≤ (5000486241829551/5000000000000000 : ℝ)^4767 := by
      have hnat : (50022638328775221983 : ℕ)^1024*5000000000000000^4767 ≤ 5000486241829551^4767*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022638328775221983 50000000000000000000 5000486241829551 5000000000000000 1024 4767 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000486241829551/5000000000000000 : ℝ)) (X := (50022638328775221983/50000000000000000000 : ℝ)) (by norm_num) 4767 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1283389836651143/50000000000000000000 : ℝ) ≤ ((1139847712897953773/1140000000000000000 : ℝ)+2*(3193377091/4560000000000 : ℝ)*(413/4000 : ℝ))^(4767/1024 : ℝ) := by
    rw [show (1139847712897953773/1140000000000000000 : ℝ)+2*(3193377091/4560000000000 : ℝ)*(413/4000 : ℝ)=(2500027567961133/2500000000000000 : ℝ) by norm_num, show 1+2*(1283389836651143/50000000000000000000 : ℝ)=(25001283389836651143/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(22638328775221983/100000000000000000000 : ℝ)+(1283389836651143/50000000000000000000 : ℝ) ≤ ((1139847712897953773/1140000000000000000 : ℝ)+(3193377091/4560000000000 : ℝ)*((16481/100000 : ℝ)+(413/4000 : ℝ)))^(4767/1024 : ℝ) := by
    rw [show (1139847712897953773/1140000000000000000 : ℝ)+(3193377091/4560000000000 : ℝ)*((16481/100000 : ℝ)+(413/4000 : ℝ))=(10000541377751817/10000000000000000 : ℝ) by norm_num, show 1+(22638328775221983/100000000000000000000 : ℝ)+(1283389836651143/50000000000000000000 : ℝ)=(100025205108448524269/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(22638328775221983/100000000000000000000 : ℝ) ≤ ((1139847712897953773/1140000000000000000 : ℝ)+2*(3193377091/4560000000000 : ℝ)*(16481/100000 : ℝ))^(4767/1024 : ℝ) := by
    rw [show (1139847712897953773/1140000000000000000 : ℝ)+2*(3193377091/4560000000000 : ℝ)*(16481/100000 : ℝ)=(5000486241829551/5000000000000000 : ℝ) by norm_num, show 1+2*(22638328775221983/100000000000000000000 : ℝ)=(50022638328775221983/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1139847712897953773/1140000000000000000 : ℝ)*(X 1 0+X 2 0)+(3193377091/4560000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4767/1024 : ℝ)) (lo := (413/4000 : ℝ)) (hi := (16481/100000 : ℝ)) (c := (1139847712897953773/1140000000000000000 : ℝ)) (alpha := (3193377091/4560000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1139847712897953773/1140000000000000000 : ℝ)*(X 0 1+X 2 1)+(3193377091/4560000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4767/1024 : ℝ)) (lo := (413/4000 : ℝ)) (hi := (16481/100000 : ℝ)) (c := (1139847712897953773/1140000000000000000 : ℝ)) (alpha := (3193377091/4560000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1139847712897953773/1140000000000000000 : ℝ)*(X 0 2+X 1 2)+(3193377091/4560000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4767/1024 : ℝ)) (lo := (413/4000 : ℝ)) (hi := (16481/100000 : ℝ)) (c := (1139847712897953773/1140000000000000000 : ℝ)) (alpha := (3193377091/4560000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1696653561/10000000000 : ℝ)*X 0 0+(2729525177/5000000000 : ℝ)*X 0 1+(647580247/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676638713/5000000000 : ℝ)*X 1 0+(-920104999/5000000000 : ℝ)*X 1 1+(8094753/15625000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334579849/625000000 : ℝ)*X 2 0+(2590320889/5000000000 : ℝ)*X 2 1+(-73608399/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2105005217/5000000000 : ℝ)*X 0 0+(3877323283/10000000000 : ℝ)*X 0 1+(142630357/312500000 : ℝ)*X 0 2+(2105005217/5000000000 : ℝ)*X 1 0+(3877323283/10000000000 : ℝ)*X 1 1+(142630357/312500000 : ℝ)*X 1 2+(2105005217/5000000000 : ℝ)*X 2 0+(3877323283/10000000000 : ℝ)*X 2 1+(142630357/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-212090513/1250000000 : ℝ)*X 0 0+(5182720647/10000000000 : ℝ)*X 0 1+(170529679/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1319824709/2500000000 : ℝ)*X 1 0+(-1563902167/10000000000 : ℝ)*X 1 1+(1364237421/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((42234391/80000000 : ℝ)*X 2 0+(2728474797/5000000000 : ℝ)*X 2 1+(-1563902241/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2105092297/5000000000 : ℝ)*X 0 0+(4559042543/10000000000 : ℝ)*X 0 1+(1941253019/5000000000 : ℝ)*X 0 2+(2105092297/5000000000 : ℝ)*X 1 0+(4559042543/10000000000 : ℝ)*X 1 1+(1941253019/5000000000 : ℝ)*X 1 2+(2105092297/5000000000 : ℝ)*X 2 0+(4559042543/10000000000 : ℝ)*X 2 1+(1941253019/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (168521839933241138352817671/19000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (52486351/4000000000000 : ℝ)*(base19) + (55780491/4000000000000 : ℝ)*(base23) + (25331/200000000000 : ℝ)*(lower2) + (23001067/12500000000000 : ℝ)*(upper3) + (200062707/100000000000000 : ℝ)*(upper5) + (2523907554725373/100000000000000 : ℝ)*(major0) + (2523907554725373/100000000000000 : ℝ)*(major1) + (2523907554725373/100000000000000 : ℝ)*(major2) + (1795930107782399/50000000000000 : ℝ)*(sp0) + (897968600636563/25000000000000 : ℝ)*(sp1) + (224492145012047/6250000000000 : ℝ)*(sp2) + (727966198606561/50000000000000 : ℝ)*(sp3) + (15499140229/100000000000000 : ℝ)*(sp4) + (3350940121/50000000000000 : ℝ)*(sp7) + (363984774773341/25000000000000 : ℝ)*(f.failure) + (3591875714705027/100000000000000 : ℝ)*(f.sum) + (42874838629/76000000000000000000000000 : ℝ)*base65 + (160077701743977443/38000000000000000000000000000000 : ℝ)*base67 + (148630266342022557/38000000000000000000000000000000 : ℝ)*base70 + (426233028225977443/38000000000000000000000000000000 : ℝ)*base71 + (24184775031/15200000000000000000000000 : ℝ)*base74 + (145131046982022557/38000000000000000000000000000000 : ℝ)*base76 + (42875203217977443/38000000000000000000000000000000 : ℝ)*base77 + (251066938505977443/38000000000000000000000000000000 : ℝ)*base79 + (425683745043/76000000000000000000000000 : ℝ)*base82 + (187391/50000000000000000000 : ℝ)*base89 + (187391/50000000000000000000 : ℝ)*base91 + (187391/50000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (39421050132053674585355777/4750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (658481113/50000000000000 : ℝ)*(base19) + (686554139/50000000000000 : ℝ)*(base23) + (83606853/50000000000000 : ℝ)*(upper3) + (552171/2000000000000 : ℝ)*(lower4) + (242270047/100000000000000 : ℝ)*(upper5) + (1281176004331651/50000000000000 : ℝ)*(major0) + (1281176004331651/50000000000000 : ℝ)*(major1) + (1281176004331651/50000000000000 : ℝ)*(major2) + (3004214351/20000000000000 : ℝ)*(sp1) + (13373403537/100000000000000 : ℝ)*(sp2) + (455823450950399/12500000000000 : ℝ)*(sp4) + (364657126956921/10000000000000 : ℝ)*(sp5) + (3646572861091377/100000000000000 : ℝ)*(sp6) + (739058066542229/50000000000000 : ℝ)*(sp7) + (739058066542229/50000000000000 : ℝ)*(f.failure) + (455823450950399/12500000000000 : ℝ)*(f.sum) + (88428440467/22800000000000000000000000 : ℝ)*base66 + (9352491614339741/19000000000000000000000000000000 : ℝ)*base67 + (6643333636339741/19000000000000000000000000000000 : ℝ)*base69 + (21178465458339741/19000000000000000000000000000000 : ℝ)*base71 + (127040515207/22800000000000000000000000 : ℝ)*base74 + (248128251820339741/19000000000000000000000000000000 : ℝ)*base75 + (4178427108660259/19000000000000000000000000000000 : ℝ)*base78 + (36128916114339741/19000000000000000000000000000000 : ℝ)*base79 + (33636810433/114000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (403321/100000000000000000000 : ℝ)*base90 + (403321/100000000000000000000 : ℝ)*base92 + (403321/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1613_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3467051/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (413/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2611/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4087/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1613_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1613_s4_0 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-424190573/2500000000 : ℝ)*x 0 + (5458508383/10000000000 : ℝ)*x 1 + (5181111599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (424190573/2500000000 : ℝ)^4771 ≤ (130616416921/1250000000000 : ℝ)^3747 := by
    have hnat : (424190573 : ℕ)^4771*1250000000000^3747 ≤ 130616416921^3747*2500000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424190573 2500000000 130616416921 1250000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5458508383/10000000000 : ℝ)^4771 ≤ (1156538716361/2500000000000 : ℝ)^3747 := by
    have hnat : (5458508383 : ℕ)^4771*2500000000000^3747 ≤ 1156538716361^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5458508383 10000000000 1156538716361 2500000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5181111599/10000000000 : ℝ)^4771 ≤ (1352785561817/3125000000000 : ℝ)^3747 := by
    have hnat : (5181111599 : ℕ)^4771*3125000000000^3747 ≤ 1352785561817^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181111599 10000000000 1352785561817 3125000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-424190573/2500000000 : ℝ), (5458508383/10000000000 : ℝ), (5181111599/10000000000 : ℝ)] ![(130616416921/1250000000000 : ℝ), (1156538716361/2500000000000 : ℝ), (1352785561817/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-424190573/2500000000 : ℝ)|^4771 ≤ (130616416921/1250000000000 : ℝ)^3747
        have hw : |(-424190573/2500000000 : ℝ)|=(424190573/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5458508383/10000000000 : ℝ)|^4771 ≤ (1156538716361/2500000000000 : ℝ)^3747
        have hw : |(5458508383/10000000000 : ℝ)|=(5458508383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5181111599/10000000000 : ℝ)|^4771 ≤ (1352785561817/3125000000000 : ℝ)^3747
        have hw : |(5181111599/10000000000 : ℝ)|=(5181111599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_s4_1 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353132189/10000000000 : ℝ)*x 0 + (-919890601/5000000000 : ℝ)*x 1 + (5181111597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353132189/10000000000 : ℝ)^4771 ≤ (4512742118107/10000000000000 : ℝ)^3747 := by
    have hnat : (5353132189 : ℕ)^4771*10000000000000^3747 ≤ 4512742118107^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353132189 10000000000 4512742118107 10000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (919890601/5000000000 : ℝ)^4771 ≤ (5791720421161/50000000000000 : ℝ)^3747 := by
    have hnat : (919890601 : ℕ)^4771*50000000000000^3747 ≤ 5791720421161^3747*5000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      919890601 5000000000 5791720421161 50000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5181111597/10000000000 : ℝ)^4771 ≤ (43289137956867/100000000000000 : ℝ)^3747 := by
    have hnat : (5181111597 : ℕ)^4771*100000000000000^3747 ≤ 43289137956867^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181111597 10000000000 43289137956867 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353132189/10000000000 : ℝ), (-919890601/5000000000 : ℝ), (5181111597/10000000000 : ℝ)] ![(4512742118107/10000000000000 : ℝ), (5791720421161/50000000000000 : ℝ), (43289137956867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353132189/10000000000 : ℝ)|^4771 ≤ (4512742118107/10000000000000 : ℝ)^3747
        have hw : |(5353132189/10000000000 : ℝ)|=(5353132189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-919890601/5000000000 : ℝ)|^4771 ≤ (5791720421161/50000000000000 : ℝ)^3747
        have hw : |(-919890601/5000000000 : ℝ)|=(919890601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5181111597/10000000000 : ℝ)|^4771 ≤ (43289137956867/100000000000000 : ℝ)^3747
        have hw : |(5181111597/10000000000 : ℝ)|=(5181111597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_s4_2 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676566089/5000000000 : ℝ)*x 0 + (518111161/1000000000 : ℝ)*x 1 + (-4599453/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676566089/5000000000 : ℝ)^4771 ≤ (45127421062997/100000000000000 : ℝ)^3747 := by
    have hnat : (2676566089 : ℕ)^4771*100000000000000^3747 ≤ 45127421062997^3747*5000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676566089 5000000000 45127421062997 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (518111161/1000000000 : ℝ)^4771 ≤ (676392782737/1562500000000 : ℝ)^3747 := by
    have hnat : (518111161 : ℕ)^4771*1562500000000^3747 ≤ 676392782737^3747*1000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518111161 1000000000 676392782737 1562500000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4599453/25000000 : ℝ)^4771 ≤ (11583440826289/100000000000000 : ℝ)^3747 := by
    have hnat : (4599453 : ℕ)^4771*100000000000000^3747 ≤ 11583440826289^3747*25000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4599453 25000000 11583440826289 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676566089/5000000000 : ℝ), (518111161/1000000000 : ℝ), (-4599453/25000000 : ℝ)] ![(45127421062997/100000000000000 : ℝ), (676392782737/1562500000000 : ℝ), (11583440826289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676566089/5000000000 : ℝ)|^4771 ≤ (45127421062997/100000000000000 : ℝ)^3747
        have hw : |(2676566089/5000000000 : ℝ)|=(2676566089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(518111161/1000000000 : ℝ)|^4771 ≤ (676392782737/1562500000000 : ℝ)^3747
        have hw : |(518111161/1000000000 : ℝ)|=(518111161/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4599453/25000000 : ℝ)|^4771 ≤ (11583440826289/100000000000000 : ℝ)^3747
        have hw : |(-4599453/25000000 : ℝ)|=(4599453/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_s4_3 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (263130057/625000000 : ℝ)*x 0 + (1939281939/5000000000 : ℝ)*x 1 + (456291587/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (263130057/625000000 : ℝ)^4771 ≤ (16618221740987/50000000000000 : ℝ)^3747 := by
    have hnat : (263130057 : ℕ)^4771*50000000000000^3747 ≤ 16618221740987^3747*625000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263130057 625000000 16618221740987 50000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1939281939/5000000000 : ℝ)^4771 ≤ (14970309240847/50000000000000 : ℝ)^3747 := by
    have hnat : (1939281939 : ℕ)^4771*50000000000000^3747 ≤ 14970309240847^3747*5000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1939281939 5000000000 14970309240847 50000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (456291587/1000000000 : ℝ)^4771 ≤ (18411469012827/50000000000000 : ℝ)^3747 := by
    have hnat : (456291587 : ℕ)^4771*50000000000000^3747 ≤ 18411469012827^3747*1000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      456291587 1000000000 18411469012827 50000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(263130057/625000000 : ℝ), (1939281939/5000000000 : ℝ), (456291587/1000000000 : ℝ)] ![(16618221740987/50000000000000 : ℝ), (14970309240847/50000000000000 : ℝ), (18411469012827/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(263130057/625000000 : ℝ)|^4771 ≤ (16618221740987/50000000000000 : ℝ)^3747
        have hw : |(263130057/625000000 : ℝ)|=(263130057/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1939281939/5000000000 : ℝ)|^4771 ≤ (14970309240847/50000000000000 : ℝ)^3747
        have hw : |(1939281939/5000000000 : ℝ)|=(1939281939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(456291587/1000000000 : ℝ)|^4771 ≤ (18411469012827/50000000000000 : ℝ)^3747
        have hw : |(456291587/1000000000 : ℝ)|=(456291587/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_s4_4 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1696832027/10000000000 : ℝ)*x 0 + (207327021/400000000 : ℝ)*x 1 + (218256911/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1696832027/10000000000 : ℝ)^4771 ≤ (208997203507/2000000000000 : ℝ)^3747 := by
    have hnat : (1696832027 : ℕ)^4771*2000000000000^3747 ≤ 208997203507^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1696832027 10000000000 208997203507 2000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207327021/400000000 : ℝ)^4771 ≤ (43311096316513/100000000000000 : ℝ)^3747 := by
    have hnat : (207327021 : ℕ)^4771*100000000000000^3747 ≤ 43311096316513^3747*400000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207327021 400000000 43311096316513 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (218256911/400000000 : ℝ)^4771 ≤ (23119521752107/50000000000000 : ℝ)^3747 := by
    have hnat : (218256911 : ℕ)^4771*50000000000000^3747 ≤ 23119521752107^3747*400000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218256911 400000000 23119521752107 50000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1696832027/10000000000 : ℝ), (207327021/400000000 : ℝ), (218256911/400000000 : ℝ)] ![(208997203507/2000000000000 : ℝ), (43311096316513/100000000000000 : ℝ), (23119521752107/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1696832027/10000000000 : ℝ)|^4771 ≤ (208997203507/2000000000000 : ℝ)^3747
        have hw : |(-1696832027/10000000000 : ℝ)|=(1696832027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(207327021/400000000 : ℝ)|^4771 ≤ (43311096316513/100000000000000 : ℝ)^3747
        have hw : |(207327021/400000000 : ℝ)|=(207327021/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(218256911/400000000 : ℝ)|^4771 ≤ (23119521752107/50000000000000 : ℝ)^3747
        have hw : |(218256911/400000000 : ℝ)|=(218256911/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_s4_5 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279423229/10000000000 : ℝ)*x 0 + (-1564470053/10000000000 : ℝ)*x 1 + (1364105699/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279423229/10000000000 : ℝ)^4771 ≤ (44337728842831/100000000000000 : ℝ)^3747 := by
    have hnat : (5279423229 : ℕ)^4771*100000000000000^3747 ≤ 44337728842831^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279423229 10000000000 44337728842831 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1564470053/10000000000 : ℝ)^4771 ≤ (9423227405563/100000000000000 : ℝ)^3747 := by
    have hnat : (1564470053 : ℕ)^4771*100000000000000^3747 ≤ 9423227405563^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1564470053 10000000000 9423227405563 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1364105699/2500000000 : ℝ)^4771 ≤ (23119521865403/50000000000000 : ℝ)^3747 := by
    have hnat : (1364105699 : ℕ)^4771*50000000000000^3747 ≤ 23119521865403^3747*2500000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364105699 2500000000 23119521865403 50000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279423229/10000000000 : ℝ), (-1564470053/10000000000 : ℝ), (1364105699/2500000000 : ℝ)] ![(44337728842831/100000000000000 : ℝ), (9423227405563/100000000000000 : ℝ), (23119521865403/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279423229/10000000000 : ℝ)|^4771 ≤ (44337728842831/100000000000000 : ℝ)^3747
        have hw : |(5279423229/10000000000 : ℝ)|=(5279423229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1564470053/10000000000 : ℝ)|^4771 ≤ (9423227405563/100000000000000 : ℝ)^3747
        have hw : |(-1564470053/10000000000 : ℝ)|=(1564470053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1364105699/2500000000 : ℝ)|^4771 ≤ (23119521865403/50000000000000 : ℝ)^3747
        have hw : |(1364105699/2500000000 : ℝ)|=(1364105699/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_s4_6 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279423267/10000000000 : ℝ)*x 0 + (5456422791/10000000000 : ℝ)*x 1 + (-1564470009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279423267/10000000000 : ℝ)^4771 ≤ (44337729249177/100000000000000 : ℝ)^3747 := by
    have hnat : (5279423267 : ℕ)^4771*100000000000000^3747 ≤ 44337729249177^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279423267 10000000000 44337729249177 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5456422791/10000000000 : ℝ)^4771 ≤ (5779880459607/12500000000000 : ℝ)^3747 := by
    have hnat : (5456422791 : ℕ)^4771*12500000000000^3747 ≤ 5779880459607^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5456422791 10000000000 5779880459607 12500000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1564470009/10000000000 : ℝ)^4771 ≤ (588951691757/6250000000000 : ℝ)^3747 := by
    have hnat : (1564470009 : ℕ)^4771*6250000000000^3747 ≤ 588951691757^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1564470009 10000000000 588951691757 6250000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279423267/10000000000 : ℝ), (5456422791/10000000000 : ℝ), (-1564470009/10000000000 : ℝ)] ![(44337729249177/100000000000000 : ℝ), (5779880459607/12500000000000 : ℝ), (588951691757/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279423267/10000000000 : ℝ)|^4771 ≤ (44337729249177/100000000000000 : ℝ)^3747
        have hw : |(5279423267/10000000000 : ℝ)|=(5279423267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5456422791/10000000000 : ℝ)|^4771 ≤ (5779880459607/12500000000000 : ℝ)^3747
        have hw : |(5456422791/10000000000 : ℝ)|=(5456422791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1564470009/10000000000 : ℝ)|^4771 ≤ (588951691757/6250000000000 : ℝ)^3747
        have hw : |(-1564470009/10000000000 : ℝ)|=(1564470009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_s4_7 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1052563243/2500000000 : ℝ)*x 0 + (1139456013/2500000000 : ℝ)*x 1 + (970927301/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1052563243/2500000000 : ℝ)^4771 ≤ (4154771628523/12500000000000 : ℝ)^3747 := by
    have hnat : (1052563243 : ℕ)^4771*12500000000000^3747 ≤ 4154771628523^3747*2500000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052563243 2500000000 4154771628523 12500000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1139456013/2500000000 : ℝ)^4771 ≤ (7354125036449/20000000000000 : ℝ)^3747 := by
    have hnat : (1139456013 : ℕ)^4771*20000000000000^3747 ≤ 7354125036449^3747*2500000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1139456013 2500000000 7354125036449 20000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (970927301/2500000000 : ℝ)^4771 ≤ (1499560088923/5000000000000 : ℝ)^3747 := by
    have hnat : (970927301 : ℕ)^4771*5000000000000^3747 ≤ 1499560088923^3747*2500000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      970927301 2500000000 1499560088923 5000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1052563243/2500000000 : ℝ), (1139456013/2500000000 : ℝ), (970927301/2500000000 : ℝ)] ![(4154771628523/12500000000000 : ℝ), (7354125036449/20000000000000 : ℝ), (1499560088923/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1052563243/2500000000 : ℝ)|^4771 ≤ (4154771628523/12500000000000 : ℝ)^3747
        have hw : |(1052563243/2500000000 : ℝ)|=(1052563243/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1139456013/2500000000 : ℝ)|^4771 ≤ (7354125036449/20000000000000 : ℝ)^3747
        have hw : |(1139456013/2500000000 : ℝ)|=(1139456013/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(970927301/2500000000 : ℝ)|^4771 ≤ (1499560088923/5000000000000 : ℝ)^3747
        have hw : |(970927301/2500000000 : ℝ)|=(970927301/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1613_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3467051/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4087/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2611/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5227/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16337/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4087/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2611/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4087/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2611/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4087/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2611/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4087/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2611/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4087/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2611/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4087/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2611/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2611/25000 : ℝ) ^ (4767/1024 : ℝ) ≤ (2707428332506741/100000000000000000000 : ℝ) := by
    have hpowers : (2611/25000 : ℝ)^4767 ≤ (2707428332506741/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2611 : ℕ)^4767*100000000000000000000^1024 ≤ 2707428332506741^1024*25000^4767 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2611 25000 2707428332506741 100000000000000000000 4767 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2611/25000 : ℝ)) (X := (2707428332506741/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4767 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4087/25000 : ℝ) ^ (4767/1024 : ℝ) ≤ (21800315552083681/100000000000000000000 : ℝ) := by
    have hpowers : (4087/25000 : ℝ)^4767 ≤ (21800315552083681/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4087 : ℕ)^4767*100000000000000000000^1024 ≤ 21800315552083681^1024*25000^4767 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4087 25000 21800315552083681 100000000000000000000 4767 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4087/25000 : ℝ)) (X := (21800315552083681/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4767 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002707428332506741/50000000000000000000 : ℝ) ≤ (10000116314146311/10000000000000000 : ℝ) ^ (4767/1024 : ℝ) := by
    have hpowers : (50002707428332506741/50000000000000000000 : ℝ)^1024 ≤ (10000116314146311/10000000000000000 : ℝ)^4767 := by
      have hnat : (50002707428332506741 : ℕ)^1024*10000000000000000^4767 ≤ 10000116314146311^4767*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002707428332506741 50000000000000000000 10000116314146311 10000000000000000 1024 4767 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000116314146311/10000000000000000 : ℝ)) (X := (50002707428332506741/50000000000000000000 : ℝ)) (by norm_num) 4767 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50012253871942295211/50000000000000000000 : ℝ) ≤ (10000526400575959/10000000000000000 : ℝ) ^ (4767/1024 : ℝ) := by
    have hpowers : (50012253871942295211/50000000000000000000 : ℝ)^1024 ≤ (10000526400575959/10000000000000000 : ℝ)^4767 := by
      have hnat : (50012253871942295211 : ℕ)^1024*10000000000000000^4767 ≤ 10000526400575959^4767*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50012253871942295211 50000000000000000000 10000526400575959 10000000000000000 1024 4767 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000526400575959/10000000000000000 : ℝ)) (X := (50012253871942295211/50000000000000000000 : ℝ)) (by norm_num) 4767 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50021800315552083681/50000000000000000000 : ℝ) ≤ (10000936487005607/10000000000000000 : ℝ) ^ (4767/1024 : ℝ) := by
    have hpowers : (50021800315552083681/50000000000000000000 : ℝ)^1024 ≤ (10000936487005607/10000000000000000 : ℝ)^4767 := by
      have hnat : (50021800315552083681 : ℕ)^1024*10000000000000000^4767 ≤ 10000936487005607^4767*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021800315552083681 50000000000000000000 10000936487005607 10000000000000000 1024 4767 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000936487005607/10000000000000000 : ℝ)) (X := (50021800315552083681/50000000000000000000 : ℝ)) (by norm_num) 4767 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2707428332506741/100000000000000000000 : ℝ) ≤ ((737901510417216659/738000000000000000 : ℝ)+2*(25630401853/36900000000000 : ℝ)*(2611/25000 : ℝ))^(4767/1024 : ℝ) := by
    rw [show (737901510417216659/738000000000000000 : ℝ)+2*(25630401853/36900000000000 : ℝ)*(2611/25000 : ℝ)=(10000116314146311/10000000000000000 : ℝ) by norm_num, show 1+2*(2707428332506741/100000000000000000000 : ℝ)=(50002707428332506741/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(21800315552083681/100000000000000000000 : ℝ)+(2707428332506741/100000000000000000000 : ℝ) ≤ ((737901510417216659/738000000000000000 : ℝ)+(25630401853/36900000000000 : ℝ)*((4087/25000 : ℝ)+(2611/25000 : ℝ)))^(4767/1024 : ℝ) := by
    rw [show (737901510417216659/738000000000000000 : ℝ)+(25630401853/36900000000000 : ℝ)*((4087/25000 : ℝ)+(2611/25000 : ℝ))=(10000526400575959/10000000000000000 : ℝ) by norm_num, show 1+(21800315552083681/100000000000000000000 : ℝ)+(2707428332506741/100000000000000000000 : ℝ)=(50012253871942295211/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(21800315552083681/100000000000000000000 : ℝ) ≤ ((737901510417216659/738000000000000000 : ℝ)+2*(25630401853/36900000000000 : ℝ)*(4087/25000 : ℝ))^(4767/1024 : ℝ) := by
    rw [show (737901510417216659/738000000000000000 : ℝ)+2*(25630401853/36900000000000 : ℝ)*(4087/25000 : ℝ)=(10000936487005607/10000000000000000 : ℝ) by norm_num, show 1+2*(21800315552083681/100000000000000000000 : ℝ)=(50021800315552083681/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (737901510417216659/738000000000000000 : ℝ)*(X 1 0+X 2 0)+(25630401853/36900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4767/1024 : ℝ)) (lo := (2611/25000 : ℝ)) (hi := (4087/25000 : ℝ)) (c := (737901510417216659/738000000000000000 : ℝ)) (alpha := (25630401853/36900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (737901510417216659/738000000000000000 : ℝ)*(X 0 1+X 2 1)+(25630401853/36900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4767/1024 : ℝ)) (lo := (2611/25000 : ℝ)) (hi := (4087/25000 : ℝ)) (c := (737901510417216659/738000000000000000 : ℝ)) (alpha := (25630401853/36900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (737901510417216659/738000000000000000 : ℝ)*(X 0 2+X 1 2)+(25630401853/36900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4767/1024 : ℝ)) (lo := (2611/25000 : ℝ)) (hi := (4087/25000 : ℝ)) (c := (737901510417216659/738000000000000000 : ℝ)) (alpha := (25630401853/36900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-424190573/2500000000 : ℝ)*X 0 0+(5458508383/10000000000 : ℝ)*X 0 1+(5181111599/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353132189/10000000000 : ℝ)*X 1 0+(-919890601/5000000000 : ℝ)*X 1 1+(5181111597/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676566089/5000000000 : ℝ)*X 2 0+(518111161/1000000000 : ℝ)*X 2 1+(-4599453/25000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((263130057/625000000 : ℝ)*X 0 0+(1939281939/5000000000 : ℝ)*X 0 1+(456291587/1000000000 : ℝ)*X 0 2+(263130057/625000000 : ℝ)*X 1 0+(1939281939/5000000000 : ℝ)*X 1 1+(456291587/1000000000 : ℝ)*X 1 2+(263130057/625000000 : ℝ)*X 2 0+(1939281939/5000000000 : ℝ)*X 2 1+(456291587/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1696832027/10000000000 : ℝ)*X 0 0+(207327021/400000000 : ℝ)*X 0 1+(218256911/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5279423229/10000000000 : ℝ)*X 1 0+(-1564470053/10000000000 : ℝ)*X 1 1+(1364105699/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5279423267/10000000000 : ℝ)*X 2 0+(5456422791/10000000000 : ℝ)*X 2 1+(-1564470009/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1052563243/2500000000 : ℝ)*X 0 0+(1139456013/2500000000 : ℝ)*X 0 1+(970927301/2500000000 : ℝ)*X 0 2+(1052563243/2500000000 : ℝ)*X 1 0+(1139456013/2500000000 : ℝ)*X 1 1+(970927301/2500000000 : ℝ)*X 1 2+(1052563243/2500000000 : ℝ)*X 2 0+(1139456013/2500000000 : ℝ)*X 2 1+(970927301/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10211068600943628159777547/1025000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1645067477/100000000000000 : ℝ)*(base19) + (1536690269/100000000000000 : ℝ)*(base23) + (5405027/10000000000000 : ℝ)*(lower2) + (245301159/100000000000000 : ℝ)*(upper3) + (86122871/50000000000000 : ℝ)*(upper5) + (633279739037699/25000000000000 : ℝ)*(major0) + (633279739037699/25000000000000 : ℝ)*(major1) + (633279739037699/25000000000000 : ℝ)*(major2) + (28839719536201/800000000000 : ℝ)*(sp0) + (1802491577561813/50000000000000 : ℝ)*(sp1) + (720996652700167/20000000000000 : ℝ)*(sp2) + (58449764068871/4000000000000 : ℝ)*(sp3) + (19858165979/100000000000000 : ℝ)*(sp4) + (1735664287/20000000000000 : ℝ)*(sp7) + (146125278004321/10000000000000 : ℝ)*(f.failure) + (28163943751493/781250000000 : ℝ)*(f.sum) + (7626001692473/1845000000000000000000000000 : ℝ)*base65 + (16863621997232359/18450000000000000000000000000000 : ℝ)*base68 + (85268263958732359/18450000000000000000000000000000 : ℝ)*base70 + (145464533044467641/18450000000000000000000000000000 : ℝ)*base71 + (3911646935111/922500000000000000000000000 : ℝ)*base74 + (36416974490367641/18450000000000000000000000000000 : ℝ)*base75 + (41865167735732359/18450000000000000000000000000000 : ℝ)*base78 + (162869680372232359/18450000000000000000000000000000 : ℝ)*base80 + (1129788565781/922500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (72629/20000000000000000000 : ℝ)*base90 + (72629/20000000000000000000 : ℝ)*base92 + (72629/20000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (36049605275003487662989903/3075000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (873953699/50000000000000 : ℝ)*(base19) + (1930435263/100000000000000 : ℝ)*(base23) + (55989917/10000000000000 : ℝ)*(lower1) + (30245169/12500000000000 : ℝ)*(upper3) + (16741479/25000000000000 : ℝ)*(lower4) + (245598201/100000000000000 : ℝ)*(upper5) + (642885818048683/25000000000000 : ℝ)*(major0) + (642885818048683/25000000000000 : ℝ)*(major1) + (642885818048683/25000000000000 : ℝ)*(major2) + (420343853/20000000000000 : ℝ)*(sp2) + (365966795630139/10000000000000 : ℝ)*(sp4) + (457458276049249/12500000000000 : ℝ)*(sp5) + (1829831962073431/50000000000000 : ℝ)*(sp6) + (23178409332913/1562500000000 : ℝ)*(sp7) + (23178409332913/1562500000000 : ℝ)*(f.failure) + (365966795630139/10000000000000 : ℝ)*(f.sum) + (2750160930817/922500000000000000000000000 : ℝ)*base66 + (162056549764290097/18450000000000000000000000000000 : ℝ)*base67 + (23741047988490097/18450000000000000000000000000000 : ℝ)*base69 + (1016037422084190097/18450000000000000000000000000000 : ℝ)*base71 + (23114725009/461250000000000000000000000 : ℝ)*base73 + (259246608859409903/18450000000000000000000000000000 : ℝ)*base76 + (32162559944009903/18450000000000000000000000000000 : ℝ)*base78 + (93263533974390097/18450000000000000000000000000000 : ℝ)*base79 + (282862722127/922500000000000000000000000 : ℝ)*base82 + (25437/3125000000000000000 : ℝ)*base90 + (25437/3125000000000000000 : ℝ)*base92 + (25437/3125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1613_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3467051/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4087/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2611/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5227/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16337/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1613_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1613_s5_0 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1696771079/10000000000 : ℝ)*x 0 + (5458464283/10000000000 : ℝ)*x 1 + (1036229971/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1696771079/10000000000 : ℝ)^4771 ≤ (10449382255931/100000000000000 : ℝ)^3747 := by
    have hnat : (1696771079 : ℕ)^4771*100000000000000^3747 ≤ 10449382255931^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1696771079 10000000000 10449382255931 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5458464283/10000000000 : ℝ)^4771 ≤ (4626107276067/10000000000000 : ℝ)^3747 := by
    have hnat : (5458464283 : ℕ)^4771*10000000000000^3747 ≤ 4626107276067^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5458464283 10000000000 4626107276067 10000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036229971/2000000000 : ℝ)^4771 ≤ (10822386241561/25000000000000 : ℝ)^3747 := by
    have hnat : (1036229971 : ℕ)^4771*25000000000000^3747 ≤ 10822386241561^3747*2000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036229971 2000000000 10822386241561 25000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1696771079/10000000000 : ℝ), (5458464283/10000000000 : ℝ), (1036229971/2000000000 : ℝ)] ![(10449382255931/100000000000000 : ℝ), (4626107276067/10000000000000 : ℝ), (10822386241561/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1696771079/10000000000 : ℝ)|^4771 ≤ (10449382255931/100000000000000 : ℝ)^3747
        have hw : |(-1696771079/10000000000 : ℝ)|=(1696771079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5458464283/10000000000 : ℝ)|^4771 ≤ (4626107276067/10000000000000 : ℝ)^3747
        have hw : |(5458464283/10000000000 : ℝ)|=(5458464283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1036229971/2000000000 : ℝ)|^4771 ≤ (10822386241561/25000000000000 : ℝ)^3747
        have hw : |(1036229971/2000000000 : ℝ)|=(1036229971/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_s5_1 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353120357/10000000000 : ℝ)*x 0 + (-1839746171/10000000000 : ℝ)*x 1 + (5181149933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353120357/10000000000 : ℝ)^4771 ≤ (45127294177391/100000000000000 : ℝ)^3747 := by
    have hnat : (5353120357 : ℕ)^4771*100000000000000^3747 ≤ 45127294177391^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353120357 10000000000 45127294177391 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1839746171/10000000000 : ℝ)^4771 ≤ (2316632001813/20000000000000 : ℝ)^3747 := by
    have hnat : (1839746171 : ℕ)^4771*20000000000000^3747 ≤ 2316632001813^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1839746171 10000000000 2316632001813 20000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5181149933/10000000000 : ℝ)^4771 ≤ (43289545796051/100000000000000 : ℝ)^3747 := by
    have hnat : (5181149933 : ℕ)^4771*100000000000000^3747 ≤ 43289545796051^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181149933 10000000000 43289545796051 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353120357/10000000000 : ℝ), (-1839746171/10000000000 : ℝ), (5181149933/10000000000 : ℝ)] ![(45127294177391/100000000000000 : ℝ), (2316632001813/20000000000000 : ℝ), (43289545796051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353120357/10000000000 : ℝ)|^4771 ≤ (45127294177391/100000000000000 : ℝ)^3747
        have hw : |(5353120357/10000000000 : ℝ)|=(5353120357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1839746171/10000000000 : ℝ)|^4771 ≤ (2316632001813/20000000000000 : ℝ)^3747
        have hw : |(-1839746171/10000000000 : ℝ)|=(1839746171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5181149933/10000000000 : ℝ)|^4771 ≤ (43289545796051/100000000000000 : ℝ)^3747
        have hw : |(5181149933/10000000000 : ℝ)|=(5181149933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_s5_2 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353120359/10000000000 : ℝ)*x 0 + (5181149907/10000000000 : ℝ)*x 1 + (-1839746203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353120359/10000000000 : ℝ)^4771 ≤ (45127294198859/100000000000000 : ℝ)^3747 := by
    have hnat : (5353120359 : ℕ)^4771*100000000000000^3747 ≤ 45127294198859^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353120359 10000000000 45127294198859 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5181149907/10000000000 : ℝ)^4771 ≤ (43289545519449/100000000000000 : ℝ)^3747 := by
    have hnat : (5181149907 : ℕ)^4771*100000000000000^3747 ≤ 43289545519449^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181149907 10000000000 43289545519449 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1839746203/10000000000 : ℝ)^4771 ≤ (11583160265599/100000000000000 : ℝ)^3747 := by
    have hnat : (1839746203 : ℕ)^4771*100000000000000^3747 ≤ 11583160265599^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1839746203 10000000000 11583160265599 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353120359/10000000000 : ℝ), (5181149907/10000000000 : ℝ), (-1839746203/10000000000 : ℝ)] ![(45127294198859/100000000000000 : ℝ), (43289545519449/100000000000000 : ℝ), (11583160265599/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353120359/10000000000 : ℝ)|^4771 ≤ (45127294198859/100000000000000 : ℝ)^3747
        have hw : |(5353120359/10000000000 : ℝ)|=(5353120359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5181149907/10000000000 : ℝ)|^4771 ≤ (43289545519449/100000000000000 : ℝ)^3747
        have hw : |(5181149907/10000000000 : ℝ)|=(5181149907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1839746203/10000000000 : ℝ)|^4771 ≤ (11583160265599/100000000000000 : ℝ)^3747
        have hw : |(-1839746203/10000000000 : ℝ)|=(1839746203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_s5_3 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2105043233/5000000000 : ℝ)*x 0 + (242416547/625000000 : ℝ)*x 1 + (570351743/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2105043233/5000000000 : ℝ)^4771 ≤ (33236499310451/100000000000000 : ℝ)^3747 := by
    have hnat : (2105043233 : ℕ)^4771*100000000000000^3747 ≤ 33236499310451^3747*5000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105043233 5000000000 33236499310451 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (242416547/625000000 : ℝ)^4771 ≤ (14970804994967/50000000000000 : ℝ)^3747 := by
    have hnat : (242416547 : ℕ)^4771*50000000000000^3747 ≤ 14970804994967^3747*625000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      242416547 625000000 14970804994967 50000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (570351743/1250000000 : ℝ)^4771 ≤ (4602736336411/12500000000000 : ℝ)^3747 := by
    have hnat : (570351743 : ℕ)^4771*12500000000000^3747 ≤ 4602736336411^3747*1250000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      570351743 1250000000 4602736336411 12500000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2105043233/5000000000 : ℝ), (242416547/625000000 : ℝ), (570351743/1250000000 : ℝ)] ![(33236499310451/100000000000000 : ℝ), (14970804994967/50000000000000 : ℝ), (4602736336411/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2105043233/5000000000 : ℝ)|^4771 ≤ (33236499310451/100000000000000 : ℝ)^3747
        have hw : |(2105043233/5000000000 : ℝ)|=(2105043233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(242416547/625000000 : ℝ)|^4771 ≤ (14970804994967/50000000000000 : ℝ)^3747
        have hw : |(242416547/625000000 : ℝ)|=(242416547/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(570351743/1250000000 : ℝ)|^4771 ≤ (4602736336411/12500000000000 : ℝ)^3747
        have hw : |(570351743/1250000000 : ℝ)|=(570351743/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_s5_4 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-424210171/2500000000 : ℝ)*x 0 + (647901569/1250000000 : ℝ)*x 1 + (1364094993/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (424210171/2500000000 : ℝ)^4771 ≤ (5224964029491/50000000000000 : ℝ)^3747 := by
    have hnat : (424210171 : ℕ)^4771*50000000000000^3747 ≤ 5224964029491^3747*2500000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424210171 2500000000 5224964029491 50000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (647901569/1250000000 : ℝ)^4771 ≤ (10827872568177/25000000000000 : ℝ)^3747 := by
    have hnat : (647901569 : ℕ)^4771*25000000000000^3747 ≤ 10827872568177^3747*1250000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647901569 1250000000 10827872568177 25000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1364094993/2500000000 : ℝ)^4771 ≤ (46238581654907/100000000000000 : ℝ)^3747 := by
    have hnat : (1364094993 : ℕ)^4771*100000000000000^3747 ≤ 46238581654907^3747*2500000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364094993 2500000000 46238581654907 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-424210171/2500000000 : ℝ), (647901569/1250000000 : ℝ), (1364094993/2500000000 : ℝ)] ![(5224964029491/50000000000000 : ℝ), (10827872568177/25000000000000 : ℝ), (46238581654907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-424210171/2500000000 : ℝ)|^4771 ≤ (5224964029491/50000000000000 : ℝ)^3747
        have hw : |(-424210171/2500000000 : ℝ)|=(424210171/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(647901569/1250000000 : ℝ)|^4771 ≤ (10827872568177/25000000000000 : ℝ)^3747
        have hw : |(647901569/1250000000 : ℝ)|=(647901569/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1364094993/2500000000 : ℝ)|^4771 ≤ (46238581654907/100000000000000 : ℝ)^3747
        have hw : |(1364094993/2500000000 : ℝ)|=(1364094993/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_s5_5 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279433453/10000000000 : ℝ)*x 0 + (-62580643/400000000 : ℝ)*x 1 + (5456379953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279433453/10000000000 : ℝ)^4771 ≤ (8867567634279/20000000000000 : ℝ)^3747 := by
    have hnat : (5279433453 : ℕ)^4771*20000000000000^3747 ≤ 8867567634279^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279433453 10000000000 8867567634279 20000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (62580643/400000000 : ℝ)^4771 ≤ (9423580365469/100000000000000 : ℝ)^3747 := by
    have hnat : (62580643 : ℕ)^4771*100000000000000^3747 ≤ 9423580365469^3747*400000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62580643 400000000 9423580365469 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5456379953/10000000000 : ℝ)^4771 ≤ (9247716289979/20000000000000 : ℝ)^3747 := by
    have hnat : (5456379953 : ℕ)^4771*20000000000000^3747 ≤ 9247716289979^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5456379953 10000000000 9247716289979 20000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279433453/10000000000 : ℝ), (-62580643/400000000 : ℝ), (5456379953/10000000000 : ℝ)] ![(8867567634279/20000000000000 : ℝ), (9423580365469/100000000000000 : ℝ), (9247716289979/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279433453/10000000000 : ℝ)|^4771 ≤ (8867567634279/20000000000000 : ℝ)^3747
        have hw : |(5279433453/10000000000 : ℝ)|=(5279433453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-62580643/400000000 : ℝ)|^4771 ≤ (9423580365469/100000000000000 : ℝ)^3747
        have hw : |(-62580643/400000000 : ℝ)|=(62580643/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5456379953/10000000000 : ℝ)|^4771 ≤ (9247716289979/20000000000000 : ℝ)^3747
        have hw : |(5456379953/10000000000 : ℝ)|=(5456379953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_s5_6 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639716717/5000000000 : ℝ)*x 0 + (1364095001/2500000000 : ℝ)*x 1 + (-1564516029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639716717/5000000000 : ℝ)^4771 ≤ (22168918984111/50000000000000 : ℝ)^3747 := by
    have hnat : (2639716717 : ℕ)^4771*50000000000000^3747 ≤ 22168918984111^3747*5000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639716717 5000000000 22168918984111 50000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1364095001/2500000000 : ℝ)^4771 ≤ (4623858200019/10000000000000 : ℝ)^3747 := by
    have hnat : (1364095001 : ℕ)^4771*10000000000000^3747 ≤ 4623858200019^3747*2500000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364095001 2500000000 4623858200019 10000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1564516029/10000000000 : ℝ)^4771 ≤ (2355895003169/25000000000000 : ℝ)^3747 := by
    have hnat : (1564516029 : ℕ)^4771*25000000000000^3747 ≤ 2355895003169^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1564516029 10000000000 2355895003169 25000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639716717/5000000000 : ℝ), (1364095001/2500000000 : ℝ), (-1564516029/10000000000 : ℝ)] ![(22168918984111/50000000000000 : ℝ), (4623858200019/10000000000000 : ℝ), (2355895003169/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639716717/5000000000 : ℝ)|^4771 ≤ (22168918984111/50000000000000 : ℝ)^3747
        have hw : |(2639716717/5000000000 : ℝ)|=(2639716717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1364095001/2500000000 : ℝ)|^4771 ≤ (4623858200019/10000000000000 : ℝ)^3747
        have hw : |(1364095001/2500000000 : ℝ)|=(1364095001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1564516029/10000000000 : ℝ)|^4771 ≤ (2355895003169/25000000000000 : ℝ)^3747
        have hw : |(-1564516029/10000000000 : ℝ)|=(1564516029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_s5_7 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4210258513/10000000000 : ℝ)*x 0 + (4557725063/10000000000 : ℝ)*x 1 + (3883806953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4210258513/10000000000 : ℝ)^4771 ≤ (2077389295413/6250000000000 : ℝ)^3747 := by
    have hnat : (4210258513 : ℕ)^4771*6250000000000^3747 ≤ 2077389295413^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4210258513 10000000000 2077389295413 6250000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4557725063/10000000000 : ℝ)^4771 ≤ (9192402084269/25000000000000 : ℝ)^3747 := by
    have hnat : (4557725063 : ℕ)^4771*25000000000000^3747 ≤ 9192402084269^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4557725063 10000000000 9192402084269 25000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3883806953/10000000000 : ℝ)^4771 ≤ (29992162918577/100000000000000 : ℝ)^3747 := by
    have hnat : (3883806953 : ℕ)^4771*100000000000000^3747 ≤ 29992162918577^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3883806953 10000000000 29992162918577 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4210258513/10000000000 : ℝ), (4557725063/10000000000 : ℝ), (3883806953/10000000000 : ℝ)] ![(2077389295413/6250000000000 : ℝ), (9192402084269/25000000000000 : ℝ), (29992162918577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4210258513/10000000000 : ℝ)|^4771 ≤ (2077389295413/6250000000000 : ℝ)^3747
        have hw : |(4210258513/10000000000 : ℝ)|=(4210258513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4557725063/10000000000 : ℝ)|^4771 ≤ (9192402084269/25000000000000 : ℝ)^3747
        have hw : |(4557725063/10000000000 : ℝ)|=(4557725063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3883806953/10000000000 : ℝ)|^4771 ≤ (29992162918577/100000000000000 : ℝ)^3747
        have hw : |(3883806953/10000000000 : ℝ)|=(3883806953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1613_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3467051/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16337/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5227/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2091/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1021/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16337/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5227/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16337/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5227/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16337/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5227/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16337/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5227/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16337/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5227/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16337/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5227/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5227/50000 : ℝ) ^ (4767/1024 : ℝ) ≤ (2719517468679831/100000000000000000000 : ℝ) := by
    have hpowers : (5227/50000 : ℝ)^4767 ≤ (2719517468679831/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5227 : ℕ)^4767*100000000000000000000^1024 ≤ 2719517468679831^1024*50000^4767 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5227 50000 2719517468679831 100000000000000000000 4767 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5227/50000 : ℝ)) (X := (2719517468679831/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4767 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16337/100000 : ℝ) ^ (4767/1024 : ℝ) ≤ (1086605639634153/5000000000000000000 : ℝ) := by
    have hpowers : (16337/100000 : ℝ)^4767 ≤ (1086605639634153/5000000000000000000 : ℝ)^1024 := by
      have hnat : (16337 : ℕ)^4767*5000000000000000000^1024 ≤ 1086605639634153^1024*100000^4767 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16337 100000 1086605639634153 5000000000000000000 4767 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16337/100000 : ℝ)) (X := (1086605639634153/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4767 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002719517468679831/50000000000000000000 : ℝ) ≤ (10000116833498019/10000000000000000 : ℝ) ^ (4767/1024 : ℝ) := by
    have hpowers : (50002719517468679831/50000000000000000000 : ℝ)^1024 ≤ (10000116833498019/10000000000000000 : ℝ)^4767 := by
      have hnat : (50002719517468679831 : ℕ)^1024*10000000000000000^4767 ≤ 10000116833498019^4767*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002719517468679831 50000000000000000000 10000116833498019 10000000000000000 1024 4767 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000116833498019/10000000000000000 : ℝ)) (X := (50002719517468679831/50000000000000000000 : ℝ)) (by norm_num) 4767 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100024451630261362891/100000000000000000000 : ℝ) ≤ (10000525195429997/10000000000000000 : ℝ) ^ (4767/1024 : ℝ) := by
    have hpowers : (100024451630261362891/100000000000000000000 : ℝ)^1024 ≤ (10000525195429997/10000000000000000 : ℝ)^4767 := by
      have hnat : (100024451630261362891 : ℕ)^1024*10000000000000000^4767 ≤ 10000525195429997^4767*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100024451630261362891 100000000000000000000 10000525195429997 10000000000000000 1024 4767 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000525195429997/10000000000000000 : ℝ)) (X := (100024451630261362891/100000000000000000000 : ℝ)) (by norm_num) 4767 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501086605639634153/2500000000000000000 : ℝ) ≤ (400037342294479/400000000000000 : ℝ) ^ (4767/1024 : ℝ) := by
    have hpowers : (2501086605639634153/2500000000000000000 : ℝ)^1024 ≤ (400037342294479/400000000000000 : ℝ)^4767 := by
      have hnat : (2501086605639634153 : ℕ)^1024*400000000000000^4767 ≤ 400037342294479^4767*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501086605639634153 2500000000000000000 400037342294479 400000000000000 1024 4767 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400037342294479/400000000000000 : ℝ)) (X := (2501086605639634153/2500000000000000000 : ℝ)) (by norm_num) 4767 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2719517468679831/100000000000000000000 : ℝ) ≤ ((58822149300195049753/58830000000000000000 : ℝ)+2*(204180965989/294150000000000 : ℝ)*(5227/50000 : ℝ))^(4767/1024 : ℝ) := by
    rw [show (58822149300195049753/58830000000000000000 : ℝ)+2*(204180965989/294150000000000 : ℝ)*(5227/50000 : ℝ)=(10000116833498019/10000000000000000 : ℝ) by norm_num, show 1+2*(2719517468679831/100000000000000000000 : ℝ)=(50002719517468679831/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1086605639634153/5000000000000000000 : ℝ)+(2719517468679831/100000000000000000000 : ℝ) ≤ ((58822149300195049753/58830000000000000000 : ℝ)+(204180965989/294150000000000 : ℝ)*((16337/100000 : ℝ)+(5227/50000 : ℝ)))^(4767/1024 : ℝ) := by
    rw [show (58822149300195049753/58830000000000000000 : ℝ)+(204180965989/294150000000000 : ℝ)*((16337/100000 : ℝ)+(5227/50000 : ℝ))=(10000525195429997/10000000000000000 : ℝ) by norm_num, show 1+(1086605639634153/5000000000000000000 : ℝ)+(2719517468679831/100000000000000000000 : ℝ)=(100024451630261362891/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1086605639634153/5000000000000000000 : ℝ) ≤ ((58822149300195049753/58830000000000000000 : ℝ)+2*(204180965989/294150000000000 : ℝ)*(16337/100000 : ℝ))^(4767/1024 : ℝ) := by
    rw [show (58822149300195049753/58830000000000000000 : ℝ)+2*(204180965989/294150000000000 : ℝ)*(16337/100000 : ℝ)=(400037342294479/400000000000000 : ℝ) by norm_num, show 1+2*(1086605639634153/5000000000000000000 : ℝ)=(2501086605639634153/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (58822149300195049753/58830000000000000000 : ℝ)*(X 1 0+X 2 0)+(204180965989/294150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4767/1024 : ℝ)) (lo := (5227/50000 : ℝ)) (hi := (16337/100000 : ℝ)) (c := (58822149300195049753/58830000000000000000 : ℝ)) (alpha := (204180965989/294150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (58822149300195049753/58830000000000000000 : ℝ)*(X 0 1+X 2 1)+(204180965989/294150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4767/1024 : ℝ)) (lo := (5227/50000 : ℝ)) (hi := (16337/100000 : ℝ)) (c := (58822149300195049753/58830000000000000000 : ℝ)) (alpha := (204180965989/294150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (58822149300195049753/58830000000000000000 : ℝ)*(X 0 2+X 1 2)+(204180965989/294150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4767/1024 : ℝ)) (lo := (5227/50000 : ℝ)) (hi := (16337/100000 : ℝ)) (c := (58822149300195049753/58830000000000000000 : ℝ)) (alpha := (204180965989/294150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1696771079/10000000000 : ℝ)*X 0 0+(5458464283/10000000000 : ℝ)*X 0 1+(1036229971/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353120357/10000000000 : ℝ)*X 1 0+(-1839746171/10000000000 : ℝ)*X 1 1+(5181149933/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353120359/10000000000 : ℝ)*X 2 0+(5181149907/10000000000 : ℝ)*X 2 1+(-1839746203/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2105043233/5000000000 : ℝ)*X 0 0+(242416547/625000000 : ℝ)*X 0 1+(570351743/1250000000 : ℝ)*X 0 2+(2105043233/5000000000 : ℝ)*X 1 0+(242416547/625000000 : ℝ)*X 1 1+(570351743/1250000000 : ℝ)*X 1 2+(2105043233/5000000000 : ℝ)*X 2 0+(242416547/625000000 : ℝ)*X 2 1+(570351743/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-424210171/2500000000 : ℝ)*X 0 0+(647901569/1250000000 : ℝ)*X 0 1+(1364094993/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5279433453/10000000000 : ℝ)*X 1 0+(-62580643/400000000 : ℝ)*X 1 1+(5456379953/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2639716717/5000000000 : ℝ)*X 2 0+(1364095001/2500000000 : ℝ)*X 2 1+(-1564516029/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4210258513/10000000000 : ℝ)*X 0 0+(4557725063/10000000000 : ℝ)*X 0 1+(3883806953/10000000000 : ℝ)*X 0 2+(4210258513/10000000000 : ℝ)*X 1 0+(4557725063/10000000000 : ℝ)*X 1 1+(3883806953/10000000000 : ℝ)*X 1 2+(4210258513/10000000000 : ℝ)*X 2 0+(4557725063/10000000000 : ℝ)*X 2 1+(3883806953/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3995937732460596860278913187/490250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1287838529/100000000000000 : ℝ)*(base19) + (1246478963/100000000000000 : ℝ)*(base23) + (52019241/25000000000000 : ℝ)*(upper3) + (22861483/100000000000000 : ℝ)*(upper4) + (38656149/25000000000000 : ℝ)*(upper5) + (1266932890538007/50000000000000 : ℝ)*(major0) + (1266932890538007/50000000000000 : ℝ)*(major1) + (1266932890538007/50000000000000 : ℝ)*(major2) + (1803015843878557/50000000000000 : ℝ)*(sp0) + (721209281960969/20000000000000 : ℝ)*(sp1) + (360604645116441/10000000000000 : ℝ)*(sp2) + (1461676235283259/100000000000000 : ℝ)*(sp3) + (16009886259/100000000000000 : ℝ)*(sp4) + (7357531507/100000000000000 : ℝ)*(sp7) + (730841796407383/50000000000000 : ℝ)*(f.failure) + (1803023848821687/50000000000000 : ℝ)*(f.sum) + (9197199219951/9805000000000000000000000000 : ℝ)*base66 + (13008893836339520757/980500000000000000000000000000000 : ℝ)*base67 + (3115427296286520757/980500000000000000000000000000000 : ℝ)*base69 + (180088204304020757/980500000000000000000000000000000 : ℝ)*base71 + (26141185360147/4902500000000000000000000000 : ℝ)*base73 + (3965616721543020757/980500000000000000000000000000000 : ℝ)*base75 + (7768674303041520757/980500000000000000000000000000000 : ℝ)*base77 + (9063432785319520757/980500000000000000000000000000000 : ℝ)*base79 + (29029006106221/9805000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (362467/100000000000000000000 : ℝ)*base90 + (362467/100000000000000000000 : ℝ)*base92 + (362467/100000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (104720536969348228153083/9805000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1694182077/100000000000000 : ℝ)*(base19) + (890828297/50000000000000 : ℝ)*(base23) + (259984711/50000000000000 : ℝ)*(lower1) + (242847147/100000000000000 : ℝ)*(upper3) + (19522051/50000000000000 : ℝ)*(lower4) + (54610109/25000000000000 : ℝ)*(upper5) + (1286147753133657/50000000000000 : ℝ)*(major0) + (1286147753133657/50000000000000 : ℝ)*(major1) + (1286147753133657/50000000000000 : ℝ)*(major2) + (1912535511/100000000000000 : ℝ)*(sp2) + (3660738526129957/100000000000000 : ℝ)*(sp4) + (91518420798697/2500000000000 : ℝ)*(sp5) + (915183707984463/25000000000000 : ℝ)*(sp6) + (741926065196997/50000000000000 : ℝ)*(sp7) + (741926065196997/50000000000000 : ℝ)*(f.failure) + (3660738526129957/100000000000000 : ℝ)*(f.sum) + (15979169323747/4902500000000000000000000000 : ℝ)*base65 + (12075847156513521093/980500000000000000000000000000000 : ℝ)*base68 + (731375600686478907/980500000000000000000000000000000 : ℝ)*base69 + (2560691463331521093/980500000000000000000000000000000 : ℝ)*base72 + (20899888338173/4902500000000000000000000000 : ℝ)*base74 + (72965959319188478907/980500000000000000000000000000000 : ℝ)*base75 + (5990168069919978907/980500000000000000000000000000000 : ℝ)*base77 + (378225874404021093/980500000000000000000000000000000 : ℝ)*base80 + (28996292201359/9805000000000000000000000000 : ℝ)*base81 + (354153/100000000000000000000 : ℝ)*base90 + (354153/100000000000000000000 : ℝ)*base92 + (354153/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1613_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3467051/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16337/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5227/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2091/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1021/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1613_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1613_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3467051/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (413/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2091/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1021/6250 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1613_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1613_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1613_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3467051/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (413/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2091/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1021/6250 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1613_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
