-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1455_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:00:27.373288+00:00
-- url     : https://prove2.me/submissions/d5999e94-e599-417d-a8b4-1b5db76a6baa

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
theorem support_rectangle_w1455_s3_0 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-389864247/2000000000 : ℝ)*x 0 + (5414738373/10000000000 : ℝ)*x 1 + (1310049231/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (389864247/2000000000 : ℝ)^4415 ≤ (5948608412197/50000000000000 : ℝ)^3391 := by
    have hnat : (389864247 : ℕ)^4415*50000000000000^3391 ≤ 5948608412197^3391*2000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389864247 2000000000 5948608412197 50000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414738373/10000000000 : ℝ)^4415 ≤ (4499086241899/10000000000000 : ℝ)^3391 := by
    have hnat : (5414738373 : ℕ)^4415*10000000000000^3391 ≤ 4499086241899^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414738373 10000000000 4499086241899 10000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310049231/2500000000 : ℝ)^4415 ≤ (10777980183129/25000000000000 : ℝ)^3391 := by
    have hnat : (1310049231 : ℕ)^4415*25000000000000^3391 ≤ 10777980183129^3391*2500000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310049231 2500000000 10777980183129 25000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-389864247/2000000000 : ℝ), (5414738373/10000000000 : ℝ), (1310049231/2500000000 : ℝ)] ![(5948608412197/50000000000000 : ℝ), (4499086241899/10000000000000 : ℝ), (10777980183129/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-389864247/2000000000 : ℝ)|^4415 ≤ (5948608412197/50000000000000 : ℝ)^3391
        have hw : |(-389864247/2000000000 : ℝ)|=(389864247/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414738373/10000000000 : ℝ)|^4415 ≤ (4499086241899/10000000000000 : ℝ)^3391
        have hw : |(5414738373/10000000000 : ℝ)|=(5414738373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310049231/2500000000 : ℝ)|^4415 ≤ (10777980183129/25000000000000 : ℝ)^3391
        have hw : |(1310049231/2500000000 : ℝ)|=(1310049231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s3_1 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348803083/10000000000 : ℝ)*x 0 + (-509578263/2500000000 : ℝ)*x 1 + (2620098377/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348803083/10000000000 : ℝ)^4415 ≤ (44278885063667/100000000000000 : ℝ)^3391 := by
    have hnat : (5348803083 : ℕ)^4415*100000000000000^3391 ≤ 44278885063667^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348803083 10000000000 44278885063667 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (509578263/2500000000 : ℝ)^4415 ≤ (12609196007187/100000000000000 : ℝ)^3391 := by
    have hnat : (509578263 : ℕ)^4415*100000000000000^3391 ≤ 12609196007187^3391*2500000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      509578263 2500000000 12609196007187 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2620098377/5000000000 : ℝ)^4415 ≤ (43111918911551/100000000000000 : ℝ)^3391 := by
    have hnat : (2620098377 : ℕ)^4415*100000000000000^3391 ≤ 43111918911551^3391*5000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620098377 5000000000 43111918911551 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348803083/10000000000 : ℝ), (-509578263/2500000000 : ℝ), (2620098377/5000000000 : ℝ)] ![(44278885063667/100000000000000 : ℝ), (12609196007187/100000000000000 : ℝ), (43111918911551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348803083/10000000000 : ℝ)|^4415 ≤ (44278885063667/100000000000000 : ℝ)^3391
        have hw : |(5348803083/10000000000 : ℝ)|=(5348803083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-509578263/2500000000 : ℝ)|^4415 ≤ (12609196007187/100000000000000 : ℝ)^3391
        have hw : |(-509578263/2500000000 : ℝ)|=(509578263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2620098377/5000000000 : ℝ)|^4415 ≤ (43111918911551/100000000000000 : ℝ)^3391
        have hw : |(2620098377/5000000000 : ℝ)|=(2620098377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s3_2 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348803313/10000000000 : ℝ)*x 0 + (2620098363/5000000000 : ℝ)*x 1 + (-1019156391/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348803313/10000000000 : ℝ)^4415 ≤ (8855777508527/20000000000000 : ℝ)^3391 := by
    have hnat : (5348803313 : ℕ)^4415*20000000000000^3391 ≤ 8855777508527^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348803313 10000000000 8855777508527 20000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2620098363/5000000000 : ℝ)^4415 ≤ (43111918611627/100000000000000 : ℝ)^3391 := by
    have hnat : (2620098363 : ℕ)^4415*100000000000000^3391 ≤ 43111918611627^3391*5000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620098363 5000000000 43111918611627 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1019156391/5000000000 : ℝ)^4415 ≤ (1576149229071/12500000000000 : ℝ)^3391 := by
    have hnat : (1019156391 : ℕ)^4415*12500000000000^3391 ≤ 1576149229071^3391*5000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019156391 5000000000 1576149229071 12500000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348803313/10000000000 : ℝ), (2620098363/5000000000 : ℝ), (-1019156391/5000000000 : ℝ)] ![(8855777508527/20000000000000 : ℝ), (43111918611627/100000000000000 : ℝ), (1576149229071/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348803313/10000000000 : ℝ)|^4415 ≤ (8855777508527/20000000000000 : ℝ)^3391
        have hw : |(5348803313/10000000000 : ℝ)|=(5348803313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2620098363/5000000000 : ℝ)|^4415 ≤ (43111918611627/100000000000000 : ℝ)^3391
        have hw : |(2620098363/5000000000 : ℝ)|=(2620098363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1019156391/5000000000 : ℝ)|^4415 ≤ (1576149229071/12500000000000 : ℝ)^3391
        have hw : |(-1019156391/5000000000 : ℝ)|=(1019156391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s3_3 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (429735869/1000000000 : ℝ)*x 0 + (4110520649/10000000000 : ℝ)*x 1 + (1122928211/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (429735869/1000000000 : ℝ)^4415 ≤ (6659894580377/20000000000000 : ℝ)^3391 := by
    have hnat : (429735869 : ℕ)^4415*20000000000000^3391 ≤ 6659894580377^3391*1000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429735869 1000000000 6659894580377 20000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4110520649/10000000000 : ℝ)^4415 ≤ (6285401291061/20000000000000 : ℝ)^3391 := by
    have hnat : (4110520649 : ℕ)^4415*20000000000000^3391 ≤ 6285401291061^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4110520649 10000000000 6285401291061 20000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1122928211/2500000000 : ℝ)^4415 ≤ (35273520617499/100000000000000 : ℝ)^3391 := by
    have hnat : (1122928211 : ℕ)^4415*100000000000000^3391 ≤ 35273520617499^3391*2500000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122928211 2500000000 35273520617499 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(429735869/1000000000 : ℝ), (4110520649/10000000000 : ℝ), (1122928211/2500000000 : ℝ)] ![(6659894580377/20000000000000 : ℝ), (6285401291061/20000000000000 : ℝ), (35273520617499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(429735869/1000000000 : ℝ)|^4415 ≤ (6659894580377/20000000000000 : ℝ)^3391
        have hw : |(429735869/1000000000 : ℝ)|=(429735869/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4110520649/10000000000 : ℝ)|^4415 ≤ (6285401291061/20000000000000 : ℝ)^3391
        have hw : |(4110520649/10000000000 : ℝ)|=(4110520649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1122928211/2500000000 : ℝ)|^4415 ≤ (35273520617499/100000000000000 : ℝ)^3391
        have hw : |(1122928211/2500000000 : ℝ)|=(1122928211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s3_4 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1949335363/10000000000 : ℝ)*x 0 + (163777731/312500000 : ℝ)*x 1 + (54140443/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1949335363/10000000000 : ℝ)^4415 ≤ (11897329089823/100000000000000 : ℝ)^3391 := by
    have hnat : (1949335363 : ℕ)^4415*100000000000000^3391 ≤ 11897329089823^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1949335363 10000000000 11897329089823 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163777731/312500000 : ℝ)^4415 ≤ (2155965843417/5000000000000 : ℝ)^3391 := by
    have hnat : (163777731 : ℕ)^4415*5000000000000^3391 ≤ 2155965843417^3391*312500000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163777731 312500000 2155965843417 5000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54140443/100000000 : ℝ)^4415 ≤ (44983354034507/100000000000000 : ℝ)^3391 := by
    have hnat : (54140443 : ℕ)^4415*100000000000000^3391 ≤ 44983354034507^3391*100000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54140443 100000000 44983354034507 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1949335363/10000000000 : ℝ), (163777731/312500000 : ℝ), (54140443/100000000 : ℝ)] ![(11897329089823/100000000000000 : ℝ), (2155965843417/5000000000000 : ℝ), (44983354034507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1949335363/10000000000 : ℝ)|^4415 ≤ (11897329089823/100000000000000 : ℝ)^3391
        have hw : |(-1949335363/10000000000 : ℝ)|=(1949335363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163777731/312500000 : ℝ)|^4415 ≤ (2155965843417/5000000000000 : ℝ)^3391
        have hw : |(163777731/312500000 : ℝ)|=(163777731/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(54140443/100000000 : ℝ)|^4415 ≤ (44983354034507/100000000000000 : ℝ)^3391
        have hw : |(54140443/100000000 : ℝ)|=(54140443/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s3_5 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (662914371/1250000000 : ℝ)*x 0 + (-1864465663/10000000000 : ℝ)*x 1 + (216561771/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (662914371/1250000000 : ℝ)^4415 ≤ (43789239526339/100000000000000 : ℝ)^3391 := by
    have hnat : (662914371 : ℕ)^4415*100000000000000^3391 ≤ 43789239526339^3391*1250000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662914371 1250000000 43789239526339 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1864465663/10000000000 : ℝ)^4415 ≤ (5613703345761/50000000000000 : ℝ)^3391 := by
    have hnat : (1864465663 : ℕ)^4415*50000000000000^3391 ≤ 5613703345761^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1864465663 10000000000 5613703345761 50000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216561771/400000000 : ℝ)^4415 ≤ (22491676882033/50000000000000 : ℝ)^3391 := by
    have hnat : (216561771 : ℕ)^4415*50000000000000^3391 ≤ 22491676882033^3391*400000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216561771 400000000 22491676882033 50000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(662914371/1250000000 : ℝ), (-1864465663/10000000000 : ℝ), (216561771/400000000 : ℝ)] ![(43789239526339/100000000000000 : ℝ), (5613703345761/50000000000000 : ℝ), (22491676882033/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(662914371/1250000000 : ℝ)|^4415 ≤ (43789239526339/100000000000000 : ℝ)^3391
        have hw : |(662914371/1250000000 : ℝ)|=(662914371/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1864465663/10000000000 : ℝ)|^4415 ≤ (5613703345761/50000000000000 : ℝ)^3391
        have hw : |(-1864465663/10000000000 : ℝ)|=(1864465663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216561771/400000000 : ℝ)|^4415 ≤ (22491676882033/50000000000000 : ℝ)^3391
        have hw : |(216561771/400000000 : ℝ)|=(216561771/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s3_6 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5303313887/10000000000 : ℝ)*x 0 + (2707022559/5000000000 : ℝ)*x 1 + (-1864465981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303313887/10000000000 : ℝ)^4415 ≤ (43789227905203/100000000000000 : ℝ)^3391 := by
    have hnat : (5303313887 : ℕ)^4415*100000000000000^3391 ≤ 43789227905203^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303313887 10000000000 43789227905203 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707022559/5000000000 : ℝ)^4415 ≤ (8996672576669/20000000000000 : ℝ)^3391 := by
    have hnat : (2707022559 : ℕ)^4415*20000000000000^3391 ≤ 8996672576669^3391*5000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707022559 5000000000 8996672576669 20000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1864465981/10000000000 : ℝ)^4415 ≤ (1122740918471/10000000000000 : ℝ)^3391 := by
    have hnat : (1864465981 : ℕ)^4415*10000000000000^3391 ≤ 1122740918471^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1864465981 10000000000 1122740918471 10000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303313887/10000000000 : ℝ), (2707022559/5000000000 : ℝ), (-1864465981/10000000000 : ℝ)] ![(43789227905203/100000000000000 : ℝ), (8996672576669/20000000000000 : ℝ), (1122740918471/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303313887/10000000000 : ℝ)|^4415 ≤ (43789227905203/100000000000000 : ℝ)^3391
        have hw : |(5303313887/10000000000 : ℝ)|=(5303313887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707022559/5000000000 : ℝ)|^4415 ≤ (8996672576669/20000000000000 : ℝ)^3391
        have hw : |(2707022559/5000000000 : ℝ)|=(2707022559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1864465981/10000000000 : ℝ)|^4415 ≤ (1122740918471/10000000000000 : ℝ)^3391
        have hw : |(-1864465981/10000000000 : ℝ)|=(1864465981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s3_7 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4297389513/10000000000 : ℝ)*x 0 + (4490205353/10000000000 : ℝ)*x 1 + (822407531/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4297389513/10000000000 : ℝ)^4415 ≤ (33299783868703/100000000000000 : ℝ)^3391 := by
    have hnat : (4297389513 : ℕ)^4415*100000000000000^3391 ≤ 33299783868703^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4297389513 10000000000 33299783868703 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4490205353/10000000000 : ℝ)^4415 ≤ (35258108139813/100000000000000 : ℝ)^3391 := by
    have hnat : (4490205353 : ℕ)^4415*100000000000000^3391 ≤ 35258108139813^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490205353 10000000000 35258108139813 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (822407531/2000000000 : ℝ)^4415 ≤ (31442107972953/100000000000000 : ℝ)^3391 := by
    have hnat : (822407531 : ℕ)^4415*100000000000000^3391 ≤ 31442107972953^3391*2000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      822407531 2000000000 31442107972953 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4297389513/10000000000 : ℝ), (4490205353/10000000000 : ℝ), (822407531/2000000000 : ℝ)] ![(33299783868703/100000000000000 : ℝ), (35258108139813/100000000000000 : ℝ), (31442107972953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4297389513/10000000000 : ℝ)|^4415 ≤ (33299783868703/100000000000000 : ℝ)^3391
        have hw : |(4297389513/10000000000 : ℝ)|=(4297389513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4490205353/10000000000 : ℝ)|^4415 ≤ (35258108139813/100000000000000 : ℝ)^3391
        have hw : |(4490205353/10000000000 : ℝ)|=(4490205353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(822407531/2000000000 : ℝ)|^4415 ≤ (31442107972953/100000000000000 : ℝ)^3391
        have hw : |(822407531/2000000000 : ℝ)|=(822407531/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1455_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159197973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15723/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5251/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11237/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7467/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15723/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5251/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15723/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5251/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15723/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5251/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15723/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5251/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15723/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5251/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15723/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5251/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
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
  have hpowlo : (5251/50000 : ℝ) ^ (2207/512 : ℝ) ≤ (60415328085207/1000000000000000000 : ℝ) := by
    have hpowers : (5251/50000 : ℝ)^2207 ≤ (60415328085207/1000000000000000000 : ℝ)^512 := by
      have hnat : (5251 : ℕ)^2207*1000000000000000000^512 ≤ 60415328085207^512*50000^2207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5251 50000 60415328085207 1000000000000000000 2207 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5251/50000 : ℝ)) (X := (60415328085207/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2207 512 (by norm_num) hpowers
    exact h
  have hpowhi : (15723/100000 : ℝ) ^ (2207/512 : ℝ) ≤ (34405529139750393/100000000000000000000 : ℝ) := by
    have hpowers : (15723/100000 : ℝ)^2207 ≤ (34405529139750393/100000000000000000000 : ℝ)^512 := by
      have hnat : (15723 : ℕ)^2207*100000000000000000000^512 ≤ 34405529139750393^512*100000^2207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15723 100000 34405529139750393 100000000000000000000 2207 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15723/100000 : ℝ)) (X := (34405529139750393/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2207 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (500060415328085207/500000000000000000 : ℝ) ≤ (10000280300977059/10000000000000000 : ℝ) ^ (2207/512 : ℝ) := by
    have hpowers : (500060415328085207/500000000000000000 : ℝ)^512 ≤ (10000280300977059/10000000000000000 : ℝ)^2207 := by
      have hnat : (500060415328085207 : ℕ)^512*10000000000000000^2207 ≤ 10000280300977059^2207*500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500060415328085207 500000000000000000 10000280300977059 10000000000000000 512 2207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000280300977059/10000000000000000 : ℝ)) (X := (500060415328085207/500000000000000000 : ℝ)) (by norm_num) 2207 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100040447061948271093/100000000000000000000 : ℝ) ≤ (10000938182147747/10000000000000000 : ℝ) ^ (2207/512 : ℝ) := by
    have hpowers : (100040447061948271093/100000000000000000000 : ℝ)^512 ≤ (10000938182147747/10000000000000000 : ℝ)^2207 := by
      have hnat : (100040447061948271093 : ℕ)^512*10000000000000000^2207 ≤ 10000938182147747^2207*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100040447061948271093 100000000000000000000 10000938182147747 10000000000000000 512 2207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000938182147747/10000000000000000 : ℝ)) (X := (100040447061948271093/100000000000000000000 : ℝ)) (by norm_num) 2207 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034405529139750393/50000000000000000000 : ℝ) ≤ (2000319212663687/2000000000000000 : ℝ) ^ (2207/512 : ℝ) := by
    have hpowers : (50034405529139750393/50000000000000000000 : ℝ)^512 ≤ (2000319212663687/2000000000000000 : ℝ)^2207 := by
      have hnat : (50034405529139750393 : ℕ)^512*2000000000000000^2207 ≤ 2000319212663687^2207*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034405529139750393 50000000000000000000 2000319212663687 2000000000000000 512 2207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000319212663687/2000000000000000 : ℝ)) (X := (50034405529139750393/50000000000000000000 : ℝ)) (by norm_num) 2207 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(60415328085207/1000000000000000000 : ℝ) ≤ ((52197645315292094287/52210000000000000000 : ℝ)+2*(2569848323/2039453125000 : ℝ)*(5251/50000 : ℝ))^(2207/512 : ℝ) := by
    rw [show (52197645315292094287/52210000000000000000 : ℝ)+2*(2569848323/2039453125000 : ℝ)*(5251/50000 : ℝ)=(10000280300977059/10000000000000000 : ℝ) by norm_num, show 1+2*(60415328085207/1000000000000000000 : ℝ)=(500060415328085207/500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34405529139750393/100000000000000000000 : ℝ)+(60415328085207/1000000000000000000 : ℝ) ≤ ((52197645315292094287/52210000000000000000 : ℝ)+(2569848323/2039453125000 : ℝ)*((15723/100000 : ℝ)+(5251/50000 : ℝ)))^(2207/512 : ℝ) := by
    rw [show (52197645315292094287/52210000000000000000 : ℝ)+(2569848323/2039453125000 : ℝ)*((15723/100000 : ℝ)+(5251/50000 : ℝ))=(10000938182147747/10000000000000000 : ℝ) by norm_num, show 1+(34405529139750393/100000000000000000000 : ℝ)+(60415328085207/1000000000000000000 : ℝ)=(100040447061948271093/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34405529139750393/100000000000000000000 : ℝ) ≤ ((52197645315292094287/52210000000000000000 : ℝ)+2*(2569848323/2039453125000 : ℝ)*(15723/100000 : ℝ))^(2207/512 : ℝ) := by
    rw [show (52197645315292094287/52210000000000000000 : ℝ)+2*(2569848323/2039453125000 : ℝ)*(15723/100000 : ℝ)=(2000319212663687/2000000000000000 : ℝ) by norm_num, show 1+2*(34405529139750393/100000000000000000000 : ℝ)=(50034405529139750393/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (52197645315292094287/52210000000000000000 : ℝ)*(X 1 0+X 2 0)+(2569848323/2039453125000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2207/512 : ℝ)) (lo := (5251/50000 : ℝ)) (hi := (15723/100000 : ℝ)) (c := (52197645315292094287/52210000000000000000 : ℝ)) (alpha := (2569848323/2039453125000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (52197645315292094287/52210000000000000000 : ℝ)*(X 0 1+X 2 1)+(2569848323/2039453125000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2207/512 : ℝ)) (lo := (5251/50000 : ℝ)) (hi := (15723/100000 : ℝ)) (c := (52197645315292094287/52210000000000000000 : ℝ)) (alpha := (2569848323/2039453125000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (52197645315292094287/52210000000000000000 : ℝ)*(X 0 2+X 1 2)+(2569848323/2039453125000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2207/512 : ℝ)) (lo := (5251/50000 : ℝ)) (hi := (15723/100000 : ℝ)) (c := (52197645315292094287/52210000000000000000 : ℝ)) (alpha := (2569848323/2039453125000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-389864247/2000000000 : ℝ)*X 0 0+(5414738373/10000000000 : ℝ)*X 0 1+(1310049231/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348803083/10000000000 : ℝ)*X 1 0+(-509578263/2500000000 : ℝ)*X 1 1+(2620098377/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348803313/10000000000 : ℝ)*X 2 0+(2620098363/5000000000 : ℝ)*X 2 1+(-1019156391/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((429735869/1000000000 : ℝ)*X 0 0+(4110520649/10000000000 : ℝ)*X 0 1+(1122928211/2500000000 : ℝ)*X 0 2+(429735869/1000000000 : ℝ)*X 1 0+(4110520649/10000000000 : ℝ)*X 1 1+(1122928211/2500000000 : ℝ)*X 1 2+(429735869/1000000000 : ℝ)*X 2 0+(4110520649/10000000000 : ℝ)*X 2 1+(1122928211/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1949335363/10000000000 : ℝ)*X 0 0+(163777731/312500000 : ℝ)*X 0 1+(54140443/100000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((662914371/1250000000 : ℝ)*X 1 0+(-1864465663/10000000000 : ℝ)*X 1 1+(216561771/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5303313887/10000000000 : ℝ)*X 2 0+(2707022559/5000000000 : ℝ)*X 2 1+(-1864465981/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4297389513/10000000000 : ℝ)*X 0 0+(4490205353/10000000000 : ℝ)*X 0 1+(822407531/2000000000 : ℝ)*X 0 2+(4297389513/10000000000 : ℝ)*X 1 0+(4490205353/10000000000 : ℝ)*X 1 1+(822407531/2000000000 : ℝ)*X 1 2+(4297389513/10000000000 : ℝ)*X 2 0+(4490205353/10000000000 : ℝ)*X 2 1+(822407531/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10431394045269508327613615997/1305250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1468953241/100000000000000 : ℝ)*(base19) + (783564611/50000000000000 : ℝ)*(base23) + (79262593/100000000000000 : ℝ)*(lower2) + (9153053/20000000000000 : ℝ)*(upper3) + (299352299/100000000000000 : ℝ)*(upper5) + (4176363254803777/100000000000000 : ℝ)*(major0) + (4176363254803777/100000000000000 : ℝ)*(major1) + (4176363254803777/100000000000000 : ℝ)*(major2) + (5729317104551917/100000000000000 : ℝ)*(sp0) + (5729347619322117/100000000000000 : ℝ)*(sp1) + (1145869504229227/20000000000000 : ℝ)*(sp2) + (1311681922409087/50000000000000 : ℝ)*(sp3) + (31983723441/100000000000000 : ℝ)*(sp4) + (66550591/500000000000 : ℝ)*(sp7) + (1311688577468187/50000000000000 : ℝ)*(f.failure) + (5729349088275357/100000000000000 : ℝ)*(f.sum) + (26129068043517/13052500000000000000000000000 : ℝ)*base66 + (255526089892483163/23000000000000000000000000000000 : ℝ)*base68 + (68674573467483163/23000000000000000000000000000000 : ℝ)*base70 + (165073735328483163/23000000000000000000000000000000 : ℝ)*base72 + (663136194917/13052500000000000000000000000 : ℝ)*base74 + (409066951497483163/23000000000000000000000000000000 : ℝ)*base76 + (272379281840483163/23000000000000000000000000000000 : ℝ)*base78 + (358753606876516837/23000000000000000000000000000000 : ℝ)*base79 + (57629043686273/13052500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (7615049/5000000000000000000000 : ℝ)*base90 + (7615049/5000000000000000000000 : ℝ)*base92 + (7615049/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19014622675758212822163417/10197265625000000000000000000000 : ℝ) := by norm_num
    linear_combination (149896391/50000000000000 : ℝ)*(base8) + (447520823/50000000000000 : ℝ)*(base21) + (59173061/50000000000000 : ℝ)*(base29) + (52534113/25000000000000 : ℝ)*(upper2) + (2104859570451323/50000000000000 : ℝ)*(major0) + (32888431712881/781250000000 : ℝ)*(major1) + (32888431712881/781250000000 : ℝ)*(major2) + (536438459/100000000000000 : ℝ)*(sp0) + (536523147/10000000000000 : ℝ)*(sp1) + (79953767/2000000000000 : ℝ)*(sp2) + (5775107934299091/100000000000000 : ℝ)*(sp4) + (5775103286952741/100000000000000 : ℝ)*(sp5) + (2887551879727107/50000000000000 : ℝ)*(sp6) + (2644329685811243/100000000000000 : ℝ)*(sp7) + (2644329685811243/100000000000000 : ℝ)*(f.failure) + (1443777192632583/25000000000000 : ℝ)*(f.sum) + (131288002663521/26105000000000000000000000000 : ℝ)*base66 + (615291875032093/89843750000000000000000000000 : ℝ)*base67 + (4522774324675247/359375000000000000000000000000 : ℝ)*base69 + (7431072086330591701/2610500000000000000000000000000000 : ℝ)*base71 + (2424121239/2216796875000000000000000 : ℝ)*base74 + (22151208286176653/40789062500000000000000000000000 : ℝ)*base76 + (27209803648404408299/2610500000000000000000000000000000 : ℝ)*base78 + (667177789752162319/81578125000000000000000000000000 : ℝ)*base79 + (2813087023493/1135000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (53789561/10000000000000000000000 : ℝ)*base90 + (53789561/10000000000000000000000 : ℝ)*base92 + (53789561/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1455_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159197973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15723/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5251/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11237/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7467/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1455_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1455_s4_0 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1950101307/10000000000 : ℝ)*x 0 + (1352004231/2500000000 : ℝ)*x 1 + (5246404099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1950101307/10000000000 : ℝ)^4415 ≤ (595170794197/5000000000000 : ℝ)^3391 := by
    have hnat : (1950101307 : ℕ)^4415*5000000000000^3391 ≤ 595170794197^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1950101307 10000000000 595170794197 5000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352004231/2500000000 : ℝ)^4415 ≤ (44918162950161/100000000000000 : ℝ)^3391 := by
    have hnat : (1352004231 : ℕ)^4415*100000000000000^3391 ≤ 44918162950161^3391*2500000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352004231 2500000000 44918162950161 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246404099/10000000000 : ℝ)^4415 ≤ (8635684228329/20000000000000 : ℝ)^3391 := by
    have hnat : (5246404099 : ℕ)^4415*20000000000000^3391 ≤ 8635684228329^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246404099 10000000000 8635684228329 20000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1950101307/10000000000 : ℝ), (1352004231/2500000000 : ℝ), (5246404099/10000000000 : ℝ)] ![(595170794197/5000000000000 : ℝ), (44918162950161/100000000000000 : ℝ), (8635684228329/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1950101307/10000000000 : ℝ)|^4415 ≤ (595170794197/5000000000000 : ℝ)^3391
        have hw : |(-1950101307/10000000000 : ℝ)|=(1950101307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352004231/2500000000 : ℝ)|^4415 ≤ (44918162950161/100000000000000 : ℝ)^3391
        have hw : |(1352004231/2500000000 : ℝ)|=(1352004231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246404099/10000000000 : ℝ)|^4415 ≤ (8635684228329/20000000000000 : ℝ)^3391
        have hw : |(5246404099/10000000000 : ℝ)|=(5246404099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s4_1 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673530967/5000000000 : ℝ)*x 0 + (-2032383251/10000000000 : ℝ)*x 1 + (5246404253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673530967/5000000000 : ℝ)^4415 ≤ (345782184957/781250000000 : ℝ)^3391 := by
    have hnat : (2673530967 : ℕ)^4415*781250000000^3391 ≤ 345782184957^3391*5000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673530967 5000000000 345782184957 781250000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2032383251/10000000000 : ℝ)^4415 ≤ (6280728762183/50000000000000 : ℝ)^3391 := by
    have hnat : (2032383251 : ℕ)^4415*50000000000000^3391 ≤ 6280728762183^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2032383251 10000000000 6280728762183 50000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246404253/10000000000 : ℝ)^4415 ≤ (8635684558363/20000000000000 : ℝ)^3391 := by
    have hnat : (5246404253 : ℕ)^4415*20000000000000^3391 ≤ 8635684558363^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246404253 10000000000 8635684558363 20000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673530967/5000000000 : ℝ), (-2032383251/10000000000 : ℝ), (5246404253/10000000000 : ℝ)] ![(345782184957/781250000000 : ℝ), (6280728762183/50000000000000 : ℝ), (8635684558363/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673530967/5000000000 : ℝ)|^4415 ≤ (345782184957/781250000000 : ℝ)^3391
        have hw : |(2673530967/5000000000 : ℝ)|=(2673530967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2032383251/10000000000 : ℝ)|^4415 ≤ (6280728762183/50000000000000 : ℝ)^3391
        have hw : |(-2032383251/10000000000 : ℝ)|=(2032383251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246404253/10000000000 : ℝ)|^4415 ≤ (8635684558363/20000000000000 : ℝ)^3391
        have hw : |(5246404253/10000000000 : ℝ)|=(5246404253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s4_2 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347061799/10000000000 : ℝ)*x 0 + (5246404411/10000000000 : ℝ)*x 1 + (-2032383221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347061799/10000000000 : ℝ)^4415 ≤ (44260118219593/100000000000000 : ℝ)^3391 := by
    have hnat : (5347061799 : ℕ)^4415*100000000000000^3391 ≤ 44260118219593^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347061799 10000000000 44260118219593 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246404411/10000000000 : ℝ)^4415 ≤ (21589212242423/50000000000000 : ℝ)^3391 := by
    have hnat : (5246404411 : ℕ)^4415*50000000000000^3391 ≤ 21589212242423^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246404411 10000000000 21589212242423 50000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2032383221/10000000000 : ℝ)^4415 ≤ (6280728641477/50000000000000 : ℝ)^3391 := by
    have hnat : (2032383221 : ℕ)^4415*50000000000000^3391 ≤ 6280728641477^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2032383221 10000000000 6280728641477 50000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347061799/10000000000 : ℝ), (5246404411/10000000000 : ℝ), (-2032383221/10000000000 : ℝ)] ![(44260118219593/100000000000000 : ℝ), (21589212242423/50000000000000 : ℝ), (6280728641477/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347061799/10000000000 : ℝ)|^4415 ≤ (44260118219593/100000000000000 : ℝ)^3391
        have hw : |(5347061799/10000000000 : ℝ)|=(5347061799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246404411/10000000000 : ℝ)|^4415 ≤ (21589212242423/50000000000000 : ℝ)^3391
        have hw : |(5246404411/10000000000 : ℝ)|=(5246404411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2032383221/10000000000 : ℝ)|^4415 ≤ (6280728641477/50000000000000 : ℝ)^3391
        have hw : |(-2032383221/10000000000 : ℝ)|=(2032383221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s4_3 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2148918487/5000000000 : ℝ)*x 0 + (412458189/1000000000 : ℝ)*x 1 + (1119384351/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2148918487/5000000000 : ℝ)^4415 ≤ (16652149142627/50000000000000 : ℝ)^3391 := by
    have hnat : (2148918487 : ℕ)^4415*50000000000000^3391 ≤ 16652149142627^3391*5000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148918487 5000000000 16652149142627 50000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (412458189/1000000000 : ℝ)^4415 ≤ (493235124669/1562500000000 : ℝ)^3391 := by
    have hnat : (412458189 : ℕ)^4415*1562500000000^3391 ≤ 493235124669^3391*1000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412458189 1000000000 493235124669 1562500000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1119384351/2500000000 : ℝ)^4415 ≤ (35128653724447/100000000000000 : ℝ)^3391 := by
    have hnat : (1119384351 : ℕ)^4415*100000000000000^3391 ≤ 35128653724447^3391*2500000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119384351 2500000000 35128653724447 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2148918487/5000000000 : ℝ), (412458189/1000000000 : ℝ), (1119384351/2500000000 : ℝ)] ![(16652149142627/50000000000000 : ℝ), (493235124669/1562500000000 : ℝ), (35128653724447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2148918487/5000000000 : ℝ)|^4415 ≤ (16652149142627/50000000000000 : ℝ)^3391
        have hw : |(2148918487/5000000000 : ℝ)|=(2148918487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(412458189/1000000000 : ℝ)|^4415 ≤ (493235124669/1562500000000 : ℝ)^3391
        have hw : |(412458189/1000000000 : ℝ)|=(412458189/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1119384351/2500000000 : ℝ)|^4415 ≤ (35128653724447/100000000000000 : ℝ)^3391
        have hw : |(1119384351/2500000000 : ℝ)|=(1119384351/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s4_4 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1950112977/10000000000 : ℝ)*x 0 + (2623498197/5000000000 : ℝ)*x 1 + (1351855359/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1950112977/10000000000 : ℝ)^4415 ≤ (11903508628533/100000000000000 : ℝ)^3391 := by
    have hnat : (1950112977 : ℕ)^4415*100000000000000^3391 ≤ 11903508628533^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1950112977 10000000000 11903508628533 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623498197/5000000000 : ℝ)^4415 ≤ (4318476792109/10000000000000 : ℝ)^3391 := by
    have hnat : (2623498197 : ℕ)^4415*10000000000000^3391 ≤ 4318476792109^3391*5000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623498197 5000000000 4318476792109 10000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351855359/2500000000 : ℝ)^4415 ≤ (22455861721311/50000000000000 : ℝ)^3391 := by
    have hnat : (1351855359 : ℕ)^4415*50000000000000^3391 ≤ 22455861721311^3391*2500000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351855359 2500000000 22455861721311 50000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1950112977/10000000000 : ℝ), (2623498197/5000000000 : ℝ), (1351855359/2500000000 : ℝ)] ![(11903508628533/100000000000000 : ℝ), (4318476792109/10000000000000 : ℝ), (22455861721311/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1950112977/10000000000 : ℝ)|^4415 ≤ (11903508628533/100000000000000 : ℝ)^3391
        have hw : |(-1950112977/10000000000 : ℝ)|=(1950112977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623498197/5000000000 : ℝ)|^4415 ≤ (4318476792109/10000000000000 : ℝ)^3391
        have hw : |(2623498197/5000000000 : ℝ)|=(2623498197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351855359/2500000000 : ℝ)|^4415 ≤ (22455861721311/50000000000000 : ℝ)^3391
        have hw : |(1351855359/2500000000 : ℝ)|=(1351855359/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s4_5 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5304942701/10000000000 : ℝ)*x 0 + (-233920759/1250000000 : ℝ)*x 1 + (5407421427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304942701/10000000000 : ℝ)^4415 ≤ (43806739048609/100000000000000 : ℝ)^3391 := by
    have hnat : (5304942701 : ℕ)^4415*100000000000000^3391 ≤ 43806739048609^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304942701 10000000000 43806739048609 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (233920759/1250000000 : ℝ)^4415 ≤ (11281537588897/100000000000000 : ℝ)^3391 := by
    have hnat : (233920759 : ℕ)^4415*100000000000000^3391 ≤ 11281537588897^3391*1250000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      233920759 1250000000 11281537588897 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407421427/10000000000 : ℝ)^4415 ≤ (44911723345299/100000000000000 : ℝ)^3391 := by
    have hnat : (5407421427 : ℕ)^4415*100000000000000^3391 ≤ 44911723345299^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407421427 10000000000 44911723345299 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304942701/10000000000 : ℝ), (-233920759/1250000000 : ℝ), (5407421427/10000000000 : ℝ)] ![(43806739048609/100000000000000 : ℝ), (11281537588897/100000000000000 : ℝ), (44911723345299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304942701/10000000000 : ℝ)|^4415 ≤ (43806739048609/100000000000000 : ℝ)^3391
        have hw : |(5304942701/10000000000 : ℝ)|=(5304942701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-233920759/1250000000 : ℝ)|^4415 ≤ (11281537588897/100000000000000 : ℝ)^3391
        have hw : |(-233920759/1250000000 : ℝ)|=(233920759/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407421427/10000000000 : ℝ)|^4415 ≤ (44911723345299/100000000000000 : ℝ)^3391
        have hw : |(5407421427/10000000000 : ℝ)|=(5407421427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s4_6 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (663117843/1250000000 : ℝ)*x 0 + (5407421401/10000000000 : ℝ)*x 1 + (-1871366049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663117843/1250000000 : ℝ)^4415 ≤ (43806739510917/100000000000000 : ℝ)^3391 := by
    have hnat : (663117843 : ℕ)^4415*100000000000000^3391 ≤ 43806739510917^3391*1250000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663117843 1250000000 43806739510917 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407421401/10000000000 : ℝ)^4415 ≤ (2806982691509/6250000000000 : ℝ)^3391 := by
    have hnat : (5407421401 : ℕ)^4415*6250000000000^3391 ≤ 2806982691509^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407421401 10000000000 2806982691509 6250000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1871366049/10000000000 : ℝ)^4415 ≤ (11281537408371/100000000000000 : ℝ)^3391 := by
    have hnat : (1871366049 : ℕ)^4415*100000000000000^3391 ≤ 11281537408371^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1871366049 10000000000 11281537408371 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663117843/1250000000 : ℝ), (5407421401/10000000000 : ℝ), (-1871366049/10000000000 : ℝ)] ![(43806739510917/100000000000000 : ℝ), (2806982691509/6250000000000 : ℝ), (11281537408371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663117843/1250000000 : ℝ)|^4415 ≤ (43806739510917/100000000000000 : ℝ)^3391
        have hw : |(663117843/1250000000 : ℝ)|=(663117843/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407421401/10000000000 : ℝ)|^4415 ≤ (2806982691509/6250000000000 : ℝ)^3391
        have hw : |(5407421401/10000000000 : ℝ)|=(5407421401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1871366049/10000000000 : ℝ)|^4415 ≤ (11281537408371/100000000000000 : ℝ)^3391
        have hw : |(-1871366049/10000000000 : ℝ)|=(1871366049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s4_7 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2148931151/5000000000 : ℝ)*x 0 + (179049753/400000000 : ℝ)*x 1 + (4125882179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2148931151/5000000000 : ℝ)^4415 ≤ (16652276911351/50000000000000 : ℝ)^3391 := by
    have hnat : (2148931151 : ℕ)^4415*50000000000000^3391 ≤ 16652276911351^3391*5000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148931151 5000000000 16652276911351 50000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (179049753/400000000 : ℝ)^4415 ≤ (35115440792069/100000000000000 : ℝ)^3391 := by
    have hnat : (179049753 : ℕ)^4415*100000000000000^3391 ≤ 35115440792069^3391*400000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179049753 400000000 35115440792069 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4125882179/10000000000 : ℝ)^4415 ≤ (31580005368399/100000000000000 : ℝ)^3391 := by
    have hnat : (4125882179 : ℕ)^4415*100000000000000^3391 ≤ 31580005368399^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4125882179 10000000000 31580005368399 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2148931151/5000000000 : ℝ), (179049753/400000000 : ℝ), (4125882179/10000000000 : ℝ)] ![(16652276911351/50000000000000 : ℝ), (35115440792069/100000000000000 : ℝ), (31580005368399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2148931151/5000000000 : ℝ)|^4415 ≤ (16652276911351/50000000000000 : ℝ)^3391
        have hw : |(2148931151/5000000000 : ℝ)|=(2148931151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(179049753/400000000 : ℝ)|^4415 ≤ (35115440792069/100000000000000 : ℝ)^3391
        have hw : |(179049753/400000000 : ℝ)|=(179049753/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4125882179/10000000000 : ℝ)|^4415 ≤ (31580005368399/100000000000000 : ℝ)^3391
        have hw : |(4125882179/10000000000 : ℝ)|=(4125882179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1455_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159197973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7467/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11237/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1137/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7397/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7467/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11237/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7467/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11237/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7467/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11237/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7467/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11237/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7467/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11237/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7467/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11237/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11237/100000 : ℝ) ^ (2207/512 : ℝ) ≤ (505433453252571/6250000000000000000 : ℝ) := by
    have hpowers : (11237/100000 : ℝ)^2207 ≤ (505433453252571/6250000000000000000 : ℝ)^512 := by
      have hnat : (11237 : ℕ)^2207*6250000000000000000^512 ≤ 505433453252571^512*100000^2207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11237 100000 505433453252571 6250000000000000000 2207 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11237/100000 : ℝ)) (X := (505433453252571/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 2207 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7467/50000 : ℝ) ^ (2207/512 : ℝ) ≤ (137789960440911/500000000000000000 : ℝ) := by
    have hpowers : (7467/50000 : ℝ)^2207 ≤ (137789960440911/500000000000000000 : ℝ)^512 := by
      have hnat : (7467 : ℕ)^2207*500000000000000000^512 ≤ 137789960440911^512*50000^2207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7467 50000 137789960440911 500000000000000000 2207 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7467/50000 : ℝ)) (X := (137789960440911/500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2207 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125505433453252571/3125000000000000000 : ℝ) ≤ (400015007716221/400000000000000 : ℝ) ^ (2207/512 : ℝ) := by
    have hpowers : (3125505433453252571/3125000000000000000 : ℝ)^512 ≤ (400015007716221/400000000000000 : ℝ)^2207 := by
      have hnat : (3125505433453252571 : ℕ)^512*400000000000000^2207 ≤ 400015007716221^2207*3125000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125505433453252571 3125000000000000000 400015007716221 400000000000000 512 2207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400015007716221/400000000000000 : ℝ)) (X := (3125505433453252571/3125000000000000000 : ℝ)) (by norm_num) 2207 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (12504455615917527917/12500000000000000000 : ℝ) ≤ (5000413405194001/5000000000000000 : ℝ) ^ (2207/512 : ℝ) := by
    have hpowers : (12504455615917527917/12500000000000000000 : ℝ)^512 ≤ (5000413405194001/5000000000000000 : ℝ)^2207 := by
      have hnat : (12504455615917527917 : ℕ)^512*5000000000000000^2207 ≤ 5000413405194001^2207*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12504455615917527917 12500000000000000000 5000413405194001 5000000000000000 512 2207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000413405194001/5000000000000000 : ℝ)) (X := (12504455615917527917/12500000000000000000 : ℝ)) (by norm_num) 2207 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (250137789960440911/250000000000000000 : ℝ) ≤ (10001278427870479/10000000000000000 : ℝ) ^ (2207/512 : ℝ) := by
    have hpowers : (250137789960440911/250000000000000000 : ℝ)^512 ≤ (10001278427870479/10000000000000000 : ℝ)^2207 := by
      have hnat : (250137789960440911 : ℕ)^512*10000000000000000^2207 ≤ 10001278427870479^2207*250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        250137789960440911 250000000000000000 10001278427870479 10000000000000000 512 2207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001278427870479/10000000000000000 : ℝ)) (X := (250137789960440911/250000000000000000 : ℝ)) (by norm_num) 2207 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(505433453252571/6250000000000000000 : ℝ) ≤ ((36961237436870537827/36970000000000000000 : ℝ)+2*(451617482477/369700000000000 : ℝ)*(11237/100000 : ℝ))^(2207/512 : ℝ) := by
    rw [show (36961237436870537827/36970000000000000000 : ℝ)+2*(451617482477/369700000000000 : ℝ)*(11237/100000 : ℝ)=(400015007716221/400000000000000 : ℝ) by norm_num, show 1+2*(505433453252571/6250000000000000000 : ℝ)=(3125505433453252571/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(137789960440911/500000000000000000 : ℝ)+(505433453252571/6250000000000000000 : ℝ) ≤ ((36961237436870537827/36970000000000000000 : ℝ)+(451617482477/369700000000000 : ℝ)*((7467/50000 : ℝ)+(11237/100000 : ℝ)))^(2207/512 : ℝ) := by
    rw [show (36961237436870537827/36970000000000000000 : ℝ)+(451617482477/369700000000000 : ℝ)*((7467/50000 : ℝ)+(11237/100000 : ℝ))=(5000413405194001/5000000000000000 : ℝ) by norm_num, show 1+(137789960440911/500000000000000000 : ℝ)+(505433453252571/6250000000000000000 : ℝ)=(12504455615917527917/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(137789960440911/500000000000000000 : ℝ) ≤ ((36961237436870537827/36970000000000000000 : ℝ)+2*(451617482477/369700000000000 : ℝ)*(7467/50000 : ℝ))^(2207/512 : ℝ) := by
    rw [show (36961237436870537827/36970000000000000000 : ℝ)+2*(451617482477/369700000000000 : ℝ)*(7467/50000 : ℝ)=(10001278427870479/10000000000000000 : ℝ) by norm_num, show 1+2*(137789960440911/500000000000000000 : ℝ)=(250137789960440911/250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (36961237436870537827/36970000000000000000 : ℝ)*(X 1 0+X 2 0)+(451617482477/369700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2207/512 : ℝ)) (lo := (11237/100000 : ℝ)) (hi := (7467/50000 : ℝ)) (c := (36961237436870537827/36970000000000000000 : ℝ)) (alpha := (451617482477/369700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (36961237436870537827/36970000000000000000 : ℝ)*(X 0 1+X 2 1)+(451617482477/369700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2207/512 : ℝ)) (lo := (11237/100000 : ℝ)) (hi := (7467/50000 : ℝ)) (c := (36961237436870537827/36970000000000000000 : ℝ)) (alpha := (451617482477/369700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (36961237436870537827/36970000000000000000 : ℝ)*(X 0 2+X 1 2)+(451617482477/369700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2207/512 : ℝ)) (lo := (11237/100000 : ℝ)) (hi := (7467/50000 : ℝ)) (c := (36961237436870537827/36970000000000000000 : ℝ)) (alpha := (451617482477/369700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1950101307/10000000000 : ℝ)*X 0 0+(1352004231/2500000000 : ℝ)*X 0 1+(5246404099/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673530967/5000000000 : ℝ)*X 1 0+(-2032383251/10000000000 : ℝ)*X 1 1+(5246404253/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347061799/10000000000 : ℝ)*X 2 0+(5246404411/10000000000 : ℝ)*X 2 1+(-2032383221/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2148918487/5000000000 : ℝ)*X 0 0+(412458189/1000000000 : ℝ)*X 0 1+(1119384351/2500000000 : ℝ)*X 0 2+(2148918487/5000000000 : ℝ)*X 1 0+(412458189/1000000000 : ℝ)*X 1 1+(1119384351/2500000000 : ℝ)*X 1 2+(2148918487/5000000000 : ℝ)*X 2 0+(412458189/1000000000 : ℝ)*X 2 1+(1119384351/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1950112977/10000000000 : ℝ)*X 0 0+(2623498197/5000000000 : ℝ)*X 0 1+(1351855359/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5304942701/10000000000 : ℝ)*X 1 0+(-233920759/1250000000 : ℝ)*X 1 1+(5407421427/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((663117843/1250000000 : ℝ)*X 2 0+(5407421401/10000000000 : ℝ)*X 2 1+(-1871366049/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2148931151/5000000000 : ℝ)*X 0 0+(179049753/400000000 : ℝ)*X 0 1+(4125882179/10000000000 : ℝ)*X 0 2+(2148931151/5000000000 : ℝ)*X 1 0+(179049753/400000000 : ℝ)*X 1 1+(4125882179/10000000000 : ℝ)*X 1 2+(2148931151/5000000000 : ℝ)*X 2 0+(179049753/400000000 : ℝ)*X 2 1+(4125882179/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8869057357883255321628323049/1848500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (129852213/25000000000000 : ℝ)*(base19) + (218596843/100000000000000 : ℝ)*(base23) + (85425931/100000000000000 : ℝ)*(lower2) + (93003957/100000000000000 : ℝ)*(upper3) + (4056657/50000000000000 : ℝ)*(lower4) + (4510446362664129/100000000000000 : ℝ)*(major0) + (4510446362664129/100000000000000 : ℝ)*(major1) + (4510446362664129/100000000000000 : ℝ)*(major2) + (6187646064011159/100000000000000 : ℝ)*(sp0) + (386728813793739/6250000000000 : ℝ)*(sp1) + (6187661321511833/100000000000000 : ℝ)*(sp2) + (113328955671363/4000000000000 : ℝ)*(sp3) + (15476097517/100000000000000 : ℝ)*(sp4) + (7133502993/100000000000000 : ℝ)*(sp7) + (708307756321767/25000000000000 : ℝ)*(f.failure) + (1546915385027169/25000000000000 : ℝ)*(f.sum) + (17986626648743/18485000000000000000000000000 : ℝ)*base65 + (24602305117989192317/3697000000000000000000000000000000 : ℝ)*base68 + (13183106640143807683/3697000000000000000000000000000000 : ℝ)*base69 + (3120442841200192317/3697000000000000000000000000000000 : ℝ)*base72 + (17290749746851/9242500000000000000000000000 : ℝ)*base74 + (15130132431199192317/3697000000000000000000000000000000 : ℝ)*base76 + (18285675343952807683/3697000000000000000000000000000000 : ℝ)*base77 + (23684291029042192317/3697000000000000000000000000000000 : ℝ)*base80 + (17008305447157/18485000000000000000000000000 : ℝ)*base82 + (17178291/2500000000000000000000 : ℝ)*base89 + (17178291/2500000000000000000000 : ℝ)*base91 + (17178291/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22927215516174140920569/2310625000000000000000000000 : ℝ) := by norm_num
    linear_combination (1565390063/100000000000000 : ℝ)*(base19) + (4491089/250000000000 : ℝ)*(base23) + (178730281/100000000000000 : ℝ)*(upper3) + (81985629/100000000000000 : ℝ)*(lower4) + (217416677/100000000000000 : ℝ)*(upper5) + (4543816968104277/100000000000000 : ℝ)*(major0) + (4543816968104277/100000000000000 : ℝ)*(major1) + (4543816968104277/100000000000000 : ℝ)*(major2) + (3320001819/10000000000000 : ℝ)*(sp1) + (18235789901/50000000000000 : ℝ)*(sp2) + (6233440877699899/100000000000000 : ℝ)*(sp4) + (1246681222458329/20000000000000 : ℝ)*(sp5) + (6233402609684497/100000000000000 : ℝ)*(sp6) + (2854192727758083/100000000000000 : ℝ)*(sp7) + (2854192727758083/100000000000000 : ℝ)*(f.failure) + (6233440877699899/100000000000000 : ℝ)*(f.sum) + (12112623987387/9242500000000000000000000000 : ℝ)*base65 + (3526059541635113921/3697000000000000000000000000000000 : ℝ)*base68 + (793196798784886079/3697000000000000000000000000000000 : ℝ)*base69 + (49194092139334886079/3697000000000000000000000000000000 : ℝ)*base71 + (18432549469549/4621250000000000000000000000 : ℝ)*base74 + (101677655484647886079/3697000000000000000000000000000000 : ℝ)*base75 + (4637965383482113921/3697000000000000000000000000000000 : ℝ)*base78 + (52399891991596113921/3697000000000000000000000000000000 : ℝ)*base80 + (32859399218941/18485000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (52034241/10000000000000000000000 : ℝ)*base90 + (52034241/10000000000000000000000 : ℝ)*base92 + (52034241/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1455_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159197973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7467/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11237/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1137/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7397/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1455_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1455_s5_0 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-390042177/2000000000 : ℝ)*x 0 + (2703511317/5000000000 : ℝ)*x 1 + (2623663109/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (390042177/2000000000 : ℝ)^4415 ≤ (2380857347209/20000000000000 : ℝ)^3391 := by
    have hnat : (390042177 : ℕ)^4415*20000000000000^3391 ≤ 2380857347209^3391*2000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      390042177 2000000000 2380857347209 20000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703511317/5000000000 : ℝ)^4415 ≤ (22453705492143/50000000000000 : ℝ)^3391 := by
    have hnat : (2703511317 : ℕ)^4415*50000000000000^3391 ≤ 22453705492143^3391*5000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703511317 5000000000 22453705492143 50000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623663109/5000000000 : ℝ)^4415 ≤ (43188302267541/100000000000000 : ℝ)^3391 := by
    have hnat : (2623663109 : ℕ)^4415*100000000000000^3391 ≤ 43188302267541^3391*5000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623663109 5000000000 43188302267541 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-390042177/2000000000 : ℝ), (2703511317/5000000000 : ℝ), (2623663109/5000000000 : ℝ)] ![(2380857347209/20000000000000 : ℝ), (22453705492143/50000000000000 : ℝ), (43188302267541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-390042177/2000000000 : ℝ)|^4415 ≤ (2380857347209/20000000000000 : ℝ)^3391
        have hw : |(-390042177/2000000000 : ℝ)|=(390042177/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703511317/5000000000 : ℝ)|^4415 ≤ (22453705492143/50000000000000 : ℝ)^3391
        have hw : |(2703511317/5000000000 : ℝ)|=(2703511317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623663109/5000000000 : ℝ)|^4415 ≤ (43188302267541/100000000000000 : ℝ)^3391
        have hw : |(2623663109/5000000000 : ℝ)|=(2623663109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s5_1 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069360951/2000000000 : ℝ)*x 0 + (-2031499907/10000000000 : ℝ)*x 1 + (2623663109/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069360951/2000000000 : ℝ)^4415 ≤ (8851469612239/20000000000000 : ℝ)^3391 := by
    have hnat : (1069360951 : ℕ)^4415*20000000000000^3391 ≤ 8851469612239^3391*2000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069360951 2000000000 8851469612239 20000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2031499907/10000000000 : ℝ)^4415 ≤ (12554349666997/100000000000000 : ℝ)^3391 := by
    have hnat : (2031499907 : ℕ)^4415*100000000000000^3391 ≤ 12554349666997^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2031499907 10000000000 12554349666997 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623663109/5000000000 : ℝ)^4415 ≤ (43188302267541/100000000000000 : ℝ)^3391 := by
    have hnat : (2623663109 : ℕ)^4415*100000000000000^3391 ≤ 43188302267541^3391*5000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623663109 5000000000 43188302267541 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069360951/2000000000 : ℝ), (-2031499907/10000000000 : ℝ), (2623663109/5000000000 : ℝ)] ![(8851469612239/20000000000000 : ℝ), (12554349666997/100000000000000 : ℝ), (43188302267541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069360951/2000000000 : ℝ)|^4415 ≤ (8851469612239/20000000000000 : ℝ)^3391
        have hw : |(1069360951/2000000000 : ℝ)|=(1069360951/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2031499907/10000000000 : ℝ)|^4415 ≤ (12554349666997/100000000000000 : ℝ)^3391
        have hw : |(-2031499907/10000000000 : ℝ)|=(2031499907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623663109/5000000000 : ℝ)|^4415 ≤ (43188302267541/100000000000000 : ℝ)^3391
        have hw : |(2623663109/5000000000 : ℝ)|=(2623663109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s5_2 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069360951/2000000000 : ℝ)*x 0 + (2623663109/5000000000 : ℝ)*x 1 + (-2031499907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069360951/2000000000 : ℝ)^4415 ≤ (8851469612239/20000000000000 : ℝ)^3391 := by
    have hnat : (1069360951 : ℕ)^4415*20000000000000^3391 ≤ 8851469612239^3391*2000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069360951 2000000000 8851469612239 20000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623663109/5000000000 : ℝ)^4415 ≤ (43188302267541/100000000000000 : ℝ)^3391 := by
    have hnat : (2623663109 : ℕ)^4415*100000000000000^3391 ≤ 43188302267541^3391*5000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623663109 5000000000 43188302267541 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2031499907/10000000000 : ℝ)^4415 ≤ (12554349666997/100000000000000 : ℝ)^3391 := by
    have hnat : (2031499907 : ℕ)^4415*100000000000000^3391 ≤ 12554349666997^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2031499907 10000000000 12554349666997 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069360951/2000000000 : ℝ), (2623663109/5000000000 : ℝ), (-2031499907/10000000000 : ℝ)] ![(8851469612239/20000000000000 : ℝ), (43188302267541/100000000000000 : ℝ), (12554349666997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069360951/2000000000 : ℝ)|^4415 ≤ (8851469612239/20000000000000 : ℝ)^3391
        have hw : |(1069360951/2000000000 : ℝ)|=(1069360951/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623663109/5000000000 : ℝ)|^4415 ≤ (43188302267541/100000000000000 : ℝ)^3391
        have hw : |(2623663109/5000000000 : ℝ)|=(2623663109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2031499907/10000000000 : ℝ)|^4415 ≤ (12554349666997/100000000000000 : ℝ)^3391
        have hw : |(-2031499907/10000000000 : ℝ)|=(2031499907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s5_3 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4297904829/10000000000 : ℝ)*x 0 + (2063333129/5000000000 : ℝ)*x 1 + (4475436757/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4297904829/10000000000 : ℝ)^4415 ≤ (33304982884093/100000000000000 : ℝ)^3391 := by
    have hnat : (4297904829 : ℕ)^4415*100000000000000^3391 ≤ 33304982884093^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4297904829 10000000000 33304982884093 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2063333129/5000000000 : ℝ)^4415 ≤ (7896954829379/25000000000000 : ℝ)^3391 := by
    have hnat : (2063333129 : ℕ)^4415*25000000000000^3391 ≤ 7896954829379^3391*5000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063333129 5000000000 7896954829379 25000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4475436757/10000000000 : ℝ)^4415 ≤ (1097099930817/3125000000000 : ℝ)^3391 := by
    have hnat : (4475436757 : ℕ)^4415*3125000000000^3391 ≤ 1097099930817^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4475436757 10000000000 1097099930817 3125000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4297904829/10000000000 : ℝ), (2063333129/5000000000 : ℝ), (4475436757/10000000000 : ℝ)] ![(33304982884093/100000000000000 : ℝ), (7896954829379/25000000000000 : ℝ), (1097099930817/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4297904829/10000000000 : ℝ)|^4415 ≤ (33304982884093/100000000000000 : ℝ)^3391
        have hw : |(4297904829/10000000000 : ℝ)|=(4297904829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2063333129/5000000000 : ℝ)|^4415 ≤ (7896954829379/25000000000000 : ℝ)^3391
        have hw : |(2063333129/5000000000 : ℝ)|=(2063333129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4475436757/10000000000 : ℝ)|^4415 ≤ (1097099930817/3125000000000 : ℝ)^3391
        have hw : |(4475436757/10000000000 : ℝ)|=(4475436757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s5_4 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-487555509/2500000000 : ℝ)*x 0 + (2623952269/5000000000 : ℝ)*x 1 + (5406441311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (487555509/2500000000 : ℝ)^4415 ≤ (2976093839377/25000000000000 : ℝ)^3391 := by
    have hnat : (487555509 : ℕ)^4415*25000000000000^3391 ≤ 2976093839377^3391*2500000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      487555509 2500000000 2976093839377 25000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623952269/5000000000 : ℝ)^4415 ≤ (5399312452907/12500000000000 : ℝ)^3391 := by
    have hnat : (2623952269 : ℕ)^4415*12500000000000^3391 ≤ 5399312452907^3391*5000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623952269 5000000000 5399312452907 12500000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406441311/10000000000 : ℝ)^4415 ≤ (5612640625157/12500000000000 : ℝ)^3391 := by
    have hnat : (5406441311 : ℕ)^4415*12500000000000^3391 ≤ 5612640625157^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406441311 10000000000 5612640625157 12500000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-487555509/2500000000 : ℝ), (2623952269/5000000000 : ℝ), (5406441311/10000000000 : ℝ)] ![(2976093839377/25000000000000 : ℝ), (5399312452907/12500000000000 : ℝ), (5612640625157/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-487555509/2500000000 : ℝ)|^4415 ≤ (2976093839377/25000000000000 : ℝ)^3391
        have hw : |(-487555509/2500000000 : ℝ)|=(487555509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623952269/5000000000 : ℝ)|^4415 ≤ (5399312452907/12500000000000 : ℝ)^3391
        have hw : |(2623952269/5000000000 : ℝ)|=(2623952269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406441311/10000000000 : ℝ)|^4415 ≤ (5612640625157/12500000000000 : ℝ)^3391
        have hw : |(5406441311/10000000000 : ℝ)|=(5406441311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s5_5 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305184681/10000000000 : ℝ)*x 0 + (-1872384813/10000000000 : ℝ)*x 1 + (540644131/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305184681/10000000000 : ℝ)^4415 ≤ (10952335169769/25000000000000 : ℝ)^3391 := by
    have hnat : (5305184681 : ℕ)^4415*25000000000000^3391 ≤ 10952335169769^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305184681 10000000000 10952335169769 25000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1872384813/10000000000 : ℝ)^4415 ≤ (11289534309777/100000000000000 : ℝ)^3391 := by
    have hnat : (1872384813 : ℕ)^4415*100000000000000^3391 ≤ 11289534309777^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1872384813 10000000000 11289534309777 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540644131/1000000000 : ℝ)^4415 ≤ (44901124990443/100000000000000 : ℝ)^3391 := by
    have hnat : (540644131 : ℕ)^4415*100000000000000^3391 ≤ 44901124990443^3391*1000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540644131 1000000000 44901124990443 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305184681/10000000000 : ℝ), (-1872384813/10000000000 : ℝ), (540644131/1000000000 : ℝ)] ![(10952335169769/25000000000000 : ℝ), (11289534309777/100000000000000 : ℝ), (44901124990443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305184681/10000000000 : ℝ)|^4415 ≤ (10952335169769/25000000000000 : ℝ)^3391
        have hw : |(5305184681/10000000000 : ℝ)|=(5305184681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1872384813/10000000000 : ℝ)|^4415 ≤ (11289534309777/100000000000000 : ℝ)^3391
        have hw : |(-1872384813/10000000000 : ℝ)|=(1872384813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(540644131/1000000000 : ℝ)|^4415 ≤ (44901124990443/100000000000000 : ℝ)^3391
        have hw : |(540644131/1000000000 : ℝ)|=(540644131/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s5_6 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326296171/2500000000 : ℝ)*x 0 + (5406441309/10000000000 : ℝ)*x 1 + (-468096203/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326296171/2500000000 : ℝ)^4415 ≤ (4380934071133/10000000000000 : ℝ)^3391 := by
    have hnat : (1326296171 : ℕ)^4415*10000000000000^3391 ≤ 4380934071133^3391*2500000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326296171 2500000000 4380934071133 10000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406441309/10000000000 : ℝ)^4415 ≤ (4490112497963/10000000000000 : ℝ)^3391 := by
    have hnat : (5406441309 : ℕ)^4415*10000000000000^3391 ≤ 4490112497963^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406441309 10000000000 4490112497963 10000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (468096203/2500000000 : ℝ)^4415 ≤ (5644767150963/50000000000000 : ℝ)^3391 := by
    have hnat : (468096203 : ℕ)^4415*50000000000000^3391 ≤ 5644767150963^3391*2500000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      468096203 2500000000 5644767150963 50000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326296171/2500000000 : ℝ), (5406441309/10000000000 : ℝ), (-468096203/2500000000 : ℝ)] ![(4380934071133/10000000000000 : ℝ), (4490112497963/10000000000000 : ℝ), (5644767150963/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326296171/2500000000 : ℝ)|^4415 ≤ (4380934071133/10000000000000 : ℝ)^3391
        have hw : |(1326296171/2500000000 : ℝ)|=(1326296171/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406441309/10000000000 : ℝ)|^4415 ≤ (4490112497963/10000000000000 : ℝ)^3391
        have hw : |(5406441309/10000000000 : ℝ)|=(5406441309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-468096203/2500000000 : ℝ)|^4415 ≤ (5644767150963/50000000000000 : ℝ)^3391
        have hw : |(-468096203/2500000000 : ℝ)|=(468096203/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s5_7 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (859585837/2000000000 : ℝ)*x 0 + (4474173727/10000000000 : ℝ)*x 1 + (4127935843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (859585837/2000000000 : ℝ)^4415 ≤ (33305228616071/100000000000000 : ℝ)^3391 := by
    have hnat : (859585837 : ℕ)^4415*100000000000000^3391 ≤ 33305228616071^3391*2000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      859585837 2000000000 33305228616071 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4474173727/10000000000 : ℝ)^4415 ≤ (35094298703697/100000000000000 : ℝ)^3391 := by
    have hnat : (4474173727 : ℕ)^4415*100000000000000^3391 ≤ 35094298703697^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4474173727 10000000000 35094298703697 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4127935843/10000000000 : ℝ)^4415 ≤ (15800236328657/50000000000000 : ℝ)^3391 := by
    have hnat : (4127935843 : ℕ)^4415*50000000000000^3391 ≤ 15800236328657^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4127935843 10000000000 15800236328657 50000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(859585837/2000000000 : ℝ), (4474173727/10000000000 : ℝ), (4127935843/10000000000 : ℝ)] ![(33305228616071/100000000000000 : ℝ), (35094298703697/100000000000000 : ℝ), (15800236328657/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(859585837/2000000000 : ℝ)|^4415 ≤ (33305228616071/100000000000000 : ℝ)^3391
        have hw : |(859585837/2000000000 : ℝ)|=(859585837/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4474173727/10000000000 : ℝ)|^4415 ≤ (35094298703697/100000000000000 : ℝ)^3391
        have hw : |(4474173727/10000000000 : ℝ)|=(4474173727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4127935843/10000000000 : ℝ)|^4415 ≤ (15800236328657/50000000000000 : ℝ)^3391
        have hw : |(4127935843/10000000000 : ℝ)|=(4127935843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1455_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159197973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7397/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1137/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (11389/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14773/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7397/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1137/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7397/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1137/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7397/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1137/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7397/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1137/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7397/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1137/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7397/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1137/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1137/10000 : ℝ) ^ (2207/512 : ℝ) ≤ (8507681477471457/100000000000000000000 : ℝ) := by
    have hpowers : (1137/10000 : ℝ)^2207 ≤ (8507681477471457/100000000000000000000 : ℝ)^512 := by
      have hnat : (1137 : ℕ)^2207*100000000000000000000^512 ≤ 8507681477471457^512*10000^2207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1137 10000 8507681477471457 100000000000000000000 2207 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1137/10000 : ℝ)) (X := (8507681477471457/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2207 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7397/50000 : ℝ) ^ (2207/512 : ℝ) ≤ (103365396092741/390625000000000000 : ℝ) := by
    have hpowers : (7397/50000 : ℝ)^2207 ≤ (103365396092741/390625000000000000 : ℝ)^512 := by
      have hnat : (7397 : ℕ)^2207*390625000000000000^512 ≤ 103365396092741^512*50000^2207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7397 50000 103365396092741 390625000000000000 2207 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7397/50000 : ℝ)) (X := (103365396092741/390625000000000000 : ℝ)) (by norm_num) (by norm_num) 2207 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008507681477471457/50000000000000000000 : ℝ) ≤ (5000197356063829/5000000000000000 : ℝ) ^ (2207/512 : ℝ) := by
    have hpowers : (50008507681477471457/50000000000000000000 : ℝ)^512 ≤ (5000197356063829/5000000000000000 : ℝ)^2207 := by
      have hnat : (50008507681477471457 : ℕ)^512*5000000000000000^2207 ≤ 5000197356063829^2207*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008507681477471457 50000000000000000000 5000197356063829 5000000000000000 512 2207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000197356063829/5000000000000000 : ℝ)) (X := (50008507681477471457/50000000000000000000 : ℝ)) (by norm_num) 2207 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100034969222877213153/100000000000000000000 : ℝ) ≤ (125010139237857/125000000000000 : ℝ) ^ (2207/512 : ℝ) := by
    have hpowers : (100034969222877213153/100000000000000000000 : ℝ)^512 ≤ (125010139237857/125000000000000 : ℝ)^2207 := by
      have hnat : (100034969222877213153 : ℕ)^512*125000000000000^2207 ≤ 125010139237857^2207*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100034969222877213153 100000000000000000000 125010139237857 125000000000000 512 2207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125010139237857/125000000000000 : ℝ)) (X := (100034969222877213153/100000000000000000000 : ℝ)) (by norm_num) 2207 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (195415865396092741/195312500000000000 : ℝ) ≤ (5000613782964731/5000000000000000 : ℝ) ^ (2207/512 : ℝ) := by
    have hpowers : (195415865396092741/195312500000000000 : ℝ)^512 ≤ (5000613782964731/5000000000000000 : ℝ)^2207 := by
      have hnat : (195415865396092741 : ℕ)^512*5000000000000000^2207 ≤ 5000613782964731^2207*195312500000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        195415865396092741 195312500000000000 5000613782964731 5000000000000000 512 2207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000613782964731/5000000000000000 : ℝ)) (X := (195415865396092741/195312500000000000 : ℝ)) (by norm_num) 2207 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8507681477471457/100000000000000000000 : ℝ) ≤ ((4278985243324823689/4280000000000000000 : ℝ)+2*(208213450451/171200000000000 : ℝ)*(1137/10000 : ℝ))^(2207/512 : ℝ) := by
    rw [show (4278985243324823689/4280000000000000000 : ℝ)+2*(208213450451/171200000000000 : ℝ)*(1137/10000 : ℝ)=(5000197356063829/5000000000000000 : ℝ) by norm_num, show 1+2*(8507681477471457/100000000000000000000 : ℝ)=(50008507681477471457/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(103365396092741/390625000000000000 : ℝ)+(8507681477471457/100000000000000000000 : ℝ) ≤ ((4278985243324823689/4280000000000000000 : ℝ)+(208213450451/171200000000000 : ℝ)*((7397/50000 : ℝ)+(1137/10000 : ℝ)))^(2207/512 : ℝ) := by
    rw [show (4278985243324823689/4280000000000000000 : ℝ)+(208213450451/171200000000000 : ℝ)*((7397/50000 : ℝ)+(1137/10000 : ℝ))=(125010139237857/125000000000000 : ℝ) by norm_num, show 1+(103365396092741/390625000000000000 : ℝ)+(8507681477471457/100000000000000000000 : ℝ)=(100034969222877213153/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(103365396092741/390625000000000000 : ℝ) ≤ ((4278985243324823689/4280000000000000000 : ℝ)+2*(208213450451/171200000000000 : ℝ)*(7397/50000 : ℝ))^(2207/512 : ℝ) := by
    rw [show (4278985243324823689/4280000000000000000 : ℝ)+2*(208213450451/171200000000000 : ℝ)*(7397/50000 : ℝ)=(5000613782964731/5000000000000000 : ℝ) by norm_num, show 1+2*(103365396092741/390625000000000000 : ℝ)=(195415865396092741/195312500000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4278985243324823689/4280000000000000000 : ℝ)*(X 1 0+X 2 0)+(208213450451/171200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2207/512 : ℝ)) (lo := (1137/10000 : ℝ)) (hi := (7397/50000 : ℝ)) (c := (4278985243324823689/4280000000000000000 : ℝ)) (alpha := (208213450451/171200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4278985243324823689/4280000000000000000 : ℝ)*(X 0 1+X 2 1)+(208213450451/171200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2207/512 : ℝ)) (lo := (1137/10000 : ℝ)) (hi := (7397/50000 : ℝ)) (c := (4278985243324823689/4280000000000000000 : ℝ)) (alpha := (208213450451/171200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4278985243324823689/4280000000000000000 : ℝ)*(X 0 2+X 1 2)+(208213450451/171200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2207/512 : ℝ)) (lo := (1137/10000 : ℝ)) (hi := (7397/50000 : ℝ)) (c := (4278985243324823689/4280000000000000000 : ℝ)) (alpha := (208213450451/171200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-390042177/2000000000 : ℝ)*X 0 0+(2703511317/5000000000 : ℝ)*X 0 1+(2623663109/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069360951/2000000000 : ℝ)*X 1 0+(-2031499907/10000000000 : ℝ)*X 1 1+(2623663109/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069360951/2000000000 : ℝ)*X 2 0+(2623663109/5000000000 : ℝ)*X 2 1+(-2031499907/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4297904829/10000000000 : ℝ)*X 0 0+(2063333129/5000000000 : ℝ)*X 0 1+(4475436757/10000000000 : ℝ)*X 0 2+(4297904829/10000000000 : ℝ)*X 1 0+(2063333129/5000000000 : ℝ)*X 1 1+(4475436757/10000000000 : ℝ)*X 1 2+(4297904829/10000000000 : ℝ)*X 2 0+(2063333129/5000000000 : ℝ)*X 2 1+(4475436757/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-487555509/2500000000 : ℝ)*X 0 0+(2623952269/5000000000 : ℝ)*X 0 1+(5406441311/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305184681/10000000000 : ℝ)*X 1 0+(-1872384813/10000000000 : ℝ)*X 1 1+(540644131/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326296171/2500000000 : ℝ)*X 2 0+(5406441309/10000000000 : ℝ)*X 2 1+(-468096203/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((859585837/2000000000 : ℝ)*X 0 0+(4474173727/10000000000 : ℝ)*X 0 1+(4127935843/10000000000 : ℝ)*X 0 2+(859585837/2000000000 : ℝ)*X 1 0+(4474173727/10000000000 : ℝ)*X 1 1+(4127935843/10000000000 : ℝ)*X 1 2+(859585837/2000000000 : ℝ)*X 2 0+(4474173727/10000000000 : ℝ)*X 2 1+(4127935843/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1133680441330992472898138007/107000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1908812933/100000000000000 : ℝ)*(base19) + (1779553073/100000000000000 : ℝ)*(base23) + (69112723/100000000000000 : ℝ)*(lower2) + (52661729/20000000000000 : ℝ)*(upper3) + (169613347/100000000000000 : ℝ)*(upper5) + (4564608651789321/100000000000000 : ℝ)*(major0) + (4564608651789321/100000000000000 : ℝ)*(major1) + (4564608651789321/100000000000000 : ℝ)*(major2) + (6261923486742617/100000000000000 : ℝ)*(sp0) + (1565490511182543/25000000000000 : ℝ)*(sp1) + (391372635874377/6250000000000 : ℝ)*(sp2) + (1433616474929111/50000000000000 : ℝ)*(sp3) + (40466800489/100000000000000 : ℝ)*(sp4) + (5011751457/25000000000000 : ℝ)*(sp7) + (57345059937281/2000000000000 : ℝ)*(f.failure) + (3130981976771553/50000000000000 : ℝ)*(f.sum) + (59547094356869/8560000000000000000000000000 : ℝ)*base66 + (3102028221033699831/428000000000000000000000000000000 : ℝ)*base68 + (1888873413661699831/428000000000000000000000000000000 : ℝ)*base70 + (3979062531841699831/428000000000000000000000000000000 : ℝ)*base72 + (14276487117909/8560000000000000000000000000 : ℝ)*base74 + (3149169023569699831/428000000000000000000000000000000 : ℝ)*base76 + (5724718012241699831/428000000000000000000000000000000 : ℝ)*base78 + (5899176984518300169/428000000000000000000000000000000 : ℝ)*base79 + (32038245777269/8560000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (331413/200000000000000000000 : ℝ)*base89 + (331413/200000000000000000000 : ℝ)*base91 + (331413/200000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (33823052629788674659761/4280000000000000000000000000 : ℝ) := by norm_num
    linear_combination (265054311/20000000000000 : ℝ)*(base19) + (1444760567/100000000000000 : ℝ)*(base23) + (161127611/100000000000000 : ℝ)*(upper3) + (52378059/100000000000000 : ℝ)*(lower4) + (81483589/50000000000000 : ℝ)*(upper5) + (2298967827305261/50000000000000 : ℝ)*(major0) + (2298967827305261/50000000000000 : ℝ)*(major1) + (2298967827305261/50000000000000 : ℝ)*(major2) + (28093682563/100000000000000 : ℝ)*(sp1) + (30285118633/100000000000000 : ℝ)*(sp2) + (252307349415801/4000000000000 : ℝ)*(sp4) + (3153827158220453/50000000000000 : ℝ)*(sp5) + (252306080220633/4000000000000 : ℝ)*(sp6) + (1444093655203299/50000000000000 : ℝ)*(sp7) + (1444093655203299/50000000000000 : ℝ)*(f.failure) + (252307349415801/4000000000000 : ℝ)*(f.sum) + (28686630518311/4280000000000000000000000000 : ℝ)*base65 + (785502767069097171/214000000000000000000000000000000 : ℝ)*base68 + (2740563045371097171/214000000000000000000000000000000 : ℝ)*base70 + (2134112825140902829/214000000000000000000000000000000 : ℝ)*base71 + (24450813827151/4280000000000000000000000000 : ℝ)*base73 + (831592189362902829/214000000000000000000000000000000 : ℝ)*base75 + (697921126044902829/214000000000000000000000000000000 : ℝ)*base77 + (4507885421435097171/214000000000000000000000000000000 : ℝ)*base80 + (9136517767471/4280000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (3712927/5000000000000000000000 : ℝ)*base89 + (3712927/5000000000000000000000 : ℝ)*base91 + (3712927/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1455_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159197973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7397/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1137/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11389/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14773/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1455_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1455_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159197973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15723/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5251/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11389/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14773/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1455_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1455_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1455_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159197973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15723/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5251/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11389/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14773/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1455_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
