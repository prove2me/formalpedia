-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1260_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:53:42.929183+00:00
-- url     : https://prove2.me/submissions/78033c7c-3bb6-45fc-a2a8-b144da68ef8f

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
theorem support_rectangle_w1260_s3_0 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1054500211/5000000000 : ℝ)*x 0 + (5418106891/10000000000 : ℝ)*x 1 + (5241977769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054500211/5000000000 : ℝ)^8453 ≤ (1282183101713/10000000000000 : ℝ)^6405 := by
    have hnat : (1054500211 : ℕ)^8453*10000000000000^6405 ≤ 1282183101713^6405*5000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054500211 5000000000 1282183101713 10000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5418106891/10000000000 : ℝ)^8453 ≤ (44539493803217/100000000000000 : ℝ)^6405 := by
    have hnat : (5418106891 : ℕ)^8453*100000000000000^6405 ≤ 44539493803217^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418106891 10000000000 44539493803217 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5241977769/10000000000 : ℝ)^8453 ≤ (42638675166073/100000000000000 : ℝ)^6405 := by
    have hnat : (5241977769 : ℕ)^8453*100000000000000^6405 ≤ 42638675166073^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241977769 10000000000 42638675166073 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1054500211/5000000000 : ℝ), (5418106891/10000000000 : ℝ), (5241977769/10000000000 : ℝ)] ![(1282183101713/10000000000000 : ℝ), (44539493803217/100000000000000 : ℝ), (42638675166073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1054500211/5000000000 : ℝ)|^8453 ≤ (1282183101713/10000000000000 : ℝ)^6405
        have hw : |(-1054500211/5000000000 : ℝ)|=(1054500211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5418106891/10000000000 : ℝ)|^8453 ≤ (44539493803217/100000000000000 : ℝ)^6405
        have hw : |(5418106891/10000000000 : ℝ)|=(5418106891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5241977769/10000000000 : ℝ)|^8453 ≤ (42638675166073/100000000000000 : ℝ)^6405
        have hw : |(5241977769/10000000000 : ℝ)|=(5241977769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s3_1 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5351097339/10000000000 : ℝ)*x 0 + (-2198821687/10000000000 : ℝ)*x 1 + (5241977871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351097339/10000000000 : ℝ)^8453 ≤ (21906974566259/50000000000000 : ℝ)^6405 := by
    have hnat : (5351097339 : ℕ)^8453*50000000000000^6405 ≤ 21906974566259^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351097339 10000000000 21906974566259 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2198821687/10000000000 : ℝ)^8453 ≤ (13547374598517/100000000000000 : ℝ)^6405 := by
    have hnat : (2198821687 : ℕ)^8453*100000000000000^6405 ≤ 13547374598517^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2198821687 10000000000 13547374598517 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5241977871/10000000000 : ℝ)^8453 ≤ (42638676261039/100000000000000 : ℝ)^6405 := by
    have hnat : (5241977871 : ℕ)^8453*100000000000000^6405 ≤ 42638676261039^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241977871 10000000000 42638676261039 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351097339/10000000000 : ℝ), (-2198821687/10000000000 : ℝ), (5241977871/10000000000 : ℝ)] ![(21906974566259/50000000000000 : ℝ), (13547374598517/100000000000000 : ℝ), (42638676261039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351097339/10000000000 : ℝ)|^8453 ≤ (21906974566259/50000000000000 : ℝ)^6405
        have hw : |(5351097339/10000000000 : ℝ)|=(5351097339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2198821687/10000000000 : ℝ)|^8453 ≤ (13547374598517/100000000000000 : ℝ)^6405
        have hw : |(-2198821687/10000000000 : ℝ)|=(2198821687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5241977871/10000000000 : ℝ)|^8453 ≤ (42638676261039/100000000000000 : ℝ)^6405
        have hw : |(5241977871/10000000000 : ℝ)|=(5241977871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s3_2 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2675548657/5000000000 : ℝ)*x 0 + (5241978347/10000000000 : ℝ)*x 1 + (-2198821091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675548657/5000000000 : ℝ)^8453 ≤ (4381394886237/10000000000000 : ℝ)^6405 := by
    have hnat : (2675548657 : ℕ)^8453*10000000000000^6405 ≤ 4381394886237^6405*5000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675548657 5000000000 4381394886237 10000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5241978347/10000000000 : ℝ)^8453 ≤ (21319340685439/50000000000000 : ℝ)^6405 := by
    have hnat : (5241978347 : ℕ)^8453*50000000000000^6405 ≤ 21319340685439^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241978347 10000000000 21319340685439 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2198821091/10000000000 : ℝ)^8453 ≤ (13547369752297/100000000000000 : ℝ)^6405 := by
    have hnat : (2198821091 : ℕ)^8453*100000000000000^6405 ≤ 13547369752297^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2198821091 10000000000 13547369752297 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675548657/5000000000 : ℝ), (5241978347/10000000000 : ℝ), (-2198821091/10000000000 : ℝ)] ![(4381394886237/10000000000000 : ℝ), (21319340685439/50000000000000 : ℝ), (13547369752297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675548657/5000000000 : ℝ)|^8453 ≤ (4381394886237/10000000000000 : ℝ)^6405
        have hw : |(2675548657/5000000000 : ℝ)|=(2675548657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5241978347/10000000000 : ℝ)|^8453 ≤ (21319340685439/50000000000000 : ℝ)^6405
        have hw : |(5241978347/10000000000 : ℝ)|=(5241978347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2198821091/10000000000 : ℝ)|^8453 ≤ (13547369752297/100000000000000 : ℝ)^6405
        have hw : |(-2198821091/10000000000 : ℝ)|=(2198821091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s3_3 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4346696643/10000000000 : ℝ)*x 0 + (2085503491/5000000000 : ℝ)*x 1 + (905907553/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4346696643/10000000000 : ℝ)^8453 ≤ (6660252636091/20000000000000 : ℝ)^6405 := by
    have hnat : (4346696643 : ℕ)^8453*20000000000000^6405 ≤ 6660252636091^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4346696643 10000000000 6660252636091 20000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2085503491/5000000000 : ℝ)^8453 ≤ (6307291043541/20000000000000 : ℝ)^6405 := by
    have hnat : (2085503491 : ℕ)^8453*20000000000000^6405 ≤ 6307291043541^6405*5000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085503491 5000000000 6307291043541 20000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (905907553/2000000000 : ℝ)^8453 ≤ (35162281586243/100000000000000 : ℝ)^6405 := by
    have hnat : (905907553 : ℕ)^8453*100000000000000^6405 ≤ 35162281586243^6405*2000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      905907553 2000000000 35162281586243 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4346696643/10000000000 : ℝ), (2085503491/5000000000 : ℝ), (905907553/2000000000 : ℝ)] ![(6660252636091/20000000000000 : ℝ), (6307291043541/20000000000000 : ℝ), (35162281586243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4346696643/10000000000 : ℝ)|^8453 ≤ (6660252636091/20000000000000 : ℝ)^6405
        have hw : |(4346696643/10000000000 : ℝ)|=(4346696643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2085503491/5000000000 : ℝ)|^8453 ≤ (6307291043541/20000000000000 : ℝ)^6405
        have hw : |(2085503491/5000000000 : ℝ)|=(2085503491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(905907553/2000000000 : ℝ)|^8453 ≤ (35162281586243/100000000000000 : ℝ)^6405
        have hw : |(905907553/2000000000 : ℝ)|=(905907553/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s3_4 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2109014453/10000000000 : ℝ)*x 0 + (163831589/312500000 : ℝ)*x 1 + (1083494013/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2109014453/10000000000 : ℝ)^8453 ≤ (2564388719061/20000000000000 : ℝ)^6405 := by
    have hnat : (2109014453 : ℕ)^8453*20000000000000^6405 ≤ 2564388719061^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109014453 10000000000 2564388719061 20000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163831589/312500000 : ℝ)^8453 ≤ (42645471372399/100000000000000 : ℝ)^6405 := by
    have hnat : (163831589 : ℕ)^8453*100000000000000^6405 ≤ 42645471372399^6405*312500000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163831589 312500000 42645471372399 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083494013/2000000000 : ℝ)^8453 ≤ (44532585012007/100000000000000 : ℝ)^6405 := by
    have hnat : (1083494013 : ℕ)^8453*100000000000000^6405 ≤ 44532585012007^6405*2000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083494013 2000000000 44532585012007 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2109014453/10000000000 : ℝ), (163831589/312500000 : ℝ), (1083494013/2000000000 : ℝ)] ![(2564388719061/20000000000000 : ℝ), (42645471372399/100000000000000 : ℝ), (44532585012007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2109014453/10000000000 : ℝ)|^8453 ≤ (2564388719061/20000000000000 : ℝ)^6405
        have hw : |(-2109014453/10000000000 : ℝ)|=(2109014453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163831589/312500000 : ℝ)|^8453 ≤ (42645471372399/100000000000000 : ℝ)^6405
        have hw : |(163831589/312500000 : ℝ)|=(163831589/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1083494013/2000000000 : ℝ)|^8453 ≤ (44532585012007/100000000000000 : ℝ)^6405
        have hw : |(1083494013/2000000000 : ℝ)|=(1083494013/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s3_5 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (265305467/500000000 : ℝ)*x 0 + (-1011664421/5000000000 : ℝ)*x 1 + (5417469903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265305467/500000000 : ℝ)^8453 ≤ (43328467604601/100000000000000 : ℝ)^6405 := by
    have hnat : (265305467 : ℕ)^8453*100000000000000^6405 ≤ 43328467604601^6405*500000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265305467 500000000 43328467604601 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1011664421/5000000000 : ℝ)^8453 ≤ (12138949129057/100000000000000 : ℝ)^6405 := by
    have hnat : (1011664421 : ℕ)^8453*100000000000000^6405 ≤ 12138949129057^6405*5000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1011664421 5000000000 12138949129057 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5417469903/10000000000 : ℝ)^8453 ≤ (44532583254537/100000000000000 : ℝ)^6405 := by
    have hnat : (5417469903 : ℕ)^8453*100000000000000^6405 ≤ 44532583254537^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417469903 10000000000 44532583254537 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265305467/500000000 : ℝ), (-1011664421/5000000000 : ℝ), (5417469903/10000000000 : ℝ)] ![(43328467604601/100000000000000 : ℝ), (12138949129057/100000000000000 : ℝ), (44532583254537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265305467/500000000 : ℝ)|^8453 ≤ (43328467604601/100000000000000 : ℝ)^6405
        have hw : |(265305467/500000000 : ℝ)|=(265305467/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1011664421/5000000000 : ℝ)|^8453 ≤ (12138949129057/100000000000000 : ℝ)^6405
        have hw : |(-1011664421/5000000000 : ℝ)|=(1011664421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5417469903/10000000000 : ℝ)|^8453 ≤ (44532583254537/100000000000000 : ℝ)^6405
        have hw : |(5417469903/10000000000 : ℝ)|=(5417469903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s3_6 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1061221737/2000000000 : ℝ)*x 0 + (5417470351/10000000000 : ℝ)*x 1 + (-2023329119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061221737/2000000000 : ℝ)^8453 ≤ (43328460545813/100000000000000 : ℝ)^6405 := by
    have hnat : (1061221737 : ℕ)^8453*100000000000000^6405 ≤ 43328460545813^6405*2000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061221737 2000000000 43328460545813 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5417470351/10000000000 : ℝ)^8453 ≤ (44532588114703/100000000000000 : ℝ)^6405 := by
    have hnat : (5417470351 : ℕ)^8453*100000000000000^6405 ≤ 44532588114703^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417470351 10000000000 44532588114703 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2023329119/10000000000 : ℝ)^8453 ≤ (12138951322297/100000000000000 : ℝ)^6405 := by
    have hnat : (2023329119 : ℕ)^8453*100000000000000^6405 ≤ 12138951322297^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2023329119 10000000000 12138951322297 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061221737/2000000000 : ℝ), (5417470351/10000000000 : ℝ), (-2023329119/10000000000 : ℝ)] ![(43328460545813/100000000000000 : ℝ), (44532588114703/100000000000000 : ℝ), (12138951322297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061221737/2000000000 : ℝ)|^8453 ≤ (43328460545813/100000000000000 : ℝ)^6405
        have hw : |(1061221737/2000000000 : ℝ)|=(1061221737/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5417470351/10000000000 : ℝ)|^8453 ≤ (44532588114703/100000000000000 : ℝ)^6405
        have hw : |(5417470351/10000000000 : ℝ)|=(5417470351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2023329119/10000000000 : ℝ)|^8453 ≤ (12138951322297/100000000000000 : ℝ)^6405
        have hw : |(-2023329119/10000000000 : ℝ)|=(2023329119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s3_7 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4346724627/10000000000 : ℝ)*x 0 + (2264124143/5000000000 : ℝ)*x 1 + (4172302433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4346724627/10000000000 : ℝ)^8453 ≤ (33301546126319/100000000000000 : ℝ)^6405 := by
    have hnat : (4346724627 : ℕ)^8453*100000000000000^6405 ≤ 33301546126319^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4346724627 10000000000 33301546126319 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2264124143/5000000000 : ℝ)^8453 ≤ (17574535692963/50000000000000 : ℝ)^6405 := by
    have hnat : (2264124143 : ℕ)^8453*50000000000000^6405 ≤ 17574535692963^6405*5000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2264124143 5000000000 17574535692963 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172302433/10000000000 : ℝ)^8453 ≤ (31549382470669/100000000000000 : ℝ)^6405 := by
    have hnat : (4172302433 : ℕ)^8453*100000000000000^6405 ≤ 31549382470669^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172302433 10000000000 31549382470669 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4346724627/10000000000 : ℝ), (2264124143/5000000000 : ℝ), (4172302433/10000000000 : ℝ)] ![(33301546126319/100000000000000 : ℝ), (17574535692963/50000000000000 : ℝ), (31549382470669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4346724627/10000000000 : ℝ)|^8453 ≤ (33301546126319/100000000000000 : ℝ)^6405
        have hw : |(4346724627/10000000000 : ℝ)|=(4346724627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2264124143/5000000000 : ℝ)|^8453 ≤ (17574535692963/50000000000000 : ℝ)^6405
        have hw : |(2264124143/5000000000 : ℝ)|=(2264124143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172302433/10000000000 : ℝ)|^8453 ≤ (31549382470669/100000000000000 : ℝ)^6405
        have hw : |(4172302433/10000000000 : ℝ)|=(4172302433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1260_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151781167/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16177/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2393/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10957/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2937/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16177/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2393/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16177/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2393/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16177/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2393/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16177/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2393/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16177/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2393/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16177/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2393/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2393/25000 : ℝ) ^ (2113/512 : ℝ) ≤ (1558066089790907/25000000000000000000 : ℝ) := by
    have hpowers : (2393/25000 : ℝ)^2113 ≤ (1558066089790907/25000000000000000000 : ℝ)^512 := by
      have hnat : (2393 : ℕ)^2113*25000000000000000000^512 ≤ 1558066089790907^512*25000^2113 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2393 25000 1558066089790907 25000000000000000000 2113 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2393/25000 : ℝ)) (X := (1558066089790907/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hpowhi : (16177/100000 : ℝ) ^ (2113/512 : ℝ) ≤ (54344934423302703/100000000000000000000 : ℝ) := by
    have hpowers : (16177/100000 : ℝ)^2113 ≤ (54344934423302703/100000000000000000000 : ℝ)^512 := by
      have hnat : (16177 : ℕ)^2113*100000000000000000000^512 ≤ 54344934423302703^512*100000^2113 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16177 100000 54344934423302703 100000000000000000000 2113 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16177/100000 : ℝ)) (X := (54344934423302703/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501558066089790907/12500000000000000000 : ℝ) ≤ (10000302013126703/10000000000000000 : ℝ) ^ (2113/512 : ℝ) := by
    have hpowers : (12501558066089790907/12500000000000000000 : ℝ)^512 ≤ (10000302013126703/10000000000000000 : ℝ)^2113 := by
      have hnat : (12501558066089790907 : ℕ)^512*10000000000000000^2113 ≤ 10000302013126703^2113*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501558066089790907 12500000000000000000 10000302013126703 10000000000000000 512 2113 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000302013126703/10000000000000000 : ℝ)) (X := (12501558066089790907/12500000000000000000 : ℝ)) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100060577198782466331/100000000000000000000 : ℝ) ≤ (2500366876602341/2500000000000000 : ℝ) ^ (2113/512 : ℝ) := by
    have hpowers : (100060577198782466331/100000000000000000000 : ℝ)^512 ≤ (2500366876602341/2500000000000000 : ℝ)^2113 := by
      have hnat : (100060577198782466331 : ℕ)^512*2500000000000000^2113 ≤ 2500366876602341^2113*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100060577198782466331 100000000000000000000 2500366876602341 2500000000000000 512 2113 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500366876602341/2500000000000000 : ℝ)) (X := (100060577198782466331/100000000000000000000 : ℝ)) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50054344934423302703/50000000000000000000 : ℝ) ≤ (400105319987681/400000000000000 : ℝ) ^ (2113/512 : ℝ) := by
    have hpowers : (50054344934423302703/50000000000000000000 : ℝ)^512 ≤ (400105319987681/400000000000000 : ℝ)^2113 := by
      have hnat : (50054344934423302703 : ℕ)^512*400000000000000^2113 ≤ 400105319987681^2113*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50054344934423302703 50000000000000000000 400105319987681 400000000000000 512 2113 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400105319987681/400000000000000 : ℝ)) (X := (50054344934423302703/50000000000000000000 : ℝ)) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1558066089790907/25000000000000000000 : ℝ) ≤ ((66029682593298611131/66050000000000000000 : ℝ)+2*(1165493282661/660500000000000 : ℝ)*(2393/25000 : ℝ))^(2113/512 : ℝ) := by
    rw [show (66029682593298611131/66050000000000000000 : ℝ)+2*(1165493282661/660500000000000 : ℝ)*(2393/25000 : ℝ)=(10000302013126703/10000000000000000 : ℝ) by norm_num, show 1+2*(1558066089790907/25000000000000000000 : ℝ)=(12501558066089790907/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(54344934423302703/100000000000000000000 : ℝ)+(1558066089790907/25000000000000000000 : ℝ) ≤ ((66029682593298611131/66050000000000000000 : ℝ)+(1165493282661/660500000000000 : ℝ)*((16177/100000 : ℝ)+(2393/25000 : ℝ)))^(2113/512 : ℝ) := by
    rw [show (66029682593298611131/66050000000000000000 : ℝ)+(1165493282661/660500000000000 : ℝ)*((16177/100000 : ℝ)+(2393/25000 : ℝ))=(2500366876602341/2500000000000000 : ℝ) by norm_num, show 1+(54344934423302703/100000000000000000000 : ℝ)+(1558066089790907/25000000000000000000 : ℝ)=(100060577198782466331/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(54344934423302703/100000000000000000000 : ℝ) ≤ ((66029682593298611131/66050000000000000000 : ℝ)+2*(1165493282661/660500000000000 : ℝ)*(16177/100000 : ℝ))^(2113/512 : ℝ) := by
    rw [show (66029682593298611131/66050000000000000000 : ℝ)+2*(1165493282661/660500000000000 : ℝ)*(16177/100000 : ℝ)=(400105319987681/400000000000000 : ℝ) by norm_num, show 1+2*(54344934423302703/100000000000000000000 : ℝ)=(50054344934423302703/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (66029682593298611131/66050000000000000000 : ℝ)*(X 1 0+X 2 0)+(1165493282661/660500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2113/512 : ℝ)) (lo := (2393/25000 : ℝ)) (hi := (16177/100000 : ℝ)) (c := (66029682593298611131/66050000000000000000 : ℝ)) (alpha := (1165493282661/660500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (66029682593298611131/66050000000000000000 : ℝ)*(X 0 1+X 2 1)+(1165493282661/660500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2113/512 : ℝ)) (lo := (2393/25000 : ℝ)) (hi := (16177/100000 : ℝ)) (c := (66029682593298611131/66050000000000000000 : ℝ)) (alpha := (1165493282661/660500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (66029682593298611131/66050000000000000000 : ℝ)*(X 0 2+X 1 2)+(1165493282661/660500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2113/512 : ℝ)) (lo := (2393/25000 : ℝ)) (hi := (16177/100000 : ℝ)) (c := (66029682593298611131/66050000000000000000 : ℝ)) (alpha := (1165493282661/660500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1054500211/5000000000 : ℝ)*X 0 0+(5418106891/10000000000 : ℝ)*X 0 1+(5241977769/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351097339/10000000000 : ℝ)*X 1 0+(-2198821687/10000000000 : ℝ)*X 1 1+(5241977871/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675548657/5000000000 : ℝ)*X 2 0+(5241978347/10000000000 : ℝ)*X 2 1+(-2198821091/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4346696643/10000000000 : ℝ)*X 0 0+(2085503491/5000000000 : ℝ)*X 0 1+(905907553/2000000000 : ℝ)*X 0 2+(4346696643/10000000000 : ℝ)*X 1 0+(2085503491/5000000000 : ℝ)*X 1 1+(905907553/2000000000 : ℝ)*X 1 2+(4346696643/10000000000 : ℝ)*X 2 0+(2085503491/5000000000 : ℝ)*X 2 1+(905907553/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2109014453/10000000000 : ℝ)*X 0 0+(163831589/312500000 : ℝ)*X 0 1+(1083494013/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((265305467/500000000 : ℝ)*X 1 0+(-1011664421/5000000000 : ℝ)*X 1 1+(5417469903/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061221737/2000000000 : ℝ)*X 2 0+(5417470351/10000000000 : ℝ)*X 2 1+(-2023329119/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4346724627/10000000000 : ℝ)*X 0 0+(2264124143/5000000000 : ℝ)*X 0 1+(4172302433/10000000000 : ℝ)*X 0 2+(4346724627/10000000000 : ℝ)*X 1 0+(2264124143/5000000000 : ℝ)*X 1 1+(4172302433/10000000000 : ℝ)*X 1 2+(4346724627/10000000000 : ℝ)*X 2 0+(2264124143/5000000000 : ℝ)*X 2 1+(4172302433/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9392859857316689447325810123/3302500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (52606327/100000000000000 : ℝ)*(base8) + (22761767/20000000000000 : ℝ)*(lower2) + (22925507/25000000000000 : ℝ)*(lower3) + (29978403/50000000000000 : ℝ)*(lower4) + (4233433814166537/100000000000000 : ℝ)*(major0) + (4233433814166537/100000000000000 : ℝ)*(major1) + (4233433814166537/100000000000000 : ℝ)*(major2) + (2838836446090701/50000000000000 : ℝ)*(sp0) + (5677683041542597/100000000000000 : ℝ)*(sp1) + (5677698166970637/100000000000000 : ℝ)*(sp2) + (139458266124263/5000000000000 : ℝ)*(sp3) + (6305545727/25000000000000 : ℝ)*(sp4) + (378135701/2500000000000 : ℝ)*(sp5) + (2022035809/50000000000000 : ℝ)*(sp7) + (1394584683278439/50000000000000 : ℝ)*(f.failure) + (5677698166970637/100000000000000 : ℝ)*(f.sum) + (269282564538507/33025000000000000000000000000 : ℝ)*base65 + (145882635034638376653/6605000000000000000000000000000000 : ℝ)*base68 + (53914168655528376653/6605000000000000000000000000000000 : ℝ)*base70 + (76334642985713376653/6605000000000000000000000000000000 : ℝ)*base72 + (3704554316683/8256250000000000000000000000 : ℝ)*base73 + (71260549568673376653/6605000000000000000000000000000000 : ℝ)*base76 + (58922713946888376653/6605000000000000000000000000000000 : ℝ)*base78 + (91850894045803376653/6605000000000000000000000000000000 : ℝ)*base80 + (89248620742891/16512500000000000000000000000 : ℝ)*base81 + (7358313/5000000000000000000000 : ℝ)*base89 + (7358313/5000000000000000000000 : ℝ)*base91 + (7358313/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1776413558523528231398390409/330250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2856499563/100000000000000 : ℝ)*(base19) + (2107607537/100000000000000 : ℝ)*(base23) + (51896583/100000000000000 : ℝ)*(upper3) + (72202303/100000000000000 : ℝ)*(lower4) + (22711693/5000000000000 : ℝ)*(upper5) + (426414992706371/10000000000000 : ℝ)*(major0) + (426414992706371/10000000000000 : ℝ)*(major1) + (426414992706371/10000000000000 : ℝ)*(major2) + (66353831321/100000000000000 : ℝ)*(sp1) + (45239737213/100000000000000 : ℝ)*(sp2) + (2859446602043427/50000000000000 : ℝ)*(sp4) + (571882399375597/10000000000000 : ℝ)*(sp5) + (714855732092763/12500000000000 : ℝ)*(sp6) + (702351617685169/25000000000000 : ℝ)*(sp7) + (702351617685169/25000000000000 : ℝ)*(f.failure) + (2859446602043427/50000000000000 : ℝ)*(f.sum) + (4528281712811/825625000000000000000000000 : ℝ)*base66 + (10317108752725684399/660500000000000000000000000000000 : ℝ)*base68 + (10619959026470684399/660500000000000000000000000000000 : ℝ)*base70 + (9004410539577184399/660500000000000000000000000000000 : ℝ)*base72 + (46368951669283/6605000000000000000000000000 : ℝ)*base74 + (11244292022026184399/660500000000000000000000000000000 : ℝ)*base76 + (3742870513808684399/660500000000000000000000000000000 : ℝ)*base78 + (2176375726517184399/660500000000000000000000000000000 : ℝ)*base80 + (19904014108317/6605000000000000000000000000 : ℝ)*base81 + (39412223/2500000000000000000000 : ℝ)*base89 + (39412223/2500000000000000000000 : ℝ)*base91 + (39412223/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1260_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151781167/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16177/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2393/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10957/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2937/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1260_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1260_s4_0 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-422236783/2000000000 : ℝ)*x 0 + (5396778723/10000000000 : ℝ)*x 1 + (328867163/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (422236783/2000000000 : ℝ)^8453 ≤ (12839353223203/100000000000000 : ℝ)^6405 := by
    have hnat : (422236783 : ℕ)^8453*100000000000000^6405 ≤ 12839353223203^6405*2000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422236783 2000000000 12839353223203 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396778723/10000000000 : ℝ)^8453 ≤ (22154125201761/50000000000000 : ℝ)^6405 := by
    have hnat : (5396778723 : ℕ)^8453*50000000000000^6405 ≤ 22154125201761^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396778723 10000000000 22154125201761 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (328867163/625000000 : ℝ)^8453 ≤ (42852396357391/100000000000000 : ℝ)^6405 := by
    have hnat : (328867163 : ℕ)^8453*100000000000000^6405 ≤ 42852396357391^6405*625000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328867163 625000000 42852396357391 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-422236783/2000000000 : ℝ), (5396778723/10000000000 : ℝ), (328867163/625000000 : ℝ)] ![(12839353223203/100000000000000 : ℝ), (22154125201761/50000000000000 : ℝ), (42852396357391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-422236783/2000000000 : ℝ)|^8453 ≤ (12839353223203/100000000000000 : ℝ)^6405
        have hw : |(-422236783/2000000000 : ℝ)|=(422236783/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396778723/10000000000 : ℝ)|^8453 ≤ (22154125201761/50000000000000 : ℝ)^6405
        have hw : |(5396778723/10000000000 : ℝ)|=(5396778723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(328867163/625000000 : ℝ)|^8453 ≤ (42852396357391/100000000000000 : ℝ)^6405
        have hw : |(328867163/625000000 : ℝ)|=(328867163/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s4_1 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672855963/5000000000 : ℝ)*x 0 + (-108983339/500000000 : ℝ)*x 1 + (5261874667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672855963/5000000000 : ℝ)^8453 ≤ (21877882109163/50000000000000 : ℝ)^6405 := by
    have hnat : (2672855963 : ℕ)^8453*50000000000000^6405 ≤ 21877882109163^6405*5000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672855963 5000000000 21877882109163 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108983339/500000000 : ℝ)^8453 ≤ (2678367755383/20000000000000 : ℝ)^6405 := by
    have hnat : (108983339 : ℕ)^8453*20000000000000^6405 ≤ 2678367755383^6405*500000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108983339 500000000 2678367755383 20000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5261874667/10000000000 : ℝ)^8453 ≤ (42852396991521/100000000000000 : ℝ)^6405 := by
    have hnat : (5261874667 : ℕ)^8453*100000000000000^6405 ≤ 42852396991521^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261874667 10000000000 42852396991521 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672855963/5000000000 : ℝ), (-108983339/500000000 : ℝ), (5261874667/10000000000 : ℝ)] ![(21877882109163/50000000000000 : ℝ), (2678367755383/20000000000000 : ℝ), (42852396991521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672855963/5000000000 : ℝ)|^8453 ≤ (21877882109163/50000000000000 : ℝ)^6405
        have hw : |(2672855963/5000000000 : ℝ)|=(2672855963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-108983339/500000000 : ℝ)|^8453 ≤ (2678367755383/20000000000000 : ℝ)^6405
        have hw : |(-108983339/500000000 : ℝ)|=(108983339/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5261874667/10000000000 : ℝ)|^8453 ≤ (42852396991521/100000000000000 : ℝ)^6405
        have hw : |(5261874667/10000000000 : ℝ)|=(5261874667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s4_2 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336427991/2500000000 : ℝ)*x 0 + (657734327/1250000000 : ℝ)*x 1 + (-2179666797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336427991/2500000000 : ℝ)^8453 ≤ (43755764628819/100000000000000 : ℝ)^6405 := by
    have hnat : (1336427991 : ℕ)^8453*100000000000000^6405 ≤ 43755764628819^6405*2500000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336427991 2500000000 43755764628819 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (657734327/1250000000 : ℝ)^8453 ≤ (342819171547/800000000000 : ℝ)^6405 := by
    have hnat : (657734327 : ℕ)^8453*800000000000^6405 ≤ 342819171547^6405*1250000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657734327 1250000000 342819171547 800000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2179666797/10000000000 : ℝ)^8453 ≤ (334795972869/2500000000000 : ℝ)^6405 := by
    have hnat : (2179666797 : ℕ)^8453*2500000000000^6405 ≤ 334795972869^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179666797 10000000000 334795972869 2500000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336427991/2500000000 : ℝ), (657734327/1250000000 : ℝ), (-2179666797/10000000000 : ℝ)] ![(43755764628819/100000000000000 : ℝ), (342819171547/800000000000 : ℝ), (334795972869/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336427991/2500000000 : ℝ)|^8453 ≤ (43755764628819/100000000000000 : ℝ)^6405
        have hw : |(1336427991/2500000000 : ℝ)|=(1336427991/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(657734327/1250000000 : ℝ)|^8453 ≤ (342819171547/800000000000 : ℝ)^6405
        have hw : |(657734327/1250000000 : ℝ)|=(657734327/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2179666797/10000000000 : ℝ)|^8453 ≤ (334795972869/2500000000000 : ℝ)^6405
        have hw : |(-2179666797/10000000000 : ℝ)|=(2179666797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s4_3 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4348007061/10000000000 : ℝ)*x 0 + (2106399313/5000000000 : ℝ)*x 1 + (897482501/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4348007061/10000000000 : ℝ)^8453 ≤ (8328628356229/25000000000000 : ℝ)^6405 := by
    have hnat : (4348007061 : ℕ)^8453*25000000000000^6405 ≤ 8328628356229^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4348007061 10000000000 8328628356229 25000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2106399313/5000000000 : ℝ)^8453 ≤ (7988534532497/25000000000000 : ℝ)^6405 := by
    have hnat : (2106399313 : ℕ)^8453*25000000000000^6405 ≤ 7988534532497^6405*5000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106399313 5000000000 7988534532497 25000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (897482501/2000000000 : ℝ)^8453 ≤ (6946269686457/20000000000000 : ℝ)^6405 := by
    have hnat : (897482501 : ℕ)^8453*20000000000000^6405 ≤ 6946269686457^6405*2000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897482501 2000000000 6946269686457 20000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4348007061/10000000000 : ℝ), (2106399313/5000000000 : ℝ), (897482501/2000000000 : ℝ)] ![(8328628356229/25000000000000 : ℝ), (7988534532497/25000000000000 : ℝ), (6946269686457/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4348007061/10000000000 : ℝ)|^8453 ≤ (8328628356229/25000000000000 : ℝ)^6405
        have hw : |(4348007061/10000000000 : ℝ)|=(4348007061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2106399313/5000000000 : ℝ)|^8453 ≤ (7988534532497/25000000000000 : ℝ)^6405
        have hw : |(2106399313/5000000000 : ℝ)|=(2106399313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(897482501/2000000000 : ℝ)|^8453 ≤ (6946269686457/20000000000000 : ℝ)^6405
        have hw : |(897482501/2000000000 : ℝ)|=(897482501/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s4_4 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2111189377/10000000000 : ℝ)*x 0 + (2631123339/5000000000 : ℝ)*x 1 + (2698202799/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2111189377/10000000000 : ℝ)^8453 ≤ (200615579097/1562500000000 : ℝ)^6405 := by
    have hnat : (2111189377 : ℕ)^8453*1562500000000^6405 ≤ 200615579097^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111189377 10000000000 200615579097 1562500000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631123339/5000000000 : ℝ)^8453 ≤ (857127907979/2000000000000 : ℝ)^6405 := by
    have hnat : (2631123339 : ℕ)^8453*2000000000000^6405 ≤ 857127907979^6405*5000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631123339 5000000000 857127907979 2000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698202799/5000000000 : ℝ)^8453 ≤ (11076051879899/25000000000000 : ℝ)^6405 := by
    have hnat : (2698202799 : ℕ)^8453*25000000000000^6405 ≤ 11076051879899^6405*5000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698202799 5000000000 11076051879899 25000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2111189377/10000000000 : ℝ), (2631123339/5000000000 : ℝ), (2698202799/5000000000 : ℝ)] ![(200615579097/1562500000000 : ℝ), (857127907979/2000000000000 : ℝ), (11076051879899/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2111189377/10000000000 : ℝ)|^8453 ≤ (200615579097/1562500000000 : ℝ)^6405
        have hw : |(-2111189377/10000000000 : ℝ)|=(2111189377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631123339/5000000000 : ℝ)|^8453 ≤ (857127907979/2000000000000 : ℝ)^6405
        have hw : |(2631123339/5000000000 : ℝ)|=(2631123339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698202799/5000000000 : ℝ)|^8453 ≤ (11076051879899/25000000000000 : ℝ)^6405
        have hw : |(2698202799/5000000000 : ℝ)|=(2698202799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s4_5 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1327812769/2500000000 : ℝ)*x 0 + (-2045135527/10000000000 : ℝ)*x 1 + (5396405351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327812769/2500000000 : ℝ)^8453 ≤ (43383887526033/100000000000000 : ℝ)^6405 := by
    have hnat : (1327812769 : ℕ)^8453*100000000000000^6405 ≤ 43383887526033^6405*2500000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327812769 2500000000 43383887526033 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2045135527/10000000000 : ℝ)^8453 ≤ (2462381522171/20000000000000 : ℝ)^6405 := by
    have hnat : (2045135527 : ℕ)^8453*20000000000000^6405 ≤ 2462381522171^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2045135527 10000000000 2462381522171 20000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396405351/10000000000 : ℝ)^8453 ≤ (11076051210833/25000000000000 : ℝ)^6405 := by
    have hnat : (5396405351 : ℕ)^8453*25000000000000^6405 ≤ 11076051210833^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396405351 10000000000 11076051210833 25000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327812769/2500000000 : ℝ), (-2045135527/10000000000 : ℝ), (5396405351/10000000000 : ℝ)] ![(43383887526033/100000000000000 : ℝ), (2462381522171/20000000000000 : ℝ), (11076051210833/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327812769/2500000000 : ℝ)|^8453 ≤ (43383887526033/100000000000000 : ℝ)^6405
        have hw : |(1327812769/2500000000 : ℝ)|=(1327812769/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2045135527/10000000000 : ℝ)|^8453 ≤ (2462381522171/20000000000000 : ℝ)^6405
        have hw : |(-2045135527/10000000000 : ℝ)|=(2045135527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5396405351/10000000000 : ℝ)|^8453 ≤ (11076051210833/25000000000000 : ℝ)^6405
        have hw : |(5396405351/10000000000 : ℝ)|=(5396405351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s4_6 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311251099/10000000000 : ℝ)*x 0 + (5396405057/10000000000 : ℝ)*x 1 + (-1022567949/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311251099/10000000000 : ℝ)^8453 ≤ (5422985971747/12500000000000 : ℝ)^6405 := by
    have hnat : (5311251099 : ℕ)^8453*12500000000000^6405 ≤ 5422985971747^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311251099 10000000000 5422985971747 12500000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396405057/10000000000 : ℝ)^8453 ≤ (22152100828909/50000000000000 : ℝ)^6405 := by
    have hnat : (5396405057 : ℕ)^8453*50000000000000^6405 ≤ 22152100828909^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396405057 10000000000 22152100828909 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1022567949/5000000000 : ℝ)^8453 ≤ (12311910558457/100000000000000 : ℝ)^6405 := by
    have hnat : (1022567949 : ℕ)^8453*100000000000000^6405 ≤ 12311910558457^6405*5000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1022567949 5000000000 12311910558457 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311251099/10000000000 : ℝ), (5396405057/10000000000 : ℝ), (-1022567949/5000000000 : ℝ)] ![(5422985971747/12500000000000 : ℝ), (22152100828909/50000000000000 : ℝ), (12311910558457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311251099/10000000000 : ℝ)|^8453 ≤ (5422985971747/12500000000000 : ℝ)^6405
        have hw : |(5311251099/10000000000 : ℝ)|=(5311251099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396405057/10000000000 : ℝ)|^8453 ≤ (22152100828909/50000000000000 : ℝ)^6405
        have hw : |(5396405057/10000000000 : ℝ)|=(5396405057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1022567949/5000000000 : ℝ)|^8453 ≤ (12311910558457/100000000000000 : ℝ)^6405
        have hw : |(-1022567949/5000000000 : ℝ)|=(1022567949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s4_7 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1087004787/2500000000 : ℝ)*x 0 + (4486655219/10000000000 : ℝ)*x 1 + (2106779553/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087004787/2500000000 : ℝ)^8453 ≤ (53303417037/160000000000 : ℝ)^6405 := by
    have hnat : (1087004787 : ℕ)^8453*160000000000^6405 ≤ 53303417037^6405*2500000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087004787 2500000000 53303417037 160000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4486655219/10000000000 : ℝ)^8453 ≤ (34723613338279/100000000000000 : ℝ)^6405 := by
    have hnat : (4486655219 : ℕ)^8453*100000000000000^6405 ≤ 34723613338279^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4486655219 10000000000 34723613338279 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2106779553/5000000000 : ℝ)^8453 ≤ (31961751001029/100000000000000 : ℝ)^6405 := by
    have hnat : (2106779553 : ℕ)^8453*100000000000000^6405 ≤ 31961751001029^6405*5000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106779553 5000000000 31961751001029 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1087004787/2500000000 : ℝ), (4486655219/10000000000 : ℝ), (2106779553/5000000000 : ℝ)] ![(53303417037/160000000000 : ℝ), (34723613338279/100000000000000 : ℝ), (31961751001029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1087004787/2500000000 : ℝ)|^8453 ≤ (53303417037/160000000000 : ℝ)^6405
        have hw : |(1087004787/2500000000 : ℝ)|=(1087004787/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4486655219/10000000000 : ℝ)|^8453 ≤ (34723613338279/100000000000000 : ℝ)^6405
        have hw : |(4486655219/10000000000 : ℝ)|=(4486655219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2106779553/5000000000 : ℝ)|^8453 ≤ (31961751001029/100000000000000 : ℝ)^6405
        have hw : |(2106779553/5000000000 : ℝ)|=(2106779553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1260_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151781167/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2937/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10957/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11381/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7119/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2937/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10957/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2937/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10957/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2937/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10957/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2937/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10957/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2937/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10957/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2937/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10957/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10957/100000 : ℝ) ^ (2113/512 : ℝ) ≤ (10885603265962631/100000000000000000000 : ℝ) := by
    have hpowers : (10957/100000 : ℝ)^2113 ≤ (10885603265962631/100000000000000000000 : ℝ)^512 := by
      have hnat : (10957 : ℕ)^2113*100000000000000000000^512 ≤ 10885603265962631^512*100000^2113 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10957 100000 10885603265962631 100000000000000000000 2113 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10957/100000 : ℝ)) (X := (10885603265962631/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2937/20000 : ℝ) ^ (2113/512 : ℝ) ≤ (18226272215247489/50000000000000000000 : ℝ) := by
    have hpowers : (2937/20000 : ℝ)^2113 ≤ (18226272215247489/50000000000000000000 : ℝ)^512 := by
      have hnat : (2937 : ℕ)^2113*50000000000000000000^512 ≤ 18226272215247489^512*20000^2113 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2937 20000 18226272215247489 50000000000000000000 2113 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2937/20000 : ℝ)) (X := (18226272215247489/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010885603265962631/50000000000000000000 : ℝ) ≤ (5000263746769473/5000000000000000 : ℝ) ^ (2113/512 : ℝ) := by
    have hpowers : (50010885603265962631/50000000000000000000 : ℝ)^512 ≤ (5000263746769473/5000000000000000 : ℝ)^2113 := by
      have hnat : (50010885603265962631 : ℕ)^512*5000000000000000^2113 ≤ 5000263746769473^2113*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010885603265962631 50000000000000000000 5000263746769473 5000000000000000 512 2113 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000263746769473/5000000000000000 : ℝ)) (X := (50010885603265962631/50000000000000000000 : ℝ)) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047338147696457609/100000000000000000000 : ℝ) ≤ (2000229368539321/2000000000000000 : ℝ) ^ (2113/512 : ℝ) := by
    have hpowers : (100047338147696457609/100000000000000000000 : ℝ)^512 ≤ (2000229368539321/2000000000000000 : ℝ)^2113 := by
      have hnat : (100047338147696457609 : ℕ)^512*2000000000000000^2113 ≤ 2000229368539321^2113*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047338147696457609 100000000000000000000 2000229368539321 2000000000000000 512 2113 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000229368539321/2000000000000000 : ℝ)) (X := (100047338147696457609/100000000000000000000 : ℝ)) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018226272215247489/25000000000000000000 : ℝ) ≤ (1250220773981783/1250000000000000 : ℝ) ^ (2113/512 : ℝ) := by
    have hpowers : (25018226272215247489/25000000000000000000 : ℝ)^512 ≤ (1250220773981783/1250000000000000 : ℝ)^2113 := by
      have hnat : (25018226272215247489 : ℕ)^512*1250000000000000^2113 ≤ 1250220773981783^2113*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018226272215247489 25000000000000000000 1250220773981783 1250000000000000 512 2113 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250220773981783/1250000000000000 : ℝ)) (X := (25018226272215247489/25000000000000000000 : ℝ)) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10885603265962631/100000000000000000000 : ℝ) ≤ ((18634197039236125681/18640000000000000000 : ℝ)+2*(619349157659/372800000000000 : ℝ)*(10957/100000 : ℝ))^(2113/512 : ℝ) := by
    rw [show (18634197039236125681/18640000000000000000 : ℝ)+2*(619349157659/372800000000000 : ℝ)*(10957/100000 : ℝ)=(5000263746769473/5000000000000000 : ℝ) by norm_num, show 1+2*(10885603265962631/100000000000000000000 : ℝ)=(50010885603265962631/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18226272215247489/50000000000000000000 : ℝ)+(10885603265962631/100000000000000000000 : ℝ) ≤ ((18634197039236125681/18640000000000000000 : ℝ)+(619349157659/372800000000000 : ℝ)*((2937/20000 : ℝ)+(10957/100000 : ℝ)))^(2113/512 : ℝ) := by
    rw [show (18634197039236125681/18640000000000000000 : ℝ)+(619349157659/372800000000000 : ℝ)*((2937/20000 : ℝ)+(10957/100000 : ℝ))=(2000229368539321/2000000000000000 : ℝ) by norm_num, show 1+(18226272215247489/50000000000000000000 : ℝ)+(10885603265962631/100000000000000000000 : ℝ)=(100047338147696457609/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18226272215247489/50000000000000000000 : ℝ) ≤ ((18634197039236125681/18640000000000000000 : ℝ)+2*(619349157659/372800000000000 : ℝ)*(2937/20000 : ℝ))^(2113/512 : ℝ) := by
    rw [show (18634197039236125681/18640000000000000000 : ℝ)+2*(619349157659/372800000000000 : ℝ)*(2937/20000 : ℝ)=(1250220773981783/1250000000000000 : ℝ) by norm_num, show 1+2*(18226272215247489/50000000000000000000 : ℝ)=(25018226272215247489/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18634197039236125681/18640000000000000000 : ℝ)*(X 1 0+X 2 0)+(619349157659/372800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2113/512 : ℝ)) (lo := (10957/100000 : ℝ)) (hi := (2937/20000 : ℝ)) (c := (18634197039236125681/18640000000000000000 : ℝ)) (alpha := (619349157659/372800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18634197039236125681/18640000000000000000 : ℝ)*(X 0 1+X 2 1)+(619349157659/372800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2113/512 : ℝ)) (lo := (10957/100000 : ℝ)) (hi := (2937/20000 : ℝ)) (c := (18634197039236125681/18640000000000000000 : ℝ)) (alpha := (619349157659/372800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18634197039236125681/18640000000000000000 : ℝ)*(X 0 2+X 1 2)+(619349157659/372800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2113/512 : ℝ)) (lo := (10957/100000 : ℝ)) (hi := (2937/20000 : ℝ)) (c := (18634197039236125681/18640000000000000000 : ℝ)) (alpha := (619349157659/372800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-422236783/2000000000 : ℝ)*X 0 0+(5396778723/10000000000 : ℝ)*X 0 1+(328867163/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672855963/5000000000 : ℝ)*X 1 0+(-108983339/500000000 : ℝ)*X 1 1+(5261874667/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336427991/2500000000 : ℝ)*X 2 0+(657734327/1250000000 : ℝ)*X 2 1+(-2179666797/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4348007061/10000000000 : ℝ)*X 0 0+(2106399313/5000000000 : ℝ)*X 0 1+(897482501/2000000000 : ℝ)*X 0 2+(4348007061/10000000000 : ℝ)*X 1 0+(2106399313/5000000000 : ℝ)*X 1 1+(897482501/2000000000 : ℝ)*X 1 2+(4348007061/10000000000 : ℝ)*X 2 0+(2106399313/5000000000 : ℝ)*X 2 1+(897482501/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2111189377/10000000000 : ℝ)*X 0 0+(2631123339/5000000000 : ℝ)*X 0 1+(2698202799/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1327812769/2500000000 : ℝ)*X 1 0+(-2045135527/10000000000 : ℝ)*X 1 1+(5396405351/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311251099/10000000000 : ℝ)*X 2 0+(5396405057/10000000000 : ℝ)*X 2 1+(-1022567949/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1087004787/2500000000 : ℝ)*X 0 0+(4486655219/10000000000 : ℝ)*X 0 1+(2106779553/5000000000 : ℝ)*X 0 2+(1087004787/2500000000 : ℝ)*X 1 0+(4486655219/10000000000 : ℝ)*X 1 1+(2106779553/5000000000 : ℝ)*X 1 2+(1087004787/2500000000 : ℝ)*X 2 0+(4486655219/10000000000 : ℝ)*X 2 1+(2106779553/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (94124061977264722872366657/23300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1358762879/100000000000000 : ℝ)*(base19) + (76768871/6250000000000 : ℝ)*(base23) + (3416009/1250000000000 : ℝ)*(upper3) + (97909059/100000000000000 : ℝ)*(upper4) + (125265917/100000000000000 : ℝ)*(upper5) + (138178060835899/2500000000000 : ℝ)*(major0) + (138178060835899/2500000000000 : ℝ)*(major1) + (138178060835899/2500000000000 : ℝ)*(major2) + (1482541307260147/20000000000000 : ℝ)*(sp0) + (3706367984972823/50000000000000 : ℝ)*(sp1) + (7412736100406589/100000000000000 : ℝ)*(sp2) + (182074498979439/5000000000000 : ℝ)*(sp3) + (3079240779/10000000000000 : ℝ)*(sp4) + (8711959649/50000000000000 : ℝ)*(sp7) + (1820753701754039/50000000000000 : ℝ)*(f.failure) + (296509493148341/4000000000000 : ℝ)*(f.sum) + (2452233893127/466000000000000000000000000 : ℝ)*base65 + (126711811680472219/46600000000000000000000000000000 : ℝ)*base67 + (381513564781872219/46600000000000000000000000000000 : ℝ)*base69 + (263770666105327781/46600000000000000000000000000000 : ℝ)*base72 + (1123517219949/466000000000000000000000000 : ℝ)*base73 + (385117228739327781/46600000000000000000000000000000 : ℝ)*base76 + (295820123665327781/46600000000000000000000000000000 : ℝ)*base78 + (507614928152927781/46600000000000000000000000000000 : ℝ)*base80 + (1178384561189/466000000000000000000000000 : ℝ)*base82 + (13616487/5000000000000000000000 : ℝ)*base90 + (13616487/5000000000000000000000 : ℝ)*base92 + (13616487/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (332070627371392577564437263/233000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (475504453/50000000000000 : ℝ)*(base19) + (1322006429/100000000000000 : ℝ)*(base23) + (197023851/100000000000000 : ℝ)*(lower3) + (237599129/100000000000000 : ℝ)*(lower4) + (1389445858399847/25000000000000 : ℝ)*(major0) + (1389445858399847/25000000000000 : ℝ)*(major1) + (1389445858399847/25000000000000 : ℝ)*(major2) + (2641233041/50000000000000 : ℝ)*(sp0) + (9696394507/25000000000000 : ℝ)*(sp1) + (1377676837/6250000000000 : ℝ)*(sp2) + (372692667009393/5000000000000 : ℝ)*(sp4) + (7453818886067009/100000000000000 : ℝ)*(sp5) + (3726917628909061/50000000000000 : ℝ)*(sp6) + (1830854098519149/50000000000000 : ℝ)*(sp7) + (1830854098519149/50000000000000 : ℝ)*(f.failure) + (3726929311326971/50000000000000 : ℝ)*(f.sum) + (10880253798533/4660000000000000000000000000 : ℝ)*base65 + (496894956296179193/466000000000000000000000000000000 : ℝ)*base68 + (4641334969032179193/466000000000000000000000000000000 : ℝ)*base70 + (5409869621304179193/466000000000000000000000000000000 : ℝ)*base72 + (18331394234033/4660000000000000000000000000 : ℝ)*base73 + (3068349964766179193/466000000000000000000000000000000 : ℝ)*base76 + (3544633954268179193/466000000000000000000000000000000 : ℝ)*base78 + (9091264948256179193/466000000000000000000000000000000 : ℝ)*base80 + (3602582355107/4660000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (7066883/5000000000000000000000 : ℝ)*base89 + (7066883/5000000000000000000000 : ℝ)*base91 + (7066883/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1260_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151781167/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2937/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10957/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11381/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1260_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1260_s5_0 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-527902001/2500000000 : ℝ)*x 0 + (1078395519/2000000000 : ℝ)*x 1 + (5266396743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527902001/2500000000 : ℝ)^8453 ≤ (12842757146521/100000000000000 : ℝ)^6405 := by
    have hnat : (527902001 : ℕ)^8453*100000000000000^6405 ≤ 12842757146521^6405*2500000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527902001 2500000000 12842757146521 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078395519/2000000000 : ℝ)^8453 ≤ (44256236047859/100000000000000 : ℝ)^6405 := by
    have hnat : (1078395519 : ℕ)^8453*100000000000000^6405 ≤ 44256236047859^6405*2000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078395519 2000000000 44256236047859 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266396743/10000000000 : ℝ)^8453 ≤ (42901006795227/100000000000000 : ℝ)^6405 := by
    have hnat : (5266396743 : ℕ)^8453*100000000000000^6405 ≤ 42901006795227^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266396743 10000000000 42901006795227 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-527902001/2500000000 : ℝ), (1078395519/2000000000 : ℝ), (5266396743/10000000000 : ℝ)] ![(12842757146521/100000000000000 : ℝ), (44256236047859/100000000000000 : ℝ), (42901006795227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-527902001/2500000000 : ℝ)|^8453 ≤ (12842757146521/100000000000000 : ℝ)^6405
        have hw : |(-527902001/2500000000 : ℝ)|=(527902001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078395519/2000000000 : ℝ)|^8453 ≤ (44256236047859/100000000000000 : ℝ)^6405
        have hw : |(1078395519/2000000000 : ℝ)|=(1078395519/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266396743/10000000000 : ℝ)|^8453 ≤ (42901006795227/100000000000000 : ℝ)^6405
        have hw : |(5266396743/10000000000 : ℝ)|=(5266396743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s5_1 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344494663/10000000000 : ℝ)*x 0 + (-43505841/200000000 : ℝ)*x 1 + (2633198387/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344494663/10000000000 : ℝ)^8453 ≤ (21871307649411/50000000000000 : ℝ)^6405 := by
    have hnat : (5344494663 : ℕ)^8453*50000000000000^6405 ≤ 21871307649411^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344494663 10000000000 21871307649411 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43505841/200000000 : ℝ)^8453 ≤ (13356377558439/100000000000000 : ℝ)^6405 := by
    have hnat : (43505841 : ℕ)^8453*100000000000000^6405 ≤ 13356377558439^6405*200000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43505841 200000000 13356377558439 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633198387/5000000000 : ℝ)^8453 ≤ (21450503564253/50000000000000 : ℝ)^6405 := by
    have hnat : (2633198387 : ℕ)^8453*50000000000000^6405 ≤ 21450503564253^6405*5000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633198387 5000000000 21450503564253 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344494663/10000000000 : ℝ), (-43505841/200000000 : ℝ), (2633198387/5000000000 : ℝ)] ![(21871307649411/50000000000000 : ℝ), (13356377558439/100000000000000 : ℝ), (21450503564253/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344494663/10000000000 : ℝ)|^8453 ≤ (21871307649411/50000000000000 : ℝ)^6405
        have hw : |(5344494663/10000000000 : ℝ)|=(5344494663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-43505841/200000000 : ℝ)|^8453 ≤ (13356377558439/100000000000000 : ℝ)^6405
        have hw : |(-43505841/200000000 : ℝ)|=(43505841/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633198387/5000000000 : ℝ)|^8453 ≤ (21450503564253/50000000000000 : ℝ)^6405
        have hw : |(2633198387/5000000000 : ℝ)|=(2633198387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s5_2 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068898977/2000000000 : ℝ)*x 0 + (1053279347/2000000000 : ℝ)*x 1 + (-1087645903/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068898977/2000000000 : ℝ)^8453 ≤ (21871308848393/50000000000000 : ℝ)^6405 := by
    have hnat : (1068898977 : ℕ)^8453*50000000000000^6405 ≤ 21871308848393^6405*2000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068898977 2000000000 21871308848393 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053279347/2000000000 : ℝ)^8453 ≤ (2145050335461/5000000000000 : ℝ)^6405 := by
    have hnat : (1053279347 : ℕ)^8453*5000000000000^6405 ≤ 2145050335461^6405*2000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053279347 2000000000 2145050335461 5000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1087645903/5000000000 : ℝ)^8453 ≤ (1335637558123/10000000000000 : ℝ)^6405 := by
    have hnat : (1087645903 : ℕ)^8453*10000000000000^6405 ≤ 1335637558123^6405*5000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087645903 5000000000 1335637558123 10000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068898977/2000000000 : ℝ), (1053279347/2000000000 : ℝ), (-1087645903/5000000000 : ℝ)] ![(21871308848393/50000000000000 : ℝ), (2145050335461/5000000000000 : ℝ), (1335637558123/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068898977/2000000000 : ℝ)|^8453 ≤ (21871308848393/50000000000000 : ℝ)^6405
        have hw : |(1068898977/2000000000 : ℝ)|=(1068898977/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053279347/2000000000 : ℝ)|^8453 ≤ (2145050335461/5000000000000 : ℝ)^6405
        have hw : |(1053279347/2000000000 : ℝ)|=(1053279347/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1087645903/5000000000 : ℝ)|^8453 ≤ (1335637558123/10000000000000 : ℝ)^6405
        have hw : |(-1087645903/5000000000 : ℝ)|=(1087645903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s5_3 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4348255117/10000000000 : ℝ)*x 0 + (527782083/1250000000 : ℝ)*x 1 + (4477891403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4348255117/10000000000 : ℝ)^8453 ≤ (16658510888991/50000000000000 : ℝ)^6405 := by
    have hnat : (4348255117 : ℕ)^8453*50000000000000^6405 ≤ 16658510888991^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4348255117 10000000000 16658510888991 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (527782083/1250000000 : ℝ)^8453 ≤ (32048850122271/100000000000000 : ℝ)^6405 := by
    have hnat : (527782083 : ℕ)^8453*100000000000000^6405 ≤ 32048850122271^6405*1250000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527782083 1250000000 32048850122271 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4477891403/10000000000 : ℝ)^8453 ≤ (8658532020043/25000000000000 : ℝ)^6405 := by
    have hnat : (4477891403 : ℕ)^8453*25000000000000^6405 ≤ 8658532020043^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4477891403 10000000000 8658532020043 25000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4348255117/10000000000 : ℝ), (527782083/1250000000 : ℝ), (4477891403/10000000000 : ℝ)] ![(16658510888991/50000000000000 : ℝ), (32048850122271/100000000000000 : ℝ), (8658532020043/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4348255117/10000000000 : ℝ)|^8453 ≤ (16658510888991/50000000000000 : ℝ)^6405
        have hw : |(4348255117/10000000000 : ℝ)|=(4348255117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(527782083/1250000000 : ℝ)|^8453 ≤ (32048850122271/100000000000000 : ℝ)^6405
        have hw : |(527782083/1250000000 : ℝ)|=(527782083/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4477891403/10000000000 : ℝ)|^8453 ≤ (8658532020043/25000000000000 : ℝ)^6405
        have hw : |(4477891403/10000000000 : ℝ)|=(4477891403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s5_4 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-65987901/312500000 : ℝ)*x 0 + (1053343873/2000000000 : ℝ)*x 1 + (5391653811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65987901/312500000 : ℝ)^8453 ≤ (6421397949707/50000000000000 : ℝ)^6405 := by
    have hnat : (65987901 : ℕ)^8453*50000000000000^6405 ≤ 6421397949707^6405*312500000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65987901 312500000 6421397949707 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053343873/2000000000 : ℝ)^8453 ≤ (42904475312633/100000000000000 : ℝ)^6405 := by
    have hnat : (1053343873 : ℕ)^8453*100000000000000^6405 ≤ 42904475312633^6405*2000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053343873 2000000000 42904475312633 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391653811/10000000000 : ℝ)^8453 ≤ (44252728776689/100000000000000 : ℝ)^6405 := by
    have hnat : (5391653811 : ℕ)^8453*100000000000000^6405 ≤ 44252728776689^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391653811 10000000000 44252728776689 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-65987901/312500000 : ℝ), (1053343873/2000000000 : ℝ), (5391653811/10000000000 : ℝ)] ![(6421397949707/50000000000000 : ℝ), (42904475312633/100000000000000 : ℝ), (44252728776689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-65987901/312500000 : ℝ)|^8453 ≤ (6421397949707/50000000000000 : ℝ)^6405
        have hw : |(-65987901/312500000 : ℝ)|=(65987901/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053343873/2000000000 : ℝ)|^8453 ≤ (42904475312633/100000000000000 : ℝ)^6405
        have hw : |(1053343873/2000000000 : ℝ)|=(1053343873/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391653811/10000000000 : ℝ)|^8453 ≤ (44252728776689/100000000000000 : ℝ)^6405
        have hw : |(5391653811/10000000000 : ℝ)|=(5391653811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s5_5 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312413881/10000000000 : ℝ)*x 0 + (-2050034829/10000000000 : ℝ)*x 1 + (2695826929/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312413881/10000000000 : ℝ)^8453 ≤ (10849105783913/25000000000000 : ℝ)^6405 := by
    have hnat : (5312413881 : ℕ)^8453*25000000000000^6405 ≤ 10849105783913^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312413881 10000000000 10849105783913 25000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2050034829/10000000000 : ℝ)^8453 ≤ (6175423781387/50000000000000 : ℝ)^6405 := by
    have hnat : (2050034829 : ℕ)^8453*50000000000000^6405 ≤ 6175423781387^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2050034829 10000000000 6175423781387 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695826929/5000000000 : ℝ)^8453 ≤ (8850545857159/20000000000000 : ℝ)^6405 := by
    have hnat : (2695826929 : ℕ)^8453*20000000000000^6405 ≤ 8850545857159^6405*5000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695826929 5000000000 8850545857159 20000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312413881/10000000000 : ℝ), (-2050034829/10000000000 : ℝ), (2695826929/5000000000 : ℝ)] ![(10849105783913/25000000000000 : ℝ), (6175423781387/50000000000000 : ℝ), (8850545857159/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312413881/10000000000 : ℝ)|^8453 ≤ (10849105783913/25000000000000 : ℝ)^6405
        have hw : |(5312413881/10000000000 : ℝ)|=(5312413881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2050034829/10000000000 : ℝ)|^8453 ≤ (6175423781387/50000000000000 : ℝ)^6405
        have hw : |(-2050034829/10000000000 : ℝ)|=(2050034829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695826929/5000000000 : ℝ)|^8453 ≤ (8850545857159/20000000000000 : ℝ)^6405
        have hw : |(2695826929/5000000000 : ℝ)|=(2695826929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s5_6 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312413773/10000000000 : ℝ)*x 0 + (5391653981/10000000000 : ℝ)*x 1 + (-256254351/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312413773/10000000000 : ℝ)^8453 ≤ (21698210985659/50000000000000 : ℝ)^6405 := by
    have hnat : (5312413773 : ℕ)^8453*50000000000000^6405 ≤ 21698210985659^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312413773 10000000000 21698210985659 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391653981/10000000000 : ℝ)^8453 ≤ (22126365309067/50000000000000 : ℝ)^6405 := by
    have hnat : (5391653981 : ℕ)^8453*50000000000000^6405 ≤ 22126365309067^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391653981 10000000000 22126365309067 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (256254351/1250000000 : ℝ)^8453 ≤ (12350847395801/100000000000000 : ℝ)^6405 := by
    have hnat : (256254351 : ℕ)^8453*100000000000000^6405 ≤ 12350847395801^6405*1250000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256254351 1250000000 12350847395801 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312413773/10000000000 : ℝ), (5391653981/10000000000 : ℝ), (-256254351/1250000000 : ℝ)] ![(21698210985659/50000000000000 : ℝ), (22126365309067/50000000000000 : ℝ), (12350847395801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312413773/10000000000 : ℝ)|^8453 ≤ (21698210985659/50000000000000 : ℝ)^6405
        have hw : |(5312413773/10000000000 : ℝ)|=(5312413773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391653981/10000000000 : ℝ)|^8453 ≤ (22126365309067/50000000000000 : ℝ)^6405
        have hw : |(5391653981/10000000000 : ℝ)|=(5391653981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-256254351/1250000000 : ℝ)|^8453 ≤ (12350847395801/100000000000000 : ℝ)^6405
        have hw : |(-256254351/1250000000 : ℝ)|=(256254351/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s5_7 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4348264901/10000000000 : ℝ)*x 0 + (4477235209/10000000000 : ℝ)*x 1 + (4222915399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4348264901/10000000000 : ℝ)^8453 ≤ (16658560357577/50000000000000 : ℝ)^6405 := by
    have hnat : (4348264901 : ℕ)^8453*50000000000000^6405 ≤ 16658560357577^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4348264901 10000000000 16658560357577 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4477235209/10000000000 : ℝ)^8453 ≤ (17313715044919/50000000000000 : ℝ)^6405 := by
    have hnat : (4477235209 : ℕ)^8453*50000000000000^6405 ≤ 17313715044919^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4477235209 10000000000 17313715044919 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4222915399/10000000000 : ℝ)^8453 ≤ (16027724583927/50000000000000 : ℝ)^6405 := by
    have hnat : (4222915399 : ℕ)^8453*50000000000000^6405 ≤ 16027724583927^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4222915399 10000000000 16027724583927 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4348264901/10000000000 : ℝ), (4477235209/10000000000 : ℝ), (4222915399/10000000000 : ℝ)] ![(16658560357577/50000000000000 : ℝ), (17313715044919/50000000000000 : ℝ), (16027724583927/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4348264901/10000000000 : ℝ)|^8453 ≤ (16658560357577/50000000000000 : ℝ)^6405
        have hw : |(4348264901/10000000000 : ℝ)|=(4348264901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4477235209/10000000000 : ℝ)|^8453 ≤ (17313715044919/50000000000000 : ℝ)^6405
        have hw : |(4477235209/10000000000 : ℝ)|=(4477235209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4222915399/10000000000 : ℝ)|^8453 ≤ (16027724583927/50000000000000 : ℝ)^6405
        have hw : |(4222915399/10000000000 : ℝ)|=(4222915399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1260_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151781167/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11381/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11477/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7069/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7119/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11381/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7119/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11381/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7119/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11381/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7119/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11381/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7119/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11381/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7119/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11381/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11381/100000 : ℝ) ^ (2113/512 : ℝ) ≤ (12732123678958659/100000000000000000000 : ℝ) := by
    have hpowers : (11381/100000 : ℝ)^2113 ≤ (12732123678958659/100000000000000000000 : ℝ)^512 := by
      have hnat : (11381 : ℕ)^2113*100000000000000000000^512 ≤ 12732123678958659^512*100000^2113 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11381 100000 12732123678958659 100000000000000000000 2113 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11381/100000 : ℝ)) (X := (12732123678958659/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7119/50000 : ℝ) ^ (2113/512 : ℝ) ≤ (32086596878518549/100000000000000000000 : ℝ) := by
    have hpowers : (7119/50000 : ℝ)^2113 ≤ (32086596878518549/100000000000000000000 : ℝ)^512 := by
      have hnat : (7119 : ℕ)^2113*100000000000000000000^512 ≤ 32086596878518549^512*50000^2113 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7119 50000 32086596878518549 100000000000000000000 2113 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7119/50000 : ℝ)) (X := (32086596878518549/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50012732123678958659/50000000000000000000 : ℝ) ≤ (400024678536843/400000000000000 : ℝ) ^ (2113/512 : ℝ) := by
    have hpowers : (50012732123678958659/50000000000000000000 : ℝ)^512 ≤ (400024678536843/400000000000000 : ℝ)^2113 := by
      have hnat : (50012732123678958659 : ℕ)^512*400000000000000^2113 ≤ 400024678536843^2113*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50012732123678958659 50000000000000000000 400024678536843 400000000000000 512 2113 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400024678536843/400000000000000 : ℝ)) (X := (50012732123678958659/50000000000000000000 : ℝ)) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505602340069684651/12500000000000000000 : ℝ) ≤ (2500271453971407/2500000000000000 : ℝ) ^ (2113/512 : ℝ) := by
    have hpowers : (12505602340069684651/12500000000000000000 : ℝ)^512 ≤ (2500271453971407/2500000000000000 : ℝ)^2113 := by
      have hnat : (12505602340069684651 : ℕ)^512*2500000000000000^2113 ≤ 2500271453971407^2113*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505602340069684651 12500000000000000000 2500271453971407 2500000000000000 512 2113 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500271453971407/2500000000000000 : ℝ)) (X := (12505602340069684651/12500000000000000000 : ℝ)) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032086596878518549/50000000000000000000 : ℝ) ≤ (10001554668350181/10000000000000000 : ℝ) ^ (2113/512 : ℝ) := by
    have hpowers : (50032086596878518549/50000000000000000000 : ℝ)^512 ≤ (10001554668350181/10000000000000000 : ℝ)^2113 := by
      have hnat : (50032086596878518549 : ℕ)^512*10000000000000000^2113 ≤ 10001554668350181^2113*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032086596878518549 50000000000000000000 10001554668350181 10000000000000000 512 2113 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001554668350181/10000000000000000 : ℝ)) (X := (50032086596878518549/50000000000000000000 : ℝ)) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(12732123678958659/100000000000000000000 : ℝ) ≤ ((28561090644695855889/28570000000000000000 : ℝ)+2*(468852464553/285700000000000 : ℝ)*(11381/100000 : ℝ))^(2113/512 : ℝ) := by
    rw [show (28561090644695855889/28570000000000000000 : ℝ)+2*(468852464553/285700000000000 : ℝ)*(11381/100000 : ℝ)=(400024678536843/400000000000000 : ℝ) by norm_num, show 1+2*(12732123678958659/100000000000000000000 : ℝ)=(50012732123678958659/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32086596878518549/100000000000000000000 : ℝ)+(12732123678958659/100000000000000000000 : ℝ) ≤ ((28561090644695855889/28570000000000000000 : ℝ)+(468852464553/285700000000000 : ℝ)*((7119/50000 : ℝ)+(11381/100000 : ℝ)))^(2113/512 : ℝ) := by
    rw [show (28561090644695855889/28570000000000000000 : ℝ)+(468852464553/285700000000000 : ℝ)*((7119/50000 : ℝ)+(11381/100000 : ℝ))=(2500271453971407/2500000000000000 : ℝ) by norm_num, show 1+(32086596878518549/100000000000000000000 : ℝ)+(12732123678958659/100000000000000000000 : ℝ)=(12505602340069684651/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32086596878518549/100000000000000000000 : ℝ) ≤ ((28561090644695855889/28570000000000000000 : ℝ)+2*(468852464553/285700000000000 : ℝ)*(7119/50000 : ℝ))^(2113/512 : ℝ) := by
    rw [show (28561090644695855889/28570000000000000000 : ℝ)+2*(468852464553/285700000000000 : ℝ)*(7119/50000 : ℝ)=(10001554668350181/10000000000000000 : ℝ) by norm_num, show 1+2*(32086596878518549/100000000000000000000 : ℝ)=(50032086596878518549/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (28561090644695855889/28570000000000000000 : ℝ)*(X 1 0+X 2 0)+(468852464553/285700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2113/512 : ℝ)) (lo := (11381/100000 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (28561090644695855889/28570000000000000000 : ℝ)) (alpha := (468852464553/285700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (28561090644695855889/28570000000000000000 : ℝ)*(X 0 1+X 2 1)+(468852464553/285700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2113/512 : ℝ)) (lo := (11381/100000 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (28561090644695855889/28570000000000000000 : ℝ)) (alpha := (468852464553/285700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (28561090644695855889/28570000000000000000 : ℝ)*(X 0 2+X 1 2)+(468852464553/285700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2113/512 : ℝ)) (lo := (11381/100000 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (28561090644695855889/28570000000000000000 : ℝ)) (alpha := (468852464553/285700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-527902001/2500000000 : ℝ)*X 0 0+(1078395519/2000000000 : ℝ)*X 0 1+(5266396743/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344494663/10000000000 : ℝ)*X 1 0+(-43505841/200000000 : ℝ)*X 1 1+(2633198387/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068898977/2000000000 : ℝ)*X 2 0+(1053279347/2000000000 : ℝ)*X 2 1+(-1087645903/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4348255117/10000000000 : ℝ)*X 0 0+(527782083/1250000000 : ℝ)*X 0 1+(4477891403/10000000000 : ℝ)*X 0 2+(4348255117/10000000000 : ℝ)*X 1 0+(527782083/1250000000 : ℝ)*X 1 1+(4477891403/10000000000 : ℝ)*X 1 2+(4348255117/10000000000 : ℝ)*X 2 0+(527782083/1250000000 : ℝ)*X 2 1+(4477891403/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-65987901/312500000 : ℝ)*X 0 0+(1053343873/2000000000 : ℝ)*X 0 1+(5391653811/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312413881/10000000000 : ℝ)*X 1 0+(-2050034829/10000000000 : ℝ)*X 1 1+(2695826929/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312413773/10000000000 : ℝ)*X 2 0+(5391653981/10000000000 : ℝ)*X 2 1+(-256254351/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4348264901/10000000000 : ℝ)*X 0 0+(4477235209/10000000000 : ℝ)*X 0 1+(4222915399/10000000000 : ℝ)*X 0 2+(4348264901/10000000000 : ℝ)*X 1 0+(4477235209/10000000000 : ℝ)*X 1 1+(4222915399/10000000000 : ℝ)*X 1 2+(4348264901/10000000000 : ℝ)*X 2 0+(4477235209/10000000000 : ℝ)*X 2 1+(4222915399/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (61886685554424703433319/7142500000000000000000000000 : ℝ) := by norm_num
    linear_combination (153468651/10000000000000 : ℝ)*(base19) + (1756230793/100000000000000 : ℝ)*(base23) + (15864261/25000000000000 : ℝ)*(lower2) + (165489971/50000000000000 : ℝ)*(upper5) + (2968742668557773/50000000000000 : ℝ)*(major0) + (2968742668557773/50000000000000 : ℝ)*(major1) + (2968742668557773/50000000000000 : ℝ)*(major2) + (24884489355153/312500000000 : ℝ)*(sp0) + (3981547513629799/50000000000000 : ℝ)*(sp1) + (1990774097345647/25000000000000 : ℝ)*(sp2) + (977963473376153/25000000000000 : ℝ)*(sp3) + (30775982211/50000000000000 : ℝ)*(sp4) + (197958409/12500000000000 : ℝ)*(sp5) + (9173147057/50000000000000 : ℝ)*(sp7) + (3911872239798727/100000000000000 : ℝ)*(f.failure) + (7963098145613381/100000000000000 : ℝ)*(f.sum) + (30562387698337/3571250000000000000000000000 : ℝ)*base65 + (5717558074658324803/1428500000000000000000000000000000 : ℝ)*base68 + (8710457317071675197/1428500000000000000000000000000000 : ℝ)*base69 + (680728500158324803/1428500000000000000000000000000000 : ℝ)*base72 + (28695593785557/3571250000000000000000000000 : ℝ)*base73 + (11577710081550675197/1428500000000000000000000000000000 : ℝ)*base75 + (15236192510567324803/1428500000000000000000000000000000 : ℝ)*base78 + (32344014537266675197/1428500000000000000000000000000000 : ℝ)*base79 + (1401854738739/446406250000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base86 + (29174409/10000000000000000000000 : ℝ)*base89 + (29174409/10000000000000000000000 : ℝ)*base91 + (29174409/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3815259677155101995108364129/357125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (418988061/25000000000000 : ℝ)*(base19) + (209575183/12500000000000 : ℝ)*(base23) + (223920067/100000000000000 : ℝ)*(upper3) + (3019691/5000000000000 : ℝ)*(lower4) + (1380959/1250000000000 : ℝ)*(upper5) + (2984061848806387/50000000000000 : ℝ)*(major0) + (2984061848806387/50000000000000 : ℝ)*(major1) + (2984061848806387/50000000000000 : ℝ)*(major2) + (46786689161/100000000000000 : ℝ)*(sp1) + (11002838859/20000000000000 : ℝ)*(sp2) + (8004188921779539/100000000000000 : ℝ)*(sp4) + (4002070229569067/50000000000000 : ℝ)*(sp5) + (400206611549189/5000000000000 : ℝ)*(sp6) + (1966029058668647/50000000000000 : ℝ)*(sp7) + (1966029058668647/50000000000000 : ℝ)*(f.failure) + (8004188921779539/100000000000000 : ℝ)*(f.sum) + (5166753647011/1785625000000000000000000000 : ℝ)*base66 + (12019754053042636957/1428500000000000000000000000000000 : ℝ)*base68 + (11625068436881636957/1428500000000000000000000000000000 : ℝ)*base70 + (3839529357422363043/1428500000000000000000000000000000 : ℝ)*base71 + (7947369203333/892812500000000000000000000 : ℝ)*base74 + (29932745088706136957/1428500000000000000000000000000000 : ℝ)*base76 + (3978361468490636957/1428500000000000000000000000000000 : ℝ)*base78 + (4184406225737636957/1428500000000000000000000000000000 : ℝ)*base80 + (30975718503331/7142500000000000000000000000 : ℝ)*base81 + (7971049/5000000000000000000000 : ℝ)*base89 + (7971049/5000000000000000000000 : ℝ)*base91 + (7971049/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1260_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151781167/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11381/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11477/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7069/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1260_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1260_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151781167/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16177/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2393/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11477/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7069/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1260_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1260_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1260_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151781167/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16177/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2393/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11477/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7069/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1260_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
