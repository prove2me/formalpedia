-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1417_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:50:14.936981+00:00
-- url     : https://prove2.me/submissions/ba7948fc-241b-4840-a3aa-67e3ba842eb6

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
theorem support_rectangle_w1417_s3_0 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-989887517/5000000000 : ℝ)*x 0 + (5418513547/10000000000 : ℝ)*x 1 + (209508099/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (989887517/5000000000 : ℝ)^4377 ≤ (241453562809/2000000000000 : ℝ)^3353 := by
    have hnat : (989887517 : ℕ)^4377*2000000000000^3353 ≤ 241453562809^3353*5000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      989887517 5000000000 241453562809 2000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5418513547/10000000000 : ℝ)^4377 ≤ (8987474127461/20000000000000 : ℝ)^3353 := by
    have hnat : (5418513547 : ℕ)^4377*20000000000000^3353 ≤ 8987474127461^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418513547 10000000000 8987474127461 20000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209508099/400000000 : ℝ)^4377 ≤ (42989951204893/100000000000000 : ℝ)^3353 := by
    have hnat : (209508099 : ℕ)^4377*100000000000000^3353 ≤ 42989951204893^3353*400000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209508099 400000000 42989951204893 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-989887517/5000000000 : ℝ), (5418513547/10000000000 : ℝ), (209508099/400000000 : ℝ)] ![(241453562809/2000000000000 : ℝ), (8987474127461/20000000000000 : ℝ), (42989951204893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-989887517/5000000000 : ℝ)|^4377 ≤ (241453562809/2000000000000 : ℝ)^3353
        have hw : |(-989887517/5000000000 : ℝ)|=(989887517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5418513547/10000000000 : ℝ)|^4377 ≤ (8987474127461/20000000000000 : ℝ)^3353
        have hw : |(5418513547/10000000000 : ℝ)|=(5418513547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(209508099/400000000 : ℝ)|^4377 ≤ (42989951204893/100000000000000 : ℝ)^3353
        have hw : |(209508099/400000000 : ℝ)|=(209508099/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_s3_1 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350070857/10000000000 : ℝ)*x 0 + (-2072027787/10000000000 : ℝ)*x 1 + (2618851217/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350070857/10000000000 : ℝ)^4377 ≤ (44197839232967/100000000000000 : ℝ)^3353 := by
    have hnat : (5350070857 : ℕ)^4377*100000000000000^3353 ≤ 44197839232967^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350070857 10000000000 44197839232967 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2072027787/10000000000 : ℝ)^4377 ≤ (12812209986791/100000000000000 : ℝ)^3353 := by
    have hnat : (2072027787 : ℕ)^4377*100000000000000^3353 ≤ 12812209986791^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072027787 10000000000 12812209986791 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2618851217/5000000000 : ℝ)^4377 ≤ (42989950765601/100000000000000 : ℝ)^3353 := by
    have hnat : (2618851217 : ℕ)^4377*100000000000000^3353 ≤ 42989950765601^3353*5000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2618851217 5000000000 42989950765601 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350070857/10000000000 : ℝ), (-2072027787/10000000000 : ℝ), (2618851217/5000000000 : ℝ)] ![(44197839232967/100000000000000 : ℝ), (12812209986791/100000000000000 : ℝ), (42989950765601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350070857/10000000000 : ℝ)|^4377 ≤ (44197839232967/100000000000000 : ℝ)^3353
        have hw : |(5350070857/10000000000 : ℝ)|=(5350070857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2072027787/10000000000 : ℝ)|^4377 ≤ (12812209986791/100000000000000 : ℝ)^3353
        have hw : |(-2072027787/10000000000 : ℝ)|=(2072027787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2618851217/5000000000 : ℝ)|^4377 ≤ (42989950765601/100000000000000 : ℝ)^3353
        have hw : |(2618851217/5000000000 : ℝ)|=(2618851217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_s3_2 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350070849/10000000000 : ℝ)*x 0 + (5237702449/10000000000 : ℝ)*x 1 + (-1036013889/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350070849/10000000000 : ℝ)^4377 ≤ (22098919573347/50000000000000 : ℝ)^3353 := by
    have hnat : (5350070849 : ℕ)^4377*50000000000000^3353 ≤ 22098919573347^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350070849 10000000000 22098919573347 50000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5237702449/10000000000 : ℝ)^4377 ≤ (21494975463159/50000000000000 : ℝ)^3353 := by
    have hnat : (5237702449 : ℕ)^4377*50000000000000^3353 ≤ 21494975463159^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237702449 10000000000 21494975463159 50000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036013889/5000000000 : ℝ)^4377 ≤ (2562441982829/20000000000000 : ℝ)^3353 := by
    have hnat : (1036013889 : ℕ)^4377*20000000000000^3353 ≤ 2562441982829^3353*5000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036013889 5000000000 2562441982829 20000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350070849/10000000000 : ℝ), (5237702449/10000000000 : ℝ), (-1036013889/5000000000 : ℝ)] ![(22098919573347/50000000000000 : ℝ), (21494975463159/50000000000000 : ℝ), (2562441982829/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350070849/10000000000 : ℝ)|^4377 ≤ (22098919573347/50000000000000 : ℝ)^3353
        have hw : |(5350070849/10000000000 : ℝ)|=(5350070849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5237702449/10000000000 : ℝ)|^4377 ≤ (21494975463159/50000000000000 : ℝ)^3353
        have hw : |(5237702449/10000000000 : ℝ)|=(5237702449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1036013889/5000000000 : ℝ)|^4377 ≤ (2562441982829/20000000000000 : ℝ)^3353
        have hw : |(-1036013889/5000000000 : ℝ)|=(1036013889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_s3_3 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4306690917/10000000000 : ℝ)*x 0 + (1028987911/2500000000 : ℝ)*x 1 + (4505387289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4306690917/10000000000 : ℝ)^4377 ≤ (16648759224413/50000000000000 : ℝ)^3353 := by
    have hnat : (4306690917 : ℕ)^4377*50000000000000^3353 ≤ 16648759224413^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4306690917 10000000000 16648759224413 50000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1028987911/2500000000 : ℝ)^4377 ≤ (31385582641251/100000000000000 : ℝ)^3353 := by
    have hnat : (1028987911 : ℕ)^4377*100000000000000^3353 ≤ 31385582641251^3353*2500000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028987911 2500000000 31385582641251 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4505387289/10000000000 : ℝ)^4377 ≤ (35316898894199/100000000000000 : ℝ)^3353 := by
    have hnat : (4505387289 : ℕ)^4377*100000000000000^3353 ≤ 35316898894199^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4505387289 10000000000 35316898894199 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4306690917/10000000000 : ℝ), (1028987911/2500000000 : ℝ), (4505387289/10000000000 : ℝ)] ![(16648759224413/50000000000000 : ℝ), (31385582641251/100000000000000 : ℝ), (35316898894199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4306690917/10000000000 : ℝ)|^4377 ≤ (16648759224413/50000000000000 : ℝ)^3353
        have hw : |(4306690917/10000000000 : ℝ)|=(4306690917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1028987911/2500000000 : ℝ)|^4377 ≤ (31385582641251/100000000000000 : ℝ)^3353
        have hw : |(1028987911/2500000000 : ℝ)|=(1028987911/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4505387289/10000000000 : ℝ)|^4377 ≤ (35316898894199/100000000000000 : ℝ)^3353
        have hw : |(4505387289/10000000000 : ℝ)|=(4505387289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_s3_4 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-98989533/500000000 : ℝ)*x 0 + (5238428141/10000000000 : ℝ)*x 1 + (5417783843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (98989533/500000000 : ℝ)^4377 ≤ (12072802528631/100000000000000 : ℝ)^3353 := by
    have hnat : (98989533 : ℕ)^4377*100000000000000^3353 ≤ 12072802528631^3353*500000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98989533 500000000 12072802528631 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5238428141/10000000000 : ℝ)^4377 ≤ (1343678952119/3125000000000 : ℝ)^3353 := by
    have hnat : (5238428141 : ℕ)^4377*3125000000000^3353 ≤ 1343678952119^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238428141 10000000000 1343678952119 3125000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5417783843/10000000000 : ℝ)^4377 ≤ (11232367744857/25000000000000 : ℝ)^3353 := by
    have hnat : (5417783843 : ℕ)^4377*25000000000000^3353 ≤ 11232367744857^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417783843 10000000000 11232367744857 25000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-98989533/500000000 : ℝ), (5238428141/10000000000 : ℝ), (5417783843/10000000000 : ℝ)] ![(12072802528631/100000000000000 : ℝ), (1343678952119/3125000000000 : ℝ), (11232367744857/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-98989533/500000000 : ℝ)|^4377 ≤ (12072802528631/100000000000000 : ℝ)^3353
        have hw : |(-98989533/500000000 : ℝ)|=(98989533/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5238428141/10000000000 : ℝ)|^4377 ≤ (1343678952119/3125000000000 : ℝ)^3353
        have hw : |(5238428141/10000000000 : ℝ)|=(5238428141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5417783843/10000000000 : ℝ)|^4377 ≤ (11232367744857/25000000000000 : ℝ)^3353
        have hw : |(5417783843/10000000000 : ℝ)|=(5417783843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_s3_5 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (331445079/625000000 : ℝ)*x 0 + (-29561663/156250000 : ℝ)*x 1 + (5417783847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331445079/625000000 : ℝ)^4377 ≤ (5461526160411/12500000000000 : ℝ)^3353 := by
    have hnat : (331445079 : ℕ)^4377*12500000000000^3353 ≤ 5461526160411^3353*625000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331445079 625000000 5461526160411 12500000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (29561663/156250000 : ℝ)^4377 ≤ (11378319677861/100000000000000 : ℝ)^3353 := by
    have hnat : (29561663 : ℕ)^4377*100000000000000^3353 ≤ 11378319677861^3353*156250000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29561663 156250000 11378319677861 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5417783847/10000000000 : ℝ)^4377 ≤ (44929471022731/100000000000000 : ℝ)^3353 := by
    have hnat : (5417783847 : ℕ)^4377*100000000000000^3353 ≤ 44929471022731^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417783847 10000000000 44929471022731 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331445079/625000000 : ℝ), (-29561663/156250000 : ℝ), (5417783847/10000000000 : ℝ)] ![(5461526160411/12500000000000 : ℝ), (11378319677861/100000000000000 : ℝ), (44929471022731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331445079/625000000 : ℝ)|^4377 ≤ (5461526160411/12500000000000 : ℝ)^3353
        have hw : |(331445079/625000000 : ℝ)|=(331445079/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-29561663/156250000 : ℝ)|^4377 ≤ (11378319677861/100000000000000 : ℝ)^3353
        have hw : |(-29561663/156250000 : ℝ)|=(29561663/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5417783847/10000000000 : ℝ)|^4377 ≤ (44929471022731/100000000000000 : ℝ)^3353
        have hw : |(5417783847/10000000000 : ℝ)|=(5417783847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_s3_6 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5303121139/10000000000 : ℝ)*x 0 + (2708891993/5000000000 : ℝ)*x 1 + (-472986603/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303121139/10000000000 : ℝ)^4377 ≤ (21846103969449/50000000000000 : ℝ)^3353 := by
    have hnat : (5303121139 : ℕ)^4377*50000000000000^3353 ≤ 21846103969449^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303121139 10000000000 21846103969449 50000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2708891993/5000000000 : ℝ)^4377 ≤ (44929472527491/100000000000000 : ℝ)^3353 := by
    have hnat : (2708891993 : ℕ)^4377*100000000000000^3353 ≤ 44929472527491^3353*5000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708891993 5000000000 44929472527491 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (472986603/2500000000 : ℝ)^4377 ≤ (5689159760423/50000000000000 : ℝ)^3353 := by
    have hnat : (472986603 : ℕ)^4377*50000000000000^3353 ≤ 5689159760423^3353*2500000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      472986603 2500000000 5689159760423 50000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303121139/10000000000 : ℝ), (2708891993/5000000000 : ℝ), (-472986603/2500000000 : ℝ)] ![(21846103969449/50000000000000 : ℝ), (44929472527491/100000000000000 : ℝ), (5689159760423/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303121139/10000000000 : ℝ)|^4377 ≤ (21846103969449/50000000000000 : ℝ)^3353
        have hw : |(5303121139/10000000000 : ℝ)|=(5303121139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2708891993/5000000000 : ℝ)|^4377 ≤ (44929472527491/100000000000000 : ℝ)^3353
        have hw : |(2708891993/5000000000 : ℝ)|=(2708891993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-472986603/2500000000 : ℝ)|^4377 ≤ (5689159760423/50000000000000 : ℝ)^3353
        have hw : |(-472986603/2500000000 : ℝ)|=(472986603/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_s3_7 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (172268993/400000000 : ℝ)*x 0 + (4503824619/10000000000 : ℝ)*x 1 + (2058761751/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (172268993/400000000 : ℝ)^4377 ≤ (16648930337749/50000000000000 : ℝ)^3353 := by
    have hnat : (172268993 : ℕ)^4377*50000000000000^3353 ≤ 16648930337749^3353*400000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172268993 400000000 16648930337749 50000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4503824619/10000000000 : ℝ)^4377 ≤ (11296290973/32000000000 : ℝ)^3353 := by
    have hnat : (4503824619 : ℕ)^4377*32000000000^3353 ≤ 11296290973^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503824619 10000000000 11296290973 32000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2058761751/5000000000 : ℝ)^4377 ≤ (7850307504661/25000000000000 : ℝ)^3353 := by
    have hnat : (2058761751 : ℕ)^4377*25000000000000^3353 ≤ 7850307504661^3353*5000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2058761751 5000000000 7850307504661 25000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(172268993/400000000 : ℝ), (4503824619/10000000000 : ℝ), (2058761751/5000000000 : ℝ)] ![(16648930337749/50000000000000 : ℝ), (11296290973/32000000000 : ℝ), (7850307504661/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(172268993/400000000 : ℝ)|^4377 ≤ (16648930337749/50000000000000 : ℝ)^3353
        have hw : |(172268993/400000000 : ℝ)|=(172268993/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4503824619/10000000000 : ℝ)|^4377 ≤ (11296290973/32000000000 : ℝ)^3353
        have hw : |(4503824619/10000000000 : ℝ)|=(4503824619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2058761751/5000000000 : ℝ)|^4377 ≤ (7850307504661/25000000000000 : ℝ)^3353
        have hw : |(2058761751/5000000000 : ℝ)|=(2058761751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1417_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19711417/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15837/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5151/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (89/800 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14953/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15837/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5151/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15837/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5151/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15837/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5151/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15837/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5151/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15837/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5151/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15837/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5151/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5151/50000 : ℝ) ^ (547/128 : ℝ) ≤ (6050369767195749/100000000000000000000 : ℝ) := by
    have hpowers : (5151/50000 : ℝ)^547 ≤ (6050369767195749/100000000000000000000 : ℝ)^128 := by
      have hnat : (5151 : ℕ)^547*100000000000000000000^128 ≤ 6050369767195749^128*50000^547 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5151 50000 6050369767195749 100000000000000000000 547 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5151/50000 : ℝ)) (X := (6050369767195749/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 547 128 (by norm_num) hpowers
    exact h
  have hpowhi : (15837/100000 : ℝ) ^ (547/128 : ℝ) ≤ (38006005778561881/100000000000000000000 : ℝ) := by
    have hpowers : (15837/100000 : ℝ)^547 ≤ (38006005778561881/100000000000000000000 : ℝ)^128 := by
      have hnat : (15837 : ℕ)^547*100000000000000000000^128 ≤ 38006005778561881^128*100000^547 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15837 100000 38006005778561881 100000000000000000000 547 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15837/100000 : ℝ)) (X := (38006005778561881/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 547 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006050369767195749/50000000000000000000 : ℝ) ≤ (10000283148607139/10000000000000000 : ℝ) ^ (547/128 : ℝ) := by
    have hpowers : (50006050369767195749/50000000000000000000 : ℝ)^128 ≤ (10000283148607139/10000000000000000 : ℝ)^547 := by
      have hnat : (50006050369767195749 : ℕ)^128*10000000000000000^547 ≤ 10000283148607139^547*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006050369767195749 50000000000000000000 10000283148607139 10000000000000000 128 547 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000283148607139/10000000000000000 : ℝ)) (X := (50006050369767195749/50000000000000000000 : ℝ)) (by norm_num) 547 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004405637554575763/10000000000000000000 : ℝ) ≤ (2500257690346563/2500000000000000 : ℝ) ^ (547/128 : ℝ) := by
    have hpowers : (10004405637554575763/10000000000000000000 : ℝ)^128 ≤ (2500257690346563/2500000000000000 : ℝ)^547 := by
      have hnat : (10004405637554575763 : ℕ)^128*2500000000000000^547 ≤ 2500257690346563^547*10000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004405637554575763 10000000000000000000 2500257690346563 2500000000000000 128 547 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500257690346563/2500000000000000 : ℝ)) (X := (10004405637554575763/10000000000000000000 : ℝ)) (by norm_num) 547 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50038006005778561881/50000000000000000000 : ℝ) ≤ (2000355674833073/2000000000000000 : ℝ) ^ (547/128 : ℝ) := by
    have hpowers : (50038006005778561881/50000000000000000000 : ℝ)^128 ≤ (2000355674833073/2000000000000000 : ℝ)^547 := by
      have hnat : (50038006005778561881 : ℕ)^128*2000000000000000^547 ≤ 2000355674833073^547*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50038006005778561881 50000000000000000000 2000355674833073 2000000000000000 128 547 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000355674833073/2000000000000000 : ℝ)) (X := (50038006005778561881/50000000000000000000 : ℝ)) (by norm_num) 547 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6050369767195749/100000000000000000000 : ℝ) ≤ ((18445387804613223371/18450000000000000000 : ℝ)+2*(747612779113/553500000000000 : ℝ)*(5151/50000 : ℝ))^(547/128 : ℝ) := by
    rw [show (18445387804613223371/18450000000000000000 : ℝ)+2*(747612779113/553500000000000 : ℝ)*(5151/50000 : ℝ)=(10000283148607139/10000000000000000 : ℝ) by norm_num, show 1+2*(6050369767195749/100000000000000000000 : ℝ)=(50006050369767195749/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(38006005778561881/100000000000000000000 : ℝ)+(6050369767195749/100000000000000000000 : ℝ) ≤ ((18445387804613223371/18450000000000000000 : ℝ)+(747612779113/553500000000000 : ℝ)*((15837/100000 : ℝ)+(5151/50000 : ℝ)))^(547/128 : ℝ) := by
    rw [show (18445387804613223371/18450000000000000000 : ℝ)+(747612779113/553500000000000 : ℝ)*((15837/100000 : ℝ)+(5151/50000 : ℝ))=(2500257690346563/2500000000000000 : ℝ) by norm_num, show 1+(38006005778561881/100000000000000000000 : ℝ)+(6050369767195749/100000000000000000000 : ℝ)=(10004405637554575763/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(38006005778561881/100000000000000000000 : ℝ) ≤ ((18445387804613223371/18450000000000000000 : ℝ)+2*(747612779113/553500000000000 : ℝ)*(15837/100000 : ℝ))^(547/128 : ℝ) := by
    rw [show (18445387804613223371/18450000000000000000 : ℝ)+2*(747612779113/553500000000000 : ℝ)*(15837/100000 : ℝ)=(2000355674833073/2000000000000000 : ℝ) by norm_num, show 1+2*(38006005778561881/100000000000000000000 : ℝ)=(50038006005778561881/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18445387804613223371/18450000000000000000 : ℝ)*(X 1 0+X 2 0)+(747612779113/553500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (547/128 : ℝ)) (lo := (5151/50000 : ℝ)) (hi := (15837/100000 : ℝ)) (c := (18445387804613223371/18450000000000000000 : ℝ)) (alpha := (747612779113/553500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18445387804613223371/18450000000000000000 : ℝ)*(X 0 1+X 2 1)+(747612779113/553500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (547/128 : ℝ)) (lo := (5151/50000 : ℝ)) (hi := (15837/100000 : ℝ)) (c := (18445387804613223371/18450000000000000000 : ℝ)) (alpha := (747612779113/553500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18445387804613223371/18450000000000000000 : ℝ)*(X 0 2+X 1 2)+(747612779113/553500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (547/128 : ℝ)) (lo := (5151/50000 : ℝ)) (hi := (15837/100000 : ℝ)) (c := (18445387804613223371/18450000000000000000 : ℝ)) (alpha := (747612779113/553500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-989887517/5000000000 : ℝ)*X 0 0+(5418513547/10000000000 : ℝ)*X 0 1+(209508099/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350070857/10000000000 : ℝ)*X 1 0+(-2072027787/10000000000 : ℝ)*X 1 1+(2618851217/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350070849/10000000000 : ℝ)*X 2 0+(5237702449/10000000000 : ℝ)*X 2 1+(-1036013889/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4306690917/10000000000 : ℝ)*X 0 0+(1028987911/2500000000 : ℝ)*X 0 1+(4505387289/10000000000 : ℝ)*X 0 2+(4306690917/10000000000 : ℝ)*X 1 0+(1028987911/2500000000 : ℝ)*X 1 1+(4505387289/10000000000 : ℝ)*X 1 2+(4306690917/10000000000 : ℝ)*X 2 0+(1028987911/2500000000 : ℝ)*X 2 1+(4505387289/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-98989533/500000000 : ℝ)*X 0 0+(5238428141/10000000000 : ℝ)*X 0 1+(5417783843/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((331445079/625000000 : ℝ)*X 1 0+(-29561663/156250000 : ℝ)*X 1 1+(5417783847/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5303121139/10000000000 : ℝ)*X 2 0+(2708891993/5000000000 : ℝ)*X 2 1+(-472986603/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((172268993/400000000 : ℝ)*X 0 0+(4503824619/10000000000 : ℝ)*X 0 1+(2058761751/5000000000 : ℝ)*X 0 2+(172268993/400000000 : ℝ)*X 1 0+(4503824619/10000000000 : ℝ)*X 1 1+(2058761751/5000000000 : ℝ)*X 1 2+(172268993/400000000 : ℝ)*X 2 0+(4503824619/10000000000 : ℝ)*X 2 1+(2058761751/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (279615639325555758711404987/153750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (222985573/50000000000000 : ℝ)*(base19) + (7214941/2000000000000 : ℝ)*(base23) + (91773233/100000000000000 : ℝ)*(upper3) + (20585489/50000000000000 : ℝ)*(upper4) + (46086741/100000000000000 : ℝ)*(upper5) + (2024617419278097/50000000000000 : ℝ)*(major0) + (2024617419278097/50000000000000 : ℝ)*(major1) + (2024617419278097/50000000000000 : ℝ)*(major2) + (553064089667077/10000000000000 : ℝ)*(sp0) + (2765322944560773/50000000000000 : ℝ)*(sp1) + (2765322987172821/50000000000000 : ℝ)*(sp2) + (256782038622629/10000000000000 : ℝ)*(sp3) + (2719210961/50000000000000 : ℝ)*(sp4) + (2895172121/100000000000000 : ℝ)*(sp7) + (641955820349603/25000000000000 : ℝ)*(f.failure) + (1382661583773173/25000000000000 : ℝ)*(f.sum) + (46044449909599/9225000000000000000000000000 : ℝ)*base65 + (1228104399919995013/922500000000000000000000000000000 : ℝ)*base68 + (550400234597504987/922500000000000000000000000000000 : ℝ)*base69 + (2893717088095004987/922500000000000000000000000000000 : ℝ)*base71 + (18170541363649/9225000000000000000000000000 : ℝ)*base73 + (12261538958382495013/922500000000000000000000000000000 : ℝ)*base76 + (1284290149864995013/922500000000000000000000000000000 : ℝ)*base78 + (16906775163304995013/922500000000000000000000000000000 : ℝ)*base80 + (14400240045437/4612500000000000000000000000 : ℝ)*base81 + (4267451/312500000000000000000 : ℝ)*base89 + (4267451/312500000000000000000 : ℝ)*base91 + (4267451/312500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6026029951525037686301404547/922500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (40451469/6250000000000 : ℝ)*(base19) + (127700811/20000000000000 : ℝ)*(base23) + (8667369/10000000000000 : ℝ)*(upper3) + (10963177/20000000000000 : ℝ)*(lower4) + (10640921/12500000000000 : ℝ)*(upper5) + (4082082201214819/100000000000000 : ℝ)*(major0) + (4082082201214819/100000000000000 : ℝ)*(major1) + (4082082201214819/100000000000000 : ℝ)*(major2) + (2355915703/20000000000000 : ℝ)*(sp1) + (10909047/78125000000 : ℝ)*(sp2) + (5575510740077359/100000000000000 : ℝ)*(sp4) + (278774915663767/5000000000000 : ℝ)*(sp5) + (696937017249143/12500000000000 : ℝ)*(sp6) + (51773068892191/2000000000000 : ℝ)*(sp7) + (51773068892191/2000000000000 : ℝ)*(f.failure) + (5575510740077359/100000000000000 : ℝ)*(f.sum) + (14314987433797/27675000000000000000000000000 : ℝ)*base65 + (18578645856553295453/5535000000000000000000000000000000 : ℝ)*base68 + (31543185958933295453/5535000000000000000000000000000000 : ℝ)*base70 + (2893419147586704547/5535000000000000000000000000000000 : ℝ)*base71 + (18158477557291/3459375000000000000000000000 : ℝ)*base74 + (1308545374711704547/5535000000000000000000000000000000 : ℝ)*base75 + (23611259018848295453/5535000000000000000000000000000000 : ℝ)*base78 + (11262727531228295453/5535000000000000000000000000000000 : ℝ)*base80 + (25153671805553/27675000000000000000000000000 : ℝ)*base82 + (94647/25000000000000000000 : ℝ)*base89 + (94647/25000000000000000000 : ℝ)*base91 + (94647/25000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1417_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19711417/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15837/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5151/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (89/800 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14953/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1417_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1417_s4_0 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-15845897/80000000 : ℝ)*x 0 + (2705167689/5000000000 : ℝ)*x 1 + (1311311861/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (15845897/80000000 : ℝ)^4377 ≤ (12080337265259/100000000000000 : ℝ)^3353 := by
    have hnat : (15845897 : ℕ)^4377*100000000000000^3353 ≤ 12080337265259^3353*80000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15845897 80000000 12080337265259 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705167689/5000000000 : ℝ)^4377 ≤ (44848853689543/100000000000000 : ℝ)^3353 := by
    have hnat : (2705167689 : ℕ)^4377*100000000000000^3353 ≤ 44848853689543^3353*5000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705167689 5000000000 44848853689543 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311311861/2500000000 : ℝ)^4377 ≤ (43070809032177/100000000000000 : ℝ)^3353 := by
    have hnat : (1311311861 : ℕ)^4377*100000000000000^3353 ≤ 43070809032177^3353*2500000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311311861 2500000000 43070809032177 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-15845897/80000000 : ℝ), (2705167689/5000000000 : ℝ), (1311311861/2500000000 : ℝ)] ![(12080337265259/100000000000000 : ℝ), (44848853689543/100000000000000 : ℝ), (43070809032177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-15845897/80000000 : ℝ)|^4377 ≤ (12080337265259/100000000000000 : ℝ)^3353
        have hw : |(-15845897/80000000 : ℝ)|=(15845897/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705167689/5000000000 : ℝ)|^4377 ≤ (44848853689543/100000000000000 : ℝ)^3353
        have hw : |(2705167689/5000000000 : ℝ)|=(2705167689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311311861/2500000000 : ℝ)|^4377 ≤ (43070809032177/100000000000000 : ℝ)^3353
        have hw : |(1311311861/2500000000 : ℝ)|=(1311311861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_s4_1 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347963957/10000000000 : ℝ)*x 0 + (-2064821337/10000000000 : ℝ)*x 1 + (5245247413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347963957/10000000000 : ℝ)^4377 ≤ (8835023909641/20000000000000 : ℝ)^3353 := by
    have hnat : (5347963957 : ℕ)^4377*20000000000000^3353 ≤ 8835023909641^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347963957 10000000000 8835023909641 20000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2064821337/10000000000 : ℝ)^4377 ≤ (3188517934369/25000000000000 : ℝ)^3353 := by
    have hnat : (2064821337 : ℕ)^4377*25000000000000^3353 ≤ 3188517934369^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064821337 10000000000 3188517934369 25000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245247413/10000000000 : ℝ)^4377 ≤ (43070808699883/100000000000000 : ℝ)^3353 := by
    have hnat : (5245247413 : ℕ)^4377*100000000000000^3353 ≤ 43070808699883^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245247413 10000000000 43070808699883 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347963957/10000000000 : ℝ), (-2064821337/10000000000 : ℝ), (5245247413/10000000000 : ℝ)] ![(8835023909641/20000000000000 : ℝ), (3188517934369/25000000000000 : ℝ), (43070808699883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347963957/10000000000 : ℝ)|^4377 ≤ (8835023909641/20000000000000 : ℝ)^3353
        have hw : |(5347963957/10000000000 : ℝ)|=(5347963957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2064821337/10000000000 : ℝ)|^4377 ≤ (3188517934369/25000000000000 : ℝ)^3353
        have hw : |(-2064821337/10000000000 : ℝ)|=(2064821337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245247413/10000000000 : ℝ)|^4377 ≤ (43070808699883/100000000000000 : ℝ)^3353
        have hw : |(5245247413/10000000000 : ℝ)|=(5245247413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_s4_2 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347963923/10000000000 : ℝ)*x 0 + (2098099/4000000 : ℝ)*x 1 + (-2064821267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347963923/10000000000 : ℝ)^4377 ≤ (44175119181589/100000000000000 : ℝ)^3353 := by
    have hnat : (5347963923 : ℕ)^4377*100000000000000^3353 ≤ 44175119181589^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347963923 10000000000 44175119181589 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2098099/4000000 : ℝ)^4377 ≤ (43070809632449/100000000000000 : ℝ)^3353 := by
    have hnat : (2098099 : ℕ)^4377*100000000000000^3353 ≤ 43070809632449^3353*4000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098099 4000000 43070809632449 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2064821267/10000000000 : ℝ)^4377 ≤ (255081423461/2000000000000 : ℝ)^3353 := by
    have hnat : (2064821267 : ℕ)^4377*2000000000000^3353 ≤ 255081423461^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064821267 10000000000 255081423461 2000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347963923/10000000000 : ℝ), (2098099/4000000 : ℝ), (-2064821267/10000000000 : ℝ)] ![(44175119181589/100000000000000 : ℝ), (43070809632449/100000000000000 : ℝ), (255081423461/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347963923/10000000000 : ℝ)|^4377 ≤ (44175119181589/100000000000000 : ℝ)^3353
        have hw : |(5347963923/10000000000 : ℝ)|=(5347963923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2098099/4000000 : ℝ)|^4377 ≤ (43070809632449/100000000000000 : ℝ)^3353
        have hw : |(2098099/4000000 : ℝ)|=(2098099/4000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2064821267/10000000000 : ℝ)|^4377 ≤ (255081423461/2000000000000 : ℝ)^3353
        have hw : |(-2064821267/10000000000 : ℝ)|=(2064821267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_s4_3 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1076820177/2500000000 : ℝ)*x 0 + (826562557/2000000000 : ℝ)*x 1 + (448838351/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076820177/2500000000 : ℝ)^4377 ≤ (33303471208913/100000000000000 : ℝ)^3353 := by
    have hnat : (1076820177 : ℕ)^4377*100000000000000^3353 ≤ 33303471208913^3353*2500000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076820177 2500000000 33303471208913 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (826562557/2000000000 : ℝ)^4377 ≤ (7888381342961/25000000000000 : ℝ)^3353 := by
    have hnat : (826562557 : ℕ)^4377*25000000000000^3353 ≤ 7888381342961^3353*2000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      826562557 2000000000 7888381342961 25000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (448838351/1000000000 : ℝ)^4377 ≤ (7028600682201/20000000000000 : ℝ)^3353 := by
    have hnat : (448838351 : ℕ)^4377*20000000000000^3353 ≤ 7028600682201^3353*1000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448838351 1000000000 7028600682201 20000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1076820177/2500000000 : ℝ), (826562557/2000000000 : ℝ), (448838351/1000000000 : ℝ)] ![(33303471208913/100000000000000 : ℝ), (7888381342961/25000000000000 : ℝ), (7028600682201/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1076820177/2500000000 : ℝ)|^4377 ≤ (33303471208913/100000000000000 : ℝ)^3353
        have hw : |(1076820177/2500000000 : ℝ)|=(1076820177/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(826562557/2000000000 : ℝ)|^4377 ≤ (7888381342961/25000000000000 : ℝ)^3353
        have hw : |(826562557/2000000000 : ℝ)|=(826562557/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(448838351/1000000000 : ℝ)|^4377 ≤ (7028600682201/20000000000000 : ℝ)^3353
        have hw : |(448838351/1000000000 : ℝ)|=(448838351/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_s4_4 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-495187299/2500000000 : ℝ)*x 0 + (524585273/1000000000 : ℝ)*x 1 + (1352431723/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (495187299/2500000000 : ℝ)^4377 ≤ (3020108342171/25000000000000 : ℝ)^3353 := by
    have hnat : (495187299 : ℕ)^4377*25000000000000^3353 ≤ 3020108342171^3353*2500000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      495187299 2500000000 3020108342171 25000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524585273/1000000000 : ℝ)^4377 ≤ (861545945867/2000000000000 : ℝ)^3353 := by
    have hnat : (524585273 : ℕ)^4377*2000000000000^3353 ≤ 861545945867^3353*1000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524585273 1000000000 861545945867 2000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352431723/2500000000 : ℝ)^4377 ≤ (5605283666729/12500000000000 : ℝ)^3353 := by
    have hnat : (1352431723 : ℕ)^4377*12500000000000^3353 ≤ 5605283666729^3353*2500000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352431723 2500000000 5605283666729 12500000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-495187299/2500000000 : ℝ), (524585273/1000000000 : ℝ), (1352431723/2500000000 : ℝ)] ![(3020108342171/25000000000000 : ℝ), (861545945867/2000000000000 : ℝ), (5605283666729/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-495187299/2500000000 : ℝ)|^4377 ≤ (3020108342171/25000000000000 : ℝ)^3353
        have hw : |(-495187299/2500000000 : ℝ)|=(495187299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524585273/1000000000 : ℝ)|^4377 ≤ (861545945867/2000000000000 : ℝ)^3353
        have hw : |(524585273/1000000000 : ℝ)|=(524585273/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352431723/2500000000 : ℝ)|^4377 ≤ (5605283666729/12500000000000 : ℝ)^3353
        have hw : |(1352431723/2500000000 : ℝ)|=(1352431723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_s4_5 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305096577/10000000000 : ℝ)*x 0 + (-1900341889/10000000000 : ℝ)*x 1 + (2704863461/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305096577/10000000000 : ℝ)^4377 ≤ (4371345522869/10000000000000 : ℝ)^3353 := by
    have hnat : (5305096577 : ℕ)^4377*10000000000000^3353 ≤ 4371345522869^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305096577 10000000000 4371345522869 10000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1900341889/10000000000 : ℝ)^4377 ≤ (11444275100251/100000000000000 : ℝ)^3353 := by
    have hnat : (1900341889 : ℕ)^4377*100000000000000^3353 ≤ 11444275100251^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1900341889 10000000000 11444275100251 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2704863461/5000000000 : ℝ)^4377 ≤ (11210567414613/25000000000000 : ℝ)^3353 := by
    have hnat : (2704863461 : ℕ)^4377*25000000000000^3353 ≤ 11210567414613^3353*5000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704863461 5000000000 11210567414613 25000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305096577/10000000000 : ℝ), (-1900341889/10000000000 : ℝ), (2704863461/5000000000 : ℝ)] ![(4371345522869/10000000000000 : ℝ), (11444275100251/100000000000000 : ℝ), (11210567414613/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305096577/10000000000 : ℝ)|^4377 ≤ (4371345522869/10000000000000 : ℝ)^3353
        have hw : |(5305096577/10000000000 : ℝ)|=(5305096577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1900341889/10000000000 : ℝ)|^4377 ≤ (11444275100251/100000000000000 : ℝ)^3353
        have hw : |(-1900341889/10000000000 : ℝ)|=(1900341889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2704863461/5000000000 : ℝ)|^4377 ≤ (11210567414613/25000000000000 : ℝ)^3353
        have hw : |(2704863461/5000000000 : ℝ)|=(2704863461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_s4_6 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305096607/10000000000 : ℝ)*x 0 + (2704863453/5000000000 : ℝ)*x 1 + (-1900341869/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305096607/10000000000 : ℝ)^4377 ≤ (2185672777569/5000000000000 : ℝ)^3353 := by
    have hnat : (5305096607 : ℕ)^4377*5000000000000^3353 ≤ 2185672777569^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305096607 10000000000 2185672777569 5000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704863453/5000000000 : ℝ)^4377 ≤ (44842269485321/100000000000000 : ℝ)^3353 := by
    have hnat : (2704863453 : ℕ)^4377*100000000000000^3353 ≤ 44842269485321^3353*5000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704863453 5000000000 44842269485321 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1900341869/10000000000 : ℝ)^4377 ≤ (11444274943023/100000000000000 : ℝ)^3353 := by
    have hnat : (1900341869 : ℕ)^4377*100000000000000^3353 ≤ 11444274943023^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1900341869 10000000000 11444274943023 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305096607/10000000000 : ℝ), (2704863453/5000000000 : ℝ), (-1900341869/10000000000 : ℝ)] ![(2185672777569/5000000000000 : ℝ), (44842269485321/100000000000000 : ℝ), (11444274943023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305096607/10000000000 : ℝ)|^4377 ≤ (2185672777569/5000000000000 : ℝ)^3353
        have hw : |(5305096607/10000000000 : ℝ)|=(5305096607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704863453/5000000000 : ℝ)|^4377 ≤ (44842269485321/100000000000000 : ℝ)^3353
        have hw : |(2704863453/5000000000 : ℝ)|=(2704863453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1900341869/10000000000 : ℝ)|^4377 ≤ (11444274943023/100000000000000 : ℝ)^3353
        have hw : |(-1900341869/10000000000 : ℝ)|=(1900341869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_s4_7 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (269206671/625000000 : ℝ)*x 0 + (1121769949/2500000000 : ℝ)*x 1 + (129191353/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269206671/625000000 : ℝ)^4377 ≤ (33303733915231/100000000000000 : ℝ)^3353 := by
    have hnat : (269206671 : ℕ)^4377*100000000000000^3353 ≤ 33303733915231^3353*625000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269206671 625000000 33303733915231 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1121769949/2500000000 : ℝ)^4377 ≤ (17564839393319/50000000000000 : ℝ)^3353 := by
    have hnat : (1121769949 : ℕ)^4377*50000000000000^3353 ≤ 17564839393319^3353*2500000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121769949 2500000000 17564839393319 50000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (129191353/312500000 : ℝ)^4377 ≤ (31566587286651/100000000000000 : ℝ)^3353 := by
    have hnat : (129191353 : ℕ)^4377*100000000000000^3353 ≤ 31566587286651^3353*312500000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129191353 312500000 31566587286651 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(269206671/625000000 : ℝ), (1121769949/2500000000 : ℝ), (129191353/312500000 : ℝ)] ![(33303733915231/100000000000000 : ℝ), (17564839393319/50000000000000 : ℝ), (31566587286651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(269206671/625000000 : ℝ)|^4377 ≤ (33303733915231/100000000000000 : ℝ)^3353
        have hw : |(269206671/625000000 : ℝ)|=(269206671/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1121769949/2500000000 : ℝ)|^4377 ≤ (17564839393319/50000000000000 : ℝ)^3353
        have hw : |(1121769949/2500000000 : ℝ)|=(1121769949/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(129191353/312500000 : ℝ)|^4377 ≤ (31566587286651/100000000000000 : ℝ)^3353
        have hw : |(129191353/312500000 : ℝ)|=(129191353/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1417_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19711417/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14953/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (89/800 : ℝ)*pair X i i ≤ pair X i h) :
    (5643/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7391/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14953/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (89/800 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14953/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (89/800 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14953/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (89/800 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14953/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (89/800 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14953/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (89/800 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14953/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (89/800 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (89/800 : ℝ) ^ (547/128 : ℝ) ≤ (2100693777005033/25000000000000000000 : ℝ) := by
    have hpowers : (89/800 : ℝ)^547 ≤ (2100693777005033/25000000000000000000 : ℝ)^128 := by
      have hnat : (89 : ℕ)^547*25000000000000000000^128 ≤ 2100693777005033^128*800^547 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        89 800 2100693777005033 25000000000000000000 547 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (89/800 : ℝ)) (X := (2100693777005033/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 547 128 (by norm_num) hpowers
    exact h
  have hpowhi : (14953/100000 : ℝ) ^ (547/128 : ℝ) ≤ (5946796916276901/20000000000000000000 : ℝ) := by
    have hpowers : (14953/100000 : ℝ)^547 ≤ (5946796916276901/20000000000000000000 : ℝ)^128 := by
      have hnat : (14953 : ℕ)^547*20000000000000000000^128 ≤ 5946796916276901^128*100000^547 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14953 100000 5946796916276901 20000000000000000000 547 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14953/100000 : ℝ)) (X := (5946796916276901/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 547 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502100693777005033/12500000000000000000 : ℝ) ≤ (10000393230710281/10000000000000000 : ℝ) ^ (547/128 : ℝ) := by
    have hpowers : (12502100693777005033/12500000000000000000 : ℝ)^128 ≤ (10000393230710281/10000000000000000 : ℝ)^547 := by
      have hnat : (12502100693777005033 : ℕ)^128*10000000000000000^547 ≤ 10000393230710281^547*12500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502100693777005033 12500000000000000000 10000393230710281 10000000000000000 128 547 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000393230710281/10000000000000000 : ℝ)) (X := (12502100693777005033/12500000000000000000 : ℝ)) (by norm_num) 547 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100038136759689404637/100000000000000000000 : ℝ) ≤ (1250111535475149/1250000000000000 : ℝ) ^ (547/128 : ℝ) := by
    have hpowers : (100038136759689404637/100000000000000000000 : ℝ)^128 ≤ (1250111535475149/1250000000000000 : ℝ)^547 := by
      have hnat : (100038136759689404637 : ℕ)^128*1250000000000000^547 ≤ 1250111535475149^547*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100038136759689404637 100000000000000000000 1250111535475149 1250000000000000 128 547 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250111535475149/1250000000000000 : ℝ)) (X := (100038136759689404637/100000000000000000000 : ℝ)) (by norm_num) 547 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (10005946796916276901/10000000000000000000 : ℝ) ≤ (10001391336892103/10000000000000000 : ℝ) ^ (547/128 : ℝ) := by
    have hpowers : (10005946796916276901/10000000000000000000 : ℝ)^128 ≤ (10001391336892103/10000000000000000 : ℝ)^547 := by
      have hnat : (10005946796916276901 : ℕ)^128*10000000000000000^547 ≤ 10001391336892103^547*10000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005946796916276901 10000000000000000000 10001391336892103 10000000000000000 128 547 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001391336892103/10000000000000000 : ℝ)) (X := (10005946796916276901/10000000000000000000 : ℝ)) (by norm_num) 547 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2100693777005033/25000000000000000000 : ℝ) ≤ ((19135200677943092959/19140000000000000000 : ℝ)+2*(499053090911/382800000000000 : ℝ)*(89/800 : ℝ))^(547/128 : ℝ) := by
    rw [show (19135200677943092959/19140000000000000000 : ℝ)+2*(499053090911/382800000000000 : ℝ)*(89/800 : ℝ)=(10000393230710281/10000000000000000 : ℝ) by norm_num, show 1+2*(2100693777005033/25000000000000000000 : ℝ)=(12502100693777005033/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5946796916276901/20000000000000000000 : ℝ)+(2100693777005033/25000000000000000000 : ℝ) ≤ ((19135200677943092959/19140000000000000000 : ℝ)+(499053090911/382800000000000 : ℝ)*((14953/100000 : ℝ)+(89/800 : ℝ)))^(547/128 : ℝ) := by
    rw [show (19135200677943092959/19140000000000000000 : ℝ)+(499053090911/382800000000000 : ℝ)*((14953/100000 : ℝ)+(89/800 : ℝ))=(1250111535475149/1250000000000000 : ℝ) by norm_num, show 1+(5946796916276901/20000000000000000000 : ℝ)+(2100693777005033/25000000000000000000 : ℝ)=(100038136759689404637/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5946796916276901/20000000000000000000 : ℝ) ≤ ((19135200677943092959/19140000000000000000 : ℝ)+2*(499053090911/382800000000000 : ℝ)*(14953/100000 : ℝ))^(547/128 : ℝ) := by
    rw [show (19135200677943092959/19140000000000000000 : ℝ)+2*(499053090911/382800000000000 : ℝ)*(14953/100000 : ℝ)=(10001391336892103/10000000000000000 : ℝ) by norm_num, show 1+2*(5946796916276901/20000000000000000000 : ℝ)=(10005946796916276901/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19135200677943092959/19140000000000000000 : ℝ)*(X 1 0+X 2 0)+(499053090911/382800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (547/128 : ℝ)) (lo := (89/800 : ℝ)) (hi := (14953/100000 : ℝ)) (c := (19135200677943092959/19140000000000000000 : ℝ)) (alpha := (499053090911/382800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19135200677943092959/19140000000000000000 : ℝ)*(X 0 1+X 2 1)+(499053090911/382800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (547/128 : ℝ)) (lo := (89/800 : ℝ)) (hi := (14953/100000 : ℝ)) (c := (19135200677943092959/19140000000000000000 : ℝ)) (alpha := (499053090911/382800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19135200677943092959/19140000000000000000 : ℝ)*(X 0 2+X 1 2)+(499053090911/382800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (547/128 : ℝ)) (lo := (89/800 : ℝ)) (hi := (14953/100000 : ℝ)) (c := (19135200677943092959/19140000000000000000 : ℝ)) (alpha := (499053090911/382800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-15845897/80000000 : ℝ)*X 0 0+(2705167689/5000000000 : ℝ)*X 0 1+(1311311861/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347963957/10000000000 : ℝ)*X 1 0+(-2064821337/10000000000 : ℝ)*X 1 1+(5245247413/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347963923/10000000000 : ℝ)*X 2 0+(2098099/4000000 : ℝ)*X 2 1+(-2064821267/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1076820177/2500000000 : ℝ)*X 0 0+(826562557/2000000000 : ℝ)*X 0 1+(448838351/1000000000 : ℝ)*X 0 2+(1076820177/2500000000 : ℝ)*X 1 0+(826562557/2000000000 : ℝ)*X 1 1+(448838351/1000000000 : ℝ)*X 1 2+(1076820177/2500000000 : ℝ)*X 2 0+(826562557/2000000000 : ℝ)*X 2 1+(448838351/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-495187299/2500000000 : ℝ)*X 0 0+(524585273/1000000000 : ℝ)*X 0 1+(1352431723/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305096577/10000000000 : ℝ)*X 1 0+(-1900341889/10000000000 : ℝ)*X 1 1+(2704863461/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305096607/10000000000 : ℝ)*X 2 0+(2704863453/5000000000 : ℝ)*X 2 1+(-1900341869/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((269206671/625000000 : ℝ)*X 0 0+(1121769949/2500000000 : ℝ)*X 0 1+(129191353/312500000 : ℝ)*X 0 2+(269206671/625000000 : ℝ)*X 1 0+(1121769949/2500000000 : ℝ)*X 1 1+(129191353/312500000 : ℝ)*X 1 2+(269206671/625000000 : ℝ)*X 2 0+(1121769949/2500000000 : ℝ)*X 2 1+(129191353/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (61555921252957824428973583/19937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (267129011/50000000000000 : ℝ)*(base19) + (230589251/50000000000000 : ℝ)*(base23) + (18487501/100000000000000 : ℝ)*(lower2) + (10214461/50000000000000 : ℝ)*(upper3) + (38034851/50000000000000 : ℝ)*(upper5) + (277181005952479/6250000000000 : ℝ)*(major0) + (277181005952479/6250000000000 : ℝ)*(major1) + (277181005952479/6250000000000 : ℝ)*(major2) + (302869428180539/5000000000000 : ℝ)*(sp0) + (6057401089927023/100000000000000 : ℝ)*(sp1) + (378587572687909/6250000000000 : ℝ)*(sp2) + (703096404613691/25000000000000 : ℝ)*(sp3) + (13060574267/100000000000000 : ℝ)*(sp4) + (4844924699/100000000000000 : ℝ)*(sp7) + (1406195231689731/50000000000000 : ℝ)*(f.failure) + (3028700812092523/50000000000000 : ℝ)*(f.sum) + (6323902114891/1196250000000000000000000000 : ℝ)*base66 + (2053996273492804639/119625000000000000000000000000000 : ℝ)*base68 + (1825410977897554639/119625000000000000000000000000000 : ℝ)*base70 + (993910924217929639/119625000000000000000000000000000 : ℝ)*base72 + (12164280572029/4785000000000000000000000000 : ℝ)*base74 + (77762342066929639/119625000000000000000000000000000 : ℝ)*base76 + (367147950550054639/119625000000000000000000000000000 : ℝ)*base78 + (502910561149054639/119625000000000000000000000000000 : ℝ)*base80 + (1212186081779/1196250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base86 + (2358827/625000000000000000000 : ℝ)*base89 + (2358827/625000000000000000000 : ℝ)*base91 + (2358827/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (93833351227278944061349779/15950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (907468963/100000000000000 : ℝ)*(base19) + (1045732841/100000000000000 : ℝ)*(base23) + (22764791/20000000000000 : ℝ)*(upper3) + (45195179/100000000000000 : ℝ)*(lower4) + (3982441/3125000000000 : ℝ)*(upper5) + (223386331773981/5000000000000 : ℝ)*(major0) + (223386331773981/5000000000000 : ℝ)*(major1) + (223386331773981/5000000000000 : ℝ)*(major2) + (19518285933/100000000000000 : ℝ)*(sp1) + (21815733413/100000000000000 : ℝ)*(sp2) + (762780389526333/12500000000000 : ℝ)*(sp4) + (762777836306971/12500000000000 : ℝ)*(sp5) + (610222025474441/10000000000000 : ℝ)*(sp6) + (708302489662403/25000000000000 : ℝ)*(sp7) + (708302489662403/25000000000000 : ℝ)*(f.failure) + (762780389526333/12500000000000 : ℝ)*(f.sum) + (37428696119/12760000000000000000000000 : ℝ)*base66 + (32908519451783407/31900000000000000000000000000000 : ℝ)*base68 + (60367540929016593/31900000000000000000000000000000 : ℝ)*base69 + (485434186158083407/31900000000000000000000000000000 : ℝ)*base72 + (149734140851/79750000000000000000000000 : ℝ)*base74 + (152863260341283407/31900000000000000000000000000000 : ℝ)*base76 + (19796321483116593/31900000000000000000000000000000 : ℝ)*base77 + (834724597107783407/31900000000000000000000000000000 : ℝ)*base80 + (38369964023/19937500000000000000000000 : ℝ)*base81 + (2255051/312500000000000000000 : ℝ)*base89 + (2255051/312500000000000000000 : ℝ)*base91 + (2255051/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1417_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19711417/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14953/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (89/800 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5643/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7391/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1417_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1417_s5_0 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1980884513/10000000000 : ℝ)*x 0 + (2704519057/5000000000 : ℝ)*x 1 + (2623223741/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1980884513/10000000000 : ℝ)^4377 ≤ (2416302141799/20000000000000 : ℝ)^3353 := by
    have hnat : (1980884513 : ℕ)^4377*20000000000000^3353 ≤ 2416302141799^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1980884513 10000000000 2416302141799 20000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704519057/5000000000 : ℝ)^4377 ≤ (4483481642071/10000000000000 : ℝ)^3353 := by
    have hnat : (2704519057 : ℕ)^4377*10000000000000^3353 ≤ 4483481642071^3353*5000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704519057 5000000000 4483481642071 10000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623223741/5000000000 : ℝ)^4377 ≤ (43083672859791/100000000000000 : ℝ)^3353 := by
    have hnat : (2623223741 : ℕ)^4377*100000000000000^3353 ≤ 43083672859791^3353*5000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623223741 5000000000 43083672859791 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1980884513/10000000000 : ℝ), (2704519057/5000000000 : ℝ), (2623223741/5000000000 : ℝ)] ![(2416302141799/20000000000000 : ℝ), (4483481642071/10000000000000 : ℝ), (43083672859791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1980884513/10000000000 : ℝ)|^4377 ≤ (2416302141799/20000000000000 : ℝ)^3353
        have hw : |(-1980884513/10000000000 : ℝ)|=(1980884513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704519057/5000000000 : ℝ)|^4377 ≤ (4483481642071/10000000000000 : ℝ)^3353
        have hw : |(2704519057/5000000000 : ℝ)|=(2704519057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623223741/5000000000 : ℝ)|^4377 ≤ (43083672859791/100000000000000 : ℝ)^3353
        have hw : |(2623223741/5000000000 : ℝ)|=(2623223741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_s5_1 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347628447/10000000000 : ℝ)*x 0 + (-1031836359/5000000000 : ℝ)*x 1 + (262322441/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347628447/10000000000 : ℝ)^4377 ≤ (44171501839761/100000000000000 : ℝ)^3353 := by
    have hnat : (5347628447 : ℕ)^4377*100000000000000^3353 ≤ 44171501839761^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347628447 10000000000 44171501839761 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1031836359/5000000000 : ℝ)^4377 ≤ (637240546913/5000000000000 : ℝ)^3353 := by
    have hnat : (1031836359 : ℕ)^4377*5000000000000^3353 ≤ 637240546913^3353*5000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031836359 5000000000 637240546913 5000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262322441/500000000 : ℝ)^4377 ≤ (43083687203007/100000000000000 : ℝ)^3353 := by
    have hnat : (262322441 : ℕ)^4377*100000000000000^3353 ≤ 43083687203007^3353*500000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262322441 500000000 43083687203007 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347628447/10000000000 : ℝ), (-1031836359/5000000000 : ℝ), (262322441/500000000 : ℝ)] ![(44171501839761/100000000000000 : ℝ), (637240546913/5000000000000 : ℝ), (43083687203007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347628447/10000000000 : ℝ)|^4377 ≤ (44171501839761/100000000000000 : ℝ)^3353
        have hw : |(5347628447/10000000000 : ℝ)|=(5347628447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1031836359/5000000000 : ℝ)|^4377 ≤ (637240546913/5000000000000 : ℝ)^3353
        have hw : |(-1031836359/5000000000 : ℝ)|=(1031836359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262322441/500000000 : ℝ)|^4377 ≤ (43083687203007/100000000000000 : ℝ)^3353
        have hw : |(262322441/500000000 : ℝ)|=(262322441/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_s5_2 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347628789/10000000000 : ℝ)*x 0 + (1311611987/2500000000 : ℝ)*x 1 + (-103183671/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347628789/10000000000 : ℝ)^4377 ≤ (22085752763707/50000000000000 : ℝ)^3353 := by
    have hnat : (5347628789 : ℕ)^4377*50000000000000^3353 ≤ 22085752763707^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347628789 10000000000 22085752763707 50000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311611987/2500000000 : ℝ)^4377 ≤ (43083677855261/100000000000000 : ℝ)^3353 := by
    have hnat : (1311611987 : ℕ)^4377*100000000000000^3353 ≤ 43083677855261^3353*2500000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311611987 2500000000 43083677855261 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (103183671/500000000 : ℝ)^4377 ≤ (1274481659769/10000000000000 : ℝ)^3353 := by
    have hnat : (103183671 : ℕ)^4377*10000000000000^3353 ≤ 1274481659769^3353*500000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103183671 500000000 1274481659769 10000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347628789/10000000000 : ℝ), (1311611987/2500000000 : ℝ), (-103183671/500000000 : ℝ)] ![(22085752763707/50000000000000 : ℝ), (43083677855261/100000000000000 : ℝ), (1274481659769/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347628789/10000000000 : ℝ)|^4377 ≤ (22085752763707/50000000000000 : ℝ)^3353
        have hw : |(5347628789/10000000000 : ℝ)|=(5347628789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311611987/2500000000 : ℝ)|^4377 ≤ (43083677855261/100000000000000 : ℝ)^3353
        have hw : |(1311611987/2500000000 : ℝ)|=(1311611987/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-103183671/500000000 : ℝ)|^4377 ≤ (1274481659769/10000000000000 : ℝ)^3353
        have hw : |(-103183671/500000000 : ℝ)|=(103183671/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_s5_3 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4307369827/10000000000 : ℝ)*x 0 + (4135492941/10000000000 : ℝ)*x 1 + (280355097/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4307369827/10000000000 : ℝ)^4377 ≤ (16652185354279/50000000000000 : ℝ)^3353 := by
    have hnat : (4307369827 : ℕ)^4377*50000000000000^3353 ≤ 16652185354279^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4307369827 10000000000 16652185354279 50000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4135492941/10000000000 : ℝ)^4377 ≤ (31580239943839/100000000000000 : ℝ)^3353 := by
    have hnat : (4135492941 : ℕ)^4377*100000000000000^3353 ≤ 31580239943839^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4135492941 10000000000 31580239943839 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (280355097/625000000 : ℝ)^4377 ≤ (3511538933127/10000000000000 : ℝ)^3353 := by
    have hnat : (280355097 : ℕ)^4377*10000000000000^3353 ≤ 3511538933127^3353*625000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280355097 625000000 3511538933127 10000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4307369827/10000000000 : ℝ), (4135492941/10000000000 : ℝ), (280355097/625000000 : ℝ)] ![(16652185354279/50000000000000 : ℝ), (31580239943839/100000000000000 : ℝ), (3511538933127/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4307369827/10000000000 : ℝ)|^4377 ≤ (16652185354279/50000000000000 : ℝ)^3353
        have hw : |(4307369827/10000000000 : ℝ)|=(4307369827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4135492941/10000000000 : ℝ)|^4377 ≤ (31580239943839/100000000000000 : ℝ)^3353
        have hw : |(4135492941/10000000000 : ℝ)|=(4135492941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(280355097/625000000 : ℝ)|^4377 ≤ (3511538933127/10000000000000 : ℝ)^3353
        have hw : |(280355097/625000000 : ℝ)|=(280355097/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_s5_4 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1980895949/10000000000 : ℝ)*x 0 + (5247035339/10000000000 : ℝ)*x 1 + (216337891/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1980895949/10000000000 : ℝ)^4377 ≤ (3020400439731/25000000000000 : ℝ)^3353 := by
    have hnat : (1980895949 : ℕ)^4377*25000000000000^3353 ≤ 3020400439731^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1980895949 10000000000 3020400439731 25000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247035339/10000000000 : ℝ)^4377 ≤ (43089974730769/100000000000000 : ℝ)^3353 := by
    have hnat : (5247035339 : ℕ)^4377*100000000000000^3353 ≤ 43089974730769^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247035339 10000000000 43089974730769 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216337891/400000000 : ℝ)^4377 ≤ (44828423486167/100000000000000 : ℝ)^3353 := by
    have hnat : (216337891 : ℕ)^4377*100000000000000^3353 ≤ 44828423486167^3353*400000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216337891 400000000 44828423486167 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1980895949/10000000000 : ℝ), (5247035339/10000000000 : ℝ), (216337891/400000000 : ℝ)] ![(3020400439731/25000000000000 : ℝ), (43089974730769/100000000000000 : ℝ), (44828423486167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1980895949/10000000000 : ℝ)|^4377 ≤ (3020400439731/25000000000000 : ℝ)^3353
        have hw : |(-1980895949/10000000000 : ℝ)|=(1980895949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247035339/10000000000 : ℝ)|^4377 ≤ (43089974730769/100000000000000 : ℝ)^3353
        have hw : |(5247035339/10000000000 : ℝ)|=(5247035339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216337891/400000000 : ℝ)|^4377 ≤ (44828423486167/100000000000000 : ℝ)^3353
        have hw : |(216337891/400000000 : ℝ)|=(216337891/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_s5_5 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305410151/10000000000 : ℝ)*x 0 + (-1901673981/10000000000 : ℝ)*x 1 + (216337891/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305410151/10000000000 : ℝ)^4377 ≤ (21858414085061/50000000000000 : ℝ)^3353 := by
    have hnat : (5305410151 : ℕ)^4377*50000000000000^3353 ≤ 21858414085061^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305410151 10000000000 21858414085061 50000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1901673981/10000000000 : ℝ)^4377 ≤ (22909496641/200000000000 : ℝ)^3353 := by
    have hnat : (1901673981 : ℕ)^4377*200000000000^3353 ≤ 22909496641^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1901673981 10000000000 22909496641 200000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216337891/400000000 : ℝ)^4377 ≤ (44828423486167/100000000000000 : ℝ)^3353 := by
    have hnat : (216337891 : ℕ)^4377*100000000000000^3353 ≤ 44828423486167^3353*400000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216337891 400000000 44828423486167 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305410151/10000000000 : ℝ), (-1901673981/10000000000 : ℝ), (216337891/400000000 : ℝ)] ![(21858414085061/50000000000000 : ℝ), (22909496641/200000000000 : ℝ), (44828423486167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305410151/10000000000 : ℝ)|^4377 ≤ (21858414085061/50000000000000 : ℝ)^3353
        have hw : |(5305410151/10000000000 : ℝ)|=(5305410151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1901673981/10000000000 : ℝ)|^4377 ≤ (22909496641/200000000000 : ℝ)^3353
        have hw : |(-1901673981/10000000000 : ℝ)|=(1901673981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216337891/400000000 : ℝ)|^4377 ≤ (44828423486167/100000000000000 : ℝ)^3353
        have hw : |(216337891/400000000 : ℝ)|=(216337891/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_s5_6 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305410151/10000000000 : ℝ)*x 0 + (1352111819/2500000000 : ℝ)*x 1 + (-1901673981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305410151/10000000000 : ℝ)^4377 ≤ (21858414085061/50000000000000 : ℝ)^3353 := by
    have hnat : (5305410151 : ℕ)^4377*50000000000000^3353 ≤ 21858414085061^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305410151 10000000000 21858414085061 50000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352111819/2500000000 : ℝ)^4377 ≤ (44828423496987/100000000000000 : ℝ)^3353 := by
    have hnat : (1352111819 : ℕ)^4377*100000000000000^3353 ≤ 44828423496987^3353*2500000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352111819 2500000000 44828423496987 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1901673981/10000000000 : ℝ)^4377 ≤ (22909496641/200000000000 : ℝ)^3353 := by
    have hnat : (1901673981 : ℕ)^4377*200000000000^3353 ≤ 22909496641^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1901673981 10000000000 22909496641 200000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305410151/10000000000 : ℝ), (1352111819/2500000000 : ℝ), (-1901673981/10000000000 : ℝ)] ![(21858414085061/50000000000000 : ℝ), (44828423496987/100000000000000 : ℝ), (22909496641/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305410151/10000000000 : ℝ)|^4377 ≤ (21858414085061/50000000000000 : ℝ)^3353
        have hw : |(5305410151/10000000000 : ℝ)|=(5305410151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352111819/2500000000 : ℝ)|^4377 ≤ (44828423496987/100000000000000 : ℝ)^3353
        have hw : |(1352111819/2500000000 : ℝ)|=(1352111819/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1901673981/10000000000 : ℝ)|^4377 ≤ (22909496641/200000000000 : ℝ)^3353
        have hw : |(-1901673981/10000000000 : ℝ)|=(1901673981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_s5_7 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4307394371/10000000000 : ℝ)*x 0 + (2242208661/5000000000 : ℝ)*x 1 + (206838199/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4307394371/10000000000 : ℝ)^4377 ≤ (3330461843809/10000000000000 : ℝ)^3353 := by
    have hnat : (4307394371 : ℕ)^4377*10000000000000^3353 ≤ 3330461843809^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4307394371 10000000000 3330461843809 10000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2242208661/5000000000 : ℝ)^4377 ≤ (35102470612561/100000000000000 : ℝ)^3353 := by
    have hnat : (2242208661 : ℕ)^4377*100000000000000^3353 ≤ 35102470612561^3353*5000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242208661 5000000000 35102470612561 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (206838199/500000000 : ℝ)^4377 ≤ (31592910929269/100000000000000 : ℝ)^3353 := by
    have hnat : (206838199 : ℕ)^4377*100000000000000^3353 ≤ 31592910929269^3353*500000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206838199 500000000 31592910929269 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4307394371/10000000000 : ℝ), (2242208661/5000000000 : ℝ), (206838199/500000000 : ℝ)] ![(3330461843809/10000000000000 : ℝ), (35102470612561/100000000000000 : ℝ), (31592910929269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4307394371/10000000000 : ℝ)|^4377 ≤ (3330461843809/10000000000000 : ℝ)^3353
        have hw : |(4307394371/10000000000 : ℝ)|=(4307394371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2242208661/5000000000 : ℝ)|^4377 ≤ (35102470612561/100000000000000 : ℝ)^3353
        have hw : |(2242208661/5000000000 : ℝ)|=(2242208661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(206838199/500000000 : ℝ)|^4377 ≤ (31592910929269/100000000000000 : ℝ)^3353
        have hw : |(206838199/500000000 : ℝ)|=(206838199/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1417_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19711417/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7391/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5643/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11311/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2951/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7391/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5643/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7391/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5643/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7391/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5643/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7391/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5643/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7391/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5643/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7391/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5643/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5643/50000 : ℝ) ^ (547/128 : ℝ) ≤ (2233721946555737/25000000000000000000 : ℝ) := by
    have hpowers : (5643/50000 : ℝ)^547 ≤ (2233721946555737/25000000000000000000 : ℝ)^128 := by
      have hnat : (5643 : ℕ)^547*25000000000000000000^128 ≤ 2233721946555737^128*50000^547 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5643 50000 2233721946555737 25000000000000000000 547 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5643/50000 : ℝ)) (X := (2233721946555737/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 547 128 (by norm_num) hpowers
    exact h
  have hpowhi : (7391/50000 : ℝ) ^ (547/128 : ℝ) ≤ (28307838750962183/100000000000000000000 : ℝ) := by
    have hpowers : (7391/50000 : ℝ)^547 ≤ (28307838750962183/100000000000000000000 : ℝ)^128 := by
      have hnat : (7391 : ℕ)^547*100000000000000000000^128 ≤ 28307838750962183^128*50000^547 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7391 50000 28307838750962183 100000000000000000000 547 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7391/50000 : ℝ)) (X := (28307838750962183/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 547 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502233721946555737/12500000000000000000 : ℝ) ≤ (10000418130665941/10000000000000000 : ℝ) ^ (547/128 : ℝ) := by
    have hpowers : (12502233721946555737/12500000000000000000 : ℝ)^128 ≤ (10000418130665941/10000000000000000 : ℝ)^547 := by
      have hnat : (12502233721946555737 : ℕ)^128*10000000000000000^547 ≤ 10000418130665941^547*12500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502233721946555737 12500000000000000000 10000418130665941 10000000000000000 128 547 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000418130665941/10000000000000000 : ℝ)) (X := (12502233721946555737/12500000000000000000 : ℝ)) (by norm_num) 547 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100037242726537185131/100000000000000000000 : ℝ) ≤ (2000174273827277/2000000000000000 : ℝ) ^ (547/128 : ℝ) := by
    have hpowers : (100037242726537185131/100000000000000000000 : ℝ)^128 ≤ (2000174273827277/2000000000000000 : ℝ)^547 := by
      have hnat : (100037242726537185131 : ℕ)^128*2000000000000000^547 ≤ 2000174273827277^547*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100037242726537185131 100000000000000000000 2000174273827277 2000000000000000 128 547 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000174273827277/2000000000000000 : ℝ)) (X := (100037242726537185131/100000000000000000000 : ℝ)) (by norm_num) 547 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50028307838750962183/50000000000000000000 : ℝ) ≤ (10001324607606829/10000000000000000 : ℝ) ^ (547/128 : ℝ) := by
    have hpowers : (50028307838750962183/50000000000000000000 : ℝ)^128 ≤ (10001324607606829/10000000000000000 : ℝ)^547 := by
      have hnat : (50028307838750962183 : ℕ)^128*10000000000000000^547 ≤ 10001324607606829^547*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028307838750962183 50000000000000000000 10001324607606829 10000000000000000 128 547 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001324607606829/10000000000000000 : ℝ)) (X := (50028307838750962183/50000000000000000000 : ℝ)) (by norm_num) 547 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2233721946555737/25000000000000000000 : ℝ) ≤ ((229942311092455709/230000000000000000 : ℝ)+2*(113309617611/87400000000000 : ℝ)*(5643/50000 : ℝ))^(547/128 : ℝ) := by
    rw [show (229942311092455709/230000000000000000 : ℝ)+2*(113309617611/87400000000000 : ℝ)*(5643/50000 : ℝ)=(10000418130665941/10000000000000000 : ℝ) by norm_num, show 1+2*(2233721946555737/25000000000000000000 : ℝ)=(12502233721946555737/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28307838750962183/100000000000000000000 : ℝ)+(2233721946555737/25000000000000000000 : ℝ) ≤ ((229942311092455709/230000000000000000 : ℝ)+(113309617611/87400000000000 : ℝ)*((7391/50000 : ℝ)+(5643/50000 : ℝ)))^(547/128 : ℝ) := by
    rw [show (229942311092455709/230000000000000000 : ℝ)+(113309617611/87400000000000 : ℝ)*((7391/50000 : ℝ)+(5643/50000 : ℝ))=(2000174273827277/2000000000000000 : ℝ) by norm_num, show 1+(28307838750962183/100000000000000000000 : ℝ)+(2233721946555737/25000000000000000000 : ℝ)=(100037242726537185131/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28307838750962183/100000000000000000000 : ℝ) ≤ ((229942311092455709/230000000000000000 : ℝ)+2*(113309617611/87400000000000 : ℝ)*(7391/50000 : ℝ))^(547/128 : ℝ) := by
    rw [show (229942311092455709/230000000000000000 : ℝ)+2*(113309617611/87400000000000 : ℝ)*(7391/50000 : ℝ)=(10001324607606829/10000000000000000 : ℝ) by norm_num, show 1+2*(28307838750962183/100000000000000000000 : ℝ)=(50028307838750962183/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (229942311092455709/230000000000000000 : ℝ)*(X 1 0+X 2 0)+(113309617611/87400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (547/128 : ℝ)) (lo := (5643/50000 : ℝ)) (hi := (7391/50000 : ℝ)) (c := (229942311092455709/230000000000000000 : ℝ)) (alpha := (113309617611/87400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (229942311092455709/230000000000000000 : ℝ)*(X 0 1+X 2 1)+(113309617611/87400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (547/128 : ℝ)) (lo := (5643/50000 : ℝ)) (hi := (7391/50000 : ℝ)) (c := (229942311092455709/230000000000000000 : ℝ)) (alpha := (113309617611/87400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (229942311092455709/230000000000000000 : ℝ)*(X 0 2+X 1 2)+(113309617611/87400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (547/128 : ℝ)) (lo := (5643/50000 : ℝ)) (hi := (7391/50000 : ℝ)) (c := (229942311092455709/230000000000000000 : ℝ)) (alpha := (113309617611/87400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1980884513/10000000000 : ℝ)*X 0 0+(2704519057/5000000000 : ℝ)*X 0 1+(2623223741/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347628447/10000000000 : ℝ)*X 1 0+(-1031836359/5000000000 : ℝ)*X 1 1+(262322441/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347628789/10000000000 : ℝ)*X 2 0+(1311611987/2500000000 : ℝ)*X 2 1+(-103183671/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4307369827/10000000000 : ℝ)*X 0 0+(4135492941/10000000000 : ℝ)*X 0 1+(280355097/625000000 : ℝ)*X 0 2+(4307369827/10000000000 : ℝ)*X 1 0+(4135492941/10000000000 : ℝ)*X 1 1+(280355097/625000000 : ℝ)*X 1 2+(4307369827/10000000000 : ℝ)*X 2 0+(4135492941/10000000000 : ℝ)*X 2 1+(280355097/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1980895949/10000000000 : ℝ)*X 0 0+(5247035339/10000000000 : ℝ)*X 0 1+(216337891/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305410151/10000000000 : ℝ)*X 1 0+(-1901673981/10000000000 : ℝ)*X 1 1+(216337891/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305410151/10000000000 : ℝ)*X 2 0+(1352111819/2500000000 : ℝ)*X 2 1+(-1901673981/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4307394371/10000000000 : ℝ)*X 0 0+(2242208661/5000000000 : ℝ)*X 0 1+(206838199/500000000 : ℝ)*X 0 2+(4307394371/10000000000 : ℝ)*X 1 0+(2242208661/5000000000 : ℝ)*X 1 1+(206838199/500000000 : ℝ)*X 1 2+(4307394371/10000000000 : ℝ)*X 2 0+(2242208661/5000000000 : ℝ)*X 2 1+(206838199/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20879743353699996516061317/2185000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1249663773/100000000000000 : ℝ)*(base19) + (55066939/3125000000000 : ℝ)*(base23) + (32360151/6250000000000 : ℝ)*(upper3) + (88131053/100000000000000 : ℝ)*(lower4) + (90061829730209/2000000000000 : ℝ)*(major0) + (90061829730209/2000000000000 : ℝ)*(major1) + (90061829730209/2000000000000 : ℝ)*(major2) + (6150490559598077/100000000000000 : ℝ)*(sp0) + (6150544817086559/100000000000000 : ℝ)*(sp1) + (615053851917099/10000000000000 : ℝ)*(sp2) + (356952018277743/12500000000000 : ℝ)*(sp3) + (433649627/781250000000 : ℝ)*(sp4) + (1157087459/20000000000000 : ℝ)*(sp6) + (20441517061/100000000000000 : ℝ)*(sp7) + (1427818293869503/50000000000000 : ℝ)*(f.failure) + (1537636516687583/25000000000000 : ℝ)*(f.sum) + (2440670173557/437000000000000000000000000 : ℝ)*base65 + (6893926719480439/8740000000000000000000000000000 : ℝ)*base67 + (44582268679279561/8740000000000000000000000000000 : ℝ)*base70 + (8364205198679561/8740000000000000000000000000000 : ℝ)*base72 + (1884292388287/437000000000000000000000000 : ℝ)*base73 + (38651443348119561/8740000000000000000000000000000 : ℝ)*base76 + (33140958353359561/8740000000000000000000000000000 : ℝ)*base78 + (135205410284239561/8740000000000000000000000000000 : ℝ)*base80 + (809603637697/218500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (4715751/625000000000000000000 : ℝ)*base89 + (4715751/625000000000000000000 : ℝ)*base91 + (4715751/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (400377007344052062669/54625000000000000000000000 : ℝ) := by norm_num
    linear_combination (622639969/50000000000000 : ℝ)*(base19) + (1352493067/100000000000000 : ℝ)*(base23) + (149882733/100000000000000 : ℝ)*(upper3) + (48554631/100000000000000 : ℝ)*(lower4) + (9430707/6250000000000 : ℝ)*(upper5) + (56698475582829/1250000000000 : ℝ)*(major0) + (56698475582829/1250000000000 : ℝ)*(major1) + (56698475582829/1250000000000 : ℝ)*(major2) + (26043095133/100000000000000 : ℝ)*(sp1) + (175094233/625000000000 : ℝ)*(sp2) + (3097663827965791/50000000000000 : ℝ)*(sp4) + (6195300367556511/100000000000000 : ℝ)*(sp5) + (1548824572090309/25000000000000 : ℝ)*(sp6) + (179776762062657/6250000000000 : ℝ)*(sp7) + (179776762062657/6250000000000 : ℝ)*(f.failure) + (3097663827965791/50000000000000 : ℝ)*(f.sum) + (827844245453/218500000000000000000000000 : ℝ)*base66 + (20053484753519459/5462500000000000000000000000000 : ℝ)*base67 + (23922203976319459/5462500000000000000000000000000 : ℝ)*base69 + (10860782367405541/5462500000000000000000000000000 : ℝ)*base72 + (372259889371/437000000000000000000000000 : ℝ)*base74 + (90850329716381959/5462500000000000000000000000000 : ℝ)*base75 + (8312684224005541/5462500000000000000000000000000 : ℝ)*base78 + (3683471840055541/5462500000000000000000000000000 : ℝ)*base80 + (142562306931/109250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (245031/78125000000000000000 : ℝ)*base90 + (245031/78125000000000000000 : ℝ)*base92 + (245031/78125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1417_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19711417/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7391/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5643/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11311/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2951/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1417_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1417_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19711417/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15837/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5151/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11311/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2951/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1417_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1417_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1417_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19711417/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15837/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5151/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11311/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2951/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1417_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
