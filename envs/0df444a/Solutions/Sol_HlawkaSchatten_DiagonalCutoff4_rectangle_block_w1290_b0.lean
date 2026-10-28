-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1290_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:25:13.368983+00:00
-- url     : https://prove2.me/submissions/bb3afc01-904b-4387-b687-60bb9d7919f9

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
theorem support_rectangle_w1290_s0_0 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-920145213/5000000000 : ℝ)*x 0 + (6019680183/10000000000 : ℝ)*x 1 + (599793949/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (920145213/5000000000 : ℝ)^2125 ≤ (1075340234313/10000000000000 : ℝ)^1613 := by
    have hnat : (920145213 : ℕ)^2125*10000000000000^1613 ≤ 1075340234313^1613*5000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      920145213 5000000000 1075340234313 10000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6019680183/10000000000 : ℝ)^2125 ≤ (25619780631217/50000000000000 : ℝ)^1613 := by
    have hnat : (6019680183 : ℕ)^2125*50000000000000^1613 ≤ 25619780631217^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6019680183 10000000000 25619780631217 50000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (599793949/1250000000 : ℝ)^2125 ≤ (7601407275319/20000000000000 : ℝ)^1613 := by
    have hnat : (599793949 : ℕ)^2125*20000000000000^1613 ≤ 7601407275319^1613*1250000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      599793949 1250000000 7601407275319 20000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-920145213/5000000000 : ℝ), (6019680183/10000000000 : ℝ), (599793949/1250000000 : ℝ)] ![(1075340234313/10000000000000 : ℝ), (25619780631217/50000000000000 : ℝ), (7601407275319/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-920145213/5000000000 : ℝ)|^2125 ≤ (1075340234313/10000000000000 : ℝ)^1613
        have hw : |(-920145213/5000000000 : ℝ)|=(920145213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6019680183/10000000000 : ℝ)|^2125 ≤ (25619780631217/50000000000000 : ℝ)^1613
        have hw : |(6019680183/10000000000 : ℝ)|=(6019680183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(599793949/1250000000 : ℝ)|^2125 ≤ (7601407275319/20000000000000 : ℝ)^1613
        have hw : |(599793949/1250000000 : ℝ)|=(599793949/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s0_1 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2753821631/5000000000 : ℝ)*x 0 + (-2537154689/10000000000 : ℝ)*x 1 + (4798351629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2753821631/5000000000 : ℝ)^2125 ≤ (9115340916407/20000000000000 : ℝ)^1613 := by
    have hnat : (2753821631 : ℕ)^2125*20000000000000^1613 ≤ 9115340916407^1613*5000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2753821631 5000000000 9115340916407 20000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2537154689/10000000000 : ℝ)^2125 ≤ (16416258641183/100000000000000 : ℝ)^1613 := by
    have hnat : (2537154689 : ℕ)^2125*100000000000000^1613 ≤ 16416258641183^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2537154689 10000000000 16416258641183 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4798351629/10000000000 : ℝ)^2125 ≤ (19003518381347/50000000000000 : ℝ)^1613 := by
    have hnat : (4798351629 : ℕ)^2125*50000000000000^1613 ≤ 19003518381347^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4798351629 10000000000 19003518381347 50000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2753821631/5000000000 : ℝ), (-2537154689/10000000000 : ℝ), (4798351629/10000000000 : ℝ)] ![(9115340916407/20000000000000 : ℝ), (16416258641183/100000000000000 : ℝ), (19003518381347/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2753821631/5000000000 : ℝ)|^2125 ≤ (9115340916407/20000000000000 : ℝ)^1613
        have hw : |(2753821631/5000000000 : ℝ)|=(2753821631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2537154689/10000000000 : ℝ)|^2125 ≤ (16416258641183/100000000000000 : ℝ)^1613
        have hw : |(-2537154689/10000000000 : ℝ)|=(2537154689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4798351629/10000000000 : ℝ)|^2125 ≤ (19003518381347/50000000000000 : ℝ)^1613
        have hw : |(4798351629/10000000000 : ℝ)|=(4798351629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s0_2 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (344227683/625000000 : ℝ)*x 0 + (4798352099/10000000000 : ℝ)*x 1 + (-126857727/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (344227683/625000000 : ℝ)^2125 ≤ (9115340188161/20000000000000 : ℝ)^1613 := by
    have hnat : (344227683 : ℕ)^2125*20000000000000^1613 ≤ 9115340188161^1613*625000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344227683 625000000 9115340188161 20000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4798352099/10000000000 : ℝ)^2125 ≤ (3800704166719/10000000000000 : ℝ)^1613 := by
    have hnat : (4798352099 : ℕ)^2125*10000000000000^1613 ≤ 3800704166719^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4798352099 10000000000 3800704166719 10000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (126857727/500000000 : ℝ)^2125 ≤ (16416257371083/100000000000000 : ℝ)^1613 := by
    have hnat : (126857727 : ℕ)^2125*100000000000000^1613 ≤ 16416257371083^1613*500000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126857727 500000000 16416257371083 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(344227683/625000000 : ℝ), (4798352099/10000000000 : ℝ), (-126857727/500000000 : ℝ)] ![(9115340188161/20000000000000 : ℝ), (3800704166719/10000000000000 : ℝ), (16416257371083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(344227683/625000000 : ℝ)|^2125 ≤ (9115340188161/20000000000000 : ℝ)^1613
        have hw : |(344227683/625000000 : ℝ)|=(344227683/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4798352099/10000000000 : ℝ)|^2125 ≤ (3800704166719/10000000000000 : ℝ)^1613
        have hw : |(4798352099/10000000000 : ℝ)|=(4798352099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-126857727/500000000 : ℝ)|^2125 ≤ (16416257371083/100000000000000 : ℝ)^1613
        have hw : |(-126857727/500000000 : ℝ)|=(126857727/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s0_3 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4186639781/10000000000 : ℝ)*x 0 + (3109565171/10000000000 : ℝ)*x 1 + (5617765413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4186639781/10000000000 : ℝ)^2125 ≤ (31756878841721/100000000000000 : ℝ)^1613 := by
    have hnat : (4186639781 : ℕ)^2125*100000000000000^1613 ≤ 31756878841721^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4186639781 10000000000 31756878841721 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3109565171/10000000000 : ℝ)^2125 ≤ (10731042389407/50000000000000 : ℝ)^1613 := by
    have hnat : (3109565171 : ℕ)^2125*50000000000000^1613 ≤ 10731042389407^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3109565171 10000000000 10731042389407 50000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5617765413/10000000000 : ℝ)^2125 ≤ (46781036365701/100000000000000 : ℝ)^1613 := by
    have hnat : (5617765413 : ℕ)^2125*100000000000000^1613 ≤ 46781036365701^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5617765413 10000000000 46781036365701 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4186639781/10000000000 : ℝ), (3109565171/10000000000 : ℝ), (5617765413/10000000000 : ℝ)] ![(31756878841721/100000000000000 : ℝ), (10731042389407/50000000000000 : ℝ), (46781036365701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4186639781/10000000000 : ℝ)|^2125 ≤ (31756878841721/100000000000000 : ℝ)^1613
        have hw : |(4186639781/10000000000 : ℝ)|=(4186639781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3109565171/10000000000 : ℝ)|^2125 ≤ (10731042389407/50000000000000 : ℝ)^1613
        have hw : |(3109565171/10000000000 : ℝ)|=(3109565171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5617765413/10000000000 : ℝ)|^2125 ≤ (46781036365701/100000000000000 : ℝ)^1613
        have hw : |(5617765413/10000000000 : ℝ)|=(5617765413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s0_4 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-57657037/312500000 : ℝ)*x 0 + (603734601/1250000000 : ℝ)*x 1 + (5987034059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (57657037/312500000 : ℝ)^2125 ≤ (10789865904209/100000000000000 : ℝ)^1613 := by
    have hnat : (57657037 : ℕ)^2125*100000000000000^1613 ≤ 10789865904209^1613*312500000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57657037 312500000 10789865904209 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (603734601/1250000000 : ℝ)^2125 ≤ (38336347589601/100000000000000 : ℝ)^1613 := by
    have hnat : (603734601 : ℕ)^2125*100000000000000^1613 ≤ 38336347589601^1613*1250000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      603734601 1250000000 38336347589601 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5987034059/10000000000 : ℝ)^2125 ≤ (50873786492653/100000000000000 : ℝ)^1613 := by
    have hnat : (5987034059 : ℕ)^2125*100000000000000^1613 ≤ 50873786492653^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5987034059 10000000000 50873786492653 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-57657037/312500000 : ℝ), (603734601/1250000000 : ℝ), (5987034059/10000000000 : ℝ)] ![(10789865904209/100000000000000 : ℝ), (38336347589601/100000000000000 : ℝ), (50873786492653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-57657037/312500000 : ℝ)|^2125 ≤ (10789865904209/100000000000000 : ℝ)^1613
        have hw : |(-57657037/312500000 : ℝ)|=(57657037/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(603734601/1250000000 : ℝ)|^2125 ≤ (38336347589601/100000000000000 : ℝ)^1613
        have hw : |(603734601/1250000000 : ℝ)|=(603734601/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5987034059/10000000000 : ℝ)|^2125 ≤ (50873786492653/100000000000000 : ℝ)^1613
        have hw : |(5987034059/10000000000 : ℝ)|=(5987034059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s0_5 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1035032027/2000000000 : ℝ)*x 0 + (-674235003/5000000000 : ℝ)*x 1 + (11693431/19531250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1035032027/2000000000 : ℝ)^2125 ≤ (20993614311157/50000000000000 : ℝ)^1613 := by
    have hnat : (1035032027 : ℕ)^2125*50000000000000^1613 ≤ 20993614311157^1613*2000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035032027 2000000000 20993614311157 50000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674235003/5000000000 : ℝ)^2125 ≤ (178473890719/2500000000000 : ℝ)^1613 := by
    have hnat : (674235003 : ℕ)^2125*2500000000000^1613 ≤ 178473890719^1613*5000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674235003 5000000000 178473890719 2500000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (11693431/19531250 : ℝ)^2125 ≤ (50873815744031/100000000000000 : ℝ)^1613 := by
    have hnat : (11693431 : ℕ)^2125*100000000000000^1613 ≤ 50873815744031^1613*19531250^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11693431 19531250 50873815744031 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1035032027/2000000000 : ℝ), (-674235003/5000000000 : ℝ), (11693431/19531250 : ℝ)] ![(20993614311157/50000000000000 : ℝ), (178473890719/2500000000000 : ℝ), (50873815744031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1035032027/2000000000 : ℝ)|^2125 ≤ (20993614311157/50000000000000 : ℝ)^1613
        have hw : |(1035032027/2000000000 : ℝ)|=(1035032027/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-674235003/5000000000 : ℝ)|^2125 ≤ (178473890719/2500000000000 : ℝ)^1613
        have hw : |(-674235003/5000000000 : ℝ)|=(674235003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(11693431/19531250 : ℝ)|^2125 ≤ (50873815744031/100000000000000 : ℝ)^1613
        have hw : |(11693431/19531250 : ℝ)|=(11693431/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s0_6 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (646895177/1250000000 : ℝ)*x 0 + (299351723/500000000 : ℝ)*x 1 + (-168558949/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (646895177/1250000000 : ℝ)^2125 ≤ (20993621157161/50000000000000 : ℝ)^1613 := by
    have hnat : (646895177 : ℕ)^2125*50000000000000^1613 ≤ 20993621157161^1613*1250000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646895177 1250000000 20993621157161 50000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (299351723/500000000 : ℝ)^2125 ≤ (5087379098167/10000000000000 : ℝ)^1613 := by
    have hnat : (299351723 : ℕ)^2125*10000000000000^1613 ≤ 5087379098167^1613*500000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299351723 500000000 5087379098167 10000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168558949/1250000000 : ℝ)^2125 ≤ (1784741672611/25000000000000 : ℝ)^1613 := by
    have hnat : (168558949 : ℕ)^2125*25000000000000^1613 ≤ 1784741672611^1613*1250000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168558949 1250000000 1784741672611 25000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(646895177/1250000000 : ℝ), (299351723/500000000 : ℝ), (-168558949/1250000000 : ℝ)] ![(20993621157161/50000000000000 : ℝ), (5087379098167/10000000000000 : ℝ), (1784741672611/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(646895177/1250000000 : ℝ)|^2125 ≤ (20993621157161/50000000000000 : ℝ)^1613
        have hw : |(646895177/1250000000 : ℝ)|=(646895177/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(299351723/500000000 : ℝ)|^2125 ≤ (5087379098167/10000000000000 : ℝ)^1613
        have hw : |(299351723/500000000 : ℝ)|=(299351723/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-168558949/1250000000 : ℝ)|^2125 ≤ (1784741672611/25000000000000 : ℝ)^1613
        have hw : |(-168558949/1250000000 : ℝ)|=(168558949/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s0_7 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2098183759/5000000000 : ℝ)*x 0 + (2776515679/5000000000 : ℝ)*x 1 + (3176601763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2098183759/5000000000 : ℝ)^2125 ≤ (7963531036701/25000000000000 : ℝ)^1613 := by
    have hnat : (2098183759 : ℕ)^2125*25000000000000^1613 ≤ 7963531036701^1613*5000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098183759 5000000000 7963531036701 25000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2776515679/5000000000 : ℝ)^2125 ≤ (46072166456731/100000000000000 : ℝ)^1613 := by
    have hnat : (2776515679 : ℕ)^2125*100000000000000^1613 ≤ 46072166456731^1613*5000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2776515679 5000000000 46072166456731 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3176601763/10000000000 : ℝ)^2125 ≤ (4414741875947/20000000000000 : ℝ)^1613 := by
    have hnat : (3176601763 : ℕ)^2125*20000000000000^1613 ≤ 4414741875947^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3176601763 10000000000 4414741875947 20000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2098183759/5000000000 : ℝ), (2776515679/5000000000 : ℝ), (3176601763/10000000000 : ℝ)] ![(7963531036701/25000000000000 : ℝ), (46072166456731/100000000000000 : ℝ), (4414741875947/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2098183759/5000000000 : ℝ)|^2125 ≤ (7963531036701/25000000000000 : ℝ)^1613
        have hw : |(2098183759/5000000000 : ℝ)|=(2098183759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2776515679/5000000000 : ℝ)|^2125 ≤ (46072166456731/100000000000000 : ℝ)^1613
        have hw : |(2776515679/5000000000 : ℝ)|=(2776515679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3176601763/10000000000 : ℝ)|^2125 ≤ (4414741875947/20000000000000 : ℝ)^1613
        have hw : |(3176601763/10000000000 : ℝ)|=(3176601763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1290_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152683333/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1017/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (109/400 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4249/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4249 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4249*1^1024 ≤ 0^1024*1^4249 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4249 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4249 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4249/1024 : ℝ) ≤ (558113002697688901/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4249 ≤ (558113002697688901/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4249*25000000000000000000^1024 ≤ 558113002697688901^1024*5^4249 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 558113002697688901 25000000000000000000 4249 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (558113002697688901/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4249 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4249/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4249 := by
      have hnat : (1 : ℕ)^1024*1^4249 ≤ 1^4249*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4249 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4249 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25558113002697688901/25000000000000000000 : ℝ) ≤ (1256668959968459/1250000000000000 : ℝ) ^ (4249/1024 : ℝ) := by
    have hpowers : (25558113002697688901/25000000000000000000 : ℝ)^1024 ≤ (1256668959968459/1250000000000000 : ℝ)^4249 := by
      have hnat : (25558113002697688901 : ℕ)^1024*1250000000000000^4249 ≤ 1256668959968459^4249*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25558113002697688901 25000000000000000000 1256668959968459 1250000000000000 1024 4249 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1256668959968459/1250000000000000 : ℝ)) (X := (25558113002697688901/25000000000000000000 : ℝ)) (by norm_num) 4249 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (13058113002697688901/12500000000000000000 : ℝ) ≤ (631668959968459/625000000000000 : ℝ) ^ (4249/1024 : ℝ) := by
    have hpowers : (13058113002697688901/12500000000000000000 : ℝ)^1024 ≤ (631668959968459/625000000000000 : ℝ)^4249 := by
      have hnat : (13058113002697688901 : ℕ)^1024*625000000000000^4249 ≤ 631668959968459^4249*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13058113002697688901 12500000000000000000 631668959968459 625000000000000 1024 4249 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (631668959968459/625000000000000 : ℝ)) (X := (13058113002697688901/12500000000000000000 : ℝ)) (by norm_num) 4249 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(6668959968459/500000000000000 : ℝ)*(0 : ℝ))^(4249/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(6668959968459/500000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(558113002697688901/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(6668959968459/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4249/1024 : ℝ) := by
    rw [show (1 : ℝ)+(6668959968459/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1256668959968459/1250000000000000 : ℝ) by norm_num, show 1+(558113002697688901/25000000000000000000 : ℝ)+(0 : ℝ)=(25558113002697688901/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(558113002697688901/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(6668959968459/500000000000000 : ℝ)*(2/5 : ℝ))^(4249/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(6668959968459/500000000000000 : ℝ)*(2/5 : ℝ)=(631668959968459/625000000000000 : ℝ) by norm_num, show 1+2*(558113002697688901/25000000000000000000 : ℝ)=(13058113002697688901/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(6668959968459/500000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4249/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6668959968459/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(6668959968459/500000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4249/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6668959968459/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(6668959968459/500000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4249/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6668959968459/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-920145213/5000000000 : ℝ)*X 0 0+(6019680183/10000000000 : ℝ)*X 0 1+(599793949/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2753821631/5000000000 : ℝ)*X 1 0+(-2537154689/10000000000 : ℝ)*X 1 1+(4798351629/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((344227683/625000000 : ℝ)*X 2 0+(4798352099/10000000000 : ℝ)*X 2 1+(-126857727/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4186639781/10000000000 : ℝ)*X 0 0+(3109565171/10000000000 : ℝ)*X 0 1+(5617765413/10000000000 : ℝ)*X 0 2+(4186639781/10000000000 : ℝ)*X 1 0+(3109565171/10000000000 : ℝ)*X 1 1+(5617765413/10000000000 : ℝ)*X 1 2+(4186639781/10000000000 : ℝ)*X 2 0+(3109565171/10000000000 : ℝ)*X 2 1+(5617765413/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-57657037/312500000 : ℝ)*X 0 0+(603734601/1250000000 : ℝ)*X 0 1+(5987034059/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1035032027/2000000000 : ℝ)*X 1 0+(-674235003/5000000000 : ℝ)*X 1 1+(11693431/19531250 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((646895177/1250000000 : ℝ)*X 2 0+(299351723/500000000 : ℝ)*X 2 1+(-168558949/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2098183759/5000000000 : ℝ)*X 0 0+(2776515679/5000000000 : ℝ)*X 0 1+(3176601763/10000000000 : ℝ)*X 0 2+(2098183759/5000000000 : ℝ)*X 1 0+(2776515679/5000000000 : ℝ)*X 1 1+(3176601763/10000000000 : ℝ)*X 1 2+(2098183759/5000000000 : ℝ)*X 2 0+(2776515679/5000000000 : ℝ)*X 2 1+(3176601763/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1876851379289332808337/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (50618971/50000000000000 : ℝ)*(base1) + (820580681/100000000000000 : ℝ)*(base19) + (385463567/50000000000000 : ℝ)*(base23) + (38643951/50000000000000 : ℝ)*(upper3) + (24429/25000000000 : ℝ)*(upper5) + (15218497288947/2500000000000 : ℝ)*(major0) + (15218497288947/2500000000000 : ℝ)*(major1) + (15218497288947/2500000000000 : ℝ)*(major2) + (818782831274761/100000000000000 : ℝ)*(sp0) + (51174029182527/6250000000000 : ℝ)*(sp1) + (40939225828699/5000000000000 : ℝ)*(sp2) + (199346643812081/50000000000000 : ℝ)*(sp3) + (2557464293/100000000000000 : ℝ)*(sp4) + (1006653797/100000000000000 : ℝ)*(sp7) + (398694395515901/100000000000000 : ℝ)*(f.failure) + (818785287501113/100000000000000 : ℝ)*(f.sum) + (262033971077/625000000000000000000000000 : ℝ)*base66 + (13921371778923/1250000000000000000000000000 : ℝ)*base67 + (4101282052673/1250000000000000000000000000 : ℝ)*base69 + (6358274882673/1250000000000000000000000000 : ℝ)*base71 + (958802835173/625000000000000000000000000 : ℝ)*base73 + (6851958391423/1250000000000000000000000000 : ℝ)*base75 + (5682169562673/1250000000000000000000000000 : ℝ)*base77 + (1729864262673/1250000000000000000000000000 : ℝ)*base79 + (228537257869/78125000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base87 + (19178033/10000000000000000000000 : ℝ)*base89 + (19178033/10000000000000000000000 : ℝ)*base91 + (19178033/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2264784980518914147/500000000000000000000000 : ℝ) := by norm_num
    linear_combination (101764419/25000000000000 : ℝ)*(base1) + (188325431/25000000000000 : ℝ)*(base19) + (184592489/20000000000000 : ℝ)*(base23) + (61260807/50000000000000 : ℝ)*(upper3) + (128498723041059/20000000000000 : ℝ)*(major0) + (128498723041059/20000000000000 : ℝ)*(major1) + (128498723041059/20000000000000 : ℝ)*(major2) + (1361845221/100000000000000 : ℝ)*(sp1) + (168273493/25000000000000 : ℝ)*(sp2) + (12489721/2000000000000 : ℝ)*(sp3) + (864186078377827/100000000000000 : ℝ)*(sp4) + (864183556173207/100000000000000 : ℝ)*(sp5) + (432092037631867/50000000000000 : ℝ)*(sp6) + (105200094140261/25000000000000 : ℝ)*(sp7) + (42080140810477/10000000000000 : ℝ)*(f.failure) + (864185671320151/100000000000000 : ℝ)*(f.sum) + (39558588081/5000000000000000000000000000 : ℝ)*base65 + (49832016778081/10000000000000000000000000000 : ℝ)*base67 + (2973988191919/10000000000000000000000000000 : ℝ)*base70 + (2838574931919/10000000000000000000000000000 : ℝ)*base72 + (10325893003081/5000000000000000000000000000 : ℝ)*base73 + (35020511391919/10000000000000000000000000000 : ℝ)*base76 + (19209210061919/10000000000000000000000000000 : ℝ)*base78 + (94552170258081/10000000000000000000000000000 : ℝ)*base79 + (11020957111919/5000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (320159/1000000000000000000000 : ℝ)*base90 + (320159/1000000000000000000000 : ℝ)*base92 + (320159/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1290_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152683333/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1017/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (109/400 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1290_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1290_s1_0 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2032624959/10000000000 : ℝ)*x 0 + (2833133969/5000000000 : ℝ)*x 1 + (5028629847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2032624959/10000000000 : ℝ)^2125 ≤ (12258014394903/100000000000000 : ℝ)^1613 := by
    have hnat : (2032624959 : ℕ)^2125*100000000000000^1613 ≤ 12258014394903^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2032624959 10000000000 12258014394903 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2833133969/5000000000 : ℝ)^2125 ≤ (11828466596149/25000000000000 : ℝ)^1613 := by
    have hnat : (2833133969 : ℕ)^2125*25000000000000^1613 ≤ 11828466596149^1613*5000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2833133969 5000000000 11828466596149 25000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5028629847/10000000000 : ℝ)^2125 ≤ (40428119205741/100000000000000 : ℝ)^1613 := by
    have hnat : (5028629847 : ℕ)^2125*100000000000000^1613 ≤ 40428119205741^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5028629847 10000000000 40428119205741 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2032624959/10000000000 : ℝ), (2833133969/5000000000 : ℝ), (5028629847/10000000000 : ℝ)] ![(12258014394903/100000000000000 : ℝ), (11828466596149/25000000000000 : ℝ), (40428119205741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2032624959/10000000000 : ℝ)|^2125 ≤ (12258014394903/100000000000000 : ℝ)^1613
        have hw : |(-2032624959/10000000000 : ℝ)|=(2032624959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2833133969/5000000000 : ℝ)|^2125 ≤ (11828466596149/25000000000000 : ℝ)^1613
        have hw : |(2833133969/5000000000 : ℝ)|=(2833133969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5028629847/10000000000 : ℝ)|^2125 ≤ (40428119205741/100000000000000 : ℝ)^1613
        have hw : |(5028629847/10000000000 : ℝ)|=(5028629847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s1_1 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2705599017/5000000000 : ℝ)*x 0 + (-118722579/500000000 : ℝ)*x 1 + (5028629779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2705599017/5000000000 : ℝ)^2125 ≤ (44528203466203/100000000000000 : ℝ)^1613 := by
    have hnat : (2705599017 : ℕ)^2125*100000000000000^1613 ≤ 44528203466203^1613*5000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705599017 5000000000 44528203466203 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (118722579/500000000 : ℝ)^2125 ≤ (15043678032963/100000000000000 : ℝ)^1613 := by
    have hnat : (118722579 : ℕ)^2125*100000000000000^1613 ≤ 15043678032963^1613*500000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118722579 500000000 15043678032963 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5028629779/10000000000 : ℝ)^2125 ≤ (40428118485517/100000000000000 : ℝ)^1613 := by
    have hnat : (5028629779 : ℕ)^2125*100000000000000^1613 ≤ 40428118485517^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5028629779 10000000000 40428118485517 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2705599017/5000000000 : ℝ), (-118722579/500000000 : ℝ), (5028629779/10000000000 : ℝ)] ![(44528203466203/100000000000000 : ℝ), (15043678032963/100000000000000 : ℝ), (40428118485517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2705599017/5000000000 : ℝ)|^2125 ≤ (44528203466203/100000000000000 : ℝ)^1613
        have hw : |(2705599017/5000000000 : ℝ)|=(2705599017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-118722579/500000000 : ℝ)|^2125 ≤ (15043678032963/100000000000000 : ℝ)^1613
        have hw : |(-118722579/500000000 : ℝ)|=(118722579/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5028629779/10000000000 : ℝ)|^2125 ≤ (40428118485517/100000000000000 : ℝ)^1613
        have hw : |(5028629779/10000000000 : ℝ)|=(5028629779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s1_2 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5411197859/10000000000 : ℝ)*x 0 + (5028629859/10000000000 : ℝ)*x 1 + (-1187225853/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5411197859/10000000000 : ℝ)^2125 ≤ (44528201569041/100000000000000 : ℝ)^1613 := by
    have hnat : (5411197859 : ℕ)^2125*100000000000000^1613 ≤ 44528201569041^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411197859 10000000000 44528201569041 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5028629859/10000000000 : ℝ)^2125 ≤ (40428119332839/100000000000000 : ℝ)^1613 := by
    have hnat : (5028629859 : ℕ)^2125*100000000000000^1613 ≤ 40428119332839^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5028629859 10000000000 40428119332839 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1187225853/5000000000 : ℝ)^2125 ≤ (15043679084649/100000000000000 : ℝ)^1613 := by
    have hnat : (1187225853 : ℕ)^2125*100000000000000^1613 ≤ 15043679084649^1613*5000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1187225853 5000000000 15043679084649 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5411197859/10000000000 : ℝ), (5028629859/10000000000 : ℝ), (-1187225853/5000000000 : ℝ)] ![(44528201569041/100000000000000 : ℝ), (40428119332839/100000000000000 : ℝ), (15043679084649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5411197859/10000000000 : ℝ)|^2125 ≤ (44528201569041/100000000000000 : ℝ)^1613
        have hw : |(5411197859/10000000000 : ℝ)|=(5411197859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5028629859/10000000000 : ℝ)|^2125 ≤ (40428119332839/100000000000000 : ℝ)^1613
        have hw : |(5028629859/10000000000 : ℝ)|=(5028629859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1187225853/5000000000 : ℝ)|^2125 ≤ (15043679084649/100000000000000 : ℝ)^1613
        have hw : |(-1187225853/5000000000 : ℝ)|=(1187225853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s1_3 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (86029827/200000000 : ℝ)*x 0 + (923498391/2500000000 : ℝ)*x 1 + (2501744629/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86029827/200000000 : ℝ)^2125 ≤ (8227389779579/25000000000000 : ℝ)^1613 := by
    have hnat : (86029827 : ℕ)^2125*25000000000000^1613 ≤ 8227389779579^1613*200000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86029827 200000000 8227389779579 25000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (923498391/2500000000 : ℝ)^2125 ≤ (26928387271831/100000000000000 : ℝ)^1613 := by
    have hnat : (923498391 : ℕ)^2125*100000000000000^1613 ≤ 26928387271831^1613*2500000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      923498391 2500000000 26928387271831 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2501744629/5000000000 : ℝ)^2125 ≤ (40162053589707/100000000000000 : ℝ)^1613 := by
    have hnat : (2501744629 : ℕ)^2125*100000000000000^1613 ≤ 40162053589707^1613*5000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2501744629 5000000000 40162053589707 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(86029827/200000000 : ℝ), (923498391/2500000000 : ℝ), (2501744629/5000000000 : ℝ)] ![(8227389779579/25000000000000 : ℝ), (26928387271831/100000000000000 : ℝ), (40162053589707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(86029827/200000000 : ℝ)|^2125 ≤ (8227389779579/25000000000000 : ℝ)^1613
        have hw : |(86029827/200000000 : ℝ)|=(86029827/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(923498391/2500000000 : ℝ)|^2125 ≤ (26928387271831/100000000000000 : ℝ)^1613
        have hw : |(923498391/2500000000 : ℝ)|=(923498391/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2501744629/5000000000 : ℝ)|^2125 ≤ (40162053589707/100000000000000 : ℝ)^1613
        have hw : |(2501744629/5000000000 : ℝ)|=(2501744629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s1_4 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-50831659/250000000 : ℝ)*x 0 + (5036955777/10000000000 : ℝ)*x 1 + (5657784233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (50831659/250000000 : ℝ)^2125 ≤ (613155525261/5000000000000 : ℝ)^1613 := by
    have hnat : (50831659 : ℕ)^2125*5000000000000^1613 ≤ 613155525261^1613*250000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50831659 250000000 613155525261 5000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5036955777/10000000000 : ℝ)^2125 ≤ (10129081663371/25000000000000 : ℝ)^1613 := by
    have hnat : (5036955777 : ℕ)^2125*25000000000000^1613 ≤ 10129081663371^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5036955777 10000000000 10129081663371 25000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5657784233/10000000000 : ℝ)^2125 ≤ (47220562825453/100000000000000 : ℝ)^1613 := by
    have hnat : (5657784233 : ℕ)^2125*100000000000000^1613 ≤ 47220562825453^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5657784233 10000000000 47220562825453 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-50831659/250000000 : ℝ), (5036955777/10000000000 : ℝ), (5657784233/10000000000 : ℝ)] ![(613155525261/5000000000000 : ℝ), (10129081663371/25000000000000 : ℝ), (47220562825453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-50831659/250000000 : ℝ)|^2125 ≤ (613155525261/5000000000000 : ℝ)^1613
        have hw : |(-50831659/250000000 : ℝ)|=(50831659/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5036955777/10000000000 : ℝ)|^2125 ≤ (10129081663371/25000000000000 : ℝ)^1613
        have hw : |(5036955777/10000000000 : ℝ)|=(5036955777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5657784233/10000000000 : ℝ)|^2125 ≤ (47220562825453/100000000000000 : ℝ)^1613
        have hw : |(5657784233/10000000000 : ℝ)|=(5657784233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s1_5 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (26232419/50000000 : ℝ)*x 0 + (-1745296859/10000000000 : ℝ)*x 1 + (5657784853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26232419/50000000 : ℝ)^2125 ≤ (21375618033869/50000000000000 : ℝ)^1613 := by
    have hnat : (26232419 : ℕ)^2125*50000000000000^1613 ≤ 21375618033869^1613*50000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26232419 50000000 21375618033869 50000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1745296859/10000000000 : ℝ)^2125 ≤ (5014097135461/50000000000000 : ℝ)^1613 := by
    have hnat : (1745296859 : ℕ)^2125*50000000000000^1613 ≤ 5014097135461^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1745296859 10000000000 5014097135461 50000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5657784853/10000000000 : ℝ)^2125 ≤ (23610284821287/50000000000000 : ℝ)^1613 := by
    have hnat : (5657784853 : ℕ)^2125*50000000000000^1613 ≤ 23610284821287^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5657784853 10000000000 23610284821287 50000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26232419/50000000 : ℝ), (-1745296859/10000000000 : ℝ), (5657784853/10000000000 : ℝ)] ![(21375618033869/50000000000000 : ℝ), (5014097135461/50000000000000 : ℝ), (23610284821287/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26232419/50000000 : ℝ)|^2125 ≤ (21375618033869/50000000000000 : ℝ)^1613
        have hw : |(26232419/50000000 : ℝ)|=(26232419/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1745296859/10000000000 : ℝ)|^2125 ≤ (5014097135461/50000000000000 : ℝ)^1613
        have hw : |(-1745296859/10000000000 : ℝ)|=(1745296859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5657784853/10000000000 : ℝ)|^2125 ≤ (23610284821287/50000000000000 : ℝ)^1613
        have hw : |(5657784853/10000000000 : ℝ)|=(5657784853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s1_6 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5246483707/10000000000 : ℝ)*x 0 + (707223059/1250000000 : ℝ)*x 1 + (-218162193/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5246483707/10000000000 : ℝ)^2125 ≤ (667988047959/1562500000000 : ℝ)^1613 := by
    have hnat : (5246483707 : ℕ)^2125*1562500000000^1613 ≤ 667988047959^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246483707 10000000000 667988047959 1562500000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (707223059/1250000000 : ℝ)^2125 ≤ (47220565453343/100000000000000 : ℝ)^1613 := by
    have hnat : (707223059 : ℕ)^2125*100000000000000^1613 ≤ 47220565453343^1613*1250000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      707223059 1250000000 47220565453343 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (218162193/1250000000 : ℝ)^2125 ≤ (5014099728079/50000000000000 : ℝ)^1613 := by
    have hnat : (218162193 : ℕ)^2125*50000000000000^1613 ≤ 5014099728079^1613*1250000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218162193 1250000000 5014099728079 50000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5246483707/10000000000 : ℝ), (707223059/1250000000 : ℝ), (-218162193/1250000000 : ℝ)] ![(667988047959/1562500000000 : ℝ), (47220565453343/100000000000000 : ℝ), (5014099728079/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5246483707/10000000000 : ℝ)|^2125 ≤ (667988047959/1562500000000 : ℝ)^1613
        have hw : |(5246483707/10000000000 : ℝ)|=(5246483707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(707223059/1250000000 : ℝ)|^2125 ≤ (47220565453343/100000000000000 : ℝ)^1613
        have hw : |(707223059/1250000000 : ℝ)|=(707223059/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-218162193/1250000000 : ℝ)|^2125 ≤ (5014099728079/50000000000000 : ℝ)^1613
        have hw : |(-218162193/1250000000 : ℝ)|=(218162193/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s1_7 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2151403949/5000000000 : ℝ)*x 0 + (4986390979/10000000000 : ℝ)*x 1 + (1855707757/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2151403949/5000000000 : ℝ)^2125 ≤ (1646141477987/5000000000000 : ℝ)^1613 := by
    have hnat : (2151403949 : ℕ)^2125*5000000000000^1613 ≤ 1646141477987^1613*5000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151403949 5000000000 1646141477987 5000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4986390979/10000000000 : ℝ)^2125 ≤ (19990671393293/50000000000000 : ℝ)^1613 := by
    have hnat : (4986390979 : ℕ)^2125*50000000000000^1613 ≤ 19990671393293^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4986390979 10000000000 19990671393293 50000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1855707757/5000000000 : ℝ)^2125 ≤ (27095827632493/100000000000000 : ℝ)^1613 := by
    have hnat : (1855707757 : ℕ)^2125*100000000000000^1613 ≤ 27095827632493^1613*5000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1855707757 5000000000 27095827632493 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2151403949/5000000000 : ℝ), (4986390979/10000000000 : ℝ), (1855707757/5000000000 : ℝ)] ![(1646141477987/5000000000000 : ℝ), (19990671393293/50000000000000 : ℝ), (27095827632493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2151403949/5000000000 : ℝ)|^2125 ≤ (1646141477987/5000000000000 : ℝ)^1613
        have hw : |(2151403949/5000000000 : ℝ)|=(2151403949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4986390979/10000000000 : ℝ)|^2125 ≤ (19990671393293/50000000000000 : ℝ)^1613
        have hw : |(4986390979/10000000000 : ℝ)|=(4986390979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1855707757/5000000000 : ℝ)|^2125 ≤ (27095827632493/100000000000000 : ℝ)^1613
        have hw : |(1855707757/5000000000 : ℝ)|=(1855707757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1290_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152683333/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (109/400 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1017/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (6389/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9933/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (109/400 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1017/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (109/400 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1017/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (109/400 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1017/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (109/400 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1017/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (109/400 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1017/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (109/400 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1017/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1017/100000 : ℝ) ^ (4249/1024 : ℝ) ≤ (53895132009/10000000000000000000 : ℝ) := by
    have hpowers : (1017/100000 : ℝ)^4249 ≤ (53895132009/10000000000000000000 : ℝ)^1024 := by
      have hnat : (1017 : ℕ)^4249*10000000000000000000^1024 ≤ 53895132009^1024*100000^4249 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1017 100000 53895132009 10000000000000000000 4249 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1017/100000 : ℝ)) (X := (53895132009/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4249 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (109/400 : ℝ) ^ (4249/1024 : ℝ) ≤ (90809615756054881/20000000000000000000 : ℝ) := by
    have hpowers : (109/400 : ℝ)^4249 ≤ (90809615756054881/20000000000000000000 : ℝ)^1024 := by
      have hnat : (109 : ℕ)^4249*20000000000000000000^1024 ≤ 90809615756054881^1024*400^4249 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        109 400 90809615756054881 20000000000000000000 4249 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (109/400 : ℝ)) (X := (90809615756054881/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4249 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000000053895132009/5000000000000000000 : ℝ) ≤ (5000000012988613/5000000000000000 : ℝ) ^ (4249/1024 : ℝ) := by
    have hpowers : (5000000053895132009/5000000000000000000 : ℝ)^1024 ≤ (5000000012988613/5000000000000000 : ℝ)^4249 := by
      have hnat : (5000000053895132009 : ℕ)^1024*5000000000000000^4249 ≤ 5000000012988613^4249*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000000053895132009 5000000000000000000 5000000012988613 5000000000000000 1024 4249 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000012988613/5000000000000000 : ℝ)) (X := (5000000053895132009/5000000000000000000 : ℝ)) (by norm_num) 4249 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20090809723546318899/20000000000000000000 : ℝ) ≤ (10010923670362743/10000000000000000 : ℝ) ^ (4249/1024 : ℝ) := by
    have hpowers : (20090809723546318899/20000000000000000000 : ℝ)^1024 ≤ (10010923670362743/10000000000000000 : ℝ)^4249 := by
      have hnat : (20090809723546318899 : ℕ)^1024*10000000000000000^4249 ≤ 10010923670362743^4249*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20090809723546318899 20000000000000000000 10010923670362743 10000000000000000 1024 4249 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10010923670362743/10000000000000000 : ℝ)) (X := (20090809723546318899/20000000000000000000 : ℝ)) (by norm_num) 4249 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10090809615756054881/10000000000000000000 : ℝ) ≤ (501092365737413/500000000000000 : ℝ) ^ (4249/1024 : ℝ) := by
    have hpowers : (10090809615756054881/10000000000000000000 : ℝ)^1024 ≤ (501092365737413/500000000000000 : ℝ)^4249 := by
      have hnat : (10090809615756054881 : ℕ)^1024*500000000000000^4249 ≤ 501092365737413^4249*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10090809615756054881 10000000000000000000 501092365737413 500000000000000 1024 4249 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (501092365737413/500000000000000 : ℝ)) (X := (10090809615756054881/10000000000000000000 : ℝ)) (by norm_num) 4249 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(53895132009/10000000000000000000 : ℝ) ≤ ((88617493915128523/88625000000000000 : ℝ)+2*(295233632041/70900000000000 : ℝ)*(1017/100000 : ℝ))^(4249/1024 : ℝ) := by
    rw [show (88617493915128523/88625000000000000 : ℝ)+2*(295233632041/70900000000000 : ℝ)*(1017/100000 : ℝ)=(5000000012988613/5000000000000000 : ℝ) by norm_num, show 1+2*(53895132009/10000000000000000000 : ℝ)=(5000000053895132009/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(90809615756054881/20000000000000000000 : ℝ)+(53895132009/10000000000000000000 : ℝ) ≤ ((88617493915128523/88625000000000000 : ℝ)+(295233632041/70900000000000 : ℝ)*((109/400 : ℝ)+(1017/100000 : ℝ)))^(4249/1024 : ℝ) := by
    rw [show (88617493915128523/88625000000000000 : ℝ)+(295233632041/70900000000000 : ℝ)*((109/400 : ℝ)+(1017/100000 : ℝ))=(10010923670362743/10000000000000000 : ℝ) by norm_num, show 1+(90809615756054881/20000000000000000000 : ℝ)+(53895132009/10000000000000000000 : ℝ)=(20090809723546318899/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(90809615756054881/20000000000000000000 : ℝ) ≤ ((88617493915128523/88625000000000000 : ℝ)+2*(295233632041/70900000000000 : ℝ)*(109/400 : ℝ))^(4249/1024 : ℝ) := by
    rw [show (88617493915128523/88625000000000000 : ℝ)+2*(295233632041/70900000000000 : ℝ)*(109/400 : ℝ)=(501092365737413/500000000000000 : ℝ) by norm_num, show 1+2*(90809615756054881/20000000000000000000 : ℝ)=(10090809615756054881/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (88617493915128523/88625000000000000 : ℝ)*(X 1 0+X 2 0)+(295233632041/70900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4249/1024 : ℝ)) (lo := (1017/100000 : ℝ)) (hi := (109/400 : ℝ)) (c := (88617493915128523/88625000000000000 : ℝ)) (alpha := (295233632041/70900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (88617493915128523/88625000000000000 : ℝ)*(X 0 1+X 2 1)+(295233632041/70900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4249/1024 : ℝ)) (lo := (1017/100000 : ℝ)) (hi := (109/400 : ℝ)) (c := (88617493915128523/88625000000000000 : ℝ)) (alpha := (295233632041/70900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (88617493915128523/88625000000000000 : ℝ)*(X 0 2+X 1 2)+(295233632041/70900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4249/1024 : ℝ)) (lo := (1017/100000 : ℝ)) (hi := (109/400 : ℝ)) (c := (88617493915128523/88625000000000000 : ℝ)) (alpha := (295233632041/70900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2032624959/10000000000 : ℝ)*X 0 0+(2833133969/5000000000 : ℝ)*X 0 1+(5028629847/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2705599017/5000000000 : ℝ)*X 1 0+(-118722579/500000000 : ℝ)*X 1 1+(5028629779/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5411197859/10000000000 : ℝ)*X 2 0+(5028629859/10000000000 : ℝ)*X 2 1+(-1187225853/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((86029827/200000000 : ℝ)*X 0 0+(923498391/2500000000 : ℝ)*X 0 1+(2501744629/5000000000 : ℝ)*X 0 2+(86029827/200000000 : ℝ)*X 1 0+(923498391/2500000000 : ℝ)*X 1 1+(2501744629/5000000000 : ℝ)*X 1 2+(86029827/200000000 : ℝ)*X 2 0+(923498391/2500000000 : ℝ)*X 2 1+(2501744629/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-50831659/250000000 : ℝ)*X 0 0+(5036955777/10000000000 : ℝ)*X 0 1+(5657784233/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((26232419/50000000 : ℝ)*X 1 0+(-1745296859/10000000000 : ℝ)*X 1 1+(5657784853/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5246483707/10000000000 : ℝ)*X 2 0+(707223059/1250000000 : ℝ)*X 2 1+(-218162193/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2151403949/5000000000 : ℝ)*X 0 0+(4986390979/10000000000 : ℝ)*X 0 1+(1855707757/5000000000 : ℝ)*X 0 2+(2151403949/5000000000 : ℝ)*X 1 0+(4986390979/10000000000 : ℝ)*X 1 1+(1855707757/5000000000 : ℝ)*X 1 2+(2151403949/5000000000 : ℝ)*X 2 0+(4986390979/10000000000 : ℝ)*X 2 1+(1855707757/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4205711955250621157464341/1107812500000000000000000000000 : ℝ) := by norm_num
    linear_combination (7205919/20000000000000 : ℝ)*(base1) + (731372819/100000000000000 : ℝ)*(base19) + (680653621/100000000000000 : ℝ)*(base23) + (105136119/100000000000000 : ℝ)*(upper3) + (8801361/20000000000000 : ℝ)*(upper5) + (145747015365331/12500000000000 : ℝ)*(major0) + (145747015365331/12500000000000 : ℝ)*(major1) + (145747015365331/12500000000000 : ℝ)*(major2) + (6126140832973/390625000000 : ℝ)*(sp0) + (784147468179009/50000000000000 : ℝ)*(sp1) + (49009218346163/3125000000000 : ℝ)*(sp2) + (381827224763173/50000000000000 : ℝ)*(sp3) + (730103869/20000000000000 : ℝ)*(sp4) + (983005733/50000000000000 : ℝ)*(sp7) + (763656451567407/100000000000000 : ℝ)*(f.failure) + (1568295667730837/100000000000000 : ℝ)*(f.sum) + (597143358103/221562500000000000000000000 : ℝ)*base65 + (7777323498290351/2215625000000000000000000000000 : ℝ)*base67 + (10309183001684101/2215625000000000000000000000000 : ℝ)*base69 + (9024306336618613/1107812500000000000000000000000 : ℝ)*base71 + (6530117562629/1772500000000000000000000000 : ℝ)*base73 + (850075585142561/138476562500000000000000000000 : ℝ)*base75 + (7068857824449863/1107812500000000000000000000000 : ℝ)*base77 + (1595434615444497/276953125000000000000000000000 : ℝ)*base79 + (1000447302203/221562500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (25072469/10000000000000000000000 : ℝ)*base90 + (25072469/10000000000000000000000 : ℝ)*base92 + (25072469/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9026711241567709080807009/2215625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (169240179/25000000000000 : ℝ)*(base19) + (83064807/12500000000000 : ℝ)*(base23) + (2840087/10000000000000 : ℝ)*(upper2) + (26747997/20000000000000 : ℝ)*(upper3) + (86146817/100000000000000 : ℝ)*(upper5) + (598769758393693/50000000000000 : ℝ)*(major0) + (598769758393693/50000000000000 : ℝ)*(major1) + (598769758393693/50000000000000 : ℝ)*(major2) + (4133757043/100000000000000 : ℝ)*(sp1) + (292264807/10000000000000 : ℝ)*(sp2) + (805374995419091/50000000000000 : ℝ)*(sp4) + (201343147515053/12500000000000 : ℝ)*(sp5) + (1610746403671657/100000000000000 : ℝ)*(sp6) + (784328906932747/100000000000000 : ℝ)*(sp7) + (784328906932747/100000000000000 : ℝ)*(f.failure) + (805374995419091/50000000000000 : ℝ)*(f.sum) + (4461480572261/886250000000000000000000000 : ℝ)*base66 + (13048241284647061/4431250000000000000000000000000 : ℝ)*base68 + (7349446605146689/4431250000000000000000000000000 : ℝ)*base69 + (27247090674453311/4431250000000000000000000000000 : ℝ)*base72 + (2892349656739/3545000000000000000000000000 : ℝ)*base74 + (22029460675897061/4431250000000000000000000000000 : ℝ)*base76 + (34967613090722061/4431250000000000000000000000000 : ℝ)*base78 + (52994873580772061/4431250000000000000000000000000 : ℝ)*base80 + (451029075593/110781250000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (18805751/10000000000000000000000 : ℝ)*base89 + (18805751/10000000000000000000000 : ℝ)*base91 + (18805751/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1290_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152683333/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (109/400 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1017/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6389/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9933/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1290_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1290_s2_0 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2077510101/10000000000 : ℝ)*x 0 + (5494863181/10000000000 : ℝ)*x 1 + (5171368463/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2077510101/10000000000 : ℝ)^2125 ≤ (12615865121927/100000000000000 : ℝ)^1613 := by
    have hnat : (2077510101 : ℕ)^2125*100000000000000^1613 ≤ 12615865121927^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077510101 10000000000 12615865121927 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5494863181/10000000000 : ℝ)^2125 ≤ (11359357229569/25000000000000 : ℝ)^1613 := by
    have hnat : (5494863181 : ℕ)^2125*25000000000000^1613 ≤ 11359357229569^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5494863181 10000000000 11359357229569 25000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5171368463/10000000000 : ℝ)^2125 ≤ (5243338241931/12500000000000 : ℝ)^1613 := by
    have hnat : (5171368463 : ℕ)^2125*12500000000000^1613 ≤ 5243338241931^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5171368463 10000000000 5243338241931 12500000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2077510101/10000000000 : ℝ), (5494863181/10000000000 : ℝ), (5171368463/10000000000 : ℝ)] ![(12615865121927/100000000000000 : ℝ), (11359357229569/25000000000000 : ℝ), (5243338241931/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2077510101/10000000000 : ℝ)|^2125 ≤ (12615865121927/100000000000000 : ℝ)^1613
        have hw : |(-2077510101/10000000000 : ℝ)|=(2077510101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5494863181/10000000000 : ℝ)|^2125 ≤ (11359357229569/25000000000000 : ℝ)^1613
        have hw : |(5494863181/10000000000 : ℝ)|=(5494863181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5171368463/10000000000 : ℝ)|^2125 ≤ (5243338241931/12500000000000 : ℝ)^1613
        have hw : |(5171368463/10000000000 : ℝ)|=(5171368463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s2_1 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5369732717/10000000000 : ℝ)*x 0 + (-2245172091/10000000000 : ℝ)*x 1 + (646421093/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369732717/10000000000 : ℝ)^2125 ≤ (44079228758523/100000000000000 : ℝ)^1613 := by
    have hnat : (5369732717 : ℕ)^2125*100000000000000^1613 ≤ 44079228758523^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369732717 10000000000 44079228758523 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2245172091/10000000000 : ℝ)^2125 ≤ (13974062288513/100000000000000 : ℝ)^1613 := by
    have hnat : (2245172091 : ℕ)^2125*100000000000000^1613 ≤ 13974062288513^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245172091 10000000000 13974062288513 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (646421093/1250000000 : ℝ)^2125 ≤ (20973354469113/50000000000000 : ℝ)^1613 := by
    have hnat : (646421093 : ℕ)^2125*50000000000000^1613 ≤ 20973354469113^1613*1250000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646421093 1250000000 20973354469113 50000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369732717/10000000000 : ℝ), (-2245172091/10000000000 : ℝ), (646421093/1250000000 : ℝ)] ![(44079228758523/100000000000000 : ℝ), (13974062288513/100000000000000 : ℝ), (20973354469113/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369732717/10000000000 : ℝ)|^2125 ≤ (44079228758523/100000000000000 : ℝ)^1613
        have hw : |(5369732717/10000000000 : ℝ)|=(5369732717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2245172091/10000000000 : ℝ)|^2125 ≤ (13974062288513/100000000000000 : ℝ)^1613
        have hw : |(-2245172091/10000000000 : ℝ)|=(2245172091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(646421093/1250000000 : ℝ)|^2125 ≤ (20973354469113/50000000000000 : ℝ)^1613
        have hw : |(646421093/1250000000 : ℝ)|=(646421093/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s2_2 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2684866421/5000000000 : ℝ)*x 0 + (32321053/62500000 : ℝ)*x 1 + (-224517227/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684866421/5000000000 : ℝ)^2125 ≤ (22039615055167/50000000000000 : ℝ)^1613 := by
    have hnat : (2684866421 : ℕ)^2125*50000000000000^1613 ≤ 22039615055167^1613*5000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684866421 5000000000 22039615055167 50000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32321053/62500000 : ℝ)^2125 ≤ (41946706117111/100000000000000 : ℝ)^1613 := by
    have hnat : (32321053 : ℕ)^2125*100000000000000^1613 ≤ 41946706117111^1613*62500000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32321053 62500000 41946706117111 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (224517227/1000000000 : ℝ)^2125 ≤ (6987031878129/50000000000000 : ℝ)^1613 := by
    have hnat : (224517227 : ℕ)^2125*50000000000000^1613 ≤ 6987031878129^1613*1000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224517227 1000000000 6987031878129 50000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684866421/5000000000 : ℝ), (32321053/62500000 : ℝ), (-224517227/1000000000 : ℝ)] ![(22039615055167/50000000000000 : ℝ), (41946706117111/100000000000000 : ℝ), (6987031878129/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684866421/5000000000 : ℝ)|^2125 ≤ (22039615055167/50000000000000 : ℝ)^1613
        have hw : |(2684866421/5000000000 : ℝ)|=(2684866421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(32321053/62500000 : ℝ)|^2125 ≤ (41946706117111/100000000000000 : ℝ)^1613
        have hw : |(32321053/62500000 : ℝ)|=(32321053/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-224517227/1000000000 : ℝ)|^2125 ≤ (6987031878129/50000000000000 : ℝ)^1613
        have hw : |(-224517227/1000000000 : ℝ)|=(224517227/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s2_3 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2166342133/5000000000 : ℝ)*x 0 + (802529943/2000000000 : ℝ)*x 1 + (2338503623/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2166342133/5000000000 : ℝ)^2125 ≤ (1661216055313/5000000000000 : ℝ)^1613 := by
    have hnat : (2166342133 : ℕ)^2125*5000000000000^1613 ≤ 1661216055313^1613*5000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166342133 5000000000 1661216055313 5000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (802529943/2000000000 : ℝ)^2125 ≤ (14662974047/48828125000 : ℝ)^1613 := by
    have hnat : (802529943 : ℕ)^2125*48828125000^1613 ≤ 14662974047^1613*2000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      802529943 2000000000 14662974047 48828125000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2338503623/5000000000 : ℝ)^2125 ≤ (36745908035691/100000000000000 : ℝ)^1613 := by
    have hnat : (2338503623 : ℕ)^2125*100000000000000^1613 ≤ 36745908035691^1613*5000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2338503623 5000000000 36745908035691 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2166342133/5000000000 : ℝ), (802529943/2000000000 : ℝ), (2338503623/5000000000 : ℝ)] ![(1661216055313/5000000000000 : ℝ), (14662974047/48828125000 : ℝ), (36745908035691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2166342133/5000000000 : ℝ)|^2125 ≤ (1661216055313/5000000000000 : ℝ)^1613
        have hw : |(2166342133/5000000000 : ℝ)|=(2166342133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(802529943/2000000000 : ℝ)|^2125 ≤ (14662974047/48828125000 : ℝ)^1613
        have hw : |(802529943/2000000000 : ℝ)|=(802529943/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2338503623/5000000000 : ℝ)|^2125 ≤ (36745908035691/100000000000000 : ℝ)^1613
        have hw : |(2338503623/5000000000 : ℝ)|=(2338503623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s2_4 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-415518611/2000000000 : ℝ)*x 0 + (5173520903/10000000000 : ℝ)*x 1 + (1098538121/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (415518611/2000000000 : ℝ)^2125 ≤ (315413219277/2500000000000 : ℝ)^1613 := by
    have hnat : (415518611 : ℕ)^2125*2500000000000^1613 ≤ 315413219277^1613*2000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415518611 2000000000 315413219277 2500000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5173520903/10000000000 : ℝ)^2125 ≤ (41969708522629/100000000000000 : ℝ)^1613 := by
    have hnat : (5173520903 : ℕ)^2125*100000000000000^1613 ≤ 41969708522629^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5173520903 10000000000 41969708522629 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1098538121/2000000000 : ℝ)^2125 ≤ (45413762684273/100000000000000 : ℝ)^1613 := by
    have hnat : (1098538121 : ℕ)^2125*100000000000000^1613 ≤ 45413762684273^1613*2000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098538121 2000000000 45413762684273 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-415518611/2000000000 : ℝ), (5173520903/10000000000 : ℝ), (1098538121/2000000000 : ℝ)] ![(315413219277/2500000000000 : ℝ), (41969708522629/100000000000000 : ℝ), (45413762684273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-415518611/2000000000 : ℝ)|^2125 ≤ (315413219277/2500000000000 : ℝ)^1613
        have hw : |(-415518611/2000000000 : ℝ)|=(415518611/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5173520903/10000000000 : ℝ)|^2125 ≤ (41969708522629/100000000000000 : ℝ)^1613
        have hw : |(5173520903/10000000000 : ℝ)|=(5173520903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1098538121/2000000000 : ℝ)|^2125 ≤ (45413762684273/100000000000000 : ℝ)^1613
        have hw : |(1098538121/2000000000 : ℝ)|=(1098538121/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s2_5 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2643420307/5000000000 : ℝ)*x 0 + (-1923849597/10000000000 : ℝ)*x 1 + (5492690747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643420307/5000000000 : ℝ)^2125 ≤ (43184997297253/100000000000000 : ℝ)^1613 := by
    have hnat : (2643420307 : ℕ)^2125*100000000000000^1613 ≤ 43184997297253^1613*5000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643420307 5000000000 43184997297253 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1923849597/10000000000 : ℝ)^2125 ≤ (5700619229511/50000000000000 : ℝ)^1613 := by
    have hnat : (1923849597 : ℕ)^2125*50000000000000^1613 ≤ 5700619229511^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1923849597 10000000000 5700619229511 50000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5492690747/10000000000 : ℝ)^2125 ≤ (22706882115503/50000000000000 : ℝ)^1613 := by
    have hnat : (5492690747 : ℕ)^2125*50000000000000^1613 ≤ 22706882115503^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5492690747 10000000000 22706882115503 50000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643420307/5000000000 : ℝ), (-1923849597/10000000000 : ℝ), (5492690747/10000000000 : ℝ)] ![(43184997297253/100000000000000 : ℝ), (5700619229511/50000000000000 : ℝ), (22706882115503/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643420307/5000000000 : ℝ)|^2125 ≤ (43184997297253/100000000000000 : ℝ)^1613
        have hw : |(2643420307/5000000000 : ℝ)|=(2643420307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1923849597/10000000000 : ℝ)|^2125 ≤ (5700619229511/50000000000000 : ℝ)^1613
        have hw : |(-1923849597/10000000000 : ℝ)|=(1923849597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5492690747/10000000000 : ℝ)|^2125 ≤ (22706882115503/50000000000000 : ℝ)^1613
        have hw : |(5492690747/10000000000 : ℝ)|=(5492690747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s2_6 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (330427549/625000000 : ℝ)*x 0 + (5492690613/10000000000 : ℝ)*x 1 + (-1923849549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330427549/625000000 : ℝ)^2125 ≤ (43184999126659/100000000000000 : ℝ)^1613 := by
    have hnat : (330427549 : ℕ)^2125*100000000000000^1613 ≤ 43184999126659^1613*625000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330427549 625000000 43184999126659 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5492690613/10000000000 : ℝ)^2125 ≤ (45413762771413/100000000000000 : ℝ)^1613 := by
    have hnat : (5492690613 : ℕ)^2125*100000000000000^1613 ≤ 45413762771413^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5492690613 10000000000 45413762771413 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1923849549/10000000000 : ℝ)^2125 ≤ (2850309521067/25000000000000 : ℝ)^1613 := by
    have hnat : (1923849549 : ℕ)^2125*25000000000000^1613 ≤ 2850309521067^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1923849549 10000000000 2850309521067 25000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330427549/625000000 : ℝ), (5492690613/10000000000 : ℝ), (-1923849549/10000000000 : ℝ)] ![(43184999126659/100000000000000 : ℝ), (45413762771413/100000000000000 : ℝ), (2850309521067/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330427549/625000000 : ℝ)|^2125 ≤ (43184999126659/100000000000000 : ℝ)^1613
        have hw : |(330427549/625000000 : ℝ)|=(330427549/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5492690613/10000000000 : ℝ)|^2125 ≤ (45413762771413/100000000000000 : ℝ)^1613
        have hw : |(5492690613/10000000000 : ℝ)|=(5492690613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1923849549/10000000000 : ℝ)|^2125 ≤ (2850309521067/25000000000000 : ℝ)^1613
        have hw : |(-1923849549/10000000000 : ℝ)|=(1923849549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s2_7 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4332854363/10000000000 : ℝ)*x 0 + (1168146329/2500000000 : ℝ)*x 1 + (62767441/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4332854363/10000000000 : ℝ)^2125 ≤ (1661301975063/5000000000000 : ℝ)^1613 := by
    have hnat : (4332854363 : ℕ)^2125*5000000000000^1613 ≤ 1661301975063^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4332854363 10000000000 1661301975063 5000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1168146329/2500000000 : ℝ)^2125 ≤ (18350072639151/50000000000000 : ℝ)^1613 := by
    have hnat : (1168146329 : ℕ)^2125*50000000000000^1613 ≤ 18350072639151^1613*2500000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1168146329 2500000000 18350072639151 50000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (62767441/156250000 : ℝ)^2125 ≤ (3007381520241/10000000000000 : ℝ)^1613 := by
    have hnat : (62767441 : ℕ)^2125*10000000000000^1613 ≤ 3007381520241^1613*156250000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62767441 156250000 3007381520241 10000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4332854363/10000000000 : ℝ), (1168146329/2500000000 : ℝ), (62767441/156250000 : ℝ)] ![(1661301975063/5000000000000 : ℝ), (18350072639151/50000000000000 : ℝ), (3007381520241/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4332854363/10000000000 : ℝ)|^2125 ≤ (1661301975063/5000000000000 : ℝ)^1613
        have hw : |(4332854363/10000000000 : ℝ)|=(4332854363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1168146329/2500000000 : ℝ)|^2125 ≤ (18350072639151/50000000000000 : ℝ)^1613
        have hw : |(1168146329/2500000000 : ℝ)|=(1168146329/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(62767441/156250000 : ℝ)|^2125 ≤ (3007381520241/10000000000000 : ℝ)^1613
        have hw : |(62767441/156250000 : ℝ)|=(62767441/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1290_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152683333/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9933/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6389/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (949/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8163/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9933/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6389/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9933/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6389/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9933/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6389/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9933/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6389/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9933/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6389/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9933/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6389/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6389/100000 : ℝ) ^ (4249/1024 : ℝ) ≤ (138088159258373/12500000000000000000 : ℝ) := by
    have hpowers : (6389/100000 : ℝ)^4249 ≤ (138088159258373/12500000000000000000 : ℝ)^1024 := by
      have hnat : (6389 : ℕ)^4249*12500000000000000000^1024 ≤ 138088159258373^1024*100000^4249 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6389 100000 138088159258373 12500000000000000000 4249 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6389/100000 : ℝ)) (X := (138088159258373/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4249 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9933/50000 : ℝ) ^ (4249/1024 : ℝ) ≤ (61170151620146483/50000000000000000000 : ℝ) := by
    have hpowers : (9933/50000 : ℝ)^4249 ≤ (61170151620146483/50000000000000000000 : ℝ)^1024 := by
      have hnat : (9933 : ℕ)^4249*50000000000000000000^1024 ≤ 61170151620146483^1024*50000^4249 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9933 50000 61170151620146483 50000000000000000000 4249 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9933/50000 : ℝ)) (X := (61170151620146483/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4249 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250138088159258373/6250000000000000000 : ℝ) ≤ (400002129835191/400000000000000 : ℝ) ^ (4249/1024 : ℝ) := by
    have hpowers : (6250138088159258373/6250000000000000000 : ℝ)^1024 ≤ (400002129835191/400000000000000 : ℝ)^4249 := by
      have hnat : (6250138088159258373 : ℕ)^1024*400000000000000^4249 ≤ 400002129835191^4249*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250138088159258373 6250000000000000000 400002129835191 400000000000000 1024 4249 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400002129835191/400000000000000 : ℝ)) (X := (6250138088159258373/6250000000000000000 : ℝ)) (by norm_num) 4249 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2002468900170287199/2000000000000000000 : ℝ) ≤ (10002973605852869/10000000000000000 : ℝ) ^ (4249/1024 : ℝ) := by
    have hpowers : (2002468900170287199/2000000000000000000 : ℝ)^1024 ≤ (10002973605852869/10000000000000000 : ℝ)^4249 := by
      have hnat : (2002468900170287199 : ℕ)^1024*10000000000000000^4249 ≤ 10002973605852869^4249*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2002468900170287199 2000000000000000000 10002973605852869 10000000000000000 1024 4249 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002973605852869/10000000000000000 : ℝ)) (X := (2002468900170287199/2000000000000000000 : ℝ)) (by norm_num) 4249 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25061170151620146483/25000000000000000000 : ℝ) ≤ (10005893965825963/10000000000000000 : ℝ) ^ (4249/1024 : ℝ) := by
    have hpowers : (25061170151620146483/25000000000000000000 : ℝ)^1024 ≤ (10005893965825963/10000000000000000 : ℝ)^4249 := by
      have hnat : (25061170151620146483 : ℕ)^1024*10000000000000000^4249 ≤ 10005893965825963^4249*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25061170151620146483 25000000000000000000 10005893965825963 10000000000000000 1024 4249 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005893965825963/10000000000000000 : ℝ)) (X := (25061170151620146483/25000000000000000000 : ℝ)) (by norm_num) 4249 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(138088159258373/12500000000000000000 : ℝ) ≤ ((134733401234985532543/134770000000000000000 : ℝ)+2*(1460179986547/673850000000000 : ℝ)*(6389/100000 : ℝ))^(4249/1024 : ℝ) := by
    rw [show (134733401234985532543/134770000000000000000 : ℝ)+2*(1460179986547/673850000000000 : ℝ)*(6389/100000 : ℝ)=(400002129835191/400000000000000 : ℝ) by norm_num, show 1+2*(138088159258373/12500000000000000000 : ℝ)=(6250138088159258373/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(61170151620146483/50000000000000000000 : ℝ)+(138088159258373/12500000000000000000 : ℝ) ≤ ((134733401234985532543/134770000000000000000 : ℝ)+(1460179986547/673850000000000 : ℝ)*((9933/50000 : ℝ)+(6389/100000 : ℝ)))^(4249/1024 : ℝ) := by
    rw [show (134733401234985532543/134770000000000000000 : ℝ)+(1460179986547/673850000000000 : ℝ)*((9933/50000 : ℝ)+(6389/100000 : ℝ))=(10002973605852869/10000000000000000 : ℝ) by norm_num, show 1+(61170151620146483/50000000000000000000 : ℝ)+(138088159258373/12500000000000000000 : ℝ)=(2002468900170287199/2000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(61170151620146483/50000000000000000000 : ℝ) ≤ ((134733401234985532543/134770000000000000000 : ℝ)+2*(1460179986547/673850000000000 : ℝ)*(9933/50000 : ℝ))^(4249/1024 : ℝ) := by
    rw [show (134733401234985532543/134770000000000000000 : ℝ)+2*(1460179986547/673850000000000 : ℝ)*(9933/50000 : ℝ)=(10005893965825963/10000000000000000 : ℝ) by norm_num, show 1+2*(61170151620146483/50000000000000000000 : ℝ)=(25061170151620146483/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (134733401234985532543/134770000000000000000 : ℝ)*(X 1 0+X 2 0)+(1460179986547/673850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4249/1024 : ℝ)) (lo := (6389/100000 : ℝ)) (hi := (9933/50000 : ℝ)) (c := (134733401234985532543/134770000000000000000 : ℝ)) (alpha := (1460179986547/673850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (134733401234985532543/134770000000000000000 : ℝ)*(X 0 1+X 2 1)+(1460179986547/673850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4249/1024 : ℝ)) (lo := (6389/100000 : ℝ)) (hi := (9933/50000 : ℝ)) (c := (134733401234985532543/134770000000000000000 : ℝ)) (alpha := (1460179986547/673850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (134733401234985532543/134770000000000000000 : ℝ)*(X 0 2+X 1 2)+(1460179986547/673850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4249/1024 : ℝ)) (lo := (6389/100000 : ℝ)) (hi := (9933/50000 : ℝ)) (c := (134733401234985532543/134770000000000000000 : ℝ)) (alpha := (1460179986547/673850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2077510101/10000000000 : ℝ)*X 0 0+(5494863181/10000000000 : ℝ)*X 0 1+(5171368463/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5369732717/10000000000 : ℝ)*X 1 0+(-2245172091/10000000000 : ℝ)*X 1 1+(646421093/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2684866421/5000000000 : ℝ)*X 2 0+(32321053/62500000 : ℝ)*X 2 1+(-224517227/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2166342133/5000000000 : ℝ)*X 0 0+(802529943/2000000000 : ℝ)*X 0 1+(2338503623/5000000000 : ℝ)*X 0 2+(2166342133/5000000000 : ℝ)*X 1 0+(802529943/2000000000 : ℝ)*X 1 1+(2338503623/5000000000 : ℝ)*X 1 2+(2166342133/5000000000 : ℝ)*X 2 0+(802529943/2000000000 : ℝ)*X 2 1+(2338503623/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-415518611/2000000000 : ℝ)*X 0 0+(5173520903/10000000000 : ℝ)*X 0 1+(1098538121/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2643420307/5000000000 : ℝ)*X 1 0+(-1923849597/10000000000 : ℝ)*X 1 1+(5492690747/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((330427549/625000000 : ℝ)*X 2 0+(5492690613/10000000000 : ℝ)*X 2 1+(-1923849549/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4332854363/10000000000 : ℝ)*X 0 0+(1168146329/2500000000 : ℝ)*X 0 1+(62767441/156250000 : ℝ)*X 0 2+(4332854363/10000000000 : ℝ)*X 1 0+(1168146329/2500000000 : ℝ)*X 1 1+(62767441/156250000 : ℝ)*X 1 2+(4332854363/10000000000 : ℝ)*X 2 0+(1168146329/2500000000 : ℝ)*X 2 1+(62767441/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1462639940686349619160593177/336925000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (221868679/12500000000000 : ℝ)*(base19) + (1656210647/100000000000000 : ℝ)*(base23) + (25600103/25000000000000 : ℝ)*(lower2) + (263336681/50000000000000 : ℝ)*(upper3) + (259128599/100000000000000 : ℝ)*(upper5) + (229825751206013/10000000000000 : ℝ)*(major0) + (229825751206013/10000000000000 : ℝ)*(major1) + (229825751206013/10000000000000 : ℝ)*(major2) + (3091257368060957/100000000000000 : ℝ)*(sp0) + (3091268578490071/100000000000000 : ℝ)*(sp1) + (386408587153607/12500000000000 : ℝ)*(sp2) + (752613779922933/50000000000000 : ℝ)*(sp3) + (2597075709/20000000000000 : ℝ)*(sp4) + (4241532521/25000000000000 : ℝ)*(sp7) + (30104890519519/2000000000000 : ℝ)*(f.failure) + (3091270353439503/100000000000000 : ℝ)*(f.sum) + (3002423448897/3369250000000000000000000000 : ℝ)*base66 + (1471626477671218941/1347700000000000000000000000000000 : ℝ)*base68 + (8729356988732618941/1347700000000000000000000000000000 : ℝ)*base70 + (9177544174882518941/1347700000000000000000000000000000 : ℝ)*base72 + (602122467223/13477000000000000000000000000 : ℝ)*base73 + (23422348973914218941/1347700000000000000000000000000000 : ℝ)*base76 + (16919994213189018941/1347700000000000000000000000000000 : ℝ)*base78 + (4786137439143181059/1347700000000000000000000000000000 : ℝ)*base79 + (52738984309/168462500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (2476827/200000000000000000000 : ℝ)*base89 + (2476827/200000000000000000000 : ℝ)*base91 + (2476827/200000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4712585402671725361791467859/1684625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (107661669/20000000000000 : ℝ)*(base19) + (793331301/100000000000000 : ℝ)*(base23) + (28812547/25000000000000 : ℝ)*(upper3) + (13100883/25000000000000 : ℝ)*(lower4) + (582344148727871/25000000000000 : ℝ)*(major0) + (582344148727871/25000000000000 : ℝ)*(major1) + (582344148727871/25000000000000 : ℝ)*(major2) + (2674457931/50000000000000 : ℝ)*(sp1) + (1773346763/20000000000000 : ℝ)*(sp2) + (9455991/100000000000000 : ℝ)*(sp3) + (78328177922037/2500000000000 : ℝ)*(sp4) + (3133121229657273/100000000000000 : ℝ)*(sp5) + (3133117456816363/100000000000000 : ℝ)*(sp6) + (1525625970238521/100000000000000 : ℝ)*(sp7) + (95351623730907/6250000000000 : ℝ)*(f.failure) + (78328177922037/2500000000000 : ℝ)*(f.sum) + (263318226763169/67385000000000000000000000000 : ℝ)*base66 + (18053988631980244047/3369250000000000000000000000000000 : ℝ)*base68 + (10194014392923494047/3369250000000000000000000000000000 : ℝ)*base70 + (20894504803587244047/3369250000000000000000000000000000 : ℝ)*base72 + (34443548790483/33692500000000000000000000000 : ℝ)*base73 + (2183010188390755953/3369250000000000000000000000000000 : ℝ)*base75 + (12558502361997744047/3369250000000000000000000000000000 : ℝ)*base78 + (14282471534249005953/3369250000000000000000000000000000 : ℝ)*base79 + (78465122273409/67385000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (873031/625000000000000000000 : ℝ)*base89 + (873031/625000000000000000000 : ℝ)*base91 + (873031/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1290_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152683333/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9933/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6389/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (949/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8163/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1290_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1290_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152683333/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (949/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8163/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1290_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1290_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1290_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152683333/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (949/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8163/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1290_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
