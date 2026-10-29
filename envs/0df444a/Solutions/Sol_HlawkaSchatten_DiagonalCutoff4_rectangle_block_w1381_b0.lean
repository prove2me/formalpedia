-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1381_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:23:28.996923+00:00
-- url     : https://prove2.me/submissions/f3e4bedd-9379-4560-89a8-909516580efd

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
theorem support_rectangle_w1381_s0_0 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-178631333/1000000000 : ℝ)*x 0 + (2990121243/5000000000 : ℝ)*x 1 + (964025677/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (178631333/1000000000 : ℝ)^4341 ≤ (5248044057447/50000000000000 : ℝ)^3317 := by
    have hnat : (178631333 : ℕ)^4341*50000000000000^3317 ≤ 5248044057447^3317*1000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      178631333 1000000000 5248044057447 50000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2990121243/5000000000 : ℝ)^4341 ≤ (51025709460407/100000000000000 : ℝ)^3317 := by
    have hnat : (2990121243 : ℕ)^4341*100000000000000^3317 ≤ 51025709460407^3317*5000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2990121243 5000000000 51025709460407 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (964025677/2000000000 : ℝ)^4341 ≤ (38478202410589/100000000000000 : ℝ)^3317 := by
    have hnat : (964025677 : ℕ)^4341*100000000000000^3317 ≤ 38478202410589^3317*2000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      964025677 2000000000 38478202410589 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-178631333/1000000000 : ℝ), (2990121243/5000000000 : ℝ), (964025677/2000000000 : ℝ)] ![(5248044057447/50000000000000 : ℝ), (51025709460407/100000000000000 : ℝ), (38478202410589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-178631333/1000000000 : ℝ)|^4341 ≤ (5248044057447/50000000000000 : ℝ)^3317
        have hw : |(-178631333/1000000000 : ℝ)|=(178631333/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2990121243/5000000000 : ℝ)|^4341 ≤ (51025709460407/100000000000000 : ℝ)^3317
        have hw : |(2990121243/5000000000 : ℝ)|=(2990121243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(964025677/2000000000 : ℝ)|^4341 ≤ (38478202410589/100000000000000 : ℝ)^3317
        have hw : |(964025677/2000000000 : ℝ)|=(964025677/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s0_1 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5497450631/10000000000 : ℝ)*x 0 + (-122193489/500000000 : ℝ)*x 1 + (241006453/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5497450631/10000000000 : ℝ)^4341 ≤ (2856444974437/6250000000000 : ℝ)^3317 := by
    have hnat : (5497450631 : ℕ)^4341*6250000000000^3317 ≤ 2856444974437^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5497450631 10000000000 2856444974437 6250000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (122193489/500000000 : ℝ)^4341 ≤ (15818670938797/100000000000000 : ℝ)^3317 := by
    have hnat : (122193489 : ℕ)^4341*100000000000000^3317 ≤ 15818670938797^3317*500000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122193489 500000000 15818670938797 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (241006453/500000000 : ℝ)^4341 ≤ (38478209462459/100000000000000 : ℝ)^3317 := by
    have hnat : (241006453 : ℕ)^4341*100000000000000^3317 ≤ 38478209462459^3317*500000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241006453 500000000 38478209462459 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5497450631/10000000000 : ℝ), (-122193489/500000000 : ℝ), (241006453/500000000 : ℝ)] ![(2856444974437/6250000000000 : ℝ), (15818670938797/100000000000000 : ℝ), (38478209462459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5497450631/10000000000 : ℝ)|^4341 ≤ (2856444974437/6250000000000 : ℝ)^3317
        have hw : |(5497450631/10000000000 : ℝ)|=(5497450631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-122193489/500000000 : ℝ)|^4341 ≤ (15818670938797/100000000000000 : ℝ)^3317
        have hw : |(-122193489/500000000 : ℝ)|=(122193489/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(241006453/500000000 : ℝ)|^4341 ≤ (38478209462459/100000000000000 : ℝ)^3317
        have hw : |(241006453/500000000 : ℝ)|=(241006453/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s0_2 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5497450493/10000000000 : ℝ)*x 0 + (4820128283/10000000000 : ℝ)*x 1 + (-488774183/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5497450493/10000000000 : ℝ)^4341 ≤ (2856444880597/6250000000000 : ℝ)^3317 := by
    have hnat : (5497450493 : ℕ)^4341*6250000000000^3317 ≤ 2856444880597^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5497450493 10000000000 2856444880597 6250000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4820128283/10000000000 : ℝ)^4341 ≤ (38478201344973/100000000000000 : ℝ)^3317 := by
    have hnat : (4820128283 : ℕ)^4341*100000000000000^3317 ≤ 38478201344973^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4820128283 10000000000 38478201344973 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (488774183/2000000000 : ℝ)^4341 ≤ (15818680553417/100000000000000 : ℝ)^3317 := by
    have hnat : (488774183 : ℕ)^4341*100000000000000^3317 ≤ 15818680553417^3317*2000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      488774183 2000000000 15818680553417 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5497450493/10000000000 : ℝ), (4820128283/10000000000 : ℝ), (-488774183/2000000000 : ℝ)] ![(2856444880597/6250000000000 : ℝ), (38478201344973/100000000000000 : ℝ), (15818680553417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5497450493/10000000000 : ℝ)|^4341 ≤ (2856444880597/6250000000000 : ℝ)^3317
        have hw : |(5497450493/10000000000 : ℝ)|=(5497450493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4820128283/10000000000 : ℝ)|^4341 ≤ (38478201344973/100000000000000 : ℝ)^3317
        have hw : |(4820128283/10000000000 : ℝ)|=(4820128283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-488774183/2000000000 : ℝ)|^4341 ≤ (15818680553417/100000000000000 : ℝ)^3317
        have hw : |(-488774183/2000000000 : ℝ)|=(488774183/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s0_3 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4172966531/10000000000 : ℝ)*x 0 + (3104857397/10000000000 : ℝ)*x 1 + (1392625697/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4172966531/10000000000 : ℝ)^4341 ≤ (1593094101147/5000000000000 : ℝ)^3317 := by
    have hnat : (4172966531 : ℕ)^4341*5000000000000^3317 ≤ 1593094101147^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172966531 10000000000 1593094101147 5000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3104857397/10000000000 : ℝ)^4341 ≤ (4327713146301/20000000000000 : ℝ)^3317 := by
    have hnat : (3104857397 : ℕ)^4341*20000000000000^3317 ≤ 4327713146301^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3104857397 10000000000 4327713146301 20000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1392625697/2500000000 : ℝ)^4341 ≤ (46499552224219/100000000000000 : ℝ)^3317 := by
    have hnat : (1392625697 : ℕ)^4341*100000000000000^3317 ≤ 46499552224219^3317*2500000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1392625697 2500000000 46499552224219 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4172966531/10000000000 : ℝ), (3104857397/10000000000 : ℝ), (1392625697/2500000000 : ℝ)] ![(1593094101147/5000000000000 : ℝ), (4327713146301/20000000000000 : ℝ), (46499552224219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4172966531/10000000000 : ℝ)|^4341 ≤ (1593094101147/5000000000000 : ℝ)^3317
        have hw : |(4172966531/10000000000 : ℝ)|=(4172966531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3104857397/10000000000 : ℝ)|^4341 ≤ (4327713146301/20000000000000 : ℝ)^3317
        have hw : |(3104857397/10000000000 : ℝ)|=(3104857397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1392625697/2500000000 : ℝ)|^4341 ≤ (46499552224219/100000000000000 : ℝ)^3317
        have hw : |(1392625697/2500000000 : ℝ)|=(1392625697/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s0_4 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-55955287/312500000 : ℝ)*x 0 + (4849913473/10000000000 : ℝ)*x 1 + (297469641/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (55955287/312500000 : ℝ)^4341 ≤ (1316103342711/12500000000000 : ℝ)^3317 := by
    have hnat : (55955287 : ℕ)^4341*12500000000000^3317 ≤ 1316103342711^3317*312500000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55955287 312500000 1316103342711 12500000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4849913473/10000000000 : ℝ)^4341 ≤ (9697417493041/25000000000000 : ℝ)^3317 := by
    have hnat : (4849913473 : ℕ)^4341*25000000000000^3317 ≤ 9697417493041^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4849913473 10000000000 9697417493041 25000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (297469641/500000000 : ℝ)^4341 ≤ (25340751635201/50000000000000 : ℝ)^3317 := by
    have hnat : (297469641 : ℕ)^4341*50000000000000^3317 ≤ 25340751635201^3317*500000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      297469641 500000000 25340751635201 50000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-55955287/312500000 : ℝ), (4849913473/10000000000 : ℝ), (297469641/500000000 : ℝ)] ![(1316103342711/12500000000000 : ℝ), (9697417493041/25000000000000 : ℝ), (25340751635201/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-55955287/312500000 : ℝ)|^4341 ≤ (1316103342711/12500000000000 : ℝ)^3317
        have hw : |(-55955287/312500000 : ℝ)|=(55955287/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4849913473/10000000000 : ℝ)|^4341 ≤ (9697417493041/25000000000000 : ℝ)^3317
        have hw : |(4849913473/10000000000 : ℝ)|=(4849913473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(297469641/500000000 : ℝ)|^4341 ≤ (25340751635201/50000000000000 : ℝ)^3317
        have hw : |(297469641/500000000 : ℝ)|=(297469641/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s0_5 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2590526409/5000000000 : ℝ)*x 0 + (-1314606661/10000000000 : ℝ)*x 1 + (2974696339/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2590526409/5000000000 : ℝ)^4341 ≤ (8458341848031/20000000000000 : ℝ)^3317 := by
    have hnat : (2590526409 : ℕ)^4341*20000000000000^3317 ≤ 8458341848031^3317*5000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590526409 5000000000 8458341848031 20000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1314606661/10000000000 : ℝ)^4341 ≤ (1756697264397/25000000000000 : ℝ)^3317 := by
    have hnat : (1314606661 : ℕ)^4341*25000000000000^3317 ≤ 1756697264397^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314606661 10000000000 1756697264397 25000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2974696339/5000000000 : ℝ)^4341 ≤ (25340750843649/50000000000000 : ℝ)^3317 := by
    have hnat : (2974696339 : ℕ)^4341*50000000000000^3317 ≤ 25340750843649^3317*5000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2974696339 5000000000 25340750843649 50000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2590526409/5000000000 : ℝ), (-1314606661/10000000000 : ℝ), (2974696339/5000000000 : ℝ)] ![(8458341848031/20000000000000 : ℝ), (1756697264397/25000000000000 : ℝ), (25340750843649/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2590526409/5000000000 : ℝ)|^4341 ≤ (8458341848031/20000000000000 : ℝ)^3317
        have hw : |(2590526409/5000000000 : ℝ)|=(2590526409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1314606661/10000000000 : ℝ)|^4341 ≤ (1756697264397/25000000000000 : ℝ)^3317
        have hw : |(-1314606661/10000000000 : ℝ)|=(1314606661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2974696339/5000000000 : ℝ)|^4341 ≤ (25340750843649/50000000000000 : ℝ)^3317
        have hw : |(2974696339/5000000000 : ℝ)|=(2974696339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s0_6 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1295263129/2500000000 : ℝ)*x 0 + (371837051/625000000 : ℝ)*x 1 + (-1314606903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1295263129/2500000000 : ℝ)^4341 ≤ (5286463251747/12500000000000 : ℝ)^3317 := by
    have hnat : (1295263129 : ℕ)^4341*12500000000000^3317 ≤ 5286463251747^3317*2500000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295263129 2500000000 5286463251747 12500000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (371837051/625000000 : ℝ)^4341 ≤ (50681503225807/100000000000000 : ℝ)^3317 := by
    have hnat : (371837051 : ℕ)^4341*100000000000000^3317 ≤ 50681503225807^3317*625000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      371837051 625000000 50681503225807 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1314606903/10000000000 : ℝ)^4341 ≤ (7026790750447/100000000000000 : ℝ)^3317 := by
    have hnat : (1314606903 : ℕ)^4341*100000000000000^3317 ≤ 7026790750447^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314606903 10000000000 7026790750447 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1295263129/2500000000 : ℝ), (371837051/625000000 : ℝ), (-1314606903/10000000000 : ℝ)] ![(5286463251747/12500000000000 : ℝ), (50681503225807/100000000000000 : ℝ), (7026790750447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1295263129/2500000000 : ℝ)|^4341 ≤ (5286463251747/12500000000000 : ℝ)^3317
        have hw : |(1295263129/2500000000 : ℝ)|=(1295263129/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(371837051/625000000 : ℝ)|^4341 ≤ (50681503225807/100000000000000 : ℝ)^3317
        have hw : |(371837051/625000000 : ℝ)|=(371837051/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1314606903/10000000000 : ℝ)|^4341 ≤ (7026790750447/100000000000000 : ℝ)^3317
        have hw : |(-1314606903/10000000000 : ℝ)|=(1314606903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s0_7 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (836401853/2000000000 : ℝ)*x 0 + (5507198917/10000000000 : ℝ)*x 1 + (3170423561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (836401853/2000000000 : ℝ)^4341 ≤ (15976135530343/50000000000000 : ℝ)^3317 := by
    have hnat : (836401853 : ℕ)^4341*50000000000000^3317 ≤ 15976135530343^3317*2000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      836401853 2000000000 15976135530343 50000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5507198917/10000000000 : ℝ)^4341 ≤ (22904604971429/50000000000000 : ℝ)^3317 := by
    have hnat : (5507198917 : ℕ)^4341*50000000000000^3317 ≤ 22904604971429^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5507198917 10000000000 22904604971429 50000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3170423561/10000000000 : ℝ)^4341 ≤ (11119259494593/50000000000000 : ℝ)^3317 := by
    have hnat : (3170423561 : ℕ)^4341*50000000000000^3317 ≤ 11119259494593^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3170423561 10000000000 11119259494593 50000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(836401853/2000000000 : ℝ), (5507198917/10000000000 : ℝ), (3170423561/10000000000 : ℝ)] ![(15976135530343/50000000000000 : ℝ), (22904604971429/50000000000000 : ℝ), (11119259494593/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(836401853/2000000000 : ℝ)|^4341 ≤ (15976135530343/50000000000000 : ℝ)^3317
        have hw : |(836401853/2000000000 : ℝ)|=(836401853/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5507198917/10000000000 : ℝ)|^4341 ≤ (22904604971429/50000000000000 : ℝ)^3317
        have hw : |(5507198917/10000000000 : ℝ)|=(5507198917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3170423561/10000000000 : ℝ)|^4341 ≤ (11119259494593/50000000000000 : ℝ)^3317
        have hw : |(3170423561/10000000000 : ℝ)|=(3170423561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1381_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1220839/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1703/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26593/100000 : ℝ)*pair X 0 0 := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (1085/256 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^1085 ≤ (0 : ℝ)^256 := by
      have hnat : (0 : ℕ)^1085*1^256 ≤ 0^256*1^1085 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 1085 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 1085 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (1085/256 : ℝ) ≤ (257233979001112143/12500000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^1085 ≤ (257233979001112143/12500000000000000000 : ℝ)^256 := by
      have hnat : (2 : ℕ)^1085*12500000000000000000^256 ≤ 257233979001112143^256*5^1085 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 257233979001112143 12500000000000000000 1085 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (257233979001112143/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 1085 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (1085/256 : ℝ) := by
    have hpowers : (1 : ℝ)^256 ≤ (1 : ℝ)^1085 := by
      have hnat : (1 : ℕ)^256*1^1085 ≤ 1^1085*1^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 256 1085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 1085 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (12757233979001112143/12500000000000000000 : ℝ) ≤ (2512044308125367/2500000000000000 : ℝ) ^ (1085/256 : ℝ) := by
    have hpowers : (12757233979001112143/12500000000000000000 : ℝ)^256 ≤ (2512044308125367/2500000000000000 : ℝ)^1085 := by
      have hnat : (12757233979001112143 : ℕ)^256*2500000000000000^1085 ≤ 2512044308125367^1085*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12757233979001112143 12500000000000000000 2512044308125367 2500000000000000 256 1085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2512044308125367/2500000000000000 : ℝ)) (X := (12757233979001112143/12500000000000000000 : ℝ)) (by norm_num) 1085 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (6507233979001112143/6250000000000000000 : ℝ) ≤ (1262044308125367/1250000000000000 : ℝ) ^ (1085/256 : ℝ) := by
    have hpowers : (6507233979001112143/6250000000000000000 : ℝ)^256 ≤ (1262044308125367/1250000000000000 : ℝ)^1085 := by
      have hnat : (6507233979001112143 : ℕ)^256*1250000000000000^1085 ≤ 1262044308125367^1085*6250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6507233979001112143 6250000000000000000 1262044308125367 1250000000000000 256 1085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1262044308125367/1250000000000000 : ℝ)) (X := (6507233979001112143/6250000000000000000 : ℝ)) (by norm_num) 1085 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(12044308125367/1000000000000000 : ℝ)*(0 : ℝ))^(1085/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(12044308125367/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(257233979001112143/12500000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(12044308125367/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(1085/256 : ℝ) := by
    rw [show (1 : ℝ)+(12044308125367/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2512044308125367/2500000000000000 : ℝ) by norm_num, show 1+(257233979001112143/12500000000000000000 : ℝ)+(0 : ℝ)=(12757233979001112143/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(257233979001112143/12500000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(12044308125367/1000000000000000 : ℝ)*(2/5 : ℝ))^(1085/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(12044308125367/1000000000000000 : ℝ)*(2/5 : ℝ)=(1262044308125367/1250000000000000 : ℝ) by norm_num, show 1+2*(257233979001112143/12500000000000000000 : ℝ)=(6507233979001112143/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(12044308125367/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1085/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12044308125367/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(12044308125367/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1085/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12044308125367/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(12044308125367/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1085/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12044308125367/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-178631333/1000000000 : ℝ)*X 0 0+(2990121243/5000000000 : ℝ)*X 0 1+(964025677/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5497450631/10000000000 : ℝ)*X 1 0+(-122193489/500000000 : ℝ)*X 1 1+(241006453/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5497450493/10000000000 : ℝ)*X 2 0+(4820128283/10000000000 : ℝ)*X 2 1+(-488774183/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4172966531/10000000000 : ℝ)*X 0 0+(3104857397/10000000000 : ℝ)*X 0 1+(1392625697/2500000000 : ℝ)*X 0 2+(4172966531/10000000000 : ℝ)*X 1 0+(3104857397/10000000000 : ℝ)*X 1 1+(1392625697/2500000000 : ℝ)*X 1 2+(4172966531/10000000000 : ℝ)*X 2 0+(3104857397/10000000000 : ℝ)*X 2 1+(1392625697/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-55955287/312500000 : ℝ)*X 0 0+(4849913473/10000000000 : ℝ)*X 0 1+(297469641/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2590526409/5000000000 : ℝ)*X 1 0+(-1314606661/10000000000 : ℝ)*X 1 1+(2974696339/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1295263129/2500000000 : ℝ)*X 2 0+(371837051/625000000 : ℝ)*X 2 1+(-1314606903/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((836401853/2000000000 : ℝ)*X 0 0+(5507198917/10000000000 : ℝ)*X 0 1+(3170423561/10000000000 : ℝ)*X 0 2+(836401853/2000000000 : ℝ)*X 1 0+(5507198917/10000000000 : ℝ)*X 1 1+(3170423561/10000000000 : ℝ)*X 1 2+(836401853/2000000000 : ℝ)*X 2 0+(5507198917/10000000000 : ℝ)*X 2 1+(3170423561/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (58108019352514571539167/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (239543667/100000000000000 : ℝ)*(base1) + (17886033/50000000000000 : ℝ)*(base16) + (1049174737/100000000000000 : ℝ)*(base19) + (265827171/25000000000000 : ℝ)*(base23) + (11433803/6250000000000 : ℝ)*(upper3) + (316891578529011/50000000000000 : ℝ)*(major0) + (316891578529011/50000000000000 : ℝ)*(major1) + (316891578529011/50000000000000 : ℝ)*(major2) + (861987789781083/100000000000000 : ℝ)*(sp0) + (861988997883747/100000000000000 : ℝ)*(sp1) + (172397803904373/20000000000000 : ℝ)*(sp2) + (405574306607567/100000000000000 : ℝ)*(sp3) + (1266296567/50000000000000 : ℝ)*(sp4) + (765089767/50000000000000 : ℝ)*(sp7) + (405576076330769/100000000000000 : ℝ)*(f.failure) + (17239801656611/2000000000000 : ℝ)*(f.sum) + (95729745997037/25000000000000000000000000000 : ℝ)*base65 + (229641109672037/50000000000000000000000000000 : ℝ)*base67 + (119233024272037/50000000000000000000000000000 : ℝ)*base69 + (334268987322037/50000000000000000000000000000 : ℝ)*base71 + (102194281597037/25000000000000000000000000000 : ℝ)*base73 + (173675575022037/50000000000000000000000000000 : ℝ)*base75 + (296332232922037/50000000000000000000000000000 : ℝ)*base77 + (768950055922037/50000000000000000000000000000 : ℝ)*base79 + (20221312147037/25000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (7691/78125000000000000000 : ℝ)*base89 + (7691/78125000000000000000 : ℝ)*base91 + (7691/78125000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5935748109058091642001/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1177844931/100000000000000 : ℝ)*(base19) + (561183839/50000000000000 : ℝ)*(base23) + (27011537/25000000000000 : ℝ)*(base32) + (32144693/20000000000000 : ℝ)*(upper3) + (55262847/50000000000000 : ℝ)*(upper5) + (33436526531599/5000000000000 : ℝ)*(major0) + (33436526531599/5000000000000 : ℝ)*(major1) + (33436526531599/5000000000000 : ℝ)*(major2) + (1343619251/50000000000000 : ℝ)*(sp1) + (661730537/25000000000000 : ℝ)*(sp2) + (181904199370059/20000000000000 : ℝ)*(sp4) + (454758565883431/50000000000000 : ℝ)*(sp5) + (909517227560469/100000000000000 : ℝ)*(sp6) + (3343279672507/781250000000 : ℝ)*(sp7) + (106984976531761/25000000000000 : ℝ)*(f.failure) + (181904199370059/20000000000000 : ℝ)*(f.sum) + (5397801428167/2500000000000000000000000000 : ℝ)*base66 + (60039608136833/5000000000000000000000000000 : ℝ)*base67 + (2358816191833/5000000000000000000000000000 : ℝ)*base69 + (24895112381833/5000000000000000000000000000 : ℝ)*base71 + (9722548246833/2500000000000000000000000000 : ℝ)*base73 + (17663702911833/5000000000000000000000000000 : ℝ)*base75 + (6103626931833/5000000000000000000000000000 : ℝ)*base77 + (41721717871833/5000000000000000000000000000 : ℝ)*base79 + (10636190350667/2500000000000000000000000000 : ℝ)*base82 + (26271/19531250000000000000 : ℝ)*base90 + (26271/19531250000000000000 : ℝ)*base92 + (26271/19531250000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1381_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1220839/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1703/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26593/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1381_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1381_s1_0 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-393103641/2000000000 : ℝ)*x 0 + (2812534517/5000000000 : ℝ)*x 1 + (39535093/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (393103641/2000000000 : ℝ)^4341 ≤ (1486875098317/12500000000000 : ℝ)^3317 := by
    have hnat : (393103641 : ℕ)^4341*12500000000000^3317 ≤ 1486875098317^3317*2000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393103641 2000000000 1486875098317 12500000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2812534517/5000000000 : ℝ)^4341 ≤ (23548278257741/50000000000000 : ℝ)^3317 := by
    have hnat : (2812534517 : ℕ)^4341*50000000000000^3317 ≤ 23548278257741^3317*5000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2812534517 5000000000 23548278257741 50000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (39535093/78125000 : ℝ)^4341 ≤ (20504221342157/50000000000000 : ℝ)^3317 := by
    have hnat : (39535093 : ℕ)^4341*50000000000000^3317 ≤ 20504221342157^3317*78125000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39535093 78125000 20504221342157 50000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-393103641/2000000000 : ℝ), (2812534517/5000000000 : ℝ), (39535093/78125000 : ℝ)] ![(1486875098317/12500000000000 : ℝ), (23548278257741/50000000000000 : ℝ), (20504221342157/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-393103641/2000000000 : ℝ)|^4341 ≤ (1486875098317/12500000000000 : ℝ)^3317
        have hw : |(-393103641/2000000000 : ℝ)|=(393103641/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2812534517/5000000000 : ℝ)|^4341 ≤ (23548278257741/50000000000000 : ℝ)^3317
        have hw : |(2812534517/5000000000 : ℝ)|=(2812534517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(39535093/78125000 : ℝ)|^4341 ≤ (20504221342157/50000000000000 : ℝ)^3317
        have hw : |(39535093/78125000 : ℝ)|=(39535093/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s1_1 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5401680689/10000000000 : ℝ)*x 0 + (-566452729/2500000000 : ℝ)*x 1 + (2530246669/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5401680689/10000000000 : ℝ)^4341 ≤ (44663956016311/100000000000000 : ℝ)^3317 := by
    have hnat : (5401680689 : ℕ)^4341*100000000000000^3317 ≤ 44663956016311^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401680689 10000000000 44663956016311 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (566452729/2500000000 : ℝ)^4341 ≤ (14327586082651/100000000000000 : ℝ)^3317 := by
    have hnat : (566452729 : ℕ)^4341*100000000000000^3317 ≤ 14327586082651^3317*2500000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566452729 2500000000 14327586082651 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2530246669/5000000000 : ℝ)^4341 ≤ (20504228946191/50000000000000 : ℝ)^3317 := by
    have hnat : (2530246669 : ℕ)^4341*50000000000000^3317 ≤ 20504228946191^3317*5000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2530246669 5000000000 20504228946191 50000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5401680689/10000000000 : ℝ), (-566452729/2500000000 : ℝ), (2530246669/5000000000 : ℝ)] ![(44663956016311/100000000000000 : ℝ), (14327586082651/100000000000000 : ℝ), (20504228946191/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5401680689/10000000000 : ℝ)|^4341 ≤ (44663956016311/100000000000000 : ℝ)^3317
        have hw : |(5401680689/10000000000 : ℝ)|=(5401680689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-566452729/2500000000 : ℝ)|^4341 ≤ (14327586082651/100000000000000 : ℝ)^3317
        have hw : |(-566452729/2500000000 : ℝ)|=(566452729/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2530246669/5000000000 : ℝ)|^4341 ≤ (20504228946191/50000000000000 : ℝ)^3317
        have hw : |(2530246669/5000000000 : ℝ)|=(2530246669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s1_2 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5401681383/10000000000 : ℝ)*x 0 + (5060492089/10000000000 : ℝ)*x 1 + (-283226451/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5401681383/10000000000 : ℝ)^4341 ≤ (1786558541047/4000000000000 : ℝ)^3317 := by
    have hnat : (5401681383 : ℕ)^4341*4000000000000^3317 ≤ 1786558541047^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401681383 10000000000 1786558541047 4000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5060492089/10000000000 : ℝ)^4341 ≤ (41008444646303/100000000000000 : ℝ)^3317 := by
    have hnat : (5060492089 : ℕ)^4341*100000000000000^3317 ≤ 41008444646303^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5060492089 10000000000 41008444646303 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (283226451/1250000000 : ℝ)^4341 ≤ (1432759180929/10000000000000 : ℝ)^3317 := by
    have hnat : (283226451 : ℕ)^4341*10000000000000^3317 ≤ 1432759180929^3317*1250000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283226451 1250000000 1432759180929 10000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5401681383/10000000000 : ℝ), (5060492089/10000000000 : ℝ), (-283226451/1250000000 : ℝ)] ![(1786558541047/4000000000000 : ℝ), (41008444646303/100000000000000 : ℝ), (1432759180929/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5401681383/10000000000 : ℝ)|^4341 ≤ (1786558541047/4000000000000 : ℝ)^3317
        have hw : |(5401681383/10000000000 : ℝ)|=(5401681383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5060492089/10000000000 : ℝ)|^4341 ≤ (41008444646303/100000000000000 : ℝ)^3317
        have hw : |(5060492089/10000000000 : ℝ)|=(5060492089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-283226451/1250000000 : ℝ)|^4341 ≤ (1432759180929/10000000000000 : ℝ)^3317
        have hw : |(-283226451/1250000000 : ℝ)|=(283226451/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s1_3 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4285323119/10000000000 : ℝ)*x 0 + (3723633351/10000000000 : ℝ)*x 1 + (984710261/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4285323119/10000000000 : ℝ)^4341 ≤ (4123654256751/12500000000000 : ℝ)^3317 := by
    have hnat : (4285323119 : ℕ)^4341*12500000000000^3317 ≤ 4123654256751^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4285323119 10000000000 4123654256751 12500000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3723633351/10000000000 : ℝ)^4341 ≤ (13724260600099/50000000000000 : ℝ)^3317 := by
    have hnat : (3723633351 : ℕ)^4341*50000000000000^3317 ≤ 13724260600099^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3723633351 10000000000 13724260600099 50000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (984710261/2000000000 : ℝ)^4341 ≤ (39562244726653/100000000000000 : ℝ)^3317 := by
    have hnat : (984710261 : ℕ)^4341*100000000000000^3317 ≤ 39562244726653^3317*2000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      984710261 2000000000 39562244726653 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4285323119/10000000000 : ℝ), (3723633351/10000000000 : ℝ), (984710261/2000000000 : ℝ)] ![(4123654256751/12500000000000 : ℝ), (13724260600099/50000000000000 : ℝ), (39562244726653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4285323119/10000000000 : ℝ)|^4341 ≤ (4123654256751/12500000000000 : ℝ)^3317
        have hw : |(4285323119/10000000000 : ℝ)|=(4285323119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3723633351/10000000000 : ℝ)|^4341 ≤ (13724260600099/50000000000000 : ℝ)^3317
        have hw : |(3723633351/10000000000 : ℝ)|=(3723633351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(984710261/2000000000 : ℝ)|^4341 ≤ (39562244726653/100000000000000 : ℝ)^3317
        have hw : |(984710261/2000000000 : ℝ)|=(984710261/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s1_4 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-393197539/2000000000 : ℝ)*x 0 + (202694639/400000000 : ℝ)*x 1 + (5618073689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (393197539/2000000000 : ℝ)^4341 ≤ (11898719340397/100000000000000 : ℝ)^3317 := by
    have hnat : (393197539 : ℕ)^4341*100000000000000^3317 ≤ 11898719340397^3317*2000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393197539 2000000000 11898719340397 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (202694639/400000000 : ℝ)^4341 ≤ (41081359869113/100000000000000 : ℝ)^3317 := by
    have hnat : (202694639 : ℕ)^4341*100000000000000^3317 ≤ 41081359869113^3317*400000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202694639 400000000 41081359869113 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5618073689/10000000000 : ℝ)^4341 ≤ (23509960388013/50000000000000 : ℝ)^3317 := by
    have hnat : (5618073689 : ℕ)^4341*50000000000000^3317 ≤ 23509960388013^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5618073689 10000000000 23509960388013 50000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-393197539/2000000000 : ℝ), (202694639/400000000 : ℝ), (5618073689/10000000000 : ℝ)] ![(11898719340397/100000000000000 : ℝ), (41081359869113/100000000000000 : ℝ), (23509960388013/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-393197539/2000000000 : ℝ)|^4341 ≤ (11898719340397/100000000000000 : ℝ)^3317
        have hw : |(-393197539/2000000000 : ℝ)|=(393197539/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(202694639/400000000 : ℝ)|^4341 ≤ (41081359869113/100000000000000 : ℝ)^3317
        have hw : |(202694639/400000000 : ℝ)|=(202694639/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5618073689/10000000000 : ℝ)|^4341 ≤ (23509960388013/50000000000000 : ℝ)^3317
        have hw : |(5618073689/10000000000 : ℝ)|=(5618073689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s1_5 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050942929/2000000000 : ℝ)*x 0 + (-85411517/500000000 : ℝ)*x 1 + (5618073771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050942929/2000000000 : ℝ)^4341 ≤ (5385042330561/12500000000000 : ℝ)^3317 := by
    have hnat : (1050942929 : ℕ)^4341*12500000000000^3317 ≤ 5385042330561^3317*2000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050942929 2000000000 5385042330561 12500000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (85411517/500000000 : ℝ)^4341 ≤ (4949869829303/50000000000000 : ℝ)^3317 := by
    have hnat : (85411517 : ℕ)^4341*50000000000000^3317 ≤ 4949869829303^3317*500000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85411517 500000000 4949869829303 50000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5618073771/10000000000 : ℝ)^4341 ≤ (47019921674183/100000000000000 : ℝ)^3317 := by
    have hnat : (5618073771 : ℕ)^4341*100000000000000^3317 ≤ 47019921674183^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5618073771 10000000000 47019921674183 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050942929/2000000000 : ℝ), (-85411517/500000000 : ℝ), (5618073771/10000000000 : ℝ)] ![(5385042330561/12500000000000 : ℝ), (4949869829303/50000000000000 : ℝ), (47019921674183/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050942929/2000000000 : ℝ)|^4341 ≤ (5385042330561/12500000000000 : ℝ)^3317
        have hw : |(1050942929/2000000000 : ℝ)|=(1050942929/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-85411517/500000000 : ℝ)|^4341 ≤ (4949869829303/50000000000000 : ℝ)^3317
        have hw : |(-85411517/500000000 : ℝ)|=(85411517/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5618073771/10000000000 : ℝ)|^4341 ≤ (47019921674183/100000000000000 : ℝ)^3317
        have hw : |(5618073771/10000000000 : ℝ)|=(5618073771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s1_6 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5254714967/10000000000 : ℝ)*x 0 + (224722963/400000000 : ℝ)*x 1 + (-854114723/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5254714967/10000000000 : ℝ)^4341 ≤ (21540171049673/50000000000000 : ℝ)^3317 := by
    have hnat : (5254714967 : ℕ)^4341*50000000000000^3317 ≤ 21540171049673^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254714967 10000000000 21540171049673 50000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (224722963/400000000 : ℝ)^4341 ≤ (47019925003939/100000000000000 : ℝ)^3317 := by
    have hnat : (224722963 : ℕ)^4341*100000000000000^3317 ≤ 47019925003939^3317*400000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224722963 400000000 47019925003939 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (854114723/5000000000 : ℝ)^4341 ≤ (9899732878147/100000000000000 : ℝ)^3317 := by
    have hnat : (854114723 : ℕ)^4341*100000000000000^3317 ≤ 9899732878147^3317*5000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      854114723 5000000000 9899732878147 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5254714967/10000000000 : ℝ), (224722963/400000000 : ℝ), (-854114723/5000000000 : ℝ)] ![(21540171049673/50000000000000 : ℝ), (47019925003939/100000000000000 : ℝ), (9899732878147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5254714967/10000000000 : ℝ)|^4341 ≤ (21540171049673/50000000000000 : ℝ)^3317
        have hw : |(5254714967/10000000000 : ℝ)|=(5254714967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(224722963/400000000 : ℝ)|^4341 ≤ (47019925003939/100000000000000 : ℝ)^3317
        have hw : |(224722963/400000000 : ℝ)|=(224722963/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-854114723/5000000000 : ℝ)|^4341 ≤ (9899732878147/100000000000000 : ℝ)^3317
        have hw : |(-854114723/5000000000 : ℝ)|=(854114723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s1_7 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071580611/2500000000 : ℝ)*x 0 + (4908942589/10000000000 : ℝ)*x 1 + (3738497621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071580611/2500000000 : ℝ)^4341 ≤ (32999302335667/100000000000000 : ℝ)^3317 := by
    have hnat : (1071580611 : ℕ)^4341*100000000000000^3317 ≤ 32999302335667^3317*2500000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071580611 2500000000 32999302335667 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4908942589/10000000000 : ℝ)^4341 ≤ (307880400173/781250000000 : ℝ)^3317 := by
    have hnat : (4908942589 : ℕ)^4341*781250000000^3317 ≤ 307880400173^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4908942589 10000000000 307880400173 781250000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3738497621/10000000000 : ℝ)^4341 ≤ (27592006434597/100000000000000 : ℝ)^3317 := by
    have hnat : (3738497621 : ℕ)^4341*100000000000000^3317 ≤ 27592006434597^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3738497621 10000000000 27592006434597 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071580611/2500000000 : ℝ), (4908942589/10000000000 : ℝ), (3738497621/10000000000 : ℝ)] ![(32999302335667/100000000000000 : ℝ), (307880400173/781250000000 : ℝ), (27592006434597/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071580611/2500000000 : ℝ)|^4341 ≤ (32999302335667/100000000000000 : ℝ)^3317
        have hw : |(1071580611/2500000000 : ℝ)|=(1071580611/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4908942589/10000000000 : ℝ)|^4341 ≤ (307880400173/781250000000 : ℝ)^3317
        have hw : |(4908942589/10000000000 : ℝ)|=(4908942589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3738497621/10000000000 : ℝ)|^4341 ≤ (27592006434597/100000000000000 : ℝ)^3317
        have hw : |(3738497621/10000000000 : ℝ)|=(3738497621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1381_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1220839/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26593/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1703/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (7243/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2397/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26593/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1703/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26593/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1703/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26593/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1703/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26593/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1703/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26593/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1703/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26593/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1703/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1703/100000 : ℝ) ^ (1085/256 : ℝ) ≤ (1593529880937/50000000000000000000 : ℝ) := by
    have hpowers : (1703/100000 : ℝ)^1085 ≤ (1593529880937/50000000000000000000 : ℝ)^256 := by
      have hnat : (1703 : ℕ)^1085*50000000000000000000^256 ≤ 1593529880937^256*100000^1085 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1703 100000 1593529880937 50000000000000000000 1085 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1703/100000 : ℝ)) (X := (1593529880937/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1085 256 (by norm_num) hpowers
    exact h
  have hpowhi : (26593/100000 : ℝ) ^ (1085/256 : ℝ) ≤ (364755774064030937/100000000000000000000 : ℝ) := by
    have hpowers : (26593/100000 : ℝ)^1085 ≤ (364755774064030937/100000000000000000000 : ℝ)^256 := by
      have hnat : (26593 : ℕ)^1085*100000000000000000000^256 ≤ 364755774064030937^256*100000^1085 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26593 100000 364755774064030937 100000000000000000000 1085 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26593/100000 : ℝ)) (X := (364755774064030937/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1085 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000001593529880937/25000000000000000000 : ℝ) ≤ (10000000150393969/10000000000000000 : ℝ) ^ (1085/256 : ℝ) := by
    have hpowers : (25000001593529880937/25000000000000000000 : ℝ)^256 ≤ (10000000150393969/10000000000000000 : ℝ)^1085 := by
      have hnat : (25000001593529880937 : ℕ)^256*10000000000000000^1085 ≤ 10000000150393969^1085*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000001593529880937 25000000000000000000 10000000150393969 10000000000000000 256 1085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000150393969/10000000000000000 : ℝ)) (X := (25000001593529880937/25000000000000000000 : ℝ)) (by norm_num) 1085 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100364758961123792811/100000000000000000000 : ℝ) ≤ (62553714545877/62500000000000 : ℝ) ^ (1085/256 : ℝ) := by
    have hpowers : (100364758961123792811/100000000000000000000 : ℝ)^256 ≤ (62553714545877/62500000000000 : ℝ)^1085 := by
      have hnat : (100364758961123792811 : ℕ)^256*62500000000000^1085 ≤ 62553714545877^1085*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100364758961123792811 100000000000000000000 62553714545877 62500000000000 256 1085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (62553714545877/62500000000000 : ℝ)) (X := (100364758961123792811/100000000000000000000 : ℝ)) (by norm_num) 1085 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50364755774064030937/50000000000000000000 : ℝ) ≤ (10017188504286671/10000000000000000 : ℝ) ^ (1085/256 : ℝ) := by
    have hpowers : (50364755774064030937/50000000000000000000 : ℝ)^256 ≤ (10017188504286671/10000000000000000 : ℝ)^1085 := by
      have hnat : (50364755774064030937 : ℕ)^256*10000000000000000^1085 ≤ 10017188504286671^1085*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50364755774064030937 50000000000000000000 10017188504286671 10000000000000000 256 1085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10017188504286671/10000000000000000 : ℝ)) (X := (50364755774064030937/50000000000000000000 : ℝ)) (by norm_num) 1085 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1593529880937/50000000000000000000 : ℝ) ≤ ((237472072496781123/237500000000000000 : ℝ)+2*(8594176946351/2489000000000000 : ℝ)*(1703/100000 : ℝ))^(1085/256 : ℝ) := by
    rw [show (237472072496781123/237500000000000000 : ℝ)+2*(8594176946351/2489000000000000 : ℝ)*(1703/100000 : ℝ)=(10000000150393969/10000000000000000 : ℝ) by norm_num, show 1+2*(1593529880937/50000000000000000000 : ℝ)=(25000001593529880937/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(364755774064030937/100000000000000000000 : ℝ)+(1593529880937/50000000000000000000 : ℝ) ≤ ((237472072496781123/237500000000000000 : ℝ)+(8594176946351/2489000000000000 : ℝ)*((26593/100000 : ℝ)+(1703/100000 : ℝ)))^(1085/256 : ℝ) := by
    rw [show (237472072496781123/237500000000000000 : ℝ)+(8594176946351/2489000000000000 : ℝ)*((26593/100000 : ℝ)+(1703/100000 : ℝ))=(62553714545877/62500000000000 : ℝ) by norm_num, show 1+(364755774064030937/100000000000000000000 : ℝ)+(1593529880937/50000000000000000000 : ℝ)=(100364758961123792811/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(364755774064030937/100000000000000000000 : ℝ) ≤ ((237472072496781123/237500000000000000 : ℝ)+2*(8594176946351/2489000000000000 : ℝ)*(26593/100000 : ℝ))^(1085/256 : ℝ) := by
    rw [show (237472072496781123/237500000000000000 : ℝ)+2*(8594176946351/2489000000000000 : ℝ)*(26593/100000 : ℝ)=(10017188504286671/10000000000000000 : ℝ) by norm_num, show 1+2*(364755774064030937/100000000000000000000 : ℝ)=(50364755774064030937/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (237472072496781123/237500000000000000 : ℝ)*(X 1 0+X 2 0)+(8594176946351/2489000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1085/256 : ℝ)) (lo := (1703/100000 : ℝ)) (hi := (26593/100000 : ℝ)) (c := (237472072496781123/237500000000000000 : ℝ)) (alpha := (8594176946351/2489000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (237472072496781123/237500000000000000 : ℝ)*(X 0 1+X 2 1)+(8594176946351/2489000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1085/256 : ℝ)) (lo := (1703/100000 : ℝ)) (hi := (26593/100000 : ℝ)) (c := (237472072496781123/237500000000000000 : ℝ)) (alpha := (8594176946351/2489000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (237472072496781123/237500000000000000 : ℝ)*(X 0 2+X 1 2)+(8594176946351/2489000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1085/256 : ℝ)) (lo := (1703/100000 : ℝ)) (hi := (26593/100000 : ℝ)) (c := (237472072496781123/237500000000000000 : ℝ)) (alpha := (8594176946351/2489000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-393103641/2000000000 : ℝ)*X 0 0+(2812534517/5000000000 : ℝ)*X 0 1+(39535093/78125000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5401680689/10000000000 : ℝ)*X 1 0+(-566452729/2500000000 : ℝ)*X 1 1+(2530246669/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5401681383/10000000000 : ℝ)*X 2 0+(5060492089/10000000000 : ℝ)*X 2 1+(-283226451/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4285323119/10000000000 : ℝ)*X 0 0+(3723633351/10000000000 : ℝ)*X 0 1+(984710261/2000000000 : ℝ)*X 0 2+(4285323119/10000000000 : ℝ)*X 1 0+(3723633351/10000000000 : ℝ)*X 1 1+(984710261/2000000000 : ℝ)*X 1 2+(4285323119/10000000000 : ℝ)*X 2 0+(3723633351/10000000000 : ℝ)*X 2 1+(984710261/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-393197539/2000000000 : ℝ)*X 0 0+(202694639/400000000 : ℝ)*X 0 1+(5618073689/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1050942929/2000000000 : ℝ)*X 1 0+(-85411517/500000000 : ℝ)*X 1 1+(5618073771/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5254714967/10000000000 : ℝ)*X 2 0+(224722963/400000000 : ℝ)*X 2 1+(-854114723/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1071580611/2500000000 : ℝ)*X 0 0+(4908942589/10000000000 : ℝ)*X 0 1+(3738497621/10000000000 : ℝ)*X 0 2+(1071580611/2500000000 : ℝ)*X 1 0+(4908942589/10000000000 : ℝ)*X 1 1+(3738497621/10000000000 : ℝ)*X 1 2+(1071580611/2500000000 : ℝ)*X 2 0+(4908942589/10000000000 : ℝ)*X 2 1+(3738497621/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1838045791440898427998337193/388906250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (332656779/50000000000000 : ℝ)*(base19) + (23240929/2500000000000 : ℝ)*(base23) + (31101391/100000000000000 : ℝ)*(upper2) + (25976663/25000000000000 : ℝ)*(upper3) + (325581345160371/25000000000000 : ℝ)*(major0) + (325581345160371/25000000000000 : ℝ)*(major1) + (325581345160371/25000000000000 : ℝ)*(major2) + (1771246538675959/100000000000000 : ℝ)*(sp0) + (885627229534921/50000000000000 : ℝ)*(sp1) + (442813357362873/25000000000000 : ℝ)*(sp2) + (104174063803447/12500000000000 : ℝ)*(sp3) + (8585707441/100000000000000 : ℝ)*(sp4) + (191323687/25000000000000 : ℝ)*(sp6) + (2968932241/100000000000000 : ℝ)*(sp7) + (833395479359817/100000000000000 : ℝ)*(f.failure) + (8856275621917/500000000000 : ℝ)*(f.sum) + (3073205808231/1944531250000000000000000000 : ℝ)*base65 + (464995663199576423/777812500000000000000000000000000 : ℝ)*base67 + (1576280945268326423/777812500000000000000000000000000 : ℝ)*base69 + (2501032680318326423/777812500000000000000000000000000 : ℝ)*base71 + (45934128240483/62225000000000000000000000000 : ℝ)*base74 + (1587826163212388923/777812500000000000000000000000000 : ℝ)*base75 + (3833903369928951423/777812500000000000000000000000000 : ℝ)*base77 + (318120312223638923/777812500000000000000000000000000 : ℝ)*base79 + (15767388764117/62225000000000000000000000000 : ℝ)*base81 + (251463/78125000000000000000 : ℝ)*base89 + (251463/78125000000000000000 : ℝ)*base91 + (251463/78125000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (361535329110838221224056389/194453125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15280681/12500000000000 : ℝ)*(base1) + (698619111/100000000000000 : ℝ)*(base19) + (27632657/3125000000000 : ℝ)*(base23) + (12515011/20000000000000 : ℝ)*(upper3) + (54529029/50000000000000 : ℝ)*(upper5) + (83444447189019/6250000000000 : ℝ)*(major0) + (83444447189019/6250000000000 : ℝ)*(major1) + (83444447189019/6250000000000 : ℝ)*(major2) + (3403387539/100000000000000 : ℝ)*(sp1) + (6061870703/100000000000000 : ℝ)*(sp2) + (907923165337749/50000000000000 : ℝ)*(sp4) + (1815842106423401/100000000000000 : ℝ)*(sp5) + (453959815578581/25000000000000 : ℝ)*(sp6) + (170875183479677/20000000000000 : ℝ)*(sp7) + (854376039643833/100000000000000 : ℝ)*(f.failure) + (36316924168601/2000000000000 : ℝ)*(f.sum) + (25024950267801/31112500000000000000000000000 : ℝ)*base65 + (113465828263146841/24306640625000000000000000000000 : ℝ)*base68 + (340535312884096943/48613281250000000000000000000000 : ℝ)*base69 + (196727372234002853/194453125000000000000000000000000 : ℝ)*base72 + (4627261162373/62225000000000000000000000000 : ℝ)*base74 + (2256564946663534103/194453125000000000000000000000000 : ℝ)*base76 + (52139022427509239/97226562500000000000000000000000 : ℝ)*base78 + (2445177709778065353/194453125000000000000000000000000 : ℝ)*base80 + (311022712463027/62225000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (64113/78125000000000000000 : ℝ)*base90 + (64113/78125000000000000000 : ℝ)*base92 + (64113/78125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1381_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1220839/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26593/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1703/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7243/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2397/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1381_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1381_s2_0 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-100119501/500000000 : ℝ)*x 0 + (1093906759/2000000000 : ℝ)*x 1 + (5192356627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (100119501/500000000 : ℝ)^4341 ≤ (6093935968319/50000000000000 : ℝ)^3317 := by
    have hnat : (100119501 : ℕ)^4341*50000000000000^3317 ≤ 6093935968319^3317*500000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100119501 500000000 6093935968319 50000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1093906759/2000000000 : ℝ)^4341 ≤ (11349905706753/25000000000000 : ℝ)^3317 := by
    have hnat : (1093906759 : ℕ)^4341*25000000000000^3317 ≤ 11349905706753^3317*2000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093906759 2000000000 11349905706753 25000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5192356627/10000000000 : ℝ)^4341 ≤ (42412505225729/100000000000000 : ℝ)^3317 := by
    have hnat : (5192356627 : ℕ)^4341*100000000000000^3317 ≤ 42412505225729^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5192356627 10000000000 42412505225729 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-100119501/500000000 : ℝ), (1093906759/2000000000 : ℝ), (5192356627/10000000000 : ℝ)] ![(6093935968319/50000000000000 : ℝ), (11349905706753/25000000000000 : ℝ), (42412505225729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-100119501/500000000 : ℝ)|^4341 ≤ (6093935968319/50000000000000 : ℝ)^3317
        have hw : |(-100119501/500000000 : ℝ)|=(100119501/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1093906759/2000000000 : ℝ)|^4341 ≤ (11349905706753/25000000000000 : ℝ)^3317
        have hw : |(1093906759/2000000000 : ℝ)|=(1093906759/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5192356627/10000000000 : ℝ)|^4341 ≤ (42412505225729/100000000000000 : ℝ)^3317
        have hw : |(5192356627/10000000000 : ℝ)|=(5192356627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s2_1 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1072653963/2000000000 : ℝ)*x 0 + (-1072658707/5000000000 : ℝ)*x 1 + (2596178301/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072653963/2000000000 : ℝ)^4341 ≤ (2765547746727/6250000000000 : ℝ)^3317 := by
    have hnat : (1072653963 : ℕ)^4341*6250000000000^3317 ≤ 2765547746727^3317*2000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072653963 2000000000 2765547746727 6250000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1072658707/5000000000 : ℝ)^4341 ≤ (13338731088137/100000000000000 : ℝ)^3317 := by
    have hnat : (1072658707 : ℕ)^4341*100000000000000^3317 ≤ 13338731088137^3317*5000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072658707 5000000000 13338731088137 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2596178301/5000000000 : ℝ)^4341 ≤ (21206252479241/50000000000000 : ℝ)^3317 := by
    have hnat : (2596178301 : ℕ)^4341*50000000000000^3317 ≤ 21206252479241^3317*5000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596178301 5000000000 21206252479241 50000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072653963/2000000000 : ℝ), (-1072658707/5000000000 : ℝ), (2596178301/5000000000 : ℝ)] ![(2765547746727/6250000000000 : ℝ), (13338731088137/100000000000000 : ℝ), (21206252479241/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072653963/2000000000 : ℝ)|^4341 ≤ (2765547746727/6250000000000 : ℝ)^3317
        have hw : |(1072653963/2000000000 : ℝ)|=(1072653963/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1072658707/5000000000 : ℝ)|^4341 ≤ (13338731088137/100000000000000 : ℝ)^3317
        have hw : |(-1072658707/5000000000 : ℝ)|=(1072658707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2596178301/5000000000 : ℝ)|^4341 ≤ (21206252479241/50000000000000 : ℝ)^3317
        have hw : |(2596178301/5000000000 : ℝ)|=(2596178301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s2_2 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2681634851/5000000000 : ℝ)*x 0 + (5192356709/10000000000 : ℝ)*x 1 + (-2145317423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681634851/5000000000 : ℝ)^4341 ≤ (2765547670471/6250000000000 : ℝ)^3317 := by
    have hnat : (2681634851 : ℕ)^4341*6250000000000^3317 ≤ 2765547670471^3317*5000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681634851 5000000000 2765547670471 6250000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5192356709/10000000000 : ℝ)^4341 ≤ (42412506102301/100000000000000 : ℝ)^3317 := by
    have hnat : (5192356709 : ℕ)^4341*100000000000000^3317 ≤ 42412506102301^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5192356709 10000000000 42412506102301 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2145317423/10000000000 : ℝ)^4341 ≤ (1333873116137/10000000000000 : ℝ)^3317 := by
    have hnat : (2145317423 : ℕ)^4341*10000000000000^3317 ≤ 1333873116137^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145317423 10000000000 1333873116137 10000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681634851/5000000000 : ℝ), (5192356709/10000000000 : ℝ), (-2145317423/10000000000 : ℝ)] ![(2765547670471/6250000000000 : ℝ), (42412506102301/100000000000000 : ℝ), (1333873116137/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681634851/5000000000 : ℝ)|^4341 ≤ (2765547670471/6250000000000 : ℝ)^3317
        have hw : |(2681634851/5000000000 : ℝ)|=(2681634851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5192356709/10000000000 : ℝ)|^4341 ≤ (42412506102301/100000000000000 : ℝ)^3317
        have hw : |(5192356709/10000000000 : ℝ)|=(5192356709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2145317423/10000000000 : ℝ)|^4341 ≤ (1333873116137/10000000000000 : ℝ)^3317
        have hw : |(-2145317423/10000000000 : ℝ)|=(2145317423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s2_3 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2155610081/5000000000 : ℝ)*x 0 + (100647311/250000000 : ℝ)*x 1 + (922998077/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2155610081/5000000000 : ℝ)^4341 ≤ (16625191269837/50000000000000 : ℝ)^3317 := by
    have hnat : (2155610081 : ℕ)^4341*50000000000000^3317 ≤ 16625191269837^3317*5000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155610081 5000000000 16625191269837 50000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (100647311/250000000 : ℝ)^4341 ≤ (15200158198071/50000000000000 : ℝ)^3317 := by
    have hnat : (100647311 : ℕ)^4341*50000000000000^3317 ≤ 15200158198071^3317*250000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100647311 250000000 15200158198071 50000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (922998077/2000000000 : ℝ)^4341 ≤ (36349301042091/100000000000000 : ℝ)^3317 := by
    have hnat : (922998077 : ℕ)^4341*100000000000000^3317 ≤ 36349301042091^3317*2000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      922998077 2000000000 36349301042091 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2155610081/5000000000 : ℝ), (100647311/250000000 : ℝ), (922998077/2000000000 : ℝ)] ![(16625191269837/50000000000000 : ℝ), (15200158198071/50000000000000 : ℝ), (36349301042091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2155610081/5000000000 : ℝ)|^4341 ≤ (16625191269837/50000000000000 : ℝ)^3317
        have hw : |(2155610081/5000000000 : ℝ)|=(2155610081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(100647311/250000000 : ℝ)|^4341 ≤ (15200158198071/50000000000000 : ℝ)^3317
        have hw : |(100647311/250000000 : ℝ)|=(100647311/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(922998077/2000000000 : ℝ)|^4341 ≤ (36349301042091/100000000000000 : ℝ)^3317
        have hw : |(922998077/2000000000 : ℝ)|=(922998077/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s2_4 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2002445379/10000000000 : ℝ)*x 0 + (1038804639/2000000000 : ℝ)*x 1 + (2733926507/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2002445379/10000000000 : ℝ)^4341 ≤ (6094156455639/50000000000000 : ℝ)^3317 := by
    have hnat : (2002445379 : ℕ)^4341*50000000000000^3317 ≤ 6094156455639^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2002445379 10000000000 6094156455639 50000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1038804639/2000000000 : ℝ)^4341 ≤ (21215160778511/50000000000000 : ℝ)^3317 := by
    have hnat : (1038804639 : ℕ)^4341*50000000000000^3317 ≤ 21215160778511^3317*2000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038804639 2000000000 21215160778511 50000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2733926507/5000000000 : ℝ)^4341 ≤ (9076273103509/20000000000000 : ℝ)^3317 := by
    have hnat : (2733926507 : ℕ)^4341*20000000000000^3317 ≤ 9076273103509^3317*5000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2733926507 5000000000 9076273103509 20000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2002445379/10000000000 : ℝ), (1038804639/2000000000 : ℝ), (2733926507/5000000000 : ℝ)] ![(6094156455639/50000000000000 : ℝ), (21215160778511/50000000000000 : ℝ), (9076273103509/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2002445379/10000000000 : ℝ)|^4341 ≤ (6094156455639/50000000000000 : ℝ)^3317
        have hw : |(-2002445379/10000000000 : ℝ)|=(2002445379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1038804639/2000000000 : ℝ)|^4341 ≤ (21215160778511/50000000000000 : ℝ)^3317
        have hw : |(1038804639/2000000000 : ℝ)|=(1038804639/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2733926507/5000000000 : ℝ)|^4341 ≤ (9076273103509/20000000000000 : ℝ)^3317
        have hw : |(2733926507/5000000000 : ℝ)|=(2733926507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s2_5 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5291533099/10000000000 : ℝ)*x 0 + (-14958573/80000000 : ℝ)*x 1 + (1093570541/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5291533099/10000000000 : ℝ)^4341 ≤ (10868951019831/25000000000000 : ℝ)^3317 := by
    have hnat : (5291533099 : ℕ)^4341*25000000000000^3317 ≤ 10868951019831^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5291533099 10000000000 10868951019831 25000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (14958573/80000000 : ℝ)^4341 ≤ (11142833745757/100000000000000 : ℝ)^3317 := by
    have hnat : (14958573 : ℕ)^4341*100000000000000^3317 ≤ 11142833745757^3317*80000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14958573 80000000 11142833745757 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1093570541/2000000000 : ℝ)^4341 ≤ (5672670270153/12500000000000 : ℝ)^3317 := by
    have hnat : (1093570541 : ℕ)^4341*12500000000000^3317 ≤ 5672670270153^3317*2000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093570541 2000000000 5672670270153 12500000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5291533099/10000000000 : ℝ), (-14958573/80000000 : ℝ), (1093570541/2000000000 : ℝ)] ![(10868951019831/25000000000000 : ℝ), (11142833745757/100000000000000 : ℝ), (5672670270153/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5291533099/10000000000 : ℝ)|^4341 ≤ (10868951019831/25000000000000 : ℝ)^3317
        have hw : |(5291533099/10000000000 : ℝ)|=(5291533099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-14958573/80000000 : ℝ)|^4341 ≤ (11142833745757/100000000000000 : ℝ)^3317
        have hw : |(-14958573/80000000 : ℝ)|=(14958573/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1093570541/2000000000 : ℝ)|^4341 ≤ (5672670270153/12500000000000 : ℝ)^3317
        have hw : |(1093570541/2000000000 : ℝ)|=(1093570541/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s2_6 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2645767289/5000000000 : ℝ)*x 0 + (5467852779/10000000000 : ℝ)*x 1 + (-934909741/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2645767289/5000000000 : ℝ)^4341 ≤ (43475819982307/100000000000000 : ℝ)^3317 := by
    have hnat : (2645767289 : ℕ)^4341*100000000000000^3317 ≤ 43475819982307^3317*5000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2645767289 5000000000 43475819982307 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5467852779/10000000000 : ℝ)^4341 ≤ (45381362965003/100000000000000 : ℝ)^3317 := by
    have hnat : (5467852779 : ℕ)^4341*100000000000000^3317 ≤ 45381362965003^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5467852779 10000000000 45381362965003 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (934909741/5000000000 : ℝ)^4341 ≤ (11142817032469/100000000000000 : ℝ)^3317 := by
    have hnat : (934909741 : ℕ)^4341*100000000000000^3317 ≤ 11142817032469^3317*5000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      934909741 5000000000 11142817032469 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2645767289/5000000000 : ℝ), (5467852779/10000000000 : ℝ), (-934909741/5000000000 : ℝ)] ![(43475819982307/100000000000000 : ℝ), (45381362965003/100000000000000 : ℝ), (11142817032469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2645767289/5000000000 : ℝ)|^4341 ≤ (43475819982307/100000000000000 : ℝ)^3317
        have hw : |(2645767289/5000000000 : ℝ)|=(2645767289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5467852779/10000000000 : ℝ)|^4341 ≤ (45381362965003/100000000000000 : ℝ)^3317
        have hw : |(5467852779/10000000000 : ℝ)|=(5467852779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-934909741/5000000000 : ℝ)|^4341 ≤ (11142817032469/100000000000000 : ℝ)^3317
        have hw : |(-934909741/5000000000 : ℝ)|=(934909741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s2_7 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (215566971/500000000 : ℝ)*x 0 + (4611448971/10000000000 : ℝ)*x 1 + (62960369/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215566971/500000000 : ℝ)^4341 ≤ (16625793136293/50000000000000 : ℝ)^3317 := by
    have hnat : (215566971 : ℕ)^4341*50000000000000^3317 ≤ 16625793136293^3317*500000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215566971 500000000 16625793136293 50000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4611448971/10000000000 : ℝ)^4341 ≤ (7262560175479/20000000000000 : ℝ)^3317 := by
    have hnat : (4611448971 : ℕ)^4341*20000000000000^3317 ≤ 7262560175479^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4611448971 10000000000 7262560175479 20000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (62960369/156250000 : ℝ)^4341 ≤ (15217806420031/50000000000000 : ℝ)^3317 := by
    have hnat : (62960369 : ℕ)^4341*50000000000000^3317 ≤ 15217806420031^3317*156250000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62960369 156250000 15217806420031 50000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215566971/500000000 : ℝ), (4611448971/10000000000 : ℝ), (62960369/156250000 : ℝ)] ![(16625793136293/50000000000000 : ℝ), (7262560175479/20000000000000 : ℝ), (15217806420031/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215566971/500000000 : ℝ)|^4341 ≤ (16625793136293/50000000000000 : ℝ)^3317
        have hw : |(215566971/500000000 : ℝ)|=(215566971/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4611448971/10000000000 : ℝ)|^4341 ≤ (7262560175479/20000000000000 : ℝ)^3317
        have hw : |(4611448971/10000000000 : ℝ)|=(4611448971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(62960369/156250000 : ℝ)|^4341 ≤ (15217806420031/50000000000000 : ℝ)^3317
        have hw : |(62960369/156250000 : ℝ)|=(62960369/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1381_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1220839/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2397/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7243/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (631/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7979/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2397/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7243/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2397/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7243/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2397/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7243/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2397/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7243/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2397/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7243/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2397/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7243/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (7243/100000 : ℝ) ^ (1085/256 : ℝ) ≤ (1472359600002131/100000000000000000000 : ℝ) := by
    have hpowers : (7243/100000 : ℝ)^1085 ≤ (1472359600002131/100000000000000000000 : ℝ)^256 := by
      have hnat : (7243 : ℕ)^1085*100000000000000000000^256 ≤ 1472359600002131^256*100000^1085 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7243 100000 1472359600002131 100000000000000000000 1085 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7243/100000 : ℝ)) (X := (1472359600002131/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1085 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2397/12500 : ℝ) ^ (1085/256 : ℝ) ≤ (91227709048218879/100000000000000000000 : ℝ) := by
    have hpowers : (2397/12500 : ℝ)^1085 ≤ (91227709048218879/100000000000000000000 : ℝ)^256 := by
      have hnat : (2397 : ℕ)^1085*100000000000000000000^256 ≤ 91227709048218879^256*12500^1085 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2397 12500 91227709048218879 100000000000000000000 1085 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2397/12500 : ℝ)) (X := (91227709048218879/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1085 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001472359600002131/50000000000000000000 : ℝ) ≤ (5000034739153679/5000000000000000 : ℝ) ^ (1085/256 : ℝ) := by
    have hpowers : (50001472359600002131/50000000000000000000 : ℝ)^256 ≤ (5000034739153679/5000000000000000 : ℝ)^1085 := by
      have hnat : (50001472359600002131 : ℕ)^256*5000000000000000^1085 ≤ 5000034739153679^1085*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001472359600002131 50000000000000000000 5000034739153679 5000000000000000 256 1085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000034739153679/5000000000000000 : ℝ)) (X := (50001472359600002131/50000000000000000000 : ℝ)) (by norm_num) 1085 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (10009270006864822101/10000000000000000000 : ℝ) ≤ (5001093217418489/5000000000000000 : ℝ) ^ (1085/256 : ℝ) := by
    have hpowers : (10009270006864822101/10000000000000000000 : ℝ)^256 ≤ (5001093217418489/5000000000000000 : ℝ)^1085 := by
      have hnat : (10009270006864822101 : ℕ)^256*5000000000000000^1085 ≤ 5001093217418489^1085*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10009270006864822101 10000000000000000000 5001093217418489 5000000000000000 256 1085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001093217418489/5000000000000000 : ℝ)) (X := (10009270006864822101/10000000000000000000 : ℝ)) (by norm_num) 1085 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50091227709048218879/50000000000000000000 : ℝ) ≤ (5002151695683299/5000000000000000 : ℝ) ^ (1085/256 : ℝ) := by
    have hpowers : (50091227709048218879/50000000000000000000 : ℝ)^256 ≤ (5002151695683299/5000000000000000 : ℝ)^1085 := by
      have hnat : (50091227709048218879 : ℕ)^256*5000000000000000^1085 ≤ 5002151695683299^1085*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50091227709048218879 50000000000000000000 5002151695683299 5000000000000000 256 1085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002151695683299/5000000000000000 : ℝ)) (X := (50091227709048218879/50000000000000000000 : ℝ)) (by norm_num) 1085 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1472359600002131/100000000000000000000 : ℝ) ≤ ((59650081426176813847/59665000000000000000 : ℝ)+2*(105847826481/59665000000000 : ℝ)*(7243/100000 : ℝ))^(1085/256 : ℝ) := by
    rw [show (59650081426176813847/59665000000000000000 : ℝ)+2*(105847826481/59665000000000 : ℝ)*(7243/100000 : ℝ)=(5000034739153679/5000000000000000 : ℝ) by norm_num, show 1+2*(1472359600002131/100000000000000000000 : ℝ)=(50001472359600002131/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(91227709048218879/100000000000000000000 : ℝ)+(1472359600002131/100000000000000000000 : ℝ) ≤ ((59650081426176813847/59665000000000000000 : ℝ)+(105847826481/59665000000000 : ℝ)*((2397/12500 : ℝ)+(7243/100000 : ℝ)))^(1085/256 : ℝ) := by
    rw [show (59650081426176813847/59665000000000000000 : ℝ)+(105847826481/59665000000000 : ℝ)*((2397/12500 : ℝ)+(7243/100000 : ℝ))=(5001093217418489/5000000000000000 : ℝ) by norm_num, show 1+(91227709048218879/100000000000000000000 : ℝ)+(1472359600002131/100000000000000000000 : ℝ)=(10009270006864822101/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(91227709048218879/100000000000000000000 : ℝ) ≤ ((59650081426176813847/59665000000000000000 : ℝ)+2*(105847826481/59665000000000 : ℝ)*(2397/12500 : ℝ))^(1085/256 : ℝ) := by
    rw [show (59650081426176813847/59665000000000000000 : ℝ)+2*(105847826481/59665000000000 : ℝ)*(2397/12500 : ℝ)=(5002151695683299/5000000000000000 : ℝ) by norm_num, show 1+2*(91227709048218879/100000000000000000000 : ℝ)=(50091227709048218879/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (59650081426176813847/59665000000000000000 : ℝ)*(X 1 0+X 2 0)+(105847826481/59665000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1085/256 : ℝ)) (lo := (7243/100000 : ℝ)) (hi := (2397/12500 : ℝ)) (c := (59650081426176813847/59665000000000000000 : ℝ)) (alpha := (105847826481/59665000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (59650081426176813847/59665000000000000000 : ℝ)*(X 0 1+X 2 1)+(105847826481/59665000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1085/256 : ℝ)) (lo := (7243/100000 : ℝ)) (hi := (2397/12500 : ℝ)) (c := (59650081426176813847/59665000000000000000 : ℝ)) (alpha := (105847826481/59665000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (59650081426176813847/59665000000000000000 : ℝ)*(X 0 2+X 1 2)+(105847826481/59665000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1085/256 : ℝ)) (lo := (7243/100000 : ℝ)) (hi := (2397/12500 : ℝ)) (c := (59650081426176813847/59665000000000000000 : ℝ)) (alpha := (105847826481/59665000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-100119501/500000000 : ℝ)*X 0 0+(1093906759/2000000000 : ℝ)*X 0 1+(5192356627/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1072653963/2000000000 : ℝ)*X 1 0+(-1072658707/5000000000 : ℝ)*X 1 1+(2596178301/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2681634851/5000000000 : ℝ)*X 2 0+(5192356709/10000000000 : ℝ)*X 2 1+(-2145317423/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2155610081/5000000000 : ℝ)*X 0 0+(100647311/250000000 : ℝ)*X 0 1+(922998077/2000000000 : ℝ)*X 0 2+(2155610081/5000000000 : ℝ)*X 1 0+(100647311/250000000 : ℝ)*X 1 1+(922998077/2000000000 : ℝ)*X 1 2+(2155610081/5000000000 : ℝ)*X 2 0+(100647311/250000000 : ℝ)*X 2 1+(922998077/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2002445379/10000000000 : ℝ)*X 0 0+(1038804639/2000000000 : ℝ)*X 0 1+(2733926507/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5291533099/10000000000 : ℝ)*X 1 0+(-14958573/80000000 : ℝ)*X 1 1+(1093570541/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2645767289/5000000000 : ℝ)*X 2 0+(5467852779/10000000000 : ℝ)*X 2 1+(-934909741/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((215566971/500000000 : ℝ)*X 0 0+(4611448971/10000000000 : ℝ)*X 0 1+(62960369/156250000 : ℝ)*X 0 2+(215566971/500000000 : ℝ)*X 1 0+(4611448971/10000000000 : ℝ)*X 1 1+(62960369/156250000 : ℝ)*X 1 2+(215566971/500000000 : ℝ)*X 2 0+(4611448971/10000000000 : ℝ)*X 2 1+(62960369/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1380260923624781524010246859/186453125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1334102571/100000000000000 : ℝ)*(base19) + (1140980623/100000000000000 : ℝ)*(base23) + (15702003/25000000000000 : ℝ)*(lower2) + (54284629/25000000000000 : ℝ)*(upper3) + (100377409/100000000000000 : ℝ)*(upper5) + (331584952611149/12500000000000 : ℝ)*(major0) + (331584952611149/12500000000000 : ℝ)*(major1) + (331584952611149/12500000000000 : ℝ)*(major2) + (1803908957568579/50000000000000 : ℝ)*(sp0) + (360783165313217/10000000000000 : ℝ)*(sp1) + (1803915923127059/50000000000000 : ℝ)*(sp2) + (84875881819443/5000000000000 : ℝ)*(sp3) + (7536048791/50000000000000 : ℝ)*(sp4) + (523212333/6250000000000 : ℝ)*(sp7) + (424381501946547/25000000000000 : ℝ)*(f.failure) + (3607832987234741/100000000000000 : ℝ)*(f.sum) + (11209788865839/5966500000000000000000000000 : ℝ)*base66 + (4941218947993969797/745812500000000000000000000000000 : ℝ)*base68 + (5798667226197155203/745812500000000000000000000000000 : ℝ)*base69 + (5825063921055594797/745812500000000000000000000000000 : ℝ)*base72 + (7685505958889/2983250000000000000000000000 : ℝ)*base74 + (1571472875525219797/745812500000000000000000000000000 : ℝ)*base76 + (2614851457607969797/745812500000000000000000000000000 : ℝ)*base78 + (5063165677390594797/745812500000000000000000000000000 : ℝ)*base80 + (19363136529043/5966500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (180433/19531250000000000000 : ℝ)*base89 + (180433/19531250000000000000 : ℝ)*base91 + (180433/19531250000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5649423577969558622318036517/745812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1326618123/100000000000000 : ℝ)*(base19) + (3583994427/100000000000000 : ℝ)*(base23) + (63117167/20000000000000 : ℝ)*(upper3) + (339176331/100000000000000 : ℝ)*(lower4) + (2482259/3125000000000 : ℝ)*(upper5) + (671270121017963/25000000000000 : ℝ)*(major0) + (671270121017963/25000000000000 : ℝ)*(major1) + (671270121017963/25000000000000 : ℝ)*(major2) + (6272804303/100000000000000 : ℝ)*(sp1) + (784581879/1562500000000 : ℝ)*(sp2) + (365190046332923/10000000000000 : ℝ)*(sp4) + (730378572781361/20000000000000 : ℝ)*(sp5) + (3651846666094547/100000000000000 : ℝ)*(sp6) + (429565063079803/25000000000000 : ℝ)*(sp7) + (429565063079803/25000000000000 : ℝ)*(f.failure) + (365190046332923/10000000000000 : ℝ)*(f.sum) + (7884269997231/5966500000000000000000000000 : ℝ)*base66 + (10640129378176383661/1491625000000000000000000000000000 : ℝ)*base67 + (8716426691972633661/1491625000000000000000000000000000 : ℝ)*base69 + (2819353373632866339/1491625000000000000000000000000000 : ℝ)*base72 + (5952829069657/11933000000000000000000000000 : ℝ)*base74 + (5593353509572741339/1491625000000000000000000000000000 : ℝ)*base76 + (4447221263735383661/1491625000000000000000000000000000 : ℝ)*base77 + (10312443579225008661/1491625000000000000000000000000000 : ℝ)*base79 + (18931348154899/5966500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (20967/19531250000000000000 : ℝ)*base89 + (20967/19531250000000000000 : ℝ)*base91 + (20967/19531250000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1381_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1220839/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2397/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7243/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (631/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7979/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1381_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1381_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1220839/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (631/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7979/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1381_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1381_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1381_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1220839/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (631/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7979/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1381_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
