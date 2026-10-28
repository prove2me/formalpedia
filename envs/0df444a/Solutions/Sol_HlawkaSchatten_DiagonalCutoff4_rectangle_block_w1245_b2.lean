-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1245_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:20:55.06623+00:00
-- url     : https://prove2.me/submissions/b1f66184-73df-40a4-8712-ee67a78f1ea5

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
theorem support_rectangle_w1245_s6_0 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2118566039/10000000000 : ℝ)*x 0 + (2695664063/5000000000 : ℝ)*x 1 + (2633539173/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2118566039/10000000000 : ℝ)^4219 ≤ (6441810517813/50000000000000 : ℝ)^3195 := by
    have hnat : (2118566039 : ℕ)^4219*50000000000000^3195 ≤ 6441810517813^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118566039 10000000000 6441810517813 50000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695664063/5000000000 : ℝ)^4219 ≤ (22114343518443/50000000000000 : ℝ)^3195 := by
    have hnat : (2695664063 : ℕ)^4219*50000000000000^3195 ≤ 22114343518443^3195*5000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695664063 5000000000 22114343518443 50000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633539173/5000000000 : ℝ)^4219 ≤ (42887691918607/100000000000000 : ℝ)^3195 := by
    have hnat : (2633539173 : ℕ)^4219*100000000000000^3195 ≤ 42887691918607^3195*5000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633539173 5000000000 42887691918607 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2118566039/10000000000 : ℝ), (2695664063/5000000000 : ℝ), (2633539173/5000000000 : ℝ)] ![(6441810517813/50000000000000 : ℝ), (22114343518443/50000000000000 : ℝ), (42887691918607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2118566039/10000000000 : ℝ)|^4219 ≤ (6441810517813/50000000000000 : ℝ)^3195
        have hw : |(-2118566039/10000000000 : ℝ)|=(2118566039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695664063/5000000000 : ℝ)|^4219 ≤ (22114343518443/50000000000000 : ℝ)^3195
        have hw : |(2695664063/5000000000 : ℝ)|=(2695664063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633539173/5000000000 : ℝ)|^4219 ≤ (42887691918607/100000000000000 : ℝ)^3195
        have hw : |(2633539173/5000000000 : ℝ)|=(2633539173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1245_s6_1 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344340329/10000000000 : ℝ)*x 0 + (-2181565717/10000000000 : ℝ)*x 1 + (2633539171/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344340329/10000000000 : ℝ)^4219 ≤ (21860191333507/50000000000000 : ℝ)^3195 := by
    have hnat : (5344340329 : ℕ)^4219*50000000000000^3195 ≤ 21860191333507^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344340329 10000000000 21860191333507 50000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2181565717/10000000000 : ℝ)^4219 ≤ (13391925445957/100000000000000 : ℝ)^3195 := by
    have hnat : (2181565717 : ℕ)^4219*100000000000000^3195 ≤ 13391925445957^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181565717 10000000000 13391925445957 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633539171/5000000000 : ℝ)^4219 ≤ (42887691875597/100000000000000 : ℝ)^3195 := by
    have hnat : (2633539171 : ℕ)^4219*100000000000000^3195 ≤ 42887691875597^3195*5000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633539171 5000000000 42887691875597 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344340329/10000000000 : ℝ), (-2181565717/10000000000 : ℝ), (2633539171/5000000000 : ℝ)] ![(21860191333507/50000000000000 : ℝ), (13391925445957/100000000000000 : ℝ), (42887691875597/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344340329/10000000000 : ℝ)|^4219 ≤ (21860191333507/50000000000000 : ℝ)^3195
        have hw : |(5344340329/10000000000 : ℝ)|=(5344340329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2181565717/10000000000 : ℝ)|^4219 ≤ (13391925445957/100000000000000 : ℝ)^3195
        have hw : |(-2181565717/10000000000 : ℝ)|=(2181565717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633539171/5000000000 : ℝ)|^4219 ≤ (42887691875597/100000000000000 : ℝ)^3195
        have hw : |(2633539171/5000000000 : ℝ)|=(2633539171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1245_s6_2 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334021271/625000000 : ℝ)*x 0 + (5267078341/10000000000 : ℝ)*x 1 + (-2181565709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334021271/625000000 : ℝ)^4219 ≤ (5465047842829/12500000000000 : ℝ)^3195 := by
    have hnat : (334021271 : ℕ)^4219*12500000000000^3195 ≤ 5465047842829^3195*625000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334021271 625000000 5465047842829 12500000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267078341/10000000000 : ℝ)^4219 ≤ (8577538372969/20000000000000 : ℝ)^3195 := by
    have hnat : (5267078341 : ℕ)^4219*20000000000000^3195 ≤ 8577538372969^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267078341 10000000000 8577538372969 20000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2181565709/10000000000 : ℝ)^4219 ≤ (3347981345277/25000000000000 : ℝ)^3195 := by
    have hnat : (2181565709 : ℕ)^4219*25000000000000^3195 ≤ 3347981345277^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181565709 10000000000 3347981345277 25000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334021271/625000000 : ℝ), (5267078341/10000000000 : ℝ), (-2181565709/10000000000 : ℝ)] ![(5465047842829/12500000000000 : ℝ), (8577538372969/20000000000000 : ℝ), (3347981345277/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334021271/625000000 : ℝ)|^4219 ≤ (5465047842829/12500000000000 : ℝ)^3195
        have hw : |(334021271/625000000 : ℝ)|=(334021271/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267078341/10000000000 : ℝ)|^4219 ≤ (8577538372969/20000000000000 : ℝ)^3195
        have hw : |(5267078341/10000000000 : ℝ)|=(5267078341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2181565709/10000000000 : ℝ)|^4219 ≤ (3347981345277/25000000000000 : ℝ)^3195
        have hw : |(-2181565709/10000000000 : ℝ)|=(2181565709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1245_s6_3 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2175176347/5000000000 : ℝ)*x 0 + (66031727/156250000 : ℝ)*x 1 + (559778249/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175176347/5000000000 : ℝ)^4219 ≤ (6663482668157/20000000000000 : ℝ)^3195 := by
    have hnat : (2175176347 : ℕ)^4219*20000000000000^3195 ≤ 6663482668157^3195*5000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175176347 5000000000 6663482668157 20000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (66031727/156250000 : ℝ)^4219 ≤ (32065922987823/100000000000000 : ℝ)^3195 := by
    have hnat : (66031727 : ℕ)^4219*100000000000000^3195 ≤ 32065922987823^3195*156250000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66031727 156250000 32065922987823 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (559778249/1250000000 : ℝ)^4219 ≤ (34616663651627/100000000000000 : ℝ)^3195 := by
    have hnat : (559778249 : ℕ)^4219*100000000000000^3195 ≤ 34616663651627^3195*1250000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559778249 1250000000 34616663651627 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2175176347/5000000000 : ℝ), (66031727/156250000 : ℝ), (559778249/1250000000 : ℝ)] ![(6663482668157/20000000000000 : ℝ), (32065922987823/100000000000000 : ℝ), (34616663651627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2175176347/5000000000 : ℝ)|^4219 ≤ (6663482668157/20000000000000 : ℝ)^3195
        have hw : |(2175176347/5000000000 : ℝ)|=(2175176347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(66031727/156250000 : ℝ)|^4219 ≤ (32065922987823/100000000000000 : ℝ)^3195
        have hw : |(66031727/156250000 : ℝ)|=(66031727/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(559778249/1250000000 : ℝ)|^4219 ≤ (34616663651627/100000000000000 : ℝ)^3195
        have hw : |(559778249/1250000000 : ℝ)|=(559778249/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1245_s6_4 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-132410687/625000000 : ℝ)*x 0 + (5267392263/10000000000 : ℝ)*x 1 + (5391012869/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132410687/625000000 : ℝ)^4219 ≤ (515346432399/4000000000000 : ℝ)^3195 := by
    have hnat : (132410687 : ℕ)^4219*4000000000000^3195 ≤ 515346432399^3195*625000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132410687 625000000 515346432399 4000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267392263/10000000000 : ℝ)^4219 ≤ (42891067282047/100000000000000 : ℝ)^3195 := by
    have hnat : (5267392263 : ℕ)^4219*100000000000000^3195 ≤ 42891067282047^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267392263 10000000000 42891067282047 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391012869/10000000000 : ℝ)^4219 ≤ (5528158987993/12500000000000 : ℝ)^3195 := by
    have hnat : (5391012869 : ℕ)^4219*12500000000000^3195 ≤ 5528158987993^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391012869 10000000000 5528158987993 12500000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-132410687/625000000 : ℝ), (5267392263/10000000000 : ℝ), (5391012869/10000000000 : ℝ)] ![(515346432399/4000000000000 : ℝ), (42891067282047/100000000000000 : ℝ), (5528158987993/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-132410687/625000000 : ℝ)|^4219 ≤ (515346432399/4000000000000 : ℝ)^3195
        have hw : |(-132410687/625000000 : ℝ)|=(132410687/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267392263/10000000000 : ℝ)|^4219 ≤ (42891067282047/100000000000000 : ℝ)^3195
        have hw : |(5267392263/10000000000 : ℝ)|=(5267392263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391012869/10000000000 : ℝ)|^4219 ≤ (5528158987993/12500000000000 : ℝ)^3195
        have hw : |(5391012869/10000000000 : ℝ)|=(5391012869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1245_s6_5 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312631413/10000000000 : ℝ)*x 0 + (-2057631183/10000000000 : ℝ)*x 1 + (539101243/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312631413/10000000000 : ℝ)^4219 ≤ (21689084941759/50000000000000 : ℝ)^3195 := by
    have hnat : (5312631413 : ℕ)^4219*50000000000000^3195 ≤ 21689084941759^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312631413 10000000000 21689084941759 50000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2057631183/10000000000 : ℝ)^4219 ≤ (387392592079/3125000000000 : ℝ)^3195 := by
    have hnat : (2057631183 : ℕ)^4219*3125000000000^3195 ≤ 387392592079^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2057631183 10000000000 387392592079 3125000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539101243/1000000000 : ℝ)^4219 ≤ (22112633574183/50000000000000 : ℝ)^3195 := by
    have hnat : (539101243 : ℕ)^4219*50000000000000^3195 ≤ 22112633574183^3195*1000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539101243 1000000000 22112633574183 50000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312631413/10000000000 : ℝ), (-2057631183/10000000000 : ℝ), (539101243/1000000000 : ℝ)] ![(21689084941759/50000000000000 : ℝ), (387392592079/3125000000000 : ℝ), (22112633574183/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312631413/10000000000 : ℝ)|^4219 ≤ (21689084941759/50000000000000 : ℝ)^3195
        have hw : |(5312631413/10000000000 : ℝ)|=(5312631413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2057631183/10000000000 : ℝ)|^4219 ≤ (387392592079/3125000000000 : ℝ)^3195
        have hw : |(-2057631183/10000000000 : ℝ)|=(2057631183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539101243/1000000000 : ℝ)|^4219 ≤ (22112633574183/50000000000000 : ℝ)^3195
        have hw : |(539101243/1000000000 : ℝ)|=(539101243/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1245_s6_6 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312631579/10000000000 : ℝ)*x 0 + (5391012159/10000000000 : ℝ)*x 1 + (-2057631329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312631579/10000000000 : ℝ)^4219 ≤ (21689085836667/50000000000000 : ℝ)^3195 := by
    have hnat : (5312631579 : ℕ)^4219*50000000000000^3195 ≤ 21689085836667^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312631579 10000000000 21689085836667 50000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391012159/10000000000 : ℝ)^4219 ≤ (4422526421269/10000000000000 : ℝ)^3195 := by
    have hnat : (5391012159 : ℕ)^4219*10000000000000^3195 ≤ 4422526421269^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391012159 10000000000 4422526421269 10000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2057631329/10000000000 : ℝ)^4219 ≤ (3099141027011/25000000000000 : ℝ)^3195 := by
    have hnat : (2057631329 : ℕ)^4219*25000000000000^3195 ≤ 3099141027011^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2057631329 10000000000 3099141027011 25000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312631579/10000000000 : ℝ), (5391012159/10000000000 : ℝ), (-2057631329/10000000000 : ℝ)] ![(21689085836667/50000000000000 : ℝ), (4422526421269/10000000000000 : ℝ), (3099141027011/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312631579/10000000000 : ℝ)|^4219 ≤ (21689085836667/50000000000000 : ℝ)^3195
        have hw : |(5312631579/10000000000 : ℝ)|=(5312631579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391012159/10000000000 : ℝ)|^4219 ≤ (4422526421269/10000000000000 : ℝ)^3195
        have hw : |(5391012159/10000000000 : ℝ)|=(5391012159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2057631329/10000000000 : ℝ)|^4219 ≤ (3099141027011/25000000000000 : ℝ)^3195
        have hw : |(-2057631329/10000000000 : ℝ)|=(2057631329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1245_s6_7 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (135948819/312500000 : ℝ)*x 0 + (4477588169/10000000000 : ℝ)*x 1 + (2113335339/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135948819/312500000 : ℝ)^4219 ≤ (33317509557111/100000000000000 : ℝ)^3195 := by
    have hnat : (135948819 : ℕ)^4219*100000000000000^3195 ≤ 33317509557111^3195*312500000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135948819 312500000 33317509557111 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4477588169/10000000000 : ℝ)^4219 ≤ (17305076622399/50000000000000 : ℝ)^3195 := by
    have hnat : (4477588169 : ℕ)^4219*50000000000000^3195 ≤ 17305076622399^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4477588169 10000000000 17305076622399 50000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2113335339/5000000000 : ℝ)^4219 ≤ (6414467436301/20000000000000 : ℝ)^3195 := by
    have hnat : (2113335339 : ℕ)^4219*20000000000000^3195 ≤ 6414467436301^3195*5000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113335339 5000000000 6414467436301 20000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(135948819/312500000 : ℝ), (4477588169/10000000000 : ℝ), (2113335339/5000000000 : ℝ)] ![(33317509557111/100000000000000 : ℝ), (17305076622399/50000000000000 : ℝ), (6414467436301/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(135948819/312500000 : ℝ)|^4219 ≤ (33317509557111/100000000000000 : ℝ)^3195
        have hw : |(135948819/312500000 : ℝ)|=(135948819/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4477588169/10000000000 : ℝ)|^4219 ≤ (17305076622399/50000000000000 : ℝ)^3195
        have hw : |(4477588169/10000000000 : ℝ)|=(4477588169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2113335339/5000000000 : ℝ)|^4219 ≤ (6414467436301/20000000000000 : ℝ)^3195
        have hw : |(2113335339/5000000000 : ℝ)|=(2113335339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1245_s6_8 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-9525029/2500000000 : ℝ)*x 0 + (295659089/500000000 : ℝ)*x 1 + (2956617441/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9525029/2500000000 : ℝ)^4219 ≤ (63916249529/100000000000000 : ℝ)^3195 := by
    have hnat : (9525029 : ℕ)^4219*100000000000000^3195 ≤ 63916249529^3195*2500000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9525029 2500000000 63916249529 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (295659089/500000000 : ℝ)^4219 ≤ (24983872798777/50000000000000 : ℝ)^3195 := by
    have hnat : (295659089 : ℕ)^4219*50000000000000^3195 ≤ 24983872798777^3195*500000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      295659089 500000000 24983872798777 50000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2956617441/5000000000 : ℝ)^4219 ≤ (780755283421/1562500000000 : ℝ)^3195 := by
    have hnat : (2956617441 : ℕ)^4219*1562500000000^3195 ≤ 780755283421^3195*5000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2956617441 5000000000 780755283421 1562500000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-9525029/2500000000 : ℝ), (295659089/500000000 : ℝ), (2956617441/5000000000 : ℝ)] ![(63916249529/100000000000000 : ℝ), (24983872798777/50000000000000 : ℝ), (780755283421/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-9525029/2500000000 : ℝ)|^4219 ≤ (63916249529/100000000000000 : ℝ)^3195
        have hw : |(-9525029/2500000000 : ℝ)|=(9525029/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(295659089/500000000 : ℝ)|^4219 ≤ (24983872798777/50000000000000 : ℝ)^3195
        have hw : |(295659089/500000000 : ℝ)|=(295659089/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2956617441/5000000000 : ℝ)|^4219 ≤ (780755283421/1562500000000 : ℝ)^3195
        have hw : |(2956617441/5000000000 : ℝ)|=(2956617441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1245_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37871821/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14131/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5729/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5739/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1411/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14131/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5729/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14131/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5729/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14131/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5729/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14131/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5729/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14131/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5729/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14131/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5729/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5729/50000 : ℝ) ^ (8437/2048 : ℝ) ≤ (13300791592592449/100000000000000000000 : ℝ) := by
    have hpowers : (5729/50000 : ℝ)^8437 ≤ (13300791592592449/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5729 : ℕ)^8437*100000000000000000000^2048 ≤ 13300791592592449^2048*50000^8437 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5729 50000 13300791592592449 100000000000000000000 8437 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5729/50000 : ℝ)) (X := (13300791592592449/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8437 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14131/100000 : ℝ) ^ (8437/2048 : ℝ) ≤ (31552058513688421/100000000000000000000 : ℝ) := by
    have hpowers : (14131/100000 : ℝ)^8437 ≤ (31552058513688421/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14131 : ℕ)^8437*100000000000000000000^2048 ≤ 31552058513688421^2048*100000^8437 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14131 100000 31552058513688421 100000000000000000000 8437 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14131/100000 : ℝ)) (X := (31552058513688421/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8437 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013300791592592449/50000000000000000000 : ℝ) ≤ (1250080707828471/1250000000000000 : ℝ) ^ (8437/2048 : ℝ) := by
    have hpowers : (50013300791592592449/50000000000000000000 : ℝ)^2048 ≤ (1250080707828471/1250000000000000 : ℝ)^8437 := by
      have hnat : (50013300791592592449 : ℕ)^2048*1250000000000000^8437 ≤ 1250080707828471^8437*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013300791592592449 50000000000000000000 1250080707828471 1250000000000000 2048 8437 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250080707828471/1250000000000000 : ℝ)) (X := (50013300791592592449/50000000000000000000 : ℝ)) (by norm_num) 8437 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004485285010628087/10000000000000000000 : ℝ) ≤ (5000544287312461/5000000000000000 : ℝ) ^ (8437/2048 : ℝ) := by
    have hpowers : (10004485285010628087/10000000000000000000 : ℝ)^2048 ≤ (5000544287312461/5000000000000000 : ℝ)^8437 := by
      have hnat : (10004485285010628087 : ℕ)^2048*5000000000000000^8437 ≤ 5000544287312461^8437*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004485285010628087 10000000000000000000 5000544287312461 5000000000000000 2048 8437 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000544287312461/5000000000000000 : ℝ)) (X := (10004485285010628087/10000000000000000000 : ℝ)) (by norm_num) 8437 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031552058513688421/50000000000000000000 : ℝ) ≤ (2500382871655519/2500000000000000 : ℝ) ^ (8437/2048 : ℝ) := by
    have hpowers : (50031552058513688421/50000000000000000000 : ℝ)^2048 ≤ (2500382871655519/2500000000000000 : ℝ)^8437 := by
      have hnat : (50031552058513688421 : ℕ)^2048*2500000000000000^8437 ≤ 2500382871655519^8437*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031552058513688421 50000000000000000000 2500382871655519 2500000000000000 2048 8437 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500382871655519/2500000000000000 : ℝ)) (X := (50031552058513688421/50000000000000000000 : ℝ)) (by norm_num) 8437 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13300791592592449/100000000000000000000 : ℝ) ≤ ((6073085473835737/6075000000000000 : ℝ)+2*(20132363507/12150000000000 : ℝ)*(5729/50000 : ℝ))^(8437/2048 : ℝ) := by
    rw [show (6073085473835737/6075000000000000 : ℝ)+2*(20132363507/12150000000000 : ℝ)*(5729/50000 : ℝ)=(1250080707828471/1250000000000000 : ℝ) by norm_num, show 1+2*(13300791592592449/100000000000000000000 : ℝ)=(50013300791592592449/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31552058513688421/100000000000000000000 : ℝ)+(13300791592592449/100000000000000000000 : ℝ) ≤ ((6073085473835737/6075000000000000 : ℝ)+(20132363507/12150000000000 : ℝ)*((14131/100000 : ℝ)+(5729/50000 : ℝ)))^(8437/2048 : ℝ) := by
    rw [show (6073085473835737/6075000000000000 : ℝ)+(20132363507/12150000000000 : ℝ)*((14131/100000 : ℝ)+(5729/50000 : ℝ))=(5000544287312461/5000000000000000 : ℝ) by norm_num, show 1+(31552058513688421/100000000000000000000 : ℝ)+(13300791592592449/100000000000000000000 : ℝ)=(10004485285010628087/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31552058513688421/100000000000000000000 : ℝ) ≤ ((6073085473835737/6075000000000000 : ℝ)+2*(20132363507/12150000000000 : ℝ)*(14131/100000 : ℝ))^(8437/2048 : ℝ) := by
    rw [show (6073085473835737/6075000000000000 : ℝ)+2*(20132363507/12150000000000 : ℝ)*(14131/100000 : ℝ)=(2500382871655519/2500000000000000 : ℝ) by norm_num, show 1+2*(31552058513688421/100000000000000000000 : ℝ)=(50031552058513688421/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6073085473835737/6075000000000000 : ℝ)*(X 1 0+X 2 0)+(20132363507/12150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8437/2048 : ℝ)) (lo := (5729/50000 : ℝ)) (hi := (14131/100000 : ℝ)) (c := (6073085473835737/6075000000000000 : ℝ)) (alpha := (20132363507/12150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6073085473835737/6075000000000000 : ℝ)*(X 0 1+X 2 1)+(20132363507/12150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8437/2048 : ℝ)) (lo := (5729/50000 : ℝ)) (hi := (14131/100000 : ℝ)) (c := (6073085473835737/6075000000000000 : ℝ)) (alpha := (20132363507/12150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6073085473835737/6075000000000000 : ℝ)*(X 0 2+X 1 2)+(20132363507/12150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8437/2048 : ℝ)) (lo := (5729/50000 : ℝ)) (hi := (14131/100000 : ℝ)) (c := (6073085473835737/6075000000000000 : ℝ)) (alpha := (20132363507/12150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2118566039/10000000000 : ℝ)*X 0 0+(2695664063/5000000000 : ℝ)*X 0 1+(2633539173/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344340329/10000000000 : ℝ)*X 1 0+(-2181565717/10000000000 : ℝ)*X 1 1+(2633539171/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334021271/625000000 : ℝ)*X 2 0+(5267078341/10000000000 : ℝ)*X 2 1+(-2181565709/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2175176347/5000000000 : ℝ)*X 0 0+(66031727/156250000 : ℝ)*X 0 1+(559778249/1250000000 : ℝ)*X 0 2+(2175176347/5000000000 : ℝ)*X 1 0+(66031727/156250000 : ℝ)*X 1 1+(559778249/1250000000 : ℝ)*X 1 2+(2175176347/5000000000 : ℝ)*X 2 0+(66031727/156250000 : ℝ)*X 2 1+(559778249/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-132410687/625000000 : ℝ)*X 0 0+(5267392263/10000000000 : ℝ)*X 0 1+(5391012869/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312631413/10000000000 : ℝ)*X 1 0+(-2057631183/10000000000 : ℝ)*X 1 1+(539101243/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312631579/10000000000 : ℝ)*X 2 0+(5391012159/10000000000 : ℝ)*X 2 1+(-2057631329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((135948819/312500000 : ℝ)*X 0 0+(4477588169/10000000000 : ℝ)*X 0 1+(2113335339/5000000000 : ℝ)*X 0 2+(135948819/312500000 : ℝ)*X 1 0+(4477588169/10000000000 : ℝ)*X 1 1+(2113335339/5000000000 : ℝ)*X 1 2+(135948819/312500000 : ℝ)*X 2 0+(4477588169/10000000000 : ℝ)*X 2 1+(2113335339/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-9525029/2500000000 : ℝ)*X 0 0+(295659089/500000000 : ℝ)*X 0 1+(2956617441/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s6_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1394287435023843254501/135000000000000000000000000 : ℝ) := by norm_num
    linear_combination (134227443/25000000000000 : ℝ)*(lower2) + (51456409/25000000000000 : ℝ)*(lower3) + (537461477/100000000000000 : ℝ)*(lower4) + (36230961/25000000000000 : ℝ)*(lower5) + (6006742844518829/100000000000000 : ℝ)*(major0) + (6006742844518829/100000000000000 : ℝ)*(major1) + (6006742844518829/100000000000000 : ℝ)*(major2) + (8048300970455537/100000000000000 : ℝ)*(sp0) + (4024148548595631/50000000000000 : ℝ)*(sp1) + (2012073786604823/25000000000000 : ℝ)*(sp2) + (123911861731717/3125000000000 : ℝ)*(sp3) + (1734432587/20000000000000 : ℝ)*(sp5) + (1327866863/12500000000000 : ℝ)*(sp6) + (4798898659/100000000000000 : ℝ)*(sp8) + (123911861731717/3125000000000 : ℝ)*(f.failure) + (8048305769354197/100000000000000 : ℝ)*(f.sum) + (19246176253429/1215000000000000000000000000 : ℝ)*base66 + (252335360511527/607500000000000000000000000000 : ℝ)*base68 + (6275511922283473/607500000000000000000000000000 : ℝ)*base69 + (23535563781675973/607500000000000000000000000000 : ℝ)*base71 + (6071975873089/1215000000000000000000000000 : ℝ)*base74 + (1264659380721527/607500000000000000000000000000 : ℝ)*base76 + (17711088777863473/607500000000000000000000000000 : ℝ)*base77 + (1589737878306527/607500000000000000000000000000 : ℝ)*base80 + (4322257121627/607500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (1090407/78125000000000000000 : ℝ)*base89 + (1090407/78125000000000000000 : ℝ)*base91 + (1090407/78125000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (121539674931539102669033/33750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (175963489/25000000000000 : ℝ)*(lower2) + (199285217/100000000000000 : ℝ)*(lower3) + (569570811/100000000000000 : ℝ)*(lower4) + (112577237/20000000000000 : ℝ)*(lower5) + (754671572058453/12500000000000 : ℝ)*(major0) + (754671572058453/12500000000000 : ℝ)*(major1) + (48298980611741/800000000000 : ℝ)*(major2) + (1685666413/4000000000000 : ℝ)*(sp0) + (1909119931/25000000000000 : ℝ)*(sp3) + (1617859391374493/20000000000000 : ℝ)*(sp4) + (8089346115540307/100000000000000 : ℝ)*(sp5) + (8089346115540307/100000000000000 : ℝ)*(sp6) + (1992695640438011/50000000000000 : ℝ)*(sp7) + (7017007517/100000000000000 : ℝ)*(sp8) + (1992699458677873/50000000000000 : ℝ)*(f.failure) + (8089346115540307/100000000000000 : ℝ)*(f.sum) + (2991281921417/303750000000000000000000000 : ℝ)*base65 + (939602789181493/37968750000000000000000000000 : ℝ)*base67 + (51661530944009/4860000000000000000000000000 : ℝ)*base69 + (479518764696493/37968750000000000000000000000 : ℝ)*base71 + (645341178827/303750000000000000000000000 : ℝ)*base73 + (25802280226349/4860000000000000000000000000 : ℝ)*base75 + (376297649497949/50625000000000000000000000000 : ℝ)*base77 + (699412571711699/50625000000000000000000000000 : ℝ)*base79 + (1871738339093/405000000000000000000000000 : ℝ)*base82 + (2916733/1250000000000000000000 : ℝ)*base89 + (2916733/1250000000000000000000 : ℝ)*base91 + (9583267/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1245_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37871821/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14131/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5729/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5739/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1411/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1245_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1245_s7_0 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2118582603/10000000000 : ℝ)*x 0 + (5391135759/10000000000 : ℝ)*x 1 + (5267259783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2118582603/10000000000 : ℝ)^4219 ≤ (3220938512637/25000000000000 : ℝ)^3195 := by
    have hnat : (2118582603 : ℕ)^4219*25000000000000^3195 ≤ 3220938512637^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118582603 10000000000 3220938512637 25000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391135759/10000000000 : ℝ)^4219 ≤ (11056650786429/25000000000000 : ℝ)^3195 := by
    have hnat : (5391135759 : ℕ)^4219*25000000000000^3195 ≤ 11056650786429^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391135759 10000000000 11056650786429 25000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267259783/10000000000 : ℝ)^4219 ≤ (21444821397633/50000000000000 : ℝ)^3195 := by
    have hnat : (5267259783 : ℕ)^4219*50000000000000^3195 ≤ 21444821397633^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267259783 10000000000 21444821397633 50000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2118582603/10000000000 : ℝ), (5391135759/10000000000 : ℝ), (5267259783/10000000000 : ℝ)] ![(3220938512637/25000000000000 : ℝ), (11056650786429/25000000000000 : ℝ), (21444821397633/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2118582603/10000000000 : ℝ)|^4219 ≤ (3220938512637/25000000000000 : ℝ)^3195
        have hw : |(-2118582603/10000000000 : ℝ)|=(2118582603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391135759/10000000000 : ℝ)|^4219 ≤ (11056650786429/25000000000000 : ℝ)^3195
        have hw : |(5391135759/10000000000 : ℝ)|=(5391135759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267259783/10000000000 : ℝ)|^4219 ≤ (21444821397633/50000000000000 : ℝ)^3195
        have hw : |(5267259783/10000000000 : ℝ)|=(5267259783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1245_s7_1 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344291421/10000000000 : ℝ)*x 0 + (-2181389907/10000000000 : ℝ)*x 1 + (2633630009/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344291421/10000000000 : ℝ)^4219 ≤ (8743970866793/20000000000000 : ℝ)^3195 := by
    have hnat : (5344291421 : ℕ)^4219*20000000000000^3195 ≤ 8743970866793^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344291421 10000000000 8743970866793 20000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2181389907/10000000000 : ℝ)^4219 ≤ (13390500326233/100000000000000 : ℝ)^3195 := by
    have hnat : (2181389907 : ℕ)^4219*100000000000000^3195 ≤ 13390500326233^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181389907 10000000000 13390500326233 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633630009/5000000000 : ℝ)^4219 ≤ (8577929064417/20000000000000 : ℝ)^3195 := by
    have hnat : (2633630009 : ℕ)^4219*20000000000000^3195 ≤ 8577929064417^3195*5000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633630009 5000000000 8577929064417 20000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344291421/10000000000 : ℝ), (-2181389907/10000000000 : ℝ), (2633630009/5000000000 : ℝ)] ![(8743970866793/20000000000000 : ℝ), (13390500326233/100000000000000 : ℝ), (8577929064417/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344291421/10000000000 : ℝ)|^4219 ≤ (8743970866793/20000000000000 : ℝ)^3195
        have hw : |(5344291421/10000000000 : ℝ)|=(5344291421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2181389907/10000000000 : ℝ)|^4219 ≤ (13390500326233/100000000000000 : ℝ)^3195
        have hw : |(-2181389907/10000000000 : ℝ)|=(2181389907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633630009/5000000000 : ℝ)|^4219 ≤ (8577929064417/20000000000000 : ℝ)^3195
        have hw : |(2633630009/5000000000 : ℝ)|=(2633630009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1245_s7_2 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1068858283/2000000000 : ℝ)*x 0 + (131681497/250000000 : ℝ)*x 1 + (-2181390099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068858283/2000000000 : ℝ)^4219 ≤ (874397085383/2000000000000 : ℝ)^3195 := by
    have hnat : (1068858283 : ℕ)^4219*2000000000000^3195 ≤ 874397085383^3195*2000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068858283 2000000000 874397085383 2000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131681497/250000000 : ℝ)^4219 ≤ (42889643838251/100000000000000 : ℝ)^3195 := by
    have hnat : (131681497 : ℕ)^4219*100000000000000^3195 ≤ 42889643838251^3195*250000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131681497 250000000 42889643838251 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2181390099/10000000000 : ℝ)^4219 ≤ (13390501882569/100000000000000 : ℝ)^3195 := by
    have hnat : (2181390099 : ℕ)^4219*100000000000000^3195 ≤ 13390501882569^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181390099 10000000000 13390501882569 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068858283/2000000000 : ℝ), (131681497/250000000 : ℝ), (-2181390099/10000000000 : ℝ)] ![(874397085383/2000000000000 : ℝ), (42889643838251/100000000000000 : ℝ), (13390501882569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068858283/2000000000 : ℝ)|^4219 ≤ (874397085383/2000000000000 : ℝ)^3195
        have hw : |(1068858283/2000000000 : ℝ)|=(1068858283/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131681497/250000000 : ℝ)|^4219 ≤ (42889643838251/100000000000000 : ℝ)^3195
        have hw : |(131681497/250000000 : ℝ)|=(131681497/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2181390099/10000000000 : ℝ)|^4219 ≤ (13390501882569/100000000000000 : ℝ)^3195
        have hw : |(-2181390099/10000000000 : ℝ)|=(2181390099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1245_s7_3 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4350362351/10000000000 : ℝ)*x 0 + (845281691/2000000000 : ℝ)*x 1 + (4477845443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4350362351/10000000000 : ℝ)^4219 ≤ (33317511003289/100000000000000 : ℝ)^3195 := by
    have hnat : (4350362351 : ℕ)^4219*100000000000000^3195 ≤ 33317511003289^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350362351 10000000000 33317511003289 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (845281691/2000000000 : ℝ)^4219 ≤ (16034854857087/50000000000000 : ℝ)^3195 := by
    have hnat : (845281691 : ℕ)^4219*50000000000000^3195 ≤ 16034854857087^3195*2000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845281691 2000000000 16034854857087 50000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4477845443/10000000000 : ℝ)^4219 ≤ (8653194816059/25000000000000 : ℝ)^3195 := by
    have hnat : (4477845443 : ℕ)^4219*25000000000000^3195 ≤ 8653194816059^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4477845443 10000000000 8653194816059 25000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4350362351/10000000000 : ℝ), (845281691/2000000000 : ℝ), (4477845443/10000000000 : ℝ)] ![(33317511003289/100000000000000 : ℝ), (16034854857087/50000000000000 : ℝ), (8653194816059/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4350362351/10000000000 : ℝ)|^4219 ≤ (33317511003289/100000000000000 : ℝ)^3195
        have hw : |(4350362351/10000000000 : ℝ)|=(4350362351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(845281691/2000000000 : ℝ)|^4219 ≤ (16034854857087/50000000000000 : ℝ)^3195
        have hw : |(845281691/2000000000 : ℝ)|=(845281691/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4477845443/10000000000 : ℝ)|^4219 ≤ (8653194816059/25000000000000 : ℝ)^3195
        have hw : |(4477845443/10000000000 : ℝ)|=(4477845443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1245_s7_4 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-264823393/1250000000 : ℝ)*x 0 + (5267572951/10000000000 : ℝ)*x 1 + (5390821543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264823393/1250000000 : ℝ)^4219 ≤ (12883790516481/100000000000000 : ℝ)^3195 := by
    have hnat : (264823393 : ℕ)^4219*100000000000000^3195 ≤ 12883790516481^3195*1250000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264823393 1250000000 12883790516481 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267572951/10000000000 : ℝ)^4219 ≤ (10723252535563/25000000000000 : ℝ)^3195 := by
    have hnat : (5267572951 : ℕ)^4219*25000000000000^3195 ≤ 10723252535563^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267572951 10000000000 10723252535563 25000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390821543/10000000000 : ℝ)^4219 ≤ (44223199328597/100000000000000 : ℝ)^3195 := by
    have hnat : (5390821543 : ℕ)^4219*100000000000000^3195 ≤ 44223199328597^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390821543 10000000000 44223199328597 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-264823393/1250000000 : ℝ), (5267572951/10000000000 : ℝ), (5390821543/10000000000 : ℝ)] ![(12883790516481/100000000000000 : ℝ), (10723252535563/25000000000000 : ℝ), (44223199328597/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-264823393/1250000000 : ℝ)|^4219 ≤ (12883790516481/100000000000000 : ℝ)^3195
        have hw : |(-264823393/1250000000 : ℝ)|=(264823393/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267572951/10000000000 : ℝ)|^4219 ≤ (10723252535563/25000000000000 : ℝ)^3195
        have hw : |(5267572951/10000000000 : ℝ)|=(5267572951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390821543/10000000000 : ℝ)|^4219 ≤ (44223199328597/100000000000000 : ℝ)^3195
        have hw : |(5390821543/10000000000 : ℝ)|=(5390821543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1245_s7_5 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1328169299/2500000000 : ℝ)*x 0 + (-205782737/1000000000 : ℝ)*x 1 + (2695411389/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328169299/2500000000 : ℝ)^4219 ≤ (17351465407/40000000000 : ℝ)^3195 := by
    have hnat : (1328169299 : ℕ)^4219*40000000000^3195 ≤ 17351465407^3195*2500000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328169299 2500000000 17351465407 40000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (205782737/1000000000 : ℝ)^4219 ≤ (6199061876903/50000000000000 : ℝ)^3195 := by
    have hnat : (205782737 : ℕ)^4219*50000000000000^3195 ≤ 6199061876903^3195*1000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205782737 1000000000 6199061876903 50000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695411389/5000000000 : ℝ)^4219 ≤ (22111606353447/50000000000000 : ℝ)^3195 := by
    have hnat : (2695411389 : ℕ)^4219*50000000000000^3195 ≤ 22111606353447^3195*5000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695411389 5000000000 22111606353447 50000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328169299/2500000000 : ℝ), (-205782737/1000000000 : ℝ), (2695411389/5000000000 : ℝ)] ![(17351465407/40000000000 : ℝ), (6199061876903/50000000000000 : ℝ), (22111606353447/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328169299/2500000000 : ℝ)|^4219 ≤ (17351465407/40000000000 : ℝ)^3195
        have hw : |(1328169299/2500000000 : ℝ)|=(1328169299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-205782737/1000000000 : ℝ)|^4219 ≤ (6199061876903/50000000000000 : ℝ)^3195
        have hw : |(-205782737/1000000000 : ℝ)|=(205782737/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695411389/5000000000 : ℝ)|^4219 ≤ (22111606353447/50000000000000 : ℝ)^3195
        have hw : |(2695411389/5000000000 : ℝ)|=(2695411389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1245_s7_6 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1328169457/2500000000 : ℝ)*x 0 + (2695410747/5000000000 : ℝ)*x 1 + (-2057828263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328169457/2500000000 : ℝ)^4219 ≤ (43378670331757/100000000000000 : ℝ)^3195 := by
    have hnat : (1328169457 : ℕ)^4219*100000000000000^3195 ≤ 43378670331757^3195*2500000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328169457 2500000000 43378670331757 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695410747/5000000000 : ℝ)^4219 ≤ (22111599398899/50000000000000 : ℝ)^3195 := by
    have hnat : (2695410747 : ℕ)^4219*50000000000000^3195 ≤ 22111599398899^3195*5000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695410747 5000000000 22111599398899 50000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2057828263/10000000000 : ℝ)^4219 ≤ (6199065429183/50000000000000 : ℝ)^3195 := by
    have hnat : (2057828263 : ℕ)^4219*50000000000000^3195 ≤ 6199065429183^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2057828263 10000000000 6199065429183 50000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328169457/2500000000 : ℝ), (2695410747/5000000000 : ℝ), (-2057828263/10000000000 : ℝ)] ![(43378670331757/100000000000000 : ℝ), (22111599398899/50000000000000 : ℝ), (6199065429183/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328169457/2500000000 : ℝ)|^4219 ≤ (43378670331757/100000000000000 : ℝ)^3195
        have hw : |(1328169457/2500000000 : ℝ)|=(1328169457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695410747/5000000000 : ℝ)|^4219 ≤ (22111599398899/50000000000000 : ℝ)^3195
        have hw : |(2695410747/5000000000 : ℝ)|=(2695410747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2057828263/10000000000 : ℝ)|^4219 ≤ (6199065429183/50000000000000 : ℝ)^3195
        have hw : |(-2057828263/10000000000 : ℝ)|=(2057828263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1245_s7_7 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4350371819/10000000000 : ℝ)*x 0 + (2238605843/5000000000 : ℝ)*x 1 + (2113522237/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4350371819/10000000000 : ℝ)^4219 ≤ (416470084431/1250000000000 : ℝ)^3195 := by
    have hnat : (4350371819 : ℕ)^4219*1250000000000^3195 ≤ 416470084431^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350371819 10000000000 416470084431 1250000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2238605843/5000000000 : ℝ)^4219 ≤ (34606310535269/100000000000000 : ℝ)^3195 := by
    have hnat : (2238605843 : ℕ)^4219*100000000000000^3195 ≤ 34606310535269^3195*5000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2238605843 5000000000 34606310535269 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2113522237/5000000000 : ℝ)^4219 ≤ (1603804134879/5000000000000 : ℝ)^3195 := by
    have hnat : (2113522237 : ℕ)^4219*5000000000000^3195 ≤ 1603804134879^3195*5000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113522237 5000000000 1603804134879 5000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4350371819/10000000000 : ℝ), (2238605843/5000000000 : ℝ), (2113522237/5000000000 : ℝ)] ![(416470084431/1250000000000 : ℝ), (34606310535269/100000000000000 : ℝ), (1603804134879/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4350371819/10000000000 : ℝ)|^4219 ≤ (416470084431/1250000000000 : ℝ)^3195
        have hw : |(4350371819/10000000000 : ℝ)|=(4350371819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2238605843/5000000000 : ℝ)|^4219 ≤ (34606310535269/100000000000000 : ℝ)^3195
        have hw : |(2238605843/5000000000 : ℝ)|=(2238605843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2113522237/5000000000 : ℝ)|^4219 ≤ (1603804134879/5000000000000 : ℝ)^3195
        have hw : |(2113522237/5000000000 : ℝ)|=(2113522237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1245_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37871821/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1411/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5739/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5741/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7053/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1411/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5739/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1411/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5739/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1411/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5739/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1411/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5739/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1411/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5739/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1411/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5739/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5739/50000 : ℝ) ^ (8437/2048 : ℝ) ≤ (3349174026687083/25000000000000000000 : ℝ) := by
    have hpowers : (5739/50000 : ℝ)^8437 ≤ (3349174026687083/25000000000000000000 : ℝ)^2048 := by
      have hnat : (5739 : ℕ)^8437*25000000000000000000^2048 ≤ 3349174026687083^2048*50000^8437 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5739 50000 3349174026687083 25000000000000000000 8437 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5739/50000 : ℝ)) (X := (3349174026687083/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8437 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1411/10000 : ℝ) ^ (8437/2048 : ℝ) ≤ (6271867827967653/20000000000000000000 : ℝ) := by
    have hpowers : (1411/10000 : ℝ)^8437 ≤ (6271867827967653/20000000000000000000 : ℝ)^2048 := by
      have hnat : (1411 : ℕ)^8437*20000000000000000000^2048 ≤ 6271867827967653^2048*10000^8437 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1411 10000 6271867827967653 20000000000000000000 8437 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1411/10000 : ℝ)) (X := (6271867827967653/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8437 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503349174026687083/12500000000000000000 : ℝ) ≤ (5000325158832501/5000000000000000 : ℝ) ^ (8437/2048 : ℝ) := by
    have hpowers : (12503349174026687083/12500000000000000000 : ℝ)^2048 ≤ (5000325158832501/5000000000000000 : ℝ)^8437 := by
      have hnat : (12503349174026687083 : ℕ)^2048*5000000000000000^8437 ≤ 5000325158832501^8437*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503349174026687083 12500000000000000000 5000325158832501 5000000000000000 2048 8437 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000325158832501/5000000000000000 : ℝ)) (X := (12503349174026687083/12500000000000000000 : ℝ)) (by norm_num) 8437 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044756035246586597/100000000000000000000 : ℝ) ≤ (10001086225335049/10000000000000000 : ℝ) ^ (8437/2048 : ℝ) := by
    have hpowers : (100044756035246586597/100000000000000000000 : ℝ)^2048 ≤ (10001086225335049/10000000000000000 : ℝ)^8437 := by
      have hnat : (100044756035246586597 : ℕ)^2048*10000000000000000^8437 ≤ 10001086225335049^8437*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044756035246586597 100000000000000000000 10001086225335049 10000000000000000 2048 8437 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001086225335049/10000000000000000 : ℝ)) (X := (100044756035246586597/100000000000000000000 : ℝ)) (by norm_num) 8437 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006271867827967653/10000000000000000000 : ℝ) ≤ (1250190266625637/1250000000000000 : ℝ) ^ (8437/2048 : ℝ) := by
    have hpowers : (10006271867827967653/10000000000000000000 : ℝ)^2048 ≤ (1250190266625637/1250000000000000 : ℝ)^8437 := by
      have hnat : (10006271867827967653 : ℕ)^2048*1250000000000000^8437 ≤ 1250190266625637^8437*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006271867827967653 10000000000000000000 1250190266625637 1250000000000000 2048 8437 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250190266625637/1250000000000000 : ℝ)) (X := (10006271867827967653/10000000000000000000 : ℝ)) (by norm_num) 8437 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3349174026687083/25000000000000000000 : ℝ) ≤ ((6577926234905171583/6580000000000000000 : ℝ)+2*(435907670047/263200000000000 : ℝ)*(5739/50000 : ℝ))^(8437/2048 : ℝ) := by
    rw [show (6577926234905171583/6580000000000000000 : ℝ)+2*(435907670047/263200000000000 : ℝ)*(5739/50000 : ℝ)=(5000325158832501/5000000000000000 : ℝ) by norm_num, show 1+2*(3349174026687083/25000000000000000000 : ℝ)=(12503349174026687083/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6271867827967653/20000000000000000000 : ℝ)+(3349174026687083/25000000000000000000 : ℝ) ≤ ((6577926234905171583/6580000000000000000 : ℝ)+(435907670047/263200000000000 : ℝ)*((1411/10000 : ℝ)+(5739/50000 : ℝ)))^(8437/2048 : ℝ) := by
    rw [show (6577926234905171583/6580000000000000000 : ℝ)+(435907670047/263200000000000 : ℝ)*((1411/10000 : ℝ)+(5739/50000 : ℝ))=(10001086225335049/10000000000000000 : ℝ) by norm_num, show 1+(6271867827967653/20000000000000000000 : ℝ)+(3349174026687083/25000000000000000000 : ℝ)=(100044756035246586597/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6271867827967653/20000000000000000000 : ℝ) ≤ ((6577926234905171583/6580000000000000000 : ℝ)+2*(435907670047/263200000000000 : ℝ)*(1411/10000 : ℝ))^(8437/2048 : ℝ) := by
    rw [show (6577926234905171583/6580000000000000000 : ℝ)+2*(435907670047/263200000000000 : ℝ)*(1411/10000 : ℝ)=(1250190266625637/1250000000000000 : ℝ) by norm_num, show 1+2*(6271867827967653/20000000000000000000 : ℝ)=(10006271867827967653/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6577926234905171583/6580000000000000000 : ℝ)*(X 1 0+X 2 0)+(435907670047/263200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8437/2048 : ℝ)) (lo := (5739/50000 : ℝ)) (hi := (1411/10000 : ℝ)) (c := (6577926234905171583/6580000000000000000 : ℝ)) (alpha := (435907670047/263200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6577926234905171583/6580000000000000000 : ℝ)*(X 0 1+X 2 1)+(435907670047/263200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8437/2048 : ℝ)) (lo := (5739/50000 : ℝ)) (hi := (1411/10000 : ℝ)) (c := (6577926234905171583/6580000000000000000 : ℝ)) (alpha := (435907670047/263200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6577926234905171583/6580000000000000000 : ℝ)*(X 0 2+X 1 2)+(435907670047/263200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8437/2048 : ℝ)) (lo := (5739/50000 : ℝ)) (hi := (1411/10000 : ℝ)) (c := (6577926234905171583/6580000000000000000 : ℝ)) (alpha := (435907670047/263200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2118582603/10000000000 : ℝ)*X 0 0+(5391135759/10000000000 : ℝ)*X 0 1+(5267259783/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344291421/10000000000 : ℝ)*X 1 0+(-2181389907/10000000000 : ℝ)*X 1 1+(2633630009/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068858283/2000000000 : ℝ)*X 2 0+(131681497/250000000 : ℝ)*X 2 1+(-2181390099/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4350362351/10000000000 : ℝ)*X 0 0+(845281691/2000000000 : ℝ)*X 0 1+(4477845443/10000000000 : ℝ)*X 0 2+(4350362351/10000000000 : ℝ)*X 1 0+(845281691/2000000000 : ℝ)*X 1 1+(4477845443/10000000000 : ℝ)*X 1 2+(4350362351/10000000000 : ℝ)*X 2 0+(845281691/2000000000 : ℝ)*X 2 1+(4477845443/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-264823393/1250000000 : ℝ)*X 0 0+(5267572951/10000000000 : ℝ)*X 0 1+(5390821543/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328169299/2500000000 : ℝ)*X 1 0+(-205782737/1000000000 : ℝ)*X 1 1+(2695411389/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328169457/2500000000 : ℝ)*X 2 0+(2695410747/5000000000 : ℝ)*X 2 1+(-2057828263/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4350371819/10000000000 : ℝ)*X 0 0+(2238605843/5000000000 : ℝ)*X 0 1+(2113522237/5000000000 : ℝ)*X 0 2+(4350371819/10000000000 : ℝ)*X 1 0+(2238605843/5000000000 : ℝ)*X 1 1+(2113522237/5000000000 : ℝ)*X 1 2+(4350371819/10000000000 : ℝ)*X 2 0+(2238605843/5000000000 : ℝ)*X 2 1+(2113522237/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (74762257437778177578327/13160000000000000000000000000 : ℝ) := by norm_num
    linear_combination (33478277/3125000000000 : ℝ)*(base19) + (275662297/25000000000000 : ℝ)*(base23) + (34153519/50000000000000 : ℝ)*(lower2) + (143907861/50000000000000 : ℝ)*(upper3) + (89901961/100000000000000 : ℝ)*(lower4) + (3012463968531311/50000000000000 : ℝ)*(major0) + (3012463968531311/50000000000000 : ℝ)*(major1) + (6024927937062623/100000000000000 : ℝ)*(major2) + (8072638646554717/100000000000000 : ℝ)*(sp0) + (8072670669048337/100000000000000 : ℝ)*(sp1) + (8072670637704013/100000000000000 : ℝ)*(sp2) + (1988579464051757/50000000000000 : ℝ)*(sp3) + (8273449621/25000000000000 : ℝ)*(sp4) + (12508150551/50000000000000 : ℝ)*(sp7) + (497147993050577/12500000000000 : ℝ)*(f.failure) + (8072671740353201/100000000000000 : ℝ)*(f.sum) + (14722540444617/5264000000000000000000000000 : ℝ)*base66 + (868693410862052187/329000000000000000000000000000000 : ℝ)*base68 + (8966577246277892209/658000000000000000000000000000000 : ℝ)*base69 + (3770554506637947813/329000000000000000000000000000000 : ℝ)*base71 + (36747044212009/5264000000000000000000000000 : ℝ)*base74 + (1547277624416107791/658000000000000000000000000000000 : ℝ)*base76 + (334666255905765759/47000000000000000000000000000000 : ℝ)*base77 + (400197212039234241/47000000000000000000000000000000 : ℝ)*base80 + (10759295356989/940000000000000000000000000 : ℝ)*base82 + (2340717/312500000000000000000 : ℝ)*base89 + (2340717/312500000000000000000 : ℝ)*base91 + (784283/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1416580105143597448748165043/329000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5113209/25000000000000 : ℝ)*(base19) + (1253036403/100000000000000 : ℝ)*(base23) + (78190471/50000000000000 : ℝ)*(upper3) + (31170811/12500000000000 : ℝ)*(lower4) + (6055529873611793/100000000000000 : ℝ)*(major0) + (6055529873611793/100000000000000 : ℝ)*(major1) + (6055529873611793/100000000000000 : ℝ)*(major2) + (34601240543/50000000000000 : ℝ)*(sp1) + (7051366437/20000000000000 : ℝ)*(sp2) + (27105142887/100000000000000 : ℝ)*(sp3) + (4056837332846409/50000000000000 : ℝ)*(sp4) + (507100340172431/6250000000000 : ℝ)*(sp5) + (8113638155824231/100000000000000 : ℝ)*(sp6) + (79947156657281/2000000000000 : ℝ)*(sp7) + (1998692469003469/50000000000000 : ℝ)*(f.failure) + (4056837332846409/50000000000000 : ℝ)*(f.sum) + (12752063969929/13160000000000000000000000000 : ℝ)*base66 + (5955880657830053319/658000000000000000000000000000000 : ℝ)*base67 + (7246749854065946681/658000000000000000000000000000000 : ℝ)*base70 + (4989022494482053319/658000000000000000000000000000000 : ℝ)*base71 + (382886112809/13160000000000000000000000000 : ℝ)*base74 + (8470781349938053319/658000000000000000000000000000000 : ℝ)*base75 + (6594448255064053319/658000000000000000000000000000000 : ℝ)*base77 + (9791568133537946681/658000000000000000000000000000000 : ℝ)*base80 + (9666337163591/13160000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (13847049/1250000000000000000000 : ℝ)*base89 + (13847049/1250000000000000000000 : ℝ)*base91 + (13847049/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1245_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37871821/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1411/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5739/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5741/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7053/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1245_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1245_s8_0 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2118585273/10000000000 : ℝ)*x 0 + (5391098717/10000000000 : ℝ)*x 1 + (1316823777/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2118585273/10000000000 : ℝ)^4219 ≤ (6441887745823/50000000000000 : ℝ)^3195 := by
    have hnat : (2118585273 : ℕ)^4219*50000000000000^3195 ≤ 6441887745823^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118585273 10000000000 6441887745823 50000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391098717/10000000000 : ℝ)^4219 ≤ (22113100938211/50000000000000 : ℝ)^3195 := by
    have hnat : (5391098717 : ℕ)^4219*50000000000000^3195 ≤ 22113100938211^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391098717 10000000000 22113100938211 50000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316823777/2500000000 : ℝ)^4219 ≤ (42890022625027/100000000000000 : ℝ)^3195 := by
    have hnat : (1316823777 : ℕ)^4219*100000000000000^3195 ≤ 42890022625027^3195*2500000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316823777 2500000000 42890022625027 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2118585273/10000000000 : ℝ), (5391098717/10000000000 : ℝ), (1316823777/2500000000 : ℝ)] ![(6441887745823/50000000000000 : ℝ), (22113100938211/50000000000000 : ℝ), (42890022625027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2118585273/10000000000 : ℝ)|^4219 ≤ (6441887745823/50000000000000 : ℝ)^3195
        have hw : |(-2118585273/10000000000 : ℝ)|=(2118585273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391098717/10000000000 : ℝ)|^4219 ≤ (22113100938211/50000000000000 : ℝ)^3195
        have hw : |(5391098717/10000000000 : ℝ)|=(5391098717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316823777/2500000000 : ℝ)|^4219 ≤ (42890022625027/100000000000000 : ℝ)^3195
        have hw : |(1316823777/2500000000 : ℝ)|=(1316823777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1245_s8_1 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344282257/10000000000 : ℝ)*x 0 + (-1090677797/5000000000 : ℝ)*x 1 + (1316823773/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344282257/10000000000 : ℝ)^4219 ≤ (43719755339207/100000000000000 : ℝ)^3195 := by
    have hnat : (5344282257 : ℕ)^4219*100000000000000^3195 ≤ 43719755339207^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344282257 10000000000 43719755339207 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1090677797/5000000000 : ℝ)^4219 ≤ (6695111094297/50000000000000 : ℝ)^3195 := by
    have hnat : (1090677797 : ℕ)^4219*50000000000000^3195 ≤ 6695111094297^3195*5000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090677797 5000000000 6695111094297 50000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316823773/2500000000 : ℝ)^4219 ≤ (10722505613247/25000000000000 : ℝ)^3195 := by
    have hnat : (1316823773 : ℕ)^4219*25000000000000^3195 ≤ 10722505613247^3195*2500000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316823773 2500000000 10722505613247 25000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344282257/10000000000 : ℝ), (-1090677797/5000000000 : ℝ), (1316823773/2500000000 : ℝ)] ![(43719755339207/100000000000000 : ℝ), (6695111094297/50000000000000 : ℝ), (10722505613247/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344282257/10000000000 : ℝ)|^4219 ≤ (43719755339207/100000000000000 : ℝ)^3195
        have hw : |(5344282257/10000000000 : ℝ)|=(5344282257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1090677797/5000000000 : ℝ)|^4219 ≤ (6695111094297/50000000000000 : ℝ)^3195
        have hw : |(-1090677797/5000000000 : ℝ)|=(1090677797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316823773/2500000000 : ℝ)|^4219 ≤ (10722505613247/25000000000000 : ℝ)^3195
        have hw : |(1316823773/2500000000 : ℝ)|=(1316823773/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1245_s8_2 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672141119/5000000000 : ℝ)*x 0 + (1316823777/2500000000 : ℝ)*x 1 + (-1090677799/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672141119/5000000000 : ℝ)^4219 ≤ (21859877566979/50000000000000 : ℝ)^3195 := by
    have hnat : (2672141119 : ℕ)^4219*50000000000000^3195 ≤ 21859877566979^3195*5000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672141119 5000000000 21859877566979 50000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316823777/2500000000 : ℝ)^4219 ≤ (42890022625027/100000000000000 : ℝ)^3195 := by
    have hnat : (1316823777 : ℕ)^4219*100000000000000^3195 ≤ 42890022625027^3195*2500000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316823777 2500000000 42890022625027 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1090677799/5000000000 : ℝ)^4219 ≤ (6695111110509/50000000000000 : ℝ)^3195 := by
    have hnat : (1090677799 : ℕ)^4219*50000000000000^3195 ≤ 6695111110509^3195*5000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090677799 5000000000 6695111110509 50000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672141119/5000000000 : ℝ), (1316823777/2500000000 : ℝ), (-1090677799/5000000000 : ℝ)] ![(21859877566979/50000000000000 : ℝ), (42890022625027/100000000000000 : ℝ), (6695111110509/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672141119/5000000000 : ℝ)|^4219 ≤ (21859877566979/50000000000000 : ℝ)^3195
        have hw : |(2672141119/5000000000 : ℝ)|=(2672141119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316823777/2500000000 : ℝ)|^4219 ≤ (42890022625027/100000000000000 : ℝ)^3195
        have hw : |(1316823777/2500000000 : ℝ)|=(1316823777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1090677799/5000000000 : ℝ)|^4219 ≤ (6695111110509/50000000000000 : ℝ)^3195
        have hw : |(-1090677799/5000000000 : ℝ)|=(1090677799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1245_s8_3 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4350363957/10000000000 : ℝ)*x 0 + (4226481883/10000000000 : ℝ)*x 1 + (4477771771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4350363957/10000000000 : ℝ)^4219 ≤ (4164690905623/12500000000000 : ℝ)^3195 := by
    have hnat : (4350363957 : ℕ)^4219*12500000000000^3195 ≤ 4164690905623^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350363957 10000000000 4164690905623 12500000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4226481883/10000000000 : ℝ)^4219 ≤ (32070445455471/100000000000000 : ℝ)^3195 := by
    have hnat : (4226481883 : ℕ)^4219*100000000000000^3195 ≤ 32070445455471^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4226481883 10000000000 32070445455471 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4477771771/10000000000 : ℝ)^4219 ≤ (34612027282399/100000000000000 : ℝ)^3195 := by
    have hnat : (4477771771 : ℕ)^4219*100000000000000^3195 ≤ 34612027282399^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4477771771 10000000000 34612027282399 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4350363957/10000000000 : ℝ), (4226481883/10000000000 : ℝ), (4477771771/10000000000 : ℝ)] ![(4164690905623/12500000000000 : ℝ), (32070445455471/100000000000000 : ℝ), (34612027282399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4350363957/10000000000 : ℝ)|^4219 ≤ (4164690905623/12500000000000 : ℝ)^3195
        have hw : |(4350363957/10000000000 : ℝ)|=(4350363957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4226481883/10000000000 : ℝ)|^4219 ≤ (32070445455471/100000000000000 : ℝ)^3195
        have hw : |(4226481883/10000000000 : ℝ)|=(4226481883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4477771771/10000000000 : ℝ)|^4219 ≤ (34612027282399/100000000000000 : ℝ)^3195
        have hw : |(4477771771/10000000000 : ℝ)|=(4477771771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1245_s8_4 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2118589477/10000000000 : ℝ)*x 0 + (5267607231/10000000000 : ℝ)*x 1 + (2695392893/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2118589477/10000000000 : ℝ)^4219 ≤ (3220952312839/25000000000000 : ℝ)^3195 := by
    have hnat : (2118589477 : ℕ)^4219*25000000000000^3195 ≤ 3220952312839^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118589477 10000000000 3220952312839 25000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267607231/10000000000 : ℝ)^4219 ≤ (42893378742731/100000000000000 : ℝ)^3195 := by
    have hnat : (5267607231 : ℕ)^4219*100000000000000^3195 ≤ 42893378742731^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267607231 10000000000 42893378742731 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695392893/5000000000 : ℝ)^4219 ≤ (5527851498337/12500000000000 : ℝ)^3195 := by
    have hnat : (2695392893 : ℕ)^4219*12500000000000^3195 ≤ 5527851498337^3195*5000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695392893 5000000000 5527851498337 12500000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2118589477/10000000000 : ℝ), (5267607231/10000000000 : ℝ), (2695392893/5000000000 : ℝ)] ![(3220952312839/25000000000000 : ℝ), (42893378742731/100000000000000 : ℝ), (5527851498337/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2118589477/10000000000 : ℝ)|^4219 ≤ (3220952312839/25000000000000 : ℝ)^3195
        have hw : |(-2118589477/10000000000 : ℝ)|=(2118589477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267607231/10000000000 : ℝ)|^4219 ≤ (42893378742731/100000000000000 : ℝ)^3195
        have hw : |(5267607231/10000000000 : ℝ)|=(5267607231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695392893/5000000000 : ℝ)|^4219 ≤ (5527851498337/12500000000000 : ℝ)^3195
        have hw : |(2695392893/5000000000 : ℝ)|=(2695392893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1245_s8_5 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656343193/5000000000 : ℝ)*x 0 + (-2057865499/10000000000 : ℝ)*x 1 + (5390785629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656343193/5000000000 : ℝ)^4219 ≤ (43378762604581/100000000000000 : ℝ)^3195 := by
    have hnat : (2656343193 : ℕ)^4219*100000000000000^3195 ≤ 43378762604581^3195*5000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656343193 5000000000 43378762604581 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2057865499/10000000000 : ℝ)^4219 ≤ (6199213551343/50000000000000 : ℝ)^3195 := by
    have hnat : (2057865499 : ℕ)^4219*50000000000000^3195 ≤ 6199213551343^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2057865499 10000000000 6199213551343 50000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390785629/10000000000 : ℝ)^4219 ≤ (44222810285977/100000000000000 : ℝ)^3195 := by
    have hnat : (5390785629 : ℕ)^4219*100000000000000^3195 ≤ 44222810285977^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390785629 10000000000 44222810285977 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656343193/5000000000 : ℝ), (-2057865499/10000000000 : ℝ), (5390785629/10000000000 : ℝ)] ![(43378762604581/100000000000000 : ℝ), (6199213551343/50000000000000 : ℝ), (44222810285977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656343193/5000000000 : ℝ)|^4219 ≤ (43378762604581/100000000000000 : ℝ)^3195
        have hw : |(2656343193/5000000000 : ℝ)|=(2656343193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2057865499/10000000000 : ℝ)|^4219 ≤ (6199213551343/50000000000000 : ℝ)^3195
        have hw : |(-2057865499/10000000000 : ℝ)|=(2057865499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390785629/10000000000 : ℝ)|^4219 ≤ (44222810285977/100000000000000 : ℝ)^3195
        have hw : |(5390785629/10000000000 : ℝ)|=(5390785629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1245_s8_6 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656343021/5000000000 : ℝ)*x 0 + (539078617/1000000000 : ℝ)*x 1 + (-2057865227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656343021/5000000000 : ℝ)^4219 ≤ (43378758895553/100000000000000 : ℝ)^3195 := by
    have hnat : (2656343021 : ℕ)^4219*100000000000000^3195 ≤ 43378758895553^3195*5000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656343021 5000000000 43378758895553 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539078617/1000000000 : ℝ)^4219 ≤ (44222816146417/100000000000000 : ℝ)^3195 := by
    have hnat : (539078617 : ℕ)^4219*100000000000000^3195 ≤ 44222816146417^3195*1000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539078617 1000000000 44222816146417 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2057865227/10000000000 : ℝ)^4219 ≤ (6199212469343/50000000000000 : ℝ)^3195 := by
    have hnat : (2057865227 : ℕ)^4219*50000000000000^3195 ≤ 6199212469343^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2057865227 10000000000 6199212469343 50000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656343021/5000000000 : ℝ), (539078617/1000000000 : ℝ), (-2057865227/10000000000 : ℝ)] ![(43378758895553/100000000000000 : ℝ), (44222816146417/100000000000000 : ℝ), (6199212469343/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656343021/5000000000 : ℝ)|^4219 ≤ (43378758895553/100000000000000 : ℝ)^3195
        have hw : |(2656343021/5000000000 : ℝ)|=(2656343021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539078617/1000000000 : ℝ)|^4219 ≤ (44222816146417/100000000000000 : ℝ)^3195
        have hw : |(539078617/1000000000 : ℝ)|=(539078617/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2057865227/10000000000 : ℝ)|^4219 ≤ (6199212469343/50000000000000 : ℝ)^3195
        have hw : |(-2057865227/10000000000 : ℝ)|=(2057865227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1245_s8_7 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4350373373/10000000000 : ℝ)*x 0 + (2238569167/5000000000 : ℝ)*x 1 + (4227117621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4350373373/10000000000 : ℝ)^4219 ≤ (16658811235151/50000000000000 : ℝ)^3195 := by
    have hnat : (4350373373 : ℕ)^4219*50000000000000^3195 ≤ 16658811235151^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350373373 10000000000 16658811235151 50000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2238569167/5000000000 : ℝ)^4219 ≤ (17302780926839/50000000000000 : ℝ)^3195 := by
    have hnat : (2238569167 : ℕ)^4219*50000000000000^3195 ≤ 17302780926839^3195*5000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2238569167 5000000000 17302780926839 50000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4227117621/10000000000 : ℝ)^4219 ≤ (256614525269/800000000000 : ℝ)^3195 := by
    have hnat : (4227117621 : ℕ)^4219*800000000000^3195 ≤ 256614525269^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227117621 10000000000 256614525269 800000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4350373373/10000000000 : ℝ), (2238569167/5000000000 : ℝ), (4227117621/10000000000 : ℝ)] ![(16658811235151/50000000000000 : ℝ), (17302780926839/50000000000000 : ℝ), (256614525269/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4350373373/10000000000 : ℝ)|^4219 ≤ (16658811235151/50000000000000 : ℝ)^3195
        have hw : |(4350373373/10000000000 : ℝ)|=(4350373373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2238569167/5000000000 : ℝ)|^4219 ≤ (17302780926839/50000000000000 : ℝ)^3195
        have hw : |(2238569167/5000000000 : ℝ)|=(2238569167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4227117621/10000000000 : ℝ)|^4219 ≤ (256614525269/800000000000 : ℝ)^3195
        have hw : |(4227117621/10000000000 : ℝ)|=(4227117621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1245_s8_8 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-7081332877/10000000000 : ℝ)*x 0 + (522305439/2000000000 : ℝ)*x 1 + (2913084659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7081332877/10000000000 : ℝ)^4219 ≤ (63398174584707/100000000000000 : ℝ)^3195 := by
    have hnat : (7081332877 : ℕ)^4219*100000000000000^3195 ≤ 63398174584707^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7081332877 10000000000 63398174584707 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (522305439/2000000000 : ℝ)^4219 ≤ (16982780661441/100000000000000 : ℝ)^3195 := by
    have hnat : (522305439 : ℕ)^4219*100000000000000^3195 ≤ 16982780661441^3195*2000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522305439 2000000000 16982780661441 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2913084659/10000000000 : ℝ)^4219 ≤ (19619044736959/100000000000000 : ℝ)^3195 := by
    have hnat : (2913084659 : ℕ)^4219*100000000000000^3195 ≤ 19619044736959^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2913084659 10000000000 19619044736959 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-7081332877/10000000000 : ℝ), (522305439/2000000000 : ℝ), (2913084659/10000000000 : ℝ)] ![(63398174584707/100000000000000 : ℝ), (16982780661441/100000000000000 : ℝ), (19619044736959/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-7081332877/10000000000 : ℝ)|^4219 ≤ (63398174584707/100000000000000 : ℝ)^3195
        have hw : |(-7081332877/10000000000 : ℝ)|=(7081332877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(522305439/2000000000 : ℝ)|^4219 ≤ (16982780661441/100000000000000 : ℝ)^3195
        have hw : |(522305439/2000000000 : ℝ)|=(522305439/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2913084659/10000000000 : ℝ)|^4219 ≤ (19619044736959/100000000000000 : ℝ)^3195
        have hw : |(2913084659/10000000000 : ℝ)|=(2913084659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1245_s8_9 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2084949083/2500000000 : ℝ)*x 0 + (-282689437/5000000000 : ℝ)*x 1 + (356316607/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2084949083/2500000000 : ℝ)^4219 ≤ (78683868358263/100000000000000 : ℝ)^3195 := by
    have hnat : (2084949083 : ℕ)^4219*100000000000000^3195 ≤ 78683868358263^3195*2500000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084949083 2500000000 78683868358263 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (282689437/5000000000 : ℝ)^4219 ≤ (450291169511/20000000000000 : ℝ)^3195 := by
    have hnat : (282689437 : ℕ)^4219*20000000000000^3195 ≤ 450291169511^3195*5000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282689437 5000000000 450291169511 20000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (356316607/1250000000 : ℝ)^4219 ≤ (19064675785879/100000000000000 : ℝ)^3195 := by
    have hnat : (356316607 : ℕ)^4219*100000000000000^3195 ≤ 19064675785879^3195*1250000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      356316607 1250000000 19064675785879 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2084949083/2500000000 : ℝ), (-282689437/5000000000 : ℝ), (356316607/1250000000 : ℝ)] ![(78683868358263/100000000000000 : ℝ), (450291169511/20000000000000 : ℝ), (19064675785879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2084949083/2500000000 : ℝ)|^4219 ≤ (78683868358263/100000000000000 : ℝ)^3195
        have hw : |(2084949083/2500000000 : ℝ)|=(2084949083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-282689437/5000000000 : ℝ)|^4219 ≤ (450291169511/20000000000000 : ℝ)^3195
        have hw : |(-282689437/5000000000 : ℝ)|=(282689437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(356316607/1250000000 : ℝ)|^4219 ≤ (19064675785879/100000000000000 : ℝ)^3195
        have hw : |(356316607/1250000000 : ℝ)|=(356316607/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1245_s8_10 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1673576769/2000000000 : ℝ)*x 0 + (2749443279/10000000000 : ℝ)*x 1 + (-83112667/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1673576769/2000000000 : ℝ)^4219 ≤ (39516993952343/50000000000000 : ℝ)^3195 := by
    have hnat : (1673576769 : ℕ)^4219*50000000000000^3195 ≤ 39516993952343^3195*2000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1673576769 2000000000 39516993952343 50000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2749443279/10000000000 : ℝ)^4219 ≤ (4544250687303/25000000000000 : ℝ)^3195 := by
    have hnat : (2749443279 : ℕ)^4219*25000000000000^3195 ≤ 4544250687303^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2749443279 10000000000 4544250687303 25000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (83112667/1250000000 : ℝ)^4219 ≤ (348626167629/12500000000000 : ℝ)^3195 := by
    have hnat : (83112667 : ℕ)^4219*12500000000000^3195 ≤ 348626167629^3195*1250000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83112667 1250000000 348626167629 12500000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1673576769/2000000000 : ℝ), (2749443279/10000000000 : ℝ), (-83112667/1250000000 : ℝ)] ![(39516993952343/50000000000000 : ℝ), (4544250687303/25000000000000 : ℝ), (348626167629/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1673576769/2000000000 : ℝ)|^4219 ≤ (39516993952343/50000000000000 : ℝ)^3195
        have hw : |(1673576769/2000000000 : ℝ)|=(1673576769/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2749443279/10000000000 : ℝ)|^4219 ≤ (4544250687303/25000000000000 : ℝ)^3195
        have hw : |(2749443279/10000000000 : ℝ)|=(2749443279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-83112667/1250000000 : ℝ)|^4219 ≤ (348626167629/12500000000000 : ℝ)^3195
        have hw : |(-83112667/1250000000 : ℝ)|=(83112667/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1245_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37871821/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7053/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5741/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11483/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2821/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7053/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5741/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7053/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5741/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7053/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5741/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7053/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5741/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7053/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5741/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7053/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5741/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5741/50000 : ℝ) ^ (8437/2048 : ℝ) ≤ (6707969838354837/50000000000000000000 : ℝ) := by
    have hpowers : (5741/50000 : ℝ)^8437 ≤ (6707969838354837/50000000000000000000 : ℝ)^2048 := by
      have hnat : (5741 : ℕ)^8437*50000000000000000000^2048 ≤ 6707969838354837^2048*50000^8437 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5741 50000 6707969838354837 50000000000000000000 8437 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5741/50000 : ℝ)) (X := (6707969838354837/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8437 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7053/50000 : ℝ) ^ (8437/2048 : ℝ) ≤ (15661365994323977/50000000000000000000 : ℝ) := by
    have hpowers : (7053/50000 : ℝ)^8437 ≤ (15661365994323977/50000000000000000000 : ℝ)^2048 := by
      have hnat : (7053 : ℕ)^8437*50000000000000000000^2048 ≤ 15661365994323977^2048*50000^8437 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7053 50000 15661365994323977 50000000000000000000 8437 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7053/50000 : ℝ)) (X := (15661365994323977/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8437 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006707969838354837/25000000000000000000 : ℝ) ≤ (2500162812928347/2500000000000000 : ℝ) ^ (8437/2048 : ℝ) := by
    have hpowers : (25006707969838354837/25000000000000000000 : ℝ)^2048 ≤ (2500162812928347/2500000000000000 : ℝ)^8437 := by
      have hnat : (25006707969838354837 : ℕ)^2048*2500000000000000^8437 ≤ 2500162812928347^8437*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006707969838354837 25000000000000000000 2500162812928347 2500000000000000 2048 8437 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500162812928347/2500000000000000 : ℝ)) (X := (25006707969838354837/25000000000000000000 : ℝ)) (by norm_num) 8437 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011184667916339407/25000000000000000000 : ℝ) ≤ (2000217160798741/2000000000000000 : ℝ) ^ (8437/2048 : ℝ) := by
    have hpowers : (25011184667916339407/25000000000000000000 : ℝ)^2048 ≤ (2000217160798741/2000000000000000 : ℝ)^8437 := by
      have hnat : (25011184667916339407 : ℕ)^2048*2000000000000000^8437 ≤ 2000217160798741^8437*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011184667916339407 25000000000000000000 2000217160798741 2000000000000000 2048 8437 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000217160798741/2000000000000000 : ℝ)) (X := (25011184667916339407/25000000000000000000 : ℝ)) (by norm_num) 8437 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015661365994323977/25000000000000000000 : ℝ) ≤ (5000760178137011/5000000000000000 : ℝ) ^ (8437/2048 : ℝ) := by
    have hpowers : (25015661365994323977/25000000000000000000 : ℝ)^2048 ≤ (5000760178137011/5000000000000000 : ℝ)^8437 := by
      have hnat : (25015661365994323977 : ℕ)^2048*5000000000000000^8437 ≤ 5000760178137011^8437*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015661365994323977 25000000000000000000 5000760178137011 5000000000000000 2048 8437 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000760178137011/5000000000000000 : ℝ)) (X := (25015661365994323977/25000000000000000000 : ℝ)) (by norm_num) 8437 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6707969838354837/50000000000000000000 : ℝ) ≤ ((6557932456482682631/6560000000000000000 : ℝ)+2*(434552280317/262400000000000 : ℝ)*(5741/50000 : ℝ))^(8437/2048 : ℝ) := by
    rw [show (6557932456482682631/6560000000000000000 : ℝ)+2*(434552280317/262400000000000 : ℝ)*(5741/50000 : ℝ)=(2500162812928347/2500000000000000 : ℝ) by norm_num, show 1+2*(6707969838354837/50000000000000000000 : ℝ)=(25006707969838354837/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15661365994323977/50000000000000000000 : ℝ)+(6707969838354837/50000000000000000000 : ℝ) ≤ ((6557932456482682631/6560000000000000000 : ℝ)+(434552280317/262400000000000 : ℝ)*((7053/50000 : ℝ)+(5741/50000 : ℝ)))^(8437/2048 : ℝ) := by
    rw [show (6557932456482682631/6560000000000000000 : ℝ)+(434552280317/262400000000000 : ℝ)*((7053/50000 : ℝ)+(5741/50000 : ℝ))=(2000217160798741/2000000000000000 : ℝ) by norm_num, show 1+(15661365994323977/50000000000000000000 : ℝ)+(6707969838354837/50000000000000000000 : ℝ)=(25011184667916339407/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15661365994323977/50000000000000000000 : ℝ) ≤ ((6557932456482682631/6560000000000000000 : ℝ)+2*(434552280317/262400000000000 : ℝ)*(7053/50000 : ℝ))^(8437/2048 : ℝ) := by
    rw [show (6557932456482682631/6560000000000000000 : ℝ)+2*(434552280317/262400000000000 : ℝ)*(7053/50000 : ℝ)=(5000760178137011/5000000000000000 : ℝ) by norm_num, show 1+2*(15661365994323977/50000000000000000000 : ℝ)=(25015661365994323977/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6557932456482682631/6560000000000000000 : ℝ)*(X 1 0+X 2 0)+(434552280317/262400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8437/2048 : ℝ)) (lo := (5741/50000 : ℝ)) (hi := (7053/50000 : ℝ)) (c := (6557932456482682631/6560000000000000000 : ℝ)) (alpha := (434552280317/262400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6557932456482682631/6560000000000000000 : ℝ)*(X 0 1+X 2 1)+(434552280317/262400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8437/2048 : ℝ)) (lo := (5741/50000 : ℝ)) (hi := (7053/50000 : ℝ)) (c := (6557932456482682631/6560000000000000000 : ℝ)) (alpha := (434552280317/262400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6557932456482682631/6560000000000000000 : ℝ)*(X 0 2+X 1 2)+(434552280317/262400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8437/2048 : ℝ)) (lo := (5741/50000 : ℝ)) (hi := (7053/50000 : ℝ)) (c := (6557932456482682631/6560000000000000000 : ℝ)) (alpha := (434552280317/262400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2118585273/10000000000 : ℝ)*X 0 0+(5391098717/10000000000 : ℝ)*X 0 1+(1316823777/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344282257/10000000000 : ℝ)*X 1 0+(-1090677797/5000000000 : ℝ)*X 1 1+(1316823773/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672141119/5000000000 : ℝ)*X 2 0+(1316823777/2500000000 : ℝ)*X 2 1+(-1090677799/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4350363957/10000000000 : ℝ)*X 0 0+(4226481883/10000000000 : ℝ)*X 0 1+(4477771771/10000000000 : ℝ)*X 0 2+(4350363957/10000000000 : ℝ)*X 1 0+(4226481883/10000000000 : ℝ)*X 1 1+(4477771771/10000000000 : ℝ)*X 1 2+(4350363957/10000000000 : ℝ)*X 2 0+(4226481883/10000000000 : ℝ)*X 2 1+(4477771771/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2118589477/10000000000 : ℝ)*X 0 0+(5267607231/10000000000 : ℝ)*X 0 1+(2695392893/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656343193/5000000000 : ℝ)*X 1 0+(-2057865499/10000000000 : ℝ)*X 1 1+(5390785629/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656343021/5000000000 : ℝ)*X 2 0+(539078617/1000000000 : ℝ)*X 2 1+(-2057865227/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4350373373/10000000000 : ℝ)*X 0 0+(2238569167/5000000000 : ℝ)*X 0 1+(4227117621/10000000000 : ℝ)*X 0 2+(4350373373/10000000000 : ℝ)*X 1 0+(2238569167/5000000000 : ℝ)*X 1 1+(4227117621/10000000000 : ℝ)*X 1 2+(4350373373/10000000000 : ℝ)*X 2 0+(2238569167/5000000000 : ℝ)*X 2 1+(4227117621/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-7081332877/10000000000 : ℝ)*X 0 0+(522305439/2000000000 : ℝ)*X 0 1+(2913084659/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s8_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2084949083/2500000000 : ℝ)*X 1 0+(-282689437/5000000000 : ℝ)*X 1 1+(356316607/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s8_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1673576769/2000000000 : ℝ)*X 2 0+(2749443279/10000000000 : ℝ)*X 2 1+(-83112667/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s8_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (69396177799672032056550813/20500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (680778693/100000000000000 : ℝ)*(base19) + (152121423/25000000000000 : ℝ)*(base23) + (23288463/100000000000000 : ℝ)*(lower2) + (17917027/20000000000000 : ℝ)*(upper3) + (45790431/100000000000000 : ℝ)*(upper5) + (753552080894743/12500000000000 : ℝ)*(major0) + (753552080894743/12500000000000 : ℝ)*(major1) + (1205683329431589/20000000000000 : ℝ)*(major2) + (403866423767333/5000000000000 : ℝ)*(sp0) + (807734558405479/10000000000000 : ℝ)*(sp1) + (8077345656347791/100000000000000 : ℝ)*(sp2) + (3979476804106841/100000000000000 : ℝ)*(sp3) + (2223685853/12500000000000 : ℝ)*(sp4) + (5056268119/50000000000000 : ℝ)*(sp7) + (1989743458321539/50000000000000 : ℝ)*(f.failure) + (8077346264833483/100000000000000 : ℝ)*(f.sum) + (24365691566893/26240000000000000000000000000 : ℝ)*base65 + (98742122530787229/41000000000000000000000000000000 : ℝ)*base67 + (858934579619329341/131200000000000000000000000000000 : ℝ)*base70 + (297636690268787229/41000000000000000000000000000000 : ℝ)*base71 + (114018359973587/26240000000000000000000000000 : ℝ)*base74 + (2165164053417470659/131200000000000000000000000000000 : ℝ)*base75 + (177439435965583833/82000000000000000000000000000000 : ℝ)*base77 + (127203573662416167/82000000000000000000000000000000 : ℝ)*base80 + (8445688279709/1640000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (14547481/1250000000000000000000 : ℝ)*base90 + (14547481/1250000000000000000000 : ℝ)*base92 + (27047481/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (52543162692519081630358101/32800000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1767379/3125000000000 : ℝ)*(upper1) + (72919499/50000000000000 : ℝ)*(lower2) + (1211799990215043/20000000000000 : ℝ)*(major0) + (1211799990215043/20000000000000 : ℝ)*(major1) + (1211799990215043/20000000000000 : ℝ)*(major2) + (32628067/500000000000 : ℝ)*(sp0) + (5278708683/25000000000000 : ℝ)*(sp2) + (1014789659176313/12500000000000 : ℝ)*(sp4) + (1623664754343991/20000000000000 : ℝ)*(sp5) + (4059150744054979/50000000000000 : ℝ)*(sp6) + (1999837805223049/50000000000000 : ℝ)*(sp7) + (109820719/25000000000000 : ℝ)*(sp8) + (466586829/100000000000000 : ℝ)*(sp9) + (1635362089/100000000000000 : ℝ)*(sp10) + (1999837805223049/50000000000000 : ℝ)*(f.failure) + (253697632447087/3125000000000 : ℝ)*(f.sum) + (574544193137/104960000000000000000000000 : ℝ)*base66 + (2140767048615593133/131200000000000000000000000000000 : ℝ)*base67 + (1506108078663593133/131200000000000000000000000000000 : ℝ)*base69 + (5609111550027606867/131200000000000000000000000000000 : ℝ)*base72 + (7029793838647/2624000000000000000000000000 : ℝ)*base73 + (193407773604393133/131200000000000000000000000000000 : ℝ)*base75 + (1889925580343593133/131200000000000000000000000000000 : ℝ)*base77 + (2770704601181993133/131200000000000000000000000000000 : ℝ)*base79 + (2348462091383/2624000000000000000000000000 : ℝ)*base81 + (1/25000000000000 : ℝ)*base84 + (1/20000000000000 : ℝ)*base88 + (10697771/1250000000000000000000 : ℝ)*base90 + (10697771/1250000000000000000000 : ℝ)*base92 + (10697771/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1245_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37871821/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7053/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5741/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11483/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2821/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1245_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1245_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37871821/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14131/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5729/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11483/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2821/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1245_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1245_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1245_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37871821/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14131/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5729/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11483/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2821/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1245_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
