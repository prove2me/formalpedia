-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1750_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:19:03.00568+00:00
-- url     : https://prove2.me/submissions/259fb746-da72-474c-b953-66fa47efd0e1

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
theorem support_rectangle_w1750_s0_0 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1177168627/10000000000 : ℝ)*x 0 + (5630339491/10000000000 : ℝ)*x 1 + (4977902583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1177168627/10000000000 : ℝ)^5775 ≤ (7422893349503/100000000000000 : ℝ)^4751 := by
    have hnat : (1177168627 : ℕ)^5775*100000000000000^4751 ≤ 7422893349503^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1177168627 10000000000 7422893349503 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5630339491/10000000000 : ℝ)^5775 ≤ (9949388864431/20000000000000 : ℝ)^4751 := by
    have hnat : (5630339491 : ℕ)^5775*20000000000000^4751 ≤ 9949388864431^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5630339491 10000000000 9949388864431 20000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4977902583/10000000000 : ℝ)^5775 ≤ (42830162317537/100000000000000 : ℝ)^4751 := by
    have hnat : (4977902583 : ℕ)^5775*100000000000000^4751 ≤ 42830162317537^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4977902583 10000000000 42830162317537 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1177168627/10000000000 : ℝ), (5630339491/10000000000 : ℝ), (4977902583/10000000000 : ℝ)] ![(7422893349503/100000000000000 : ℝ), (9949388864431/20000000000000 : ℝ), (42830162317537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1177168627/10000000000 : ℝ)|^5775 ≤ (7422893349503/100000000000000 : ℝ)^4751
        have hw : |(-1177168627/10000000000 : ℝ)|=(1177168627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5630339491/10000000000 : ℝ)|^5775 ≤ (9949388864431/20000000000000 : ℝ)^4751
        have hw : |(5630339491/10000000000 : ℝ)|=(5630339491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4977902583/10000000000 : ℝ)|^5775 ≤ (42830162317537/100000000000000 : ℝ)^4751
        have hw : |(4977902583/10000000000 : ℝ)|=(4977902583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1750_s0_1 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1074359047/2000000000 : ℝ)*x 0 + (-381795083/2500000000 : ℝ)*x 1 + (4977903011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074359047/2000000000 : ℝ)^5775 ≤ (2349206181707/5000000000000 : ℝ)^4751 := by
    have hnat : (1074359047 : ℕ)^5775*5000000000000^4751 ≤ 2349206181707^4751*2000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074359047 2000000000 2349206181707 5000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (381795083/2500000000 : ℝ)^5775 ≤ (2546427390449/25000000000000 : ℝ)^4751 := by
    have hnat : (381795083 : ℕ)^5775*25000000000000^4751 ≤ 2546427390449^4751*2500000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      381795083 2500000000 2546427390449 25000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4977903011/10000000000 : ℝ)^5775 ≤ (5353770849223/12500000000000 : ℝ)^4751 := by
    have hnat : (4977903011 : ℕ)^5775*12500000000000^4751 ≤ 5353770849223^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4977903011 10000000000 5353770849223 12500000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074359047/2000000000 : ℝ), (-381795083/2500000000 : ℝ), (4977903011/10000000000 : ℝ)] ![(2349206181707/5000000000000 : ℝ), (2546427390449/25000000000000 : ℝ), (5353770849223/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074359047/2000000000 : ℝ)|^5775 ≤ (2349206181707/5000000000000 : ℝ)^4751
        have hw : |(1074359047/2000000000 : ℝ)|=(1074359047/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-381795083/2500000000 : ℝ)|^5775 ≤ (2546427390449/25000000000000 : ℝ)^4751
        have hw : |(-381795083/2500000000 : ℝ)|=(381795083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4977903011/10000000000 : ℝ)|^5775 ≤ (5353770849223/12500000000000 : ℝ)^4751
        have hw : |(4977903011/10000000000 : ℝ)|=(4977903011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1750_s0_2 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (67147461/125000000 : ℝ)*x 0 + (622237759/1250000000 : ℝ)*x 1 + (-305435877/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67147461/125000000 : ℝ)^5775 ≤ (46984141123123/100000000000000 : ℝ)^4751 := by
    have hnat : (67147461 : ℕ)^5775*100000000000000^4751 ≤ 46984141123123^4751*125000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67147461 125000000 46984141123123 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (622237759/1250000000 : ℝ)^5775 ≤ (42830156973233/100000000000000 : ℝ)^4751 := by
    have hnat : (622237759 : ℕ)^5775*100000000000000^4751 ≤ 42830156973233^4751*1250000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      622237759 1250000000 42830156973233 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (305435877/2000000000 : ℝ)^5775 ≤ (10185701884331/100000000000000 : ℝ)^4751 := by
    have hnat : (305435877 : ℕ)^5775*100000000000000^4751 ≤ 10185701884331^4751*2000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      305435877 2000000000 10185701884331 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(67147461/125000000 : ℝ), (622237759/1250000000 : ℝ), (-305435877/2000000000 : ℝ)] ![(46984141123123/100000000000000 : ℝ), (42830156973233/100000000000000 : ℝ), (10185701884331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(67147461/125000000 : ℝ)|^5775 ≤ (46984141123123/100000000000000 : ℝ)^4751
        have hw : |(67147461/125000000 : ℝ)|=(67147461/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(622237759/1250000000 : ℝ)|^5775 ≤ (42830156973233/100000000000000 : ℝ)^4751
        have hw : |(622237759/1250000000 : ℝ)|=(622237759/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-305435877/2000000000 : ℝ)|^5775 ≤ (10185701884331/100000000000000 : ℝ)^4751
        have hw : |(-305435877/2000000000 : ℝ)|=(305435877/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1750_s0_3 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1988771021/5000000000 : ℝ)*x 0 + (745974961/2500000000 : ℝ)*x 1 + (5127535177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1988771021/5000000000 : ℝ)^5775 ≤ (163037807443/500000000000 : ℝ)^4751 := by
    have hnat : (1988771021 : ℕ)^5775*500000000000^4751 ≤ 163037807443^4751*5000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1988771021 5000000000 163037807443 500000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (745974961/2500000000 : ℝ)^5775 ≤ (22992310372791/100000000000000 : ℝ)^4751 := by
    have hnat : (745974961 : ℕ)^5775*100000000000000^4751 ≤ 22992310372791^4751*2500000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      745974961 2500000000 22992310372791 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5127535177/10000000000 : ℝ)^5775 ≤ (8880025624413/20000000000000 : ℝ)^4751 := by
    have hnat : (5127535177 : ℕ)^5775*20000000000000^4751 ≤ 8880025624413^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5127535177 10000000000 8880025624413 20000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1988771021/5000000000 : ℝ), (745974961/2500000000 : ℝ), (5127535177/10000000000 : ℝ)] ![(163037807443/500000000000 : ℝ), (22992310372791/100000000000000 : ℝ), (8880025624413/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1988771021/5000000000 : ℝ)|^5775 ≤ (163037807443/500000000000 : ℝ)^4751
        have hw : |(1988771021/5000000000 : ℝ)|=(1988771021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(745974961/2500000000 : ℝ)|^5775 ≤ (22992310372791/100000000000000 : ℝ)^4751
        have hw : |(745974961/2500000000 : ℝ)|=(745974961/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5127535177/10000000000 : ℝ)|^5775 ≤ (8880025624413/20000000000000 : ℝ)^4751
        have hw : |(5127535177/10000000000 : ℝ)|=(5127535177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1750_s0_4 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1178532751/10000000000 : ℝ)*x 0 + (4994523639/10000000000 : ℝ)*x 1 + (5613168707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1178532751/10000000000 : ℝ)^5775 ≤ (7433350408673/100000000000000 : ℝ)^4751 := by
    have hnat : (1178532751 : ℕ)^5775*100000000000000^4751 ≤ 7433350408673^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1178532751 10000000000 7433350408673 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4994523639/10000000000 : ℝ)^5775 ≤ (21502028240501/50000000000000 : ℝ)^4751 := by
    have hnat : (4994523639 : ℕ)^5775*50000000000000^4751 ≤ 21502028240501^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4994523639 10000000000 21502028240501 50000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5613168707/10000000000 : ℝ)^5775 ≤ (49562593091971/100000000000000 : ℝ)^4751 := by
    have hnat : (5613168707 : ℕ)^5775*100000000000000^4751 ≤ 49562593091971^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5613168707 10000000000 49562593091971 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1178532751/10000000000 : ℝ), (4994523639/10000000000 : ℝ), (5613168707/10000000000 : ℝ)] ![(7433350408673/100000000000000 : ℝ), (21502028240501/50000000000000 : ℝ), (49562593091971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1178532751/10000000000 : ℝ)|^5775 ≤ (7433350408673/100000000000000 : ℝ)^4751
        have hw : |(-1178532751/10000000000 : ℝ)|=(1178532751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4994523639/10000000000 : ℝ)|^5775 ≤ (21502028240501/50000000000000 : ℝ)^4751
        have hw : |(4994523639/10000000000 : ℝ)|=(4994523639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5613168707/10000000000 : ℝ)|^5775 ≤ (49562593091971/100000000000000 : ℝ)^4751
        have hw : |(5613168707/10000000000 : ℝ)|=(5613168707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1750_s0_5 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2598851837/5000000000 : ℝ)*x 0 + (-891913367/10000000000 : ℝ)*x 1 + (2806584403/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2598851837/5000000000 : ℝ)^5775 ≤ (2821235725473/6250000000000 : ℝ)^4751 := by
    have hnat : (2598851837 : ℕ)^5775*6250000000000^4751 ≤ 2821235725473^4751*5000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598851837 5000000000 2821235725473 6250000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (891913367/10000000000 : ℝ)^5775 ≤ (5297634223431/100000000000000 : ℝ)^4751 := by
    have hnat : (891913367 : ℕ)^5775*100000000000000^4751 ≤ 5297634223431^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      891913367 10000000000 5297634223431 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2806584403/5000000000 : ℝ)^5775 ≤ (49562594154517/100000000000000 : ℝ)^4751 := by
    have hnat : (2806584403 : ℕ)^5775*100000000000000^4751 ≤ 49562594154517^4751*5000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2806584403 5000000000 49562594154517 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2598851837/5000000000 : ℝ), (-891913367/10000000000 : ℝ), (2806584403/5000000000 : ℝ)] ![(2821235725473/6250000000000 : ℝ), (5297634223431/100000000000000 : ℝ), (49562594154517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2598851837/5000000000 : ℝ)|^5775 ≤ (2821235725473/6250000000000 : ℝ)^4751
        have hw : |(2598851837/5000000000 : ℝ)|=(2598851837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-891913367/10000000000 : ℝ)|^5775 ≤ (5297634223431/100000000000000 : ℝ)^4751
        have hw : |(-891913367/10000000000 : ℝ)|=(891913367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2806584403/5000000000 : ℝ)|^5775 ≤ (49562594154517/100000000000000 : ℝ)^4751
        have hw : |(2806584403/5000000000 : ℝ)|=(2806584403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1750_s0_6 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5197703283/10000000000 : ℝ)*x 0 + (1122633761/2000000000 : ℝ)*x 1 + (-44595697/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5197703283/10000000000 : ℝ)^5775 ≤ (1805590699201/4000000000000 : ℝ)^4751 := by
    have hnat : (5197703283 : ℕ)^5775*4000000000000^4751 ≤ 1805590699201^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5197703283 10000000000 1805590699201 4000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1122633761/2000000000 : ℝ)^5775 ≤ (9912518828757/20000000000000 : ℝ)^4751 := by
    have hnat : (1122633761 : ℕ)^5775*20000000000000^4751 ≤ 9912518828757^4751*2000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122633761 2000000000 9912518828757 20000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (44595697/500000000 : ℝ)^5775 ≤ (5297638360387/100000000000000 : ℝ)^4751 := by
    have hnat : (44595697 : ℕ)^5775*100000000000000^4751 ≤ 5297638360387^4751*500000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44595697 500000000 5297638360387 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5197703283/10000000000 : ℝ), (1122633761/2000000000 : ℝ), (-44595697/500000000 : ℝ)] ![(1805590699201/4000000000000 : ℝ), (9912518828757/20000000000000 : ℝ), (5297638360387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5197703283/10000000000 : ℝ)|^5775 ≤ (1805590699201/4000000000000 : ℝ)^4751
        have hw : |(5197703283/10000000000 : ℝ)|=(5197703283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1122633761/2000000000 : ℝ)|^5775 ≤ (9912518828757/20000000000000 : ℝ)^4751
        have hw : |(1122633761/2000000000 : ℝ)|=(1122633761/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-44595697/500000000 : ℝ)|^5775 ≤ (5297638360387/100000000000000 : ℝ)^4751
        have hw : |(-44595697/500000000 : ℝ)|=(44595697/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1750_s0_7 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (398202459/1000000000 : ℝ)*x 0 + (5072924031/10000000000 : ℝ)*x 1 + (760078887/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (398202459/1000000000 : ℝ)^5775 ≤ (32652234803131/100000000000000 : ℝ)^4751 := by
    have hnat : (398202459 : ℕ)^5775*100000000000000^4751 ≤ 32652234803131^4751*1000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398202459 1000000000 32652234803131 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5072924031/10000000000 : ℝ)^5775 ≤ (21912990186113/50000000000000 : ℝ)^4751 := by
    have hnat : (5072924031 : ℕ)^5775*50000000000000^4751 ≤ 21912990186113^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5072924031 10000000000 21912990186113 50000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (760078887/2500000000 : ℝ)^5775 ≤ (294022310063/1250000000000 : ℝ)^4751 := by
    have hnat : (760078887 : ℕ)^5775*1250000000000^4751 ≤ 294022310063^4751*2500000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      760078887 2500000000 294022310063 1250000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(398202459/1000000000 : ℝ), (5072924031/10000000000 : ℝ), (760078887/2500000000 : ℝ)] ![(32652234803131/100000000000000 : ℝ), (21912990186113/50000000000000 : ℝ), (294022310063/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(398202459/1000000000 : ℝ)|^5775 ≤ (32652234803131/100000000000000 : ℝ)^4751
        have hw : |(398202459/1000000000 : ℝ)|=(398202459/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5072924031/10000000000 : ℝ)|^5775 ≤ (21912990186113/50000000000000 : ℝ)^4751
        have hw : |(5072924031/10000000000 : ℝ)|=(5072924031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(760078887/2500000000 : ℝ)|^5775 ≤ (294022310063/1250000000000 : ℝ)^4751
        have hw : |(760078887/2500000000 : ℝ)|=(760078887/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1750_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (214278987/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (269/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5207/25000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (5759/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5759 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5759*1^1024 ≤ 0^1024*1^5759 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5759 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5759 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5759/1024 : ℝ) ≤ (578064187385093753/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5759 ≤ (578064187385093753/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5759*100000000000000000000^1024 ≤ 578064187385093753^1024*5^5759 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 578064187385093753 100000000000000000000 5759 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (578064187385093753/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5759 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5759/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5759 := by
      have hnat : (1 : ℕ)^1024*1^5759 ≤ 1^5759*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5759 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5759 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100578064187385093753/100000000000000000000 : ℝ) ≤ (2002050828157357/2000000000000000 : ℝ) ^ (5759/1024 : ℝ) := by
    have hpowers : (100578064187385093753/100000000000000000000 : ℝ)^1024 ≤ (2002050828157357/2000000000000000 : ℝ)^5759 := by
      have hnat : (100578064187385093753 : ℕ)^1024*2000000000000000^5759 ≤ 2002050828157357^5759*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100578064187385093753 100000000000000000000 2002050828157357 2000000000000000 1024 5759 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2002050828157357/2000000000000000 : ℝ)) (X := (100578064187385093753/100000000000000000000 : ℝ)) (by norm_num) 5759 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50578064187385093753/50000000000000000000 : ℝ) ≤ (1002050828157357/1000000000000000 : ℝ) ^ (5759/1024 : ℝ) := by
    have hpowers : (50578064187385093753/50000000000000000000 : ℝ)^1024 ≤ (1002050828157357/1000000000000000 : ℝ)^5759 := by
      have hnat : (50578064187385093753 : ℕ)^1024*1000000000000000^5759 ≤ 1002050828157357^5759*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50578064187385093753 50000000000000000000 1002050828157357 1000000000000000 1024 5759 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1002050828157357/1000000000000000 : ℝ)) (X := (50578064187385093753/50000000000000000000 : ℝ)) (by norm_num) 5759 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(2050828157357/800000000000000 : ℝ)*(0 : ℝ))^(5759/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(2050828157357/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(578064187385093753/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(2050828157357/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5759/1024 : ℝ) := by
    rw [show (1 : ℝ)+(2050828157357/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2002050828157357/2000000000000000 : ℝ) by norm_num, show 1+(578064187385093753/100000000000000000000 : ℝ)+(0 : ℝ)=(100578064187385093753/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(578064187385093753/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(2050828157357/800000000000000 : ℝ)*(2/5 : ℝ))^(5759/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(2050828157357/800000000000000 : ℝ)*(2/5 : ℝ)=(1002050828157357/1000000000000000 : ℝ) by norm_num, show 1+2*(578064187385093753/100000000000000000000 : ℝ)=(50578064187385093753/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(2050828157357/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5759/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2050828157357/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(2050828157357/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5759/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2050828157357/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(2050828157357/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5759/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2050828157357/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1177168627/10000000000 : ℝ)*X 0 0+(5630339491/10000000000 : ℝ)*X 0 1+(4977902583/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1074359047/2000000000 : ℝ)*X 1 0+(-381795083/2500000000 : ℝ)*X 1 1+(4977903011/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((67147461/125000000 : ℝ)*X 2 0+(622237759/1250000000 : ℝ)*X 2 1+(-305435877/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1988771021/5000000000 : ℝ)*X 0 0+(745974961/2500000000 : ℝ)*X 0 1+(5127535177/10000000000 : ℝ)*X 0 2+(1988771021/5000000000 : ℝ)*X 1 0+(745974961/2500000000 : ℝ)*X 1 1+(5127535177/10000000000 : ℝ)*X 1 2+(1988771021/5000000000 : ℝ)*X 2 0+(745974961/2500000000 : ℝ)*X 2 1+(5127535177/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1178532751/10000000000 : ℝ)*X 0 0+(4994523639/10000000000 : ℝ)*X 0 1+(5613168707/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2598851837/5000000000 : ℝ)*X 1 0+(-891913367/10000000000 : ℝ)*X 1 1+(2806584403/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5197703283/10000000000 : ℝ)*X 2 0+(1122633761/2000000000 : ℝ)*X 2 1+(-44595697/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((398202459/1000000000 : ℝ)*X 0 0+(5072924031/10000000000 : ℝ)*X 0 1+(760078887/2500000000 : ℝ)*X 0 2+(398202459/1000000000 : ℝ)*X 1 0+(5072924031/10000000000 : ℝ)*X 1 1+(760078887/2500000000 : ℝ)*X 1 2+(398202459/1000000000 : ℝ)*X 2 0+(5072924031/10000000000 : ℝ)*X 2 1+(760078887/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (146468512181647271652501/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (613992581/50000000000000 : ℝ)*(base19) + (1597024627/100000000000000 : ℝ)*(base23) + (2821/50000000000 : ℝ)*(base24) + (1017253/2000000000000 : ℝ)*(upper4) + (426127541/100000000000000 : ℝ)*(upper5) + (499808193507331/50000000000000 : ℝ)*(major0) + (499808193507331/50000000000000 : ℝ)*(major1) + (499808193507331/50000000000000 : ℝ)*(major2) + (766359748389577/50000000000000 : ℝ)*(sp0) + (766364504641741/50000000000000 : ℝ)*(sp1) + (766364317301009/50000000000000 : ℝ)*(sp2) + (466500256499253/100000000000000 : ℝ)*(sp3) + (1074048949/10000000000000 : ℝ)*(sp4) + (2036147231/100000000000000 : ℝ)*(sp7) + (116625573161621/25000000000000 : ℝ)*(f.failure) + (306546047453729/20000000000000 : ℝ)*(f.sum) + (67050526275833/20000000000000000000000000000 : ℝ)*base66 + (165939824404167/40000000000000000000000000000 : ℝ)*base67 + (287897217844167/40000000000000000000000000000 : ℝ)*base69 + (14406726355833/40000000000000000000000000000 : ℝ)*base72 + (43153172295833/20000000000000000000000000000 : ℝ)*base74 + (368184414244167/40000000000000000000000000000 : ℝ)*base75 + (52898549155833/40000000000000000000000000000 : ℝ)*base78 + (73650438475833/40000000000000000000000000000 : ℝ)*base80 + (20742372304167/20000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (14842073/2500000000000000000000 : ℝ)*base90 + (14842073/2500000000000000000000 : ℝ)*base92 + (14842073/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (33428506858207725404247/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (773046437/50000000000000 : ℝ)*(base19) + (287820203/20000000000000 : ℝ)*(base23) + (1354853/5000000000000 : ℝ)*(upper2) + (10646043/4000000000000 : ℝ)*(upper3) + (1892707/800000000000 : ℝ)*(upper5) + (263551719072257/25000000000000 : ℝ)*(major0) + (263551719072257/25000000000000 : ℝ)*(major1) + (263551719072257/25000000000000 : ℝ)*(major2) + (6738856053/100000000000000 : ℝ)*(sp1) + (140459053/2500000000000 : ℝ)*(sp2) + (1616434875608593/100000000000000 : ℝ)*(sp4) + (808213295329833/50000000000000 : ℝ)*(sp5) + (1616427818145457/100000000000000 : ℝ)*(sp6) + (491978654112747/100000000000000 : ℝ)*(sp7) + (491978654112747/100000000000000 : ℝ)*(f.failure) + (1616434875608593/100000000000000 : ℝ)*(f.sum) + (26252344725251/10000000000000000000000000000 : ℝ)*base66 + (43258212535251/20000000000000000000000000000 : ℝ)*base68 + (13397057004749/20000000000000000000000000000 : ℝ)*base69 + (64645467764749/20000000000000000000000000000 : ℝ)*base71 + (8121332245251/10000000000000000000000000000 : ℝ)*base74 + (52002045555251/20000000000000000000000000000 : ℝ)*base76 + (47875455924749/20000000000000000000000000000 : ℝ)*base77 + (190158755504749/20000000000000000000000000000 : ℝ)*base79 + (10205386615251/10000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (10947289/10000000000000000000000 : ℝ)*base89 + (10947289/10000000000000000000000 : ℝ)*base91 + (10947289/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1750_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (214278987/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (269/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5207/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1750_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1750_s1_0 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1221116757/10000000000 : ℝ)*x 0 + (5500351201/10000000000 : ℝ)*x 1 + (1269624667/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1221116757/10000000000 : ℝ)^5775 ≤ (121267027527/1562500000000 : ℝ)^4751 := by
    have hnat : (1221116757 : ℕ)^5775*1562500000000^4751 ≤ 121267027527^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1221116757 10000000000 121267027527 1562500000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5500351201/10000000000 : ℝ)^5775 ≤ (967087647287/2000000000000 : ℝ)^4751 := by
    have hnat : (5500351201 : ℕ)^5775*2000000000000^4751 ≤ 967087647287^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5500351201 10000000000 967087647287 2000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1269624667/2500000000 : ℝ)^5775 ≤ (1755381114299/4000000000000 : ℝ)^4751 := by
    have hnat : (1269624667 : ℕ)^5775*4000000000000^4751 ≤ 1755381114299^4751*2500000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1269624667 2500000000 1755381114299 4000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1221116757/10000000000 : ℝ), (5500351201/10000000000 : ℝ), (1269624667/2500000000 : ℝ)] ![(121267027527/1562500000000 : ℝ), (967087647287/2000000000000 : ℝ), (1755381114299/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1221116757/10000000000 : ℝ)|^5775 ≤ (121267027527/1562500000000 : ℝ)^4751
        have hw : |(-1221116757/10000000000 : ℝ)|=(1221116757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5500351201/10000000000 : ℝ)|^5775 ≤ (967087647287/2000000000000 : ℝ)^4751
        have hw : |(5500351201/10000000000 : ℝ)|=(5500351201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1269624667/2500000000 : ℝ)|^5775 ≤ (1755381114299/4000000000000 : ℝ)^4751
        have hw : |(1269624667/2500000000 : ℝ)|=(1269624667/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1750_s1_1 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2668604083/5000000000 : ℝ)*x 0 + (-720966007/5000000000 : ℝ)*x 1 + (5078498661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2668604083/5000000000 : ℝ)^5775 ≤ (9323332664167/20000000000000 : ℝ)^4751 := by
    have hnat : (2668604083 : ℕ)^5775*20000000000000^4751 ≤ 9323332664167^4751*5000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2668604083 5000000000 9323332664167 20000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (720966007/5000000000 : ℝ)^5775 ≤ (4749404438123/50000000000000 : ℝ)^4751 := by
    have hnat : (720966007 : ℕ)^5775*50000000000000^4751 ≤ 4749404438123^4751*5000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      720966007 5000000000 4749404438123 50000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5078498661/10000000000 : ℝ)^5775 ≤ (43884527783949/100000000000000 : ℝ)^4751 := by
    have hnat : (5078498661 : ℕ)^5775*100000000000000^4751 ≤ 43884527783949^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5078498661 10000000000 43884527783949 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2668604083/5000000000 : ℝ), (-720966007/5000000000 : ℝ), (5078498661/10000000000 : ℝ)] ![(9323332664167/20000000000000 : ℝ), (4749404438123/50000000000000 : ℝ), (43884527783949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2668604083/5000000000 : ℝ)|^5775 ≤ (9323332664167/20000000000000 : ℝ)^4751
        have hw : |(2668604083/5000000000 : ℝ)|=(2668604083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-720966007/5000000000 : ℝ)|^5775 ≤ (4749404438123/50000000000000 : ℝ)^4751
        have hw : |(-720966007/5000000000 : ℝ)|=(720966007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5078498661/10000000000 : ℝ)|^5775 ≤ (43884527783949/100000000000000 : ℝ)^4751
        have hw : |(5078498661/10000000000 : ℝ)|=(5078498661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1750_s1_2 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2668603963/5000000000 : ℝ)*x 0 + (5078498851/10000000000 : ℝ)*x 1 + (-360483021/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2668603963/5000000000 : ℝ)^5775 ≤ (46616660772801/100000000000000 : ℝ)^4751 := by
    have hnat : (2668603963 : ℕ)^5775*100000000000000^4751 ≤ 46616660772801^4751*5000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2668603963 5000000000 46616660772801 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5078498851/10000000000 : ℝ)^5775 ≤ (5485566222457/12500000000000 : ℝ)^4751 := by
    have hnat : (5078498851 : ℕ)^5775*12500000000000^4751 ≤ 5485566222457^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5078498851 10000000000 5485566222457 12500000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (360483021/2500000000 : ℝ)^5775 ≤ (9498809436763/100000000000000 : ℝ)^4751 := by
    have hnat : (360483021 : ℕ)^5775*100000000000000^4751 ≤ 9498809436763^4751*2500000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      360483021 2500000000 9498809436763 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2668603963/5000000000 : ℝ), (5078498851/10000000000 : ℝ), (-360483021/2500000000 : ℝ)] ![(46616660772801/100000000000000 : ℝ), (5485566222457/12500000000000 : ℝ), (9498809436763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2668603963/5000000000 : ℝ)|^5775 ≤ (46616660772801/100000000000000 : ℝ)^4751
        have hw : |(2668603963/5000000000 : ℝ)|=(2668603963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5078498851/10000000000 : ℝ)|^5775 ≤ (5485566222457/12500000000000 : ℝ)^4751
        have hw : |(5078498851/10000000000 : ℝ)|=(5078498851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-360483021/2500000000 : ℝ)|^5775 ≤ (9498809436763/100000000000000 : ℝ)^4751
        have hw : |(-360483021/2500000000 : ℝ)|=(360483021/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1750_s1_3 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (804003739/2000000000 : ℝ)*x 0 + (671899211/2000000000 : ℝ)*x 1 + (189820987/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (804003739/2000000000 : ℝ)^5775 ≤ (1651566023931/5000000000000 : ℝ)^4751 := by
    have hnat : (804003739 : ℕ)^5775*5000000000000^4751 ≤ 1651566023931^4751*2000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      804003739 2000000000 1651566023931 5000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (671899211/2000000000 : ℝ)^5775 ≤ (26556467646749/100000000000000 : ℝ)^4751 := by
    have hnat : (671899211 : ℕ)^5775*100000000000000^4751 ≤ 26556467646749^4751*2000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671899211 2000000000 26556467646749 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (189820987/400000000 : ℝ)^5775 ≤ (10103052962751/25000000000000 : ℝ)^4751 := by
    have hnat : (189820987 : ℕ)^5775*25000000000000^4751 ≤ 10103052962751^4751*400000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      189820987 400000000 10103052962751 25000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(804003739/2000000000 : ℝ), (671899211/2000000000 : ℝ), (189820987/400000000 : ℝ)] ![(1651566023931/5000000000000 : ℝ), (26556467646749/100000000000000 : ℝ), (10103052962751/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(804003739/2000000000 : ℝ)|^5775 ≤ (1651566023931/5000000000000 : ℝ)^4751
        have hw : |(804003739/2000000000 : ℝ)|=(804003739/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(671899211/2000000000 : ℝ)|^5775 ≤ (26556467646749/100000000000000 : ℝ)^4751
        have hw : |(671899211/2000000000 : ℝ)|=(671899211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(189820987/400000000 : ℝ)|^5775 ≤ (10103052962751/25000000000000 : ℝ)^4751
        have hw : |(189820987/400000000 : ℝ)|=(189820987/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1750_s1_4 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1221483333/10000000000 : ℝ)*x 0 + (635682273/1250000000 : ℝ)*x 1 + (219729733/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1221483333/10000000000 : ℝ)^5775 ≤ (155278437491/2000000000000 : ℝ)^4751 := by
    have hnat : (1221483333 : ℕ)^5775*2000000000000^4751 ≤ 155278437491^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1221483333 10000000000 155278437491 2000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (635682273/1250000000 : ℝ)^5775 ≤ (43957639441451/100000000000000 : ℝ)^4751 := by
    have hnat : (635682273 : ℕ)^5775*100000000000000^4751 ≤ 43957639441451^4751*1250000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      635682273 1250000000 43957639441451 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (219729733/400000000 : ℝ)^5775 ≤ (48278438670821/100000000000000 : ℝ)^4751 := by
    have hnat : (219729733 : ℕ)^5775*100000000000000^4751 ≤ 48278438670821^4751*400000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219729733 400000000 48278438670821 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1221483333/10000000000 : ℝ), (635682273/1250000000 : ℝ), (219729733/400000000 : ℝ)] ![(155278437491/2000000000000 : ℝ), (43957639441451/100000000000000 : ℝ), (48278438670821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1221483333/10000000000 : ℝ)|^5775 ≤ (155278437491/2000000000000 : ℝ)^4751
        have hw : |(-1221483333/10000000000 : ℝ)|=(1221483333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(635682273/1250000000 : ℝ)|^5775 ≤ (43957639441451/100000000000000 : ℝ)^4751
        have hw : |(635682273/1250000000 : ℝ)|=(635682273/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(219729733/400000000 : ℝ)|^5775 ≤ (48278438670821/100000000000000 : ℝ)^4751
        have hw : |(219729733/400000000 : ℝ)|=(219729733/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1750_s1_5 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1045072281/2000000000 : ℝ)*x 0 + (-102718749/1000000000 : ℝ)*x 1 + (5493243211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1045072281/2000000000 : ℝ)^5775 ≤ (11357976043421/25000000000000 : ℝ)^4751 := by
    have hnat : (1045072281 : ℕ)^5775*25000000000000^4751 ≤ 11357976043421^4751*2000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045072281 2000000000 11357976043421 25000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (102718749/1000000000 : ℝ)^5775 ≤ (125793167071/2000000000000 : ℝ)^4751 := by
    have hnat : (102718749 : ℕ)^5775*2000000000000^4751 ≤ 125793167071^4751*1000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102718749 1000000000 125793167071 2000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5493243211/10000000000 : ℝ)^5775 ≤ (12069609363241/25000000000000 : ℝ)^4751 := by
    have hnat : (5493243211 : ℕ)^5775*25000000000000^4751 ≤ 12069609363241^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5493243211 10000000000 12069609363241 25000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1045072281/2000000000 : ℝ), (-102718749/1000000000 : ℝ), (5493243211/10000000000 : ℝ)] ![(11357976043421/25000000000000 : ℝ), (125793167071/2000000000000 : ℝ), (12069609363241/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1045072281/2000000000 : ℝ)|^5775 ≤ (11357976043421/25000000000000 : ℝ)^4751
        have hw : |(1045072281/2000000000 : ℝ)|=(1045072281/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-102718749/1000000000 : ℝ)|^5775 ≤ (125793167071/2000000000000 : ℝ)^4751
        have hw : |(-102718749/1000000000 : ℝ)|=(102718749/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5493243211/10000000000 : ℝ)|^5775 ≤ (12069609363241/25000000000000 : ℝ)^4751
        have hw : |(5493243211/10000000000 : ℝ)|=(5493243211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1750_s1_6 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5225360789/10000000000 : ℝ)*x 0 + (1373310927/2500000000 : ℝ)*x 1 + (-256796913/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5225360789/10000000000 : ℝ)^5775 ≤ (9086379532703/20000000000000 : ℝ)^4751 := by
    have hnat : (5225360789 : ℕ)^5775*20000000000000^4751 ≤ 9086379532703^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225360789 10000000000 9086379532703 20000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1373310927/2500000000 : ℝ)^5775 ≤ (6034805345299/12500000000000 : ℝ)^4751 := by
    have hnat : (1373310927 : ℕ)^5775*12500000000000^4751 ≤ 6034805345299^4751*2500000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1373310927 2500000000 6034805345299 12500000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (256796913/2500000000 : ℝ)^5775 ≤ (3144829779653/50000000000000 : ℝ)^4751 := by
    have hnat : (256796913 : ℕ)^5775*50000000000000^4751 ≤ 3144829779653^4751*2500000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256796913 2500000000 3144829779653 50000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5225360789/10000000000 : ℝ), (1373310927/2500000000 : ℝ), (-256796913/2500000000 : ℝ)] ![(9086379532703/20000000000000 : ℝ), (6034805345299/12500000000000 : ℝ), (3144829779653/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5225360789/10000000000 : ℝ)|^5775 ≤ (9086379532703/20000000000000 : ℝ)^4751
        have hw : |(5225360789/10000000000 : ℝ)|=(5225360789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1373310927/2500000000 : ℝ)|^5775 ≤ (6034805345299/12500000000000 : ℝ)^4751
        have hw : |(1373310927/2500000000 : ℝ)|=(1373310927/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-256796913/2500000000 : ℝ)|^5775 ≤ (3144829779653/50000000000000 : ℝ)^4751
        have hw : |(-256796913/2500000000 : ℝ)|=(256796913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1750_s1_7 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4021221221/10000000000 : ℝ)*x 0 + (2361329423/5000000000 : ℝ)*x 1 + (845712223/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4021221221/10000000000 : ℝ)^5775 ≤ (1321733252649/4000000000000 : ℝ)^4751 := by
    have hnat : (4021221221 : ℕ)^5775*4000000000000^4751 ≤ 1321733252649^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4021221221 10000000000 1321733252649 4000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2361329423/5000000000 : ℝ)^5775 ≤ (40175643611521/100000000000000 : ℝ)^4751 := by
    have hnat : (2361329423 : ℕ)^5775*100000000000000^4751 ≤ 40175643611521^4751*5000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2361329423 5000000000 40175643611521 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (845712223/2500000000 : ℝ)^5775 ≤ (26781025064487/100000000000000 : ℝ)^4751 := by
    have hnat : (845712223 : ℕ)^5775*100000000000000^4751 ≤ 26781025064487^4751*2500000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845712223 2500000000 26781025064487 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4021221221/10000000000 : ℝ), (2361329423/5000000000 : ℝ), (845712223/2500000000 : ℝ)] ![(1321733252649/4000000000000 : ℝ), (40175643611521/100000000000000 : ℝ), (26781025064487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4021221221/10000000000 : ℝ)|^5775 ≤ (1321733252649/4000000000000 : ℝ)^4751
        have hw : |(4021221221/10000000000 : ℝ)|=(4021221221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2361329423/5000000000 : ℝ)|^5775 ≤ (40175643611521/100000000000000 : ℝ)^4751
        have hw : |(2361329423/5000000000 : ℝ)|=(2361329423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(845712223/2500000000 : ℝ)|^5775 ≤ (26781025064487/100000000000000 : ℝ)^4751
        have hw : |(845712223/2500000000 : ℝ)|=(845712223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1750_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (214278987/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5207/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (269/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (4491/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9023/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5207/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (269/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5207/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (269/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5207/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (269/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5207/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (269/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5207/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (269/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5207/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (269/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (269/4000 : ℝ) ^ (5759/1024 : ℝ) ≤ (25521955996207/100000000000000000000 : ℝ) := by
    have hpowers : (269/4000 : ℝ)^5759 ≤ (25521955996207/100000000000000000000 : ℝ)^1024 := by
      have hnat : (269 : ℕ)^5759*100000000000000000000^1024 ≤ 25521955996207^1024*4000^5759 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        269 4000 25521955996207 100000000000000000000 5759 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (269/4000 : ℝ)) (X := (25521955996207/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5759 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (5207/25000 : ℝ) ^ (5759/1024 : ℝ) ≤ (14725090033785653/100000000000000000000 : ℝ) := by
    have hpowers : (5207/25000 : ℝ)^5759 ≤ (14725090033785653/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5207 : ℕ)^5759*100000000000000000000^1024 ≤ 14725090033785653^1024*25000^5759 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5207 25000 14725090033785653 100000000000000000000 5759 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5207/25000 : ℝ)) (X := (14725090033785653/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5759 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000025521955996207/50000000000000000000 : ℝ) ≤ (2000000181520941/2000000000000000 : ℝ) ^ (5759/1024 : ℝ) := by
    have hpowers : (50000025521955996207/50000000000000000000 : ℝ)^1024 ≤ (2000000181520941/2000000000000000 : ℝ)^5759 := by
      have hnat : (50000025521955996207 : ℕ)^1024*2000000000000000^5759 ≤ 2000000181520941^5759*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000025521955996207 50000000000000000000 2000000181520941 2000000000000000 1024 5759 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000181520941/2000000000000000 : ℝ)) (X := (50000025521955996207/50000000000000000000 : ℝ)) (by norm_num) 5759 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5000737530599489093/5000000000000000000 : ℝ) ≤ (2500065565683401/2500000000000000 : ℝ) ^ (5759/1024 : ℝ) := by
    have hpowers : (5000737530599489093/5000000000000000000 : ℝ)^1024 ≤ (2500065565683401/2500000000000000 : ℝ)^5759 := by
      have hnat : (5000737530599489093 : ℕ)^1024*2500000000000000^5759 ≤ 2500065565683401^5759*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000737530599489093 5000000000000000000 2500065565683401 2500000000000000 1024 5759 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500065565683401/2500000000000000 : ℝ)) (X := (5000737530599489093/5000000000000000000 : ℝ)) (by norm_num) 5759 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50014725090033785653/50000000000000000000 : ℝ) ≤ (10000523617862503/10000000000000000 : ℝ) ^ (5759/1024 : ℝ) := by
    have hpowers : (50014725090033785653/50000000000000000000 : ℝ)^1024 ≤ (10000523617862503/10000000000000000 : ℝ)^5759 := by
      have hnat : (50014725090033785653 : ℕ)^1024*10000000000000000^5759 ≤ 10000523617862503^5759*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014725090033785653 50000000000000000000 10000523617862503 10000000000000000 1024 5759 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000523617862503/10000000000000000 : ℝ)) (X := (50014725090033785653/50000000000000000000 : ℝ)) (by norm_num) 5759 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(25521955996207/100000000000000000000 : ℝ) ≤ ((28205299514693092613/28206000000000000000 : ℝ)+2*(261355128899/1410300000000000 : ℝ)*(269/4000 : ℝ))^(5759/1024 : ℝ) := by
    rw [show (28205299514693092613/28206000000000000000 : ℝ)+2*(261355128899/1410300000000000 : ℝ)*(269/4000 : ℝ)=(2000000181520941/2000000000000000 : ℝ) by norm_num, show 1+2*(25521955996207/100000000000000000000 : ℝ)=(50000025521955996207/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14725090033785653/100000000000000000000 : ℝ)+(25521955996207/100000000000000000000 : ℝ) ≤ ((28205299514693092613/28206000000000000000 : ℝ)+(261355128899/1410300000000000 : ℝ)*((5207/25000 : ℝ)+(269/4000 : ℝ)))^(5759/1024 : ℝ) := by
    rw [show (28205299514693092613/28206000000000000000 : ℝ)+(261355128899/1410300000000000 : ℝ)*((5207/25000 : ℝ)+(269/4000 : ℝ))=(2500065565683401/2500000000000000 : ℝ) by norm_num, show 1+(14725090033785653/100000000000000000000 : ℝ)+(25521955996207/100000000000000000000 : ℝ)=(5000737530599489093/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14725090033785653/100000000000000000000 : ℝ) ≤ ((28205299514693092613/28206000000000000000 : ℝ)+2*(261355128899/1410300000000000 : ℝ)*(5207/25000 : ℝ))^(5759/1024 : ℝ) := by
    rw [show (28205299514693092613/28206000000000000000 : ℝ)+2*(261355128899/1410300000000000 : ℝ)*(5207/25000 : ℝ)=(10000523617862503/10000000000000000 : ℝ) by norm_num, show 1+2*(14725090033785653/100000000000000000000 : ℝ)=(50014725090033785653/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (28205299514693092613/28206000000000000000 : ℝ)*(X 1 0+X 2 0)+(261355128899/1410300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5759/1024 : ℝ)) (lo := (269/4000 : ℝ)) (hi := (5207/25000 : ℝ)) (c := (28205299514693092613/28206000000000000000 : ℝ)) (alpha := (261355128899/1410300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (28205299514693092613/28206000000000000000 : ℝ)*(X 0 1+X 2 1)+(261355128899/1410300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5759/1024 : ℝ)) (lo := (269/4000 : ℝ)) (hi := (5207/25000 : ℝ)) (c := (28205299514693092613/28206000000000000000 : ℝ)) (alpha := (261355128899/1410300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (28205299514693092613/28206000000000000000 : ℝ)*(X 0 2+X 1 2)+(261355128899/1410300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5759/1024 : ℝ)) (lo := (269/4000 : ℝ)) (hi := (5207/25000 : ℝ)) (c := (28205299514693092613/28206000000000000000 : ℝ)) (alpha := (261355128899/1410300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1221116757/10000000000 : ℝ)*X 0 0+(5500351201/10000000000 : ℝ)*X 0 1+(1269624667/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2668604083/5000000000 : ℝ)*X 1 0+(-720966007/5000000000 : ℝ)*X 1 1+(5078498661/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2668603963/5000000000 : ℝ)*X 2 0+(5078498851/10000000000 : ℝ)*X 2 1+(-360483021/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((804003739/2000000000 : ℝ)*X 0 0+(671899211/2000000000 : ℝ)*X 0 1+(189820987/400000000 : ℝ)*X 0 2+(804003739/2000000000 : ℝ)*X 1 0+(671899211/2000000000 : ℝ)*X 1 1+(189820987/400000000 : ℝ)*X 1 2+(804003739/2000000000 : ℝ)*X 2 0+(671899211/2000000000 : ℝ)*X 2 1+(189820987/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1221483333/10000000000 : ℝ)*X 0 0+(635682273/1250000000 : ℝ)*X 0 1+(219729733/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1045072281/2000000000 : ℝ)*X 1 0+(-102718749/1000000000 : ℝ)*X 1 1+(5493243211/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5225360789/10000000000 : ℝ)*X 2 0+(1373310927/2500000000 : ℝ)*X 2 1+(-256796913/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4021221221/10000000000 : ℝ)*X 0 0+(2361329423/5000000000 : ℝ)*X 0 1+(845712223/2500000000 : ℝ)*X 0 2+(4021221221/10000000000 : ℝ)*X 1 0+(2361329423/5000000000 : ℝ)*X 1 1+(845712223/2500000000 : ℝ)*X 1 2+(4021221221/10000000000 : ℝ)*X 2 0+(2361329423/5000000000 : ℝ)*X 2 1+(845712223/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2133664468613587563145467647/235050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1330073157/100000000000000 : ℝ)*(base19) + (1122802159/100000000000000 : ℝ)*(base23) + (1679139/3125000000000 : ℝ)*(lower2) + (48447313/20000000000000 : ℝ)*(upper3) + (116136667/100000000000000 : ℝ)*(upper5) + (773002395001327/50000000000000 : ℝ)*(major0) + (773002395001327/50000000000000 : ℝ)*(major1) + (773002395001327/50000000000000 : ℝ)*(major2) + (296313477805341/12500000000000 : ℝ)*(sp0) + (2370516394842039/100000000000000 : ℝ)*(sp1) + (592629150528259/25000000000000 : ℝ)*(sp2) + (360744173617323/50000000000000 : ℝ)*(sp3) + (9902472467/100000000000000 : ℝ)*(sp4) + (3205272391/100000000000000 : ℝ)*(sp7) + (360745776253519/50000000000000 : ℝ)*(f.failure) + (592629431228799/25000000000000 : ℝ)*(f.sum) + (42889617508667/8814375000000000000000000000 : ℝ)*base65 + (2909144575585585817/470100000000000000000000000000000 : ℝ)*base67 + (7190452773822685817/470100000000000000000000000000000 : ℝ)*base69 + (4818301399747285817/470100000000000000000000000000000 : ℝ)*base71 + (48271102068401/17628750000000000000000000000 : ℝ)*base74 + (3725961175752685817/470100000000000000000000000000000 : ℝ)*base75 + (7988546331321085817/470100000000000000000000000000000 : ℝ)*base77 + (5424280468447585817/470100000000000000000000000000000 : ℝ)*base79 + (27230412947747/8814375000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (6505253/5000000000000000000000 : ℝ)*base89 + (6505253/5000000000000000000000 : ℝ)*base91 + (6505253/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3273939533555923914331444373/470100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (493513597/50000000000000 : ℝ)*(base19) + (869711299/100000000000000 : ℝ)*(base23) + (47635409/50000000000000 : ℝ)*(upper2) + (28565989/20000000000000 : ℝ)*(upper3) + (95585209/50000000000000 : ℝ)*(upper5) + (1599322468341521/100000000000000 : ℝ)*(major0) + (1599322468341521/100000000000000 : ℝ)*(major1) + (1599322468341521/100000000000000 : ℝ)*(major2) + (330376033/5000000000000 : ℝ)*(sp1) + (764326587/12500000000000 : ℝ)*(sp2) + (1226135393824673/50000000000000 : ℝ)*(sp4) + (2452263193101493/100000000000000 : ℝ)*(sp5) + (306532975415669/12500000000000 : ℝ)*(sp6) + (74637391688879/10000000000000 : ℝ)*(sp7) + (74637391688879/10000000000000 : ℝ)*(f.failure) + (1226135393824673/50000000000000 : ℝ)*(f.sum) + (227311353446201/70515000000000000000000000000 : ℝ)*base66 + (329718180397154791/940200000000000000000000000000000 : ℝ)*base67 + (7258849151531954791/940200000000000000000000000000000 : ℝ)*base69 + (2986852185105045209/940200000000000000000000000000000 : ℝ)*base72 + (79493731717571/70515000000000000000000000000 : ℝ)*base74 + (2557717778454645209/940200000000000000000000000000000 : ℝ)*base76 + (3293417556964845209/940200000000000000000000000000000 : ℝ)*base78 + (6777206466692445209/940200000000000000000000000000000 : ℝ)*base80 + (240064440088699/70515000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1285573/1000000000000000000000 : ℝ)*base89 + (1285573/1000000000000000000000 : ℝ)*base91 + (1285573/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1750_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (214278987/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5207/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (269/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4491/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9023/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1750_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1750_s2_0 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1222140177/10000000000 : ℝ)*x 0 + (2748533181/5000000000 : ℝ)*x 1 + (5081087329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1222140177/10000000000 : ℝ)^5775 ≤ (7768997013883/100000000000000 : ℝ)^4751 := by
    have hnat : (1222140177 : ℕ)^5775*100000000000000^4751 ≤ 7768997013883^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1222140177 10000000000 7768997013883 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2748533181/5000000000 : ℝ)^5775 ≤ (9663856611977/20000000000000 : ℝ)^4751 := by
    have hnat : (2748533181 : ℕ)^5775*20000000000000^4751 ≤ 9663856611977^4751*5000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2748533181 5000000000 9663856611977 20000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5081087329/10000000000 : ℝ)^5775 ≤ (43911719915551/100000000000000 : ℝ)^4751 := by
    have hnat : (5081087329 : ℕ)^5775*100000000000000^4751 ≤ 43911719915551^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5081087329 10000000000 43911719915551 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1222140177/10000000000 : ℝ), (2748533181/5000000000 : ℝ), (5081087329/10000000000 : ℝ)] ![(7768997013883/100000000000000 : ℝ), (9663856611977/20000000000000 : ℝ), (43911719915551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1222140177/10000000000 : ℝ)|^5775 ≤ (7768997013883/100000000000000 : ℝ)^4751
        have hw : |(-1222140177/10000000000 : ℝ)|=(1222140177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2748533181/5000000000 : ℝ)|^5775 ≤ (9663856611977/20000000000000 : ℝ)^4751
        have hw : |(2748533181/5000000000 : ℝ)|=(2748533181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5081087329/10000000000 : ℝ)|^5775 ≤ (43911719915551/100000000000000 : ℝ)^4751
        have hw : |(5081087329/10000000000 : ℝ)|=(5081087329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1750_s2_1 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1334074113/2500000000 : ℝ)*x 0 + (-1439744523/10000000000 : ℝ)*x 1 + (508108737/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1334074113/2500000000 : ℝ)^5775 ≤ (46606984005703/100000000000000 : ℝ)^4751 := by
    have hnat : (1334074113 : ℕ)^5775*100000000000000^4751 ≤ 46606984005703^4751*2500000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1334074113 2500000000 46606984005703 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1439744523/10000000000 : ℝ)^5775 ≤ (9481295633707/100000000000000 : ℝ)^4751 := by
    have hnat : (1439744523 : ℕ)^5775*100000000000000^4751 ≤ 9481295633707^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1439744523 10000000000 9481295633707 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (508108737/1000000000 : ℝ)^5775 ≤ (35129376277/80000000000 : ℝ)^4751 := by
    have hnat : (508108737 : ℕ)^5775*80000000000^4751 ≤ 35129376277^4751*1000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508108737 1000000000 35129376277 80000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1334074113/2500000000 : ℝ), (-1439744523/10000000000 : ℝ), (508108737/1000000000 : ℝ)] ![(46606984005703/100000000000000 : ℝ), (9481295633707/100000000000000 : ℝ), (35129376277/80000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1334074113/2500000000 : ℝ)|^5775 ≤ (46606984005703/100000000000000 : ℝ)^4751
        have hw : |(1334074113/2500000000 : ℝ)|=(1334074113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1439744523/10000000000 : ℝ)|^5775 ≤ (9481295633707/100000000000000 : ℝ)^4751
        have hw : |(-1439744523/10000000000 : ℝ)|=(1439744523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(508108737/1000000000 : ℝ)|^5775 ≤ (35129376277/80000000000 : ℝ)^4751
        have hw : |(508108737/1000000000 : ℝ)|=(508108737/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1750_s2_2 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1067259279/2000000000 : ℝ)*x 0 + (2540543699/5000000000 : ℝ)*x 1 + (-719872281/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1067259279/2000000000 : ℝ)^5775 ≤ (46606983400567/100000000000000 : ℝ)^4751 := by
    have hnat : (1067259279 : ℕ)^5775*100000000000000^4751 ≤ 46606983400567^4751*2000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067259279 2000000000 46606983400567 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2540543699/5000000000 : ℝ)^5775 ≤ (43911720640387/100000000000000 : ℝ)^4751 := by
    have hnat : (2540543699 : ℕ)^5775*100000000000000^4751 ≤ 43911720640387^4751*5000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2540543699 5000000000 43911720640387 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (719872281/5000000000 : ℝ)^5775 ≤ (4740647972947/50000000000000 : ℝ)^4751 := by
    have hnat : (719872281 : ℕ)^5775*50000000000000^4751 ≤ 4740647972947^4751*5000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      719872281 5000000000 4740647972947 50000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1067259279/2000000000 : ℝ), (2540543699/5000000000 : ℝ), (-719872281/5000000000 : ℝ)] ![(46606983400567/100000000000000 : ℝ), (43911720640387/100000000000000 : ℝ), (4740647972947/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1067259279/2000000000 : ℝ)|^5775 ≤ (46606983400567/100000000000000 : ℝ)^4751
        have hw : |(1067259279/2000000000 : ℝ)|=(1067259279/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2540543699/5000000000 : ℝ)|^5775 ≤ (43911720640387/100000000000000 : ℝ)^4751
        have hw : |(2540543699/5000000000 : ℝ)|=(2540543699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-719872281/5000000000 : ℝ)|^5775 ≤ (4740647972947/50000000000000 : ℝ)^4751
        have hw : |(-719872281/5000000000 : ℝ)|=(719872281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1750_s2_3 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2010428573/5000000000 : ℝ)*x 0 + (21056757/62500000 : ℝ)*x 1 + (4735813389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2010428573/5000000000 : ℝ)^5775 ≤ (516245232047/1562500000000 : ℝ)^4751 := by
    have hnat : (2010428573 : ℕ)^5775*1562500000000^4751 ≤ 516245232047^4751*5000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010428573 5000000000 516245232047 1562500000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21056757/62500000 : ℝ)^5775 ≤ (26648595638921/100000000000000 : ℝ)^4751 := by
    have hnat : (21056757 : ℕ)^5775*100000000000000^4751 ≤ 26648595638921^4751*62500000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21056757 62500000 26648595638921 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4735813389/10000000000 : ℝ)^5775 ≤ (40311709493629/100000000000000 : ℝ)^4751 := by
    have hnat : (4735813389 : ℕ)^5775*100000000000000^4751 ≤ 40311709493629^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4735813389 10000000000 40311709493629 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2010428573/5000000000 : ℝ), (21056757/62500000 : ℝ), (4735813389/10000000000 : ℝ)] ![(516245232047/1562500000000 : ℝ), (26648595638921/100000000000000 : ℝ), (40311709493629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2010428573/5000000000 : ℝ)|^5775 ≤ (516245232047/1562500000000 : ℝ)^4751
        have hw : |(2010428573/5000000000 : ℝ)|=(2010428573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(21056757/62500000 : ℝ)|^5775 ≤ (26648595638921/100000000000000 : ℝ)^4751
        have hw : |(21056757/62500000 : ℝ)|=(21056757/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4735813389/10000000000 : ℝ)|^5775 ≤ (40311709493629/100000000000000 : ℝ)^4751
        have hw : |(4735813389/10000000000 : ℝ)|=(4735813389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1750_s2_4 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-611245643/5000000000 : ℝ)*x 0 + (2543927311/5000000000 : ℝ)*x 1 + (5490157057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (611245643/5000000000 : ℝ)^5775 ≤ (971463764623/12500000000000 : ℝ)^4751 := by
    have hnat : (611245643 : ℕ)^5775*12500000000000^4751 ≤ 971463764623^4751*5000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      611245643 5000000000 971463764623 12500000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2543927311/5000000000 : ℝ)^5775 ≤ (21991409829621/50000000000000 : ℝ)^4751 := by
    have hnat : (2543927311 : ℕ)^5775*50000000000000^4751 ≤ 21991409829621^4751*5000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2543927311 5000000000 21991409829621 50000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5490157057/10000000000 : ℝ)^5775 ≤ (48245470209833/100000000000000 : ℝ)^4751 := by
    have hnat : (5490157057 : ℕ)^5775*100000000000000^4751 ≤ 48245470209833^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490157057 10000000000 48245470209833 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-611245643/5000000000 : ℝ), (2543927311/5000000000 : ℝ), (5490157057/10000000000 : ℝ)] ![(971463764623/12500000000000 : ℝ), (21991409829621/50000000000000 : ℝ), (48245470209833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-611245643/5000000000 : ℝ)|^5775 ≤ (971463764623/12500000000000 : ℝ)^4751
        have hw : |(-611245643/5000000000 : ℝ)|=(611245643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2543927311/5000000000 : ℝ)|^5775 ≤ (21991409829621/50000000000000 : ℝ)^4751
        have hw : |(2543927311/5000000000 : ℝ)|=(2543927311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5490157057/10000000000 : ℝ)|^5775 ≤ (48245470209833/100000000000000 : ℝ)^4751
        have hw : |(5490157057/10000000000 : ℝ)|=(5490157057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1750_s2_5 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5226023929/10000000000 : ℝ)*x 0 + (-1030674791/10000000000 : ℝ)*x 1 + (2745078531/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5226023929/10000000000 : ℝ)^5775 ≤ (45438906125433/100000000000000 : ℝ)^4751 := by
    have hnat : (5226023929 : ℕ)^5775*100000000000000^4751 ≤ 45438906125433^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226023929 10000000000 45438906125433 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1030674791/10000000000 : ℝ)^5775 ≤ (6315623600137/100000000000000 : ℝ)^4751 := by
    have hnat : (1030674791 : ℕ)^5775*100000000000000^4751 ≤ 6315623600137^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030674791 10000000000 6315623600137 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2745078531/5000000000 : ℝ)^5775 ≤ (48245470263241/100000000000000 : ℝ)^4751 := by
    have hnat : (2745078531 : ℕ)^5775*100000000000000^4751 ≤ 48245470263241^4751*5000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2745078531 5000000000 48245470263241 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5226023929/10000000000 : ℝ), (-1030674791/10000000000 : ℝ), (2745078531/5000000000 : ℝ)] ![(45438906125433/100000000000000 : ℝ), (6315623600137/100000000000000 : ℝ), (48245470263241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5226023929/10000000000 : ℝ)|^5775 ≤ (45438906125433/100000000000000 : ℝ)^4751
        have hw : |(5226023929/10000000000 : ℝ)|=(5226023929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1030674791/10000000000 : ℝ)|^5775 ≤ (6315623600137/100000000000000 : ℝ)^4751
        have hw : |(-1030674791/10000000000 : ℝ)|=(1030674791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2745078531/5000000000 : ℝ)|^5775 ≤ (48245470263241/100000000000000 : ℝ)^4751
        have hw : |(2745078531/5000000000 : ℝ)|=(2745078531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1750_s2_6 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5226023929/10000000000 : ℝ)*x 0 + (5490157061/10000000000 : ℝ)*x 1 + (-1030674791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5226023929/10000000000 : ℝ)^5775 ≤ (45438906125433/100000000000000 : ℝ)^4751 := by
    have hnat : (5226023929 : ℕ)^5775*100000000000000^4751 ≤ 45438906125433^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226023929 10000000000 45438906125433 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5490157061/10000000000 : ℝ)^5775 ≤ (48245470252559/100000000000000 : ℝ)^4751 := by
    have hnat : (5490157061 : ℕ)^5775*100000000000000^4751 ≤ 48245470252559^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490157061 10000000000 48245470252559 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1030674791/10000000000 : ℝ)^5775 ≤ (6315623600137/100000000000000 : ℝ)^4751 := by
    have hnat : (1030674791 : ℕ)^5775*100000000000000^4751 ≤ 6315623600137^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030674791 10000000000 6315623600137 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5226023929/10000000000 : ℝ), (5490157061/10000000000 : ℝ), (-1030674791/10000000000 : ℝ)] ![(45438906125433/100000000000000 : ℝ), (48245470252559/100000000000000 : ℝ), (6315623600137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5226023929/10000000000 : ℝ)|^5775 ≤ (45438906125433/100000000000000 : ℝ)^4751
        have hw : |(5226023929/10000000000 : ℝ)|=(5226023929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5490157061/10000000000 : ℝ)|^5775 ≤ (48245470252559/100000000000000 : ℝ)^4751
        have hw : |(5490157061/10000000000 : ℝ)|=(5490157061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1030674791/10000000000 : ℝ)|^5775 ≤ (6315623600137/100000000000000 : ℝ)^4751
        have hw : |(-1030674791/10000000000 : ℝ)|=(1030674791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1750_s2_7 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2011005247/5000000000 : ℝ)*x 0 + (2356789423/5000000000 : ℝ)*x 1 + (3391782103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2011005247/5000000000 : ℝ)^5775 ≤ (33051215000973/100000000000000 : ℝ)^4751 := by
    have hnat : (2011005247 : ℕ)^5775*100000000000000^4751 ≤ 33051215000973^4751*5000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011005247 5000000000 33051215000973 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2356789423/5000000000 : ℝ)^5775 ≤ (40081770970617/100000000000000 : ℝ)^4751 := by
    have hnat : (2356789423 : ℕ)^5775*100000000000000^4751 ≤ 40081770970617^4751*5000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2356789423 5000000000 40081770970617 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3391782103/10000000000 : ℝ)^5775 ≤ (26867014012859/100000000000000 : ℝ)^4751 := by
    have hnat : (3391782103 : ℕ)^5775*100000000000000^4751 ≤ 26867014012859^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3391782103 10000000000 26867014012859 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2011005247/5000000000 : ℝ), (2356789423/5000000000 : ℝ), (3391782103/10000000000 : ℝ)] ![(33051215000973/100000000000000 : ℝ), (40081770970617/100000000000000 : ℝ), (26867014012859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2011005247/5000000000 : ℝ)|^5775 ≤ (33051215000973/100000000000000 : ℝ)^4751
        have hw : |(2011005247/5000000000 : ℝ)|=(2011005247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2356789423/5000000000 : ℝ)|^5775 ≤ (40081770970617/100000000000000 : ℝ)^4751
        have hw : |(2356789423/5000000000 : ℝ)|=(2356789423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3391782103/10000000000 : ℝ)|^5775 ≤ (26867014012859/100000000000000 : ℝ)^4751
        have hw : |(3391782103/10000000000 : ℝ)|=(3391782103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1750_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (214278987/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9023/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4491/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (9039/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2247/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9023/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4491/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9023/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4491/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9023/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4491/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9023/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4491/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9023/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4491/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9023/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4491/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4491/50000 : ℝ) ^ (5759/1024 : ℝ) ≤ (129940791242783/100000000000000000000 : ℝ) := by
    have hpowers : (4491/50000 : ℝ)^5759 ≤ (129940791242783/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4491 : ℕ)^5759*100000000000000000000^1024 ≤ 129940791242783^1024*50000^5759 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4491 50000 129940791242783 100000000000000000000 5759 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4491/50000 : ℝ)) (X := (129940791242783/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5759 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9023/50000 : ℝ) ^ (5759/1024 : ℝ) ≤ (82182446234897/1250000000000000000 : ℝ) := by
    have hpowers : (9023/50000 : ℝ)^5759 ≤ (82182446234897/1250000000000000000 : ℝ)^1024 := by
      have hnat : (9023 : ℕ)^5759*1250000000000000000^1024 ≤ 82182446234897^1024*50000^5759 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9023 50000 82182446234897 1250000000000000000 5759 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9023/50000 : ℝ)) (X := (82182446234897/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 5759 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000129940791242783/50000000000000000000 : ℝ) ≤ (10000004620914329/10000000000000000 : ℝ) ^ (5759/1024 : ℝ) := by
    have hpowers : (50000129940791242783/50000000000000000000 : ℝ)^1024 ≤ (10000004620914329/10000000000000000 : ℝ)^5759 := by
      have hnat : (50000129940791242783 : ℕ)^1024*10000000000000000^5759 ≤ 10000004620914329^5759*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000129940791242783 50000000000000000000 10000004620914329 10000000000000000 1024 5759 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000004620914329/10000000000000000 : ℝ)) (X := (50000129940791242783/50000000000000000000 : ℝ)) (by norm_num) 5759 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100006704536490034543/100000000000000000000 : ℝ) ≤ (10000119209170823/10000000000000000 : ℝ) ^ (5759/1024 : ℝ) := by
    have hpowers : (100006704536490034543/100000000000000000000 : ℝ)^1024 ≤ (10000119209170823/10000000000000000 : ℝ)^5759 := by
      have hnat : (100006704536490034543 : ℕ)^1024*10000000000000000^5759 ≤ 10000119209170823^5759*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100006704536490034543 100000000000000000000 10000119209170823 10000000000000000 1024 5759 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000119209170823/10000000000000000 : ℝ)) (X := (100006704536490034543/100000000000000000000 : ℝ)) (by norm_num) 5759 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (625082182446234897/625000000000000000 : ℝ) ≤ (10000233797427317/10000000000000000 : ℝ) ^ (5759/1024 : ℝ) := by
    have hpowers : (625082182446234897/625000000000000000 : ℝ)^1024 ≤ (10000233797427317/10000000000000000 : ℝ)^5759 := by
      have hnat : (625082182446234897 : ℕ)^1024*10000000000000000^5759 ≤ 10000233797427317^5759*625000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        625082182446234897 625000000000000000 10000233797427317 10000000000000000 1024 5759 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000233797427317/10000000000000000 : ℝ)) (X := (625082182446234897/625000000000000000 : ℝ)) (by norm_num) 5759 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(129940791242783/100000000000000000000 : ℝ) ≤ ((283243698189149437/283250000000000000 : ℝ)+2*(57294128247/453200000000000 : ℝ)*(4491/50000 : ℝ))^(5759/1024 : ℝ) := by
    rw [show (283243698189149437/283250000000000000 : ℝ)+2*(57294128247/453200000000000 : ℝ)*(4491/50000 : ℝ)=(10000004620914329/10000000000000000 : ℝ) by norm_num, show 1+2*(129940791242783/100000000000000000000 : ℝ)=(50000129940791242783/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(82182446234897/1250000000000000000 : ℝ)+(129940791242783/100000000000000000000 : ℝ) ≤ ((283243698189149437/283250000000000000 : ℝ)+(57294128247/453200000000000 : ℝ)*((9023/50000 : ℝ)+(4491/50000 : ℝ)))^(5759/1024 : ℝ) := by
    rw [show (283243698189149437/283250000000000000 : ℝ)+(57294128247/453200000000000 : ℝ)*((9023/50000 : ℝ)+(4491/50000 : ℝ))=(10000119209170823/10000000000000000 : ℝ) by norm_num, show 1+(82182446234897/1250000000000000000 : ℝ)+(129940791242783/100000000000000000000 : ℝ)=(100006704536490034543/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(82182446234897/1250000000000000000 : ℝ) ≤ ((283243698189149437/283250000000000000 : ℝ)+2*(57294128247/453200000000000 : ℝ)*(9023/50000 : ℝ))^(5759/1024 : ℝ) := by
    rw [show (283243698189149437/283250000000000000 : ℝ)+2*(57294128247/453200000000000 : ℝ)*(9023/50000 : ℝ)=(10000233797427317/10000000000000000 : ℝ) by norm_num, show 1+2*(82182446234897/1250000000000000000 : ℝ)=(625082182446234897/625000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (283243698189149437/283250000000000000 : ℝ)*(X 1 0+X 2 0)+(57294128247/453200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5759/1024 : ℝ)) (lo := (4491/50000 : ℝ)) (hi := (9023/50000 : ℝ)) (c := (283243698189149437/283250000000000000 : ℝ)) (alpha := (57294128247/453200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (283243698189149437/283250000000000000 : ℝ)*(X 0 1+X 2 1)+(57294128247/453200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5759/1024 : ℝ)) (lo := (4491/50000 : ℝ)) (hi := (9023/50000 : ℝ)) (c := (283243698189149437/283250000000000000 : ℝ)) (alpha := (57294128247/453200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (283243698189149437/283250000000000000 : ℝ)*(X 0 2+X 1 2)+(57294128247/453200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5759/1024 : ℝ)) (lo := (4491/50000 : ℝ)) (hi := (9023/50000 : ℝ)) (c := (283243698189149437/283250000000000000 : ℝ)) (alpha := (57294128247/453200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1222140177/10000000000 : ℝ)*X 0 0+(2748533181/5000000000 : ℝ)*X 0 1+(5081087329/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1334074113/2500000000 : ℝ)*X 1 0+(-1439744523/10000000000 : ℝ)*X 1 1+(508108737/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1067259279/2000000000 : ℝ)*X 2 0+(2540543699/5000000000 : ℝ)*X 2 1+(-719872281/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2010428573/5000000000 : ℝ)*X 0 0+(21056757/62500000 : ℝ)*X 0 1+(4735813389/10000000000 : ℝ)*X 0 2+(2010428573/5000000000 : ℝ)*X 1 0+(21056757/62500000 : ℝ)*X 1 1+(4735813389/10000000000 : ℝ)*X 1 2+(2010428573/5000000000 : ℝ)*X 2 0+(21056757/62500000 : ℝ)*X 2 1+(4735813389/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-611245643/5000000000 : ℝ)*X 0 0+(2543927311/5000000000 : ℝ)*X 0 1+(5490157057/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5226023929/10000000000 : ℝ)*X 1 0+(-1030674791/10000000000 : ℝ)*X 1 1+(2745078531/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5226023929/10000000000 : ℝ)*X 2 0+(5490157061/10000000000 : ℝ)*X 2 1+(-1030674791/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2011005247/5000000000 : ℝ)*X 0 0+(2356789423/5000000000 : ℝ)*X 0 1+(3391782103/10000000000 : ℝ)*X 0 2+(2011005247/5000000000 : ℝ)*X 1 0+(2356789423/5000000000 : ℝ)*X 1 1+(3391782103/10000000000 : ℝ)*X 1 2+(2011005247/5000000000 : ℝ)*X 2 0+(2356789423/5000000000 : ℝ)*X 2 1+(3391782103/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (188364788678777657580276429/14162500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1787512059/100000000000000 : ℝ)*(base19) + (25392079/1562500000000 : ℝ)*(base23) + (570069/781250000000 : ℝ)*(lower2) + (336336703/100000000000000 : ℝ)*(upper3) + (215089409/100000000000000 : ℝ)*(upper5) + (1567838131916911/100000000000000 : ℝ)*(major0) + (1567838131916911/100000000000000 : ℝ)*(major1) + (1567838131916911/100000000000000 : ℝ)*(major2) + (120199077104083/5000000000000 : ℝ)*(sp0) + (1201996633849797/50000000000000 : ℝ)*(sp1) + (2403993430118597/100000000000000 : ℝ)*(sp2) + (91459509959167/12500000000000 : ℝ)*(sp3) + (13513129993/100000000000000 : ℝ)*(sp4) + (18303153/390625000000 : ℝ)*(sp7) + (91460095660063/12500000000000 : ℝ)*(f.failure) + (2403995055211653/100000000000000 : ℝ)*(f.sum) + (37997481226783/22660000000000000000000000000 : ℝ)*base66 + (26128422905496317/7081250000000000000000000000000 : ℝ)*base68 + (13372037771034933/7081250000000000000000000000000 : ℝ)*base69 + (10669027016841183/7081250000000000000000000000000 : ℝ)*base71 + (120359229325743/22660000000000000000000000000 : ℝ)*base74 + (14144382351116183/7081250000000000000000000000000 : ℝ)*base75 + (17156867554977567/7081250000000000000000000000000 : ℝ)*base78 + (18857752523753683/7081250000000000000000000000000 : ℝ)*base79 + (26891934509023/22660000000000000000000000000 : ℝ)*base82 + (8496181/1250000000000000000000 : ℝ)*base89 + (8496181/1250000000000000000000 : ℝ)*base91 + (8496181/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (88744216844375291518827/22660000000000000000000000000 : ℝ) := by norm_num
    linear_combination (508458651/100000000000000 : ℝ)*(base19) + (136446221/25000000000000 : ℝ)*(base23) + (72395399/50000000000000 : ℝ)*(lower1) + (1339983/1562500000000 : ℝ)*(upper3) + (3301289/20000000000000 : ℝ)*(lower4) + (81719191/100000000000000 : ℝ)*(upper5) + (1621116642395307/100000000000000 : ℝ)*(major0) + (1621116642395307/100000000000000 : ℝ)*(major1) + (1621116642395307/100000000000000 : ℝ)*(major2) + (272083213/100000000000000 : ℝ)*(sp2) + (1242844151746243/50000000000000 : ℝ)*(sp4) + (1242843897516917/50000000000000 : ℝ)*(sp5) + (2485687485624389/100000000000000 : ℝ)*(sp6) + (756544850753521/100000000000000 : ℝ)*(sp7) + (756544850753521/100000000000000 : ℝ)*(f.failure) + (1242844151746243/50000000000000 : ℝ)*(f.sum) + (72065725148651/22660000000000000000000000000 : ℝ)*base66 + (25713612704540071/7081250000000000000000000000000 : ℝ)*base67 + (22994261824346321/7081250000000000000000000000000 : ℝ)*base69 + (321932397442747429/7081250000000000000000000000000 : ℝ)*base72 + (33130535774691/22660000000000000000000000000 : ℝ)*base74 + (76070623994358821/7081250000000000000000000000000 : ℝ)*base75 + (4999070305809929/7081250000000000000000000000000 : ℝ)*base78 + (19651992039603679/7081250000000000000000000000000 : ℝ)*base80 + (112415070550549/22660000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (33436773/10000000000000000000000 : ℝ)*base90 + (33436773/10000000000000000000000 : ℝ)*base92 + (33436773/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1750_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (214278987/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9023/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4491/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9039/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2247/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1750_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1750_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (214278987/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9039/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2247/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1750_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1750_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1750_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (214278987/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9039/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2247/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1750_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
