-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1486_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:14:51.611989+00:00
-- url     : https://prove2.me/submissions/c629c76e-37ce-42d9-ba11-57a7043924b0

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
theorem support_rectangle_w1486_s6_0 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-190712333/1000000000 : ℝ)*x 0 + (5436635093/10000000000 : ℝ)*x 1 + (5216212203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (190712333/1000000000 : ℝ)^4469 ≤ (2913512347547/25000000000000 : ℝ)^3445 := by
    have hnat : (190712333 : ℕ)^4469*25000000000000^3445 ≤ 2913512347547^3445*1000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190712333 1000000000 2913512347547 25000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5436635093/10000000000 : ℝ)^4469 ≤ (9071708648209/20000000000000 : ℝ)^3445 := by
    have hnat : (5436635093 : ℕ)^4469*20000000000000^3445 ≤ 9071708648209^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436635093 10000000000 9071708648209 20000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216212203/10000000000 : ℝ)^4469 ≤ (21493703674189/50000000000000 : ℝ)^3445 := by
    have hnat : (5216212203 : ℕ)^4469*50000000000000^3445 ≤ 21493703674189^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216212203 10000000000 21493703674189 50000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-190712333/1000000000 : ℝ), (5436635093/10000000000 : ℝ), (5216212203/10000000000 : ℝ)] ![(2913512347547/25000000000000 : ℝ), (9071708648209/20000000000000 : ℝ), (21493703674189/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-190712333/1000000000 : ℝ)|^4469 ≤ (2913512347547/25000000000000 : ℝ)^3445
        have hw : |(-190712333/1000000000 : ℝ)|=(190712333/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5436635093/10000000000 : ℝ)|^4469 ≤ (9071708648209/20000000000000 : ℝ)^3445
        have hw : |(5436635093/10000000000 : ℝ)|=(5436635093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216212203/10000000000 : ℝ)|^4469 ≤ (21493703674189/50000000000000 : ℝ)^3445
        have hw : |(5216212203/10000000000 : ℝ)|=(5216212203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s6_1 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676497747/5000000000 : ℝ)*x 0 + (-404014877/2000000000 : ℝ)*x 1 + (1043242441/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676497747/5000000000 : ℝ)^4469 ≤ (444553841819/1000000000000 : ℝ)^3445 := by
    have hnat : (2676497747 : ℕ)^4469*1000000000000^3445 ≤ 444553841819^3445*5000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676497747 5000000000 444553841819 1000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (404014877/2000000000 : ℝ)^4469 ≤ (12557208429857/100000000000000 : ℝ)^3445 := by
    have hnat : (404014877 : ℕ)^4469*100000000000000^3445 ≤ 12557208429857^3445*2000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404014877 2000000000 12557208429857 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043242441/2000000000 : ℝ)^4469 ≤ (268671296061/625000000000 : ℝ)^3445 := by
    have hnat : (1043242441 : ℕ)^4469*625000000000^3445 ≤ 268671296061^3445*2000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043242441 2000000000 268671296061 625000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676497747/5000000000 : ℝ), (-404014877/2000000000 : ℝ), (1043242441/2000000000 : ℝ)] ![(444553841819/1000000000000 : ℝ), (12557208429857/100000000000000 : ℝ), (268671296061/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676497747/5000000000 : ℝ)|^4469 ≤ (444553841819/1000000000000 : ℝ)^3445
        have hw : |(2676497747/5000000000 : ℝ)|=(2676497747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-404014877/2000000000 : ℝ)|^4469 ≤ (12557208429857/100000000000000 : ℝ)^3445
        have hw : |(-404014877/2000000000 : ℝ)|=(404014877/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043242441/2000000000 : ℝ)|^4469 ≤ (268671296061/625000000000 : ℝ)^3445
        have hw : |(1043242441/2000000000 : ℝ)|=(1043242441/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s6_2 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338248873/2500000000 : ℝ)*x 0 + (1043242441/2000000000 : ℝ)*x 1 + (-2020074389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338248873/2500000000 : ℝ)^4469 ≤ (22227692080177/50000000000000 : ℝ)^3445 := by
    have hnat : (1338248873 : ℕ)^4469*50000000000000^3445 ≤ 22227692080177^3445*2500000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338248873 2500000000 22227692080177 50000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043242441/2000000000 : ℝ)^4469 ≤ (268671296061/625000000000 : ℝ)^3445 := by
    have hnat : (1043242441 : ℕ)^4469*625000000000^3445 ≤ 268671296061^3445*2000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043242441 2000000000 268671296061 625000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2020074389/10000000000 : ℝ)^4469 ≤ (12557208462113/100000000000000 : ℝ)^3445 := by
    have hnat : (2020074389 : ℕ)^4469*100000000000000^3445 ≤ 12557208462113^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2020074389 10000000000 12557208462113 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338248873/2500000000 : ℝ), (1043242441/2000000000 : ℝ), (-2020074389/10000000000 : ℝ)] ![(22227692080177/50000000000000 : ℝ), (268671296061/625000000000 : ℝ), (12557208462113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338248873/2500000000 : ℝ)|^4469 ≤ (22227692080177/50000000000000 : ℝ)^3445
        have hw : |(1338248873/2500000000 : ℝ)|=(1338248873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043242441/2000000000 : ℝ)|^4469 ≤ (268671296061/625000000000 : ℝ)^3445
        have hw : |(1043242441/2000000000 : ℝ)|=(1043242441/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2020074389/10000000000 : ℝ)|^4469 ≤ (12557208462113/100000000000000 : ℝ)^3445
        have hw : |(-2020074389/10000000000 : ℝ)|=(2020074389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s6_3 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4282035943/10000000000 : ℝ)*x 0 + (1010698127/2500000000 : ℝ)*x 1 + (4533476697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4282035943/10000000000 : ℝ)^4469 ≤ (33278302816939/100000000000000 : ℝ)^3445 := by
    have hnat : (4282035943 : ℕ)^4469*100000000000000^3445 ≤ 33278302816939^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4282035943 10000000000 33278302816939 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1010698127/2500000000 : ℝ)^4469 ≤ (30886628952999/100000000000000 : ℝ)^3445 := by
    have hnat : (1010698127 : ℕ)^4469*100000000000000^3445 ≤ 30886628952999^3445*2500000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1010698127 2500000000 30886628952999 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4533476697/10000000000 : ℝ)^4469 ≤ (35835068222173/100000000000000 : ℝ)^3445 := by
    have hnat : (4533476697 : ℕ)^4469*100000000000000^3445 ≤ 35835068222173^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4533476697 10000000000 35835068222173 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4282035943/10000000000 : ℝ), (1010698127/2500000000 : ℝ), (4533476697/10000000000 : ℝ)] ![(33278302816939/100000000000000 : ℝ), (30886628952999/100000000000000 : ℝ), (35835068222173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4282035943/10000000000 : ℝ)|^4469 ≤ (33278302816939/100000000000000 : ℝ)^3445
        have hw : |(4282035943/10000000000 : ℝ)|=(4282035943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1010698127/2500000000 : ℝ)|^4469 ≤ (30886628952999/100000000000000 : ℝ)^3445
        have hw : |(1010698127/2500000000 : ℝ)|=(1010698127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4533476697/10000000000 : ℝ)|^4469 ≤ (35835068222173/100000000000000 : ℝ)^3445
        have hw : |(4533476697/10000000000 : ℝ)|=(4533476697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s6_4 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-381430681/2000000000 : ℝ)*x 0 + (5217341089/10000000000 : ℝ)*x 1 + (5435497911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (381430681/2000000000 : ℝ)^4469 ≤ (11654287800951/100000000000000 : ℝ)^3445 := by
    have hnat : (381430681 : ℕ)^4469*100000000000000^3445 ≤ 11654287800951^3445*2000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      381430681 2000000000 11654287800951 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217341089/10000000000 : ℝ)^4469 ≤ (42999476345547/100000000000000 : ℝ)^3445 := by
    have hnat : (5217341089 : ℕ)^4469*100000000000000^3445 ≤ 42999476345547^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217341089 10000000000 42999476345547 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5435497911/10000000000 : ℝ)^4469 ≤ (11336558958833/25000000000000 : ℝ)^3445 := by
    have hnat : (5435497911 : ℕ)^4469*25000000000000^3445 ≤ 11336558958833^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435497911 10000000000 11336558958833 25000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-381430681/2000000000 : ℝ), (5217341089/10000000000 : ℝ), (5435497911/10000000000 : ℝ)] ![(11654287800951/100000000000000 : ℝ), (42999476345547/100000000000000 : ℝ), (11336558958833/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-381430681/2000000000 : ℝ)|^4469 ≤ (11654287800951/100000000000000 : ℝ)^3445
        have hw : |(-381430681/2000000000 : ℝ)|=(381430681/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217341089/10000000000 : ℝ)|^4469 ≤ (42999476345547/100000000000000 : ℝ)^3445
        have hw : |(5217341089/10000000000 : ℝ)|=(5217341089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5435497911/10000000000 : ℝ)|^4469 ≤ (11336558958833/25000000000000 : ℝ)^3445
        have hw : |(5435497911/10000000000 : ℝ)|=(5435497911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s6_5 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323842679/2500000000 : ℝ)*x 0 + (-900394343/5000000000 : ℝ)*x 1 + (339718619/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323842679/2500000000 : ℝ)^4469 ≤ (8767114220669/20000000000000 : ℝ)^3445 := by
    have hnat : (1323842679 : ℕ)^4469*20000000000000^3445 ≤ 8767114220669^3445*2500000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323842679 2500000000 8767114220669 20000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (900394343/5000000000 : ℝ)^4469 ≤ (5409096561273/50000000000000 : ℝ)^3445 := by
    have hnat : (900394343 : ℕ)^4469*50000000000000^3445 ≤ 5409096561273^3445*5000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900394343 5000000000 5409096561273 50000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339718619/625000000 : ℝ)^4469 ≤ (5668279469947/12500000000000 : ℝ)^3445 := by
    have hnat : (339718619 : ℕ)^4469*12500000000000^3445 ≤ 5668279469947^3445*625000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339718619 625000000 5668279469947 12500000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323842679/2500000000 : ℝ), (-900394343/5000000000 : ℝ), (339718619/625000000 : ℝ)] ![(8767114220669/20000000000000 : ℝ), (5409096561273/50000000000000 : ℝ), (5668279469947/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323842679/2500000000 : ℝ)|^4469 ≤ (8767114220669/20000000000000 : ℝ)^3445
        have hw : |(1323842679/2500000000 : ℝ)|=(1323842679/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-900394343/5000000000 : ℝ)|^4469 ≤ (5409096561273/50000000000000 : ℝ)^3445
        have hw : |(-900394343/5000000000 : ℝ)|=(900394343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(339718619/625000000 : ℝ)|^4469 ≤ (5668279469947/12500000000000 : ℝ)^3445
        have hw : |(339718619/625000000 : ℝ)|=(339718619/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s6_6 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295370711/10000000000 : ℝ)*x 0 + (2717748957/5000000000 : ℝ)*x 1 + (-1800788679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295370711/10000000000 : ℝ)^4469 ≤ (43835571049651/100000000000000 : ℝ)^3445 := by
    have hnat : (5295370711 : ℕ)^4469*100000000000000^3445 ≤ 43835571049651^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295370711 10000000000 43835571049651 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2717748957/5000000000 : ℝ)^4469 ≤ (226731179339/500000000000 : ℝ)^3445 := by
    have hnat : (2717748957 : ℕ)^4469*500000000000^3445 ≤ 226731179339^3445*5000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717748957 5000000000 226731179339 500000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1800788679/10000000000 : ℝ)^4469 ≤ (5409096533997/50000000000000 : ℝ)^3445 := by
    have hnat : (1800788679 : ℕ)^4469*50000000000000^3445 ≤ 5409096533997^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1800788679 10000000000 5409096533997 50000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295370711/10000000000 : ℝ), (2717748957/5000000000 : ℝ), (-1800788679/10000000000 : ℝ)] ![(43835571049651/100000000000000 : ℝ), (226731179339/500000000000 : ℝ), (5409096533997/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295370711/10000000000 : ℝ)|^4469 ≤ (43835571049651/100000000000000 : ℝ)^3445
        have hw : |(5295370711/10000000000 : ℝ)|=(5295370711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2717748957/5000000000 : ℝ)|^4469 ≤ (226731179339/500000000000 : ℝ)^3445
        have hw : |(2717748957/5000000000 : ℝ)|=(2717748957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1800788679/10000000000 : ℝ)|^4469 ≤ (5409096533997/50000000000000 : ℝ)^3445
        have hw : |(-1800788679/10000000000 : ℝ)|=(1800788679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s6_7 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (428210287/1000000000 : ℝ)*x 0 + (113274093/250000000 : ℝ)*x 1 + (2022661997/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (428210287/1000000000 : ℝ)^4469 ≤ (8319744388419/25000000000000 : ℝ)^3445 := by
    have hnat : (428210287 : ℕ)^4469*25000000000000^3445 ≤ 8319744388419^3445*1000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428210287 1000000000 8319744388419 25000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (113274093/250000000 : ℝ)^4469 ≤ (35809302002481/100000000000000 : ℝ)^3445 := by
    have hnat : (113274093 : ℕ)^4469*100000000000000^3445 ≤ 35809302002481^3445*250000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113274093 250000000 35809302002481 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2022661997/5000000000 : ℝ)^4469 ≤ (30911720424169/100000000000000 : ℝ)^3445 := by
    have hnat : (2022661997 : ℕ)^4469*100000000000000^3445 ≤ 30911720424169^3445*5000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2022661997 5000000000 30911720424169 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(428210287/1000000000 : ℝ), (113274093/250000000 : ℝ), (2022661997/5000000000 : ℝ)] ![(8319744388419/25000000000000 : ℝ), (35809302002481/100000000000000 : ℝ), (30911720424169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(428210287/1000000000 : ℝ)|^4469 ≤ (8319744388419/25000000000000 : ℝ)^3445
        have hw : |(428210287/1000000000 : ℝ)|=(428210287/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(113274093/250000000 : ℝ)|^4469 ≤ (35809302002481/100000000000000 : ℝ)^3445
        have hw : |(113274093/250000000 : ℝ)|=(113274093/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2022661997/5000000000 : ℝ)|^4469 ≤ (30911720424169/100000000000000 : ℝ)^3445
        have hw : |(2022661997/5000000000 : ℝ)|=(2022661997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1486_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161305179/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7739/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1081/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (10811/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15477/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7739/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1081/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7739/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1081/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7739/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1081/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7739/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1081/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7739/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1081/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7739/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1081/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1081/10000 : ℝ) ^ (4467/1024 : ℝ) ≤ (6098925042514063/100000000000000000000 : ℝ) := by
    have hpowers : (1081/10000 : ℝ)^4467 ≤ (6098925042514063/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1081 : ℕ)^4467*100000000000000000000^1024 ≤ 6098925042514063^1024*10000^4467 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1081 10000 6098925042514063 100000000000000000000 4467 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1081/10000 : ℝ)) (X := (6098925042514063/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4467 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7739/50000 : ℝ) ^ (4467/1024 : ℝ) ≤ (14596853953932899/50000000000000000000 : ℝ) := by
    have hpowers : (7739/50000 : ℝ)^4467 ≤ (14596853953932899/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7739 : ℕ)^4467*50000000000000000000^1024 ≤ 14596853953932899^1024*50000^4467 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7739 50000 14596853953932899 50000000000000000000 4467 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7739/50000 : ℝ)) (X := (14596853953932899/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4467 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006098925042514063/50000000000000000000 : ℝ) ≤ (2500069901563509/2500000000000000 : ℝ) ^ (4467/1024 : ℝ) := by
    have hpowers : (50006098925042514063/50000000000000000000 : ℝ)^1024 ≤ (2500069901563509/2500000000000000 : ℝ)^4467 := by
      have hnat : (50006098925042514063 : ℕ)^1024*2500000000000000^4467 ≤ 2500069901563509^4467*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006098925042514063 50000000000000000000 2500069901563509 2500000000000000 1024 4467 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500069901563509/2500000000000000 : ℝ)) (X := (50006098925042514063/50000000000000000000 : ℝ)) (by norm_num) 4467 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100035292632950379861/100000000000000000000 : ℝ) ≤ (5000404463194109/5000000000000000 : ℝ) ^ (4467/1024 : ℝ) := by
    have hpowers : (100035292632950379861/100000000000000000000 : ℝ)^1024 ≤ (5000404463194109/5000000000000000 : ℝ)^4467 := by
      have hnat : (100035292632950379861 : ℕ)^1024*5000000000000000^4467 ≤ 5000404463194109^4467*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100035292632950379861 100000000000000000000 5000404463194109 5000000000000000 1024 4467 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000404463194109/5000000000000000 : ℝ)) (X := (100035292632950379861/100000000000000000000 : ℝ)) (by norm_num) 4467 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014596853953932899/25000000000000000000 : ℝ) ≤ (12501672808153/12500000000000 : ℝ) ^ (4467/1024 : ℝ) := by
    have hpowers : (25014596853953932899/25000000000000000000 : ℝ)^1024 ≤ (12501672808153/12500000000000 : ℝ)^4467 := by
      have hnat : (25014596853953932899 : ℕ)^1024*12500000000000^4467 ≤ 12501672808153^4467*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014596853953932899 25000000000000000000 12501672808153 12500000000000 1024 4467 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12501672808153/12500000000000 : ℝ)) (X := (25014596853953932899/25000000000000000000 : ℝ)) (by norm_num) 4467 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6098925042514063/100000000000000000000 : ℝ) ≤ ((5833732662586603151/5835000000000000000 : ℝ)+2*(264660067091/233400000000000 : ℝ)*(1081/10000 : ℝ))^(4467/1024 : ℝ) := by
    rw [show (5833732662586603151/5835000000000000000 : ℝ)+2*(264660067091/233400000000000 : ℝ)*(1081/10000 : ℝ)=(2500069901563509/2500000000000000 : ℝ) by norm_num, show 1+2*(6098925042514063/100000000000000000000 : ℝ)=(50006098925042514063/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14596853953932899/50000000000000000000 : ℝ)+(6098925042514063/100000000000000000000 : ℝ) ≤ ((5833732662586603151/5835000000000000000 : ℝ)+(264660067091/233400000000000 : ℝ)*((7739/50000 : ℝ)+(1081/10000 : ℝ)))^(4467/1024 : ℝ) := by
    rw [show (5833732662586603151/5835000000000000000 : ℝ)+(264660067091/233400000000000 : ℝ)*((7739/50000 : ℝ)+(1081/10000 : ℝ))=(5000404463194109/5000000000000000 : ℝ) by norm_num, show 1+(14596853953932899/50000000000000000000 : ℝ)+(6098925042514063/100000000000000000000 : ℝ)=(100035292632950379861/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14596853953932899/50000000000000000000 : ℝ) ≤ ((5833732662586603151/5835000000000000000 : ℝ)+2*(264660067091/233400000000000 : ℝ)*(7739/50000 : ℝ))^(4467/1024 : ℝ) := by
    rw [show (5833732662586603151/5835000000000000000 : ℝ)+2*(264660067091/233400000000000 : ℝ)*(7739/50000 : ℝ)=(12501672808153/12500000000000 : ℝ) by norm_num, show 1+2*(14596853953932899/50000000000000000000 : ℝ)=(25014596853953932899/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5833732662586603151/5835000000000000000 : ℝ)*(X 1 0+X 2 0)+(264660067091/233400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4467/1024 : ℝ)) (lo := (1081/10000 : ℝ)) (hi := (7739/50000 : ℝ)) (c := (5833732662586603151/5835000000000000000 : ℝ)) (alpha := (264660067091/233400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5833732662586603151/5835000000000000000 : ℝ)*(X 0 1+X 2 1)+(264660067091/233400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4467/1024 : ℝ)) (lo := (1081/10000 : ℝ)) (hi := (7739/50000 : ℝ)) (c := (5833732662586603151/5835000000000000000 : ℝ)) (alpha := (264660067091/233400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5833732662586603151/5835000000000000000 : ℝ)*(X 0 2+X 1 2)+(264660067091/233400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4467/1024 : ℝ)) (lo := (1081/10000 : ℝ)) (hi := (7739/50000 : ℝ)) (c := (5833732662586603151/5835000000000000000 : ℝ)) (alpha := (264660067091/233400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-190712333/1000000000 : ℝ)*X 0 0+(5436635093/10000000000 : ℝ)*X 0 1+(5216212203/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676497747/5000000000 : ℝ)*X 1 0+(-404014877/2000000000 : ℝ)*X 1 1+(1043242441/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338248873/2500000000 : ℝ)*X 2 0+(1043242441/2000000000 : ℝ)*X 2 1+(-2020074389/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4282035943/10000000000 : ℝ)*X 0 0+(1010698127/2500000000 : ℝ)*X 0 1+(4533476697/10000000000 : ℝ)*X 0 2+(4282035943/10000000000 : ℝ)*X 1 0+(1010698127/2500000000 : ℝ)*X 1 1+(4533476697/10000000000 : ℝ)*X 1 2+(4282035943/10000000000 : ℝ)*X 2 0+(1010698127/2500000000 : ℝ)*X 2 1+(4533476697/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-381430681/2000000000 : ℝ)*X 0 0+(5217341089/10000000000 : ℝ)*X 0 1+(5435497911/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323842679/2500000000 : ℝ)*X 1 0+(-900394343/5000000000 : ℝ)*X 1 1+(339718619/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295370711/10000000000 : ℝ)*X 2 0+(2717748957/5000000000 : ℝ)*X 2 1+(-1800788679/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((428210287/1000000000 : ℝ)*X 0 0+(113274093/250000000 : ℝ)*X 0 1+(2022661997/5000000000 : ℝ)*X 0 2+(428210287/1000000000 : ℝ)*X 1 0+(113274093/250000000 : ℝ)*X 1 1+(2022661997/5000000000 : ℝ)*X 1 2+(428210287/1000000000 : ℝ)*X 2 0+(113274093/250000000 : ℝ)*X 2 1+(2022661997/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (41017014446232036103203/3890000000000000000000000000 : ℝ) := by norm_num
    linear_combination (468965899/25000000000000 : ℝ)*(base19) + (218474927/12500000000000 : ℝ)*(base23) + (67645339/100000000000000 : ℝ)*(lower2) + (2653069/1000000000000 : ℝ)*(upper3) + (84361077/50000000000000 : ℝ)*(upper5) + (3287395347787681/100000000000000 : ℝ)*(major0) + (3287395347787681/100000000000000 : ℝ)*(major1) + (3287395347787681/100000000000000 : ℝ)*(major2) + (4536764082750139/100000000000000 : ℝ)*(sp0) + (1134197768035491/25000000000000 : ℝ)*(sp1) + (70887362503221/1562500000000 : ℝ)*(sp2) + (509495818308301/25000000000000 : ℝ)*(sp3) + (28865255421/100000000000000 : ℝ)*(sp4) + (14122862603/100000000000000 : ℝ)*(sp7) + (2037997396095807/100000000000000 : ℝ)*(f.failure) + (113419823700139/2500000000000 : ℝ)*(f.sum) + (4071752177719/11670000000000000000000000000 : ℝ)*base66 + (4740832230495142169/583500000000000000000000000000000 : ℝ)*base68 + (3418151588850142169/583500000000000000000000000000000 : ℝ)*base70 + (6961136561669857831/583500000000000000000000000000000 : ℝ)*base71 + (15476680322869/11670000000000000000000000000 : ℝ)*base74 + (2457227269337857831/583500000000000000000000000000000 : ℝ)*base75 + (3412060460897857831/583500000000000000000000000000000 : ℝ)*base77 + (508978713849142169/583500000000000000000000000000000 : ℝ)*base80 + (24826578149209/11670000000000000000000000000 : ℝ)*base82 + (50715547/10000000000000000000000 : ℝ)*base90 + (50715547/10000000000000000000000 : ℝ)*base92 + (50715547/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (771753953439635635387956549/97250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (258818463/20000000000000 : ℝ)*(base19) + (697868023/50000000000000 : ℝ)*(base23) + (424705737/100000000000000 : ℝ)*(lower1) + (162774293/100000000000000 : ℝ)*(upper3) + (46313211/100000000000000 : ℝ)*(lower4) + (38586959/25000000000000 : ℝ)*(upper5) + (3321484495854699/100000000000000 : ℝ)*(major0) + (3321484495854699/100000000000000 : ℝ)*(major1) + (3321484495854699/100000000000000 : ℝ)*(major2) + (1701147227/100000000000000 : ℝ)*(sp2) + (1145959501468149/25000000000000 : ℝ)*(sp4) + (4583836711780281/100000000000000 : ℝ)*(sp5) + (1145958727247331/25000000000000 : ℝ)*(sp6) + (2059130721311/100000000000 : ℝ)*(sp7) + (2059130721311/100000000000 : ℝ)*(f.failure) + (1145959501468149/25000000000000 : ℝ)*(f.sum) + (11771798741597/3890000000000000000000000000 : ℝ)*base66 + (9524984634679072817/194500000000000000000000000000000 : ℝ)*base68 + (644435434436927183/194500000000000000000000000000000 : ℝ)*base69 + (14903260542243072817/194500000000000000000000000000000 : ℝ)*base72 + (448936950057/3890000000000000000000000000 : ℝ)*base74 + (16555724983210927183/194500000000000000000000000000000 : ℝ)*base75 + (1686390148957072817/194500000000000000000000000000000 : ℝ)*base78 + (1748812127630572817/194500000000000000000000000000000 : ℝ)*base80 + (5777390746687/3890000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (69669/10000000000000000000 : ℝ)*base89 + (69669/10000000000000000000 : ℝ)*base91 + (69669/10000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1486_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161305179/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7739/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1081/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10811/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15477/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1486_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1486_box_0 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1688722283/10000000000 : ℝ)*x 0 + (5405650259/10000000000 : ℝ)*x 1 + (54056507/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1688722283/10000000000 : ℝ)^4469 ≤ (1990608254069/20000000000000 : ℝ)^3445 := by
    have hnat : (1688722283 : ℕ)^4469*20000000000000^3445 ≤ 1990608254069^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1688722283 10000000000 1990608254069 20000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5405650259/10000000000 : ℝ)^4469 ≤ (9004695394947/20000000000000 : ℝ)^3445 := by
    have hnat : (5405650259 : ℕ)^4469*20000000000000^3445 ≤ 9004695394947^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405650259 10000000000 9004695394947 20000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54056507/100000000 : ℝ)^4469 ≤ (45023481739603/100000000000000 : ℝ)^3445 := by
    have hnat : (54056507 : ℕ)^4469*100000000000000^3445 ≤ 45023481739603^3445*100000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54056507 100000000 45023481739603 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1688722283/10000000000 : ℝ), (5405650259/10000000000 : ℝ), (54056507/100000000 : ℝ)] ![(1990608254069/20000000000000 : ℝ), (9004695394947/20000000000000 : ℝ), (45023481739603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1688722283/10000000000 : ℝ)|^4469 ≤ (1990608254069/20000000000000 : ℝ)^3445
        have hw : |(-1688722283/10000000000 : ℝ)|=(1688722283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5405650259/10000000000 : ℝ)|^4469 ≤ (9004695394947/20000000000000 : ℝ)^3445
        have hw : |(5405650259/10000000000 : ℝ)|=(5405650259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(54056507/100000000 : ℝ)|^4469 ≤ (45023481739603/100000000000000 : ℝ)^3445
        have hw : |(54056507/100000000 : ℝ)|=(54056507/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_box_1 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2635177169/5000000000 : ℝ)*x 0 + (-117261677/625000000 : ℝ)*x 1 + (5405650523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2635177169/5000000000 : ℝ)^4469 ≤ (43567116727101/100000000000000 : ℝ)^3445 := by
    have hnat : (2635177169 : ℕ)^4469*100000000000000^3445 ≤ 43567116727101^3445*5000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635177169 5000000000 43567116727101 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (117261677/625000000 : ℝ)^4469 ≤ (5704701715233/50000000000000 : ℝ)^3445 := by
    have hnat : (117261677 : ℕ)^4469*50000000000000^3445 ≤ 5704701715233^3445*625000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117261677 625000000 5704701715233 50000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5405650523/10000000000 : ℝ)^4469 ≤ (45023479827173/100000000000000 : ℝ)^3445 := by
    have hnat : (5405650523 : ℕ)^4469*100000000000000^3445 ≤ 45023479827173^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405650523 10000000000 45023479827173 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2635177169/5000000000 : ℝ), (-117261677/625000000 : ℝ), (5405650523/10000000000 : ℝ)] ![(43567116727101/100000000000000 : ℝ), (5704701715233/50000000000000 : ℝ), (45023479827173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2635177169/5000000000 : ℝ)|^4469 ≤ (43567116727101/100000000000000 : ℝ)^3445
        have hw : |(2635177169/5000000000 : ℝ)|=(2635177169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-117261677/625000000 : ℝ)|^4469 ≤ (5704701715233/50000000000000 : ℝ)^3445
        have hw : |(-117261677/625000000 : ℝ)|=(117261677/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5405650523/10000000000 : ℝ)|^4469 ≤ (45023479827173/100000000000000 : ℝ)^3445
        have hw : |(5405650523/10000000000 : ℝ)|=(5405650523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_box_2 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5270354871/10000000000 : ℝ)*x 0 + (270282509/500000000 : ℝ)*x 1 + (-1876186577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5270354871/10000000000 : ℝ)^4469 ≤ (21783561221387/50000000000000 : ℝ)^3445 := by
    have hnat : (5270354871 : ℕ)^4469*50000000000000^3445 ≤ 21783561221387^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5270354871 10000000000 21783561221387 50000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270282509/500000000 : ℝ)^4469 ≤ (9004695224233/20000000000000 : ℝ)^3445 := by
    have hnat : (270282509 : ℕ)^4469*20000000000000^3445 ≤ 9004695224233^3445*500000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270282509 500000000 9004695224233 20000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1876186577/10000000000 : ℝ)^4469 ≤ (2852350354709/25000000000000 : ℝ)^3445 := by
    have hnat : (1876186577 : ℕ)^4469*25000000000000^3445 ≤ 2852350354709^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1876186577 10000000000 2852350354709 25000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5270354871/10000000000 : ℝ), (270282509/500000000 : ℝ), (-1876186577/10000000000 : ℝ)] ![(21783561221387/50000000000000 : ℝ), (9004695224233/20000000000000 : ℝ), (2852350354709/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5270354871/10000000000 : ℝ)|^4469 ≤ (21783561221387/50000000000000 : ℝ)^3445
        have hw : |(5270354871/10000000000 : ℝ)|=(5270354871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270282509/500000000 : ℝ)|^4469 ≤ (9004695224233/20000000000000 : ℝ)^3445
        have hw : |(270282509/500000000 : ℝ)|=(270282509/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1876186577/10000000000 : ℝ)|^4469 ≤ (2852350354709/25000000000000 : ℝ)^3445
        have hw : |(-1876186577/10000000000 : ℝ)|=(1876186577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_box_3 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2243169767/5000000000 : ℝ)*x 0 + (837408043/2000000000 : ℝ)*x 1 + (2093520483/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2243169767/5000000000 : ℝ)^4469 ≤ (35352467310399/100000000000000 : ℝ)^3445 := by
    have hnat : (2243169767 : ℕ)^4469*100000000000000^3445 ≤ 35352467310399^3445*5000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243169767 5000000000 35352467310399 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (837408043/2000000000 : ℝ)^4469 ≤ (32323762577533/100000000000000 : ℝ)^3445 := by
    have hnat : (837408043 : ℕ)^4469*100000000000000^3445 ≤ 32323762577533^3445*2000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      837408043 2000000000 32323762577533 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2093520483/5000000000 : ℝ)^4469 ≤ (32323770098537/100000000000000 : ℝ)^3445 := by
    have hnat : (2093520483 : ℕ)^4469*100000000000000^3445 ≤ 32323770098537^3445*5000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093520483 5000000000 32323770098537 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2243169767/5000000000 : ℝ), (837408043/2000000000 : ℝ), (2093520483/5000000000 : ℝ)] ![(35352467310399/100000000000000 : ℝ), (32323762577533/100000000000000 : ℝ), (32323770098537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2243169767/5000000000 : ℝ)|^4469 ≤ (35352467310399/100000000000000 : ℝ)^3445
        have hw : |(2243169767/5000000000 : ℝ)|=(2243169767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(837408043/2000000000 : ℝ)|^4469 ≤ (32323762577533/100000000000000 : ℝ)^3445
        have hw : |(837408043/2000000000 : ℝ)|=(837408043/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2093520483/5000000000 : ℝ)|^4469 ≤ (32323770098537/100000000000000 : ℝ)^3445
        have hw : |(2093520483/5000000000 : ℝ)|=(2093520483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_box_4 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1065492767/5000000000 : ℝ)*x 0 + (5242681727/10000000000 : ℝ)*x 1 + (2621341209/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1065492767/5000000000 : ℝ)^4469 ≤ (1682349349979/12500000000000 : ℝ)^3445 := by
    have hnat : (1065492767 : ℕ)^4469*12500000000000^3445 ≤ 1682349349979^3445*5000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065492767 5000000000 1682349349979 12500000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242681727/10000000000 : ℝ)^4469 ≤ (21635299447017/50000000000000 : ℝ)^3445 := by
    have hnat : (5242681727 : ℕ)^4469*50000000000000^3445 ≤ 21635299447017^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242681727 10000000000 21635299447017 50000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621341209/5000000000 : ℝ)^4469 ≤ (43270606292447/100000000000000 : ℝ)^3445 := by
    have hnat : (2621341209 : ℕ)^4469*100000000000000^3445 ≤ 43270606292447^3445*5000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621341209 5000000000 43270606292447 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1065492767/5000000000 : ℝ), (5242681727/10000000000 : ℝ), (2621341209/5000000000 : ℝ)] ![(1682349349979/12500000000000 : ℝ), (21635299447017/50000000000000 : ℝ), (43270606292447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1065492767/5000000000 : ℝ)|^4469 ≤ (1682349349979/12500000000000 : ℝ)^3445
        have hw : |(-1065492767/5000000000 : ℝ)|=(1065492767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242681727/10000000000 : ℝ)|^4469 ≤ (21635299447017/50000000000000 : ℝ)^3445
        have hw : |(5242681727/10000000000 : ℝ)|=(5242681727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621341209/5000000000 : ℝ)|^4469 ≤ (43270606292447/100000000000000 : ℝ)^3445
        have hw : |(2621341209/5000000000 : ℝ)|=(2621341209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_box_5 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (336502933/625000000 : ℝ)*x 0 + (-1942994187/10000000000 : ℝ)*x 1 + (1310670589/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (336502933/625000000 : ℝ)^4469 ≤ (22395099250521/50000000000000 : ℝ)^3445 := by
    have hnat : (336502933 : ℕ)^4469*50000000000000^3445 ≤ 22395099250521^3445*625000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336502933 625000000 22395099250521 50000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1942994187/10000000000 : ℝ)^4469 ≤ (477567834339/4000000000000 : ℝ)^3445 := by
    have hnat : (1942994187 : ℕ)^4469*4000000000000^3445 ≤ 477567834339^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1942994187 10000000000 477567834339 4000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310670589/2500000000 : ℝ)^4469 ≤ (346164845029/800000000000 : ℝ)^3445 := by
    have hnat : (1310670589 : ℕ)^4469*800000000000^3445 ≤ 346164845029^3445*2500000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310670589 2500000000 346164845029 800000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(336502933/625000000 : ℝ), (-1942994187/10000000000 : ℝ), (1310670589/2500000000 : ℝ)] ![(22395099250521/50000000000000 : ℝ), (477567834339/4000000000000 : ℝ), (346164845029/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(336502933/625000000 : ℝ)|^4469 ≤ (22395099250521/50000000000000 : ℝ)^3445
        have hw : |(336502933/625000000 : ℝ)|=(336502933/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1942994187/10000000000 : ℝ)|^4469 ≤ (477567834339/4000000000000 : ℝ)^3445
        have hw : |(-1942994187/10000000000 : ℝ)|=(1942994187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310670589/2500000000 : ℝ)|^4469 ≤ (346164845029/800000000000 : ℝ)^3445
        have hw : |(1310670589/2500000000 : ℝ)|=(1310670589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_box_6 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5384046909/10000000000 : ℝ)*x 0 + (2621341029/5000000000 : ℝ)*x 1 + (-1942994613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5384046909/10000000000 : ℝ)^4469 ≤ (44790198295997/100000000000000 : ℝ)^3445 := by
    have hnat : (5384046909 : ℕ)^4469*100000000000000^3445 ≤ 44790198295997^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384046909 10000000000 44790198295997 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621341029/5000000000 : ℝ)^4469 ≤ (5408825304749/12500000000000 : ℝ)^3445 := by
    have hnat : (2621341029 : ℕ)^4469*12500000000000^3445 ≤ 5408825304749^3445*5000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621341029 5000000000 5408825304749 12500000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1942994613/10000000000 : ℝ)^4469 ≤ (5969599627107/50000000000000 : ℝ)^3445 := by
    have hnat : (1942994613 : ℕ)^4469*50000000000000^3445 ≤ 5969599627107^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1942994613 10000000000 5969599627107 50000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5384046909/10000000000 : ℝ), (2621341029/5000000000 : ℝ), (-1942994613/10000000000 : ℝ)] ![(44790198295997/100000000000000 : ℝ), (5408825304749/12500000000000 : ℝ), (5969599627107/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5384046909/10000000000 : ℝ)|^4469 ≤ (44790198295997/100000000000000 : ℝ)^3445
        have hw : |(5384046909/10000000000 : ℝ)|=(5384046909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621341029/5000000000 : ℝ)|^4469 ≤ (5408825304749/12500000000000 : ℝ)^3445
        have hw : |(2621341029/5000000000 : ℝ)|=(2621341029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1942994613/10000000000 : ℝ)|^4469 ≤ (5969599627107/50000000000000 : ℝ)^3445
        have hw : |(-1942994613/10000000000 : ℝ)|=(1942994613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_box_7 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2037721269/5000000000 : ℝ)*x 0 + (878470249/2000000000 : ℝ)*x 1 + (4392351301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2037721269/5000000000 : ℝ)^4469 ≤ (31210605634679/100000000000000 : ℝ)^3445 := by
    have hnat : (2037721269 : ℕ)^4469*100000000000000^3445 ≤ 31210605634679^3445*5000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2037721269 5000000000 31210605634679 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (878470249/2000000000 : ℝ)^4469 ≤ (34394696893873/100000000000000 : ℝ)^3445 := by
    have hnat : (878470249 : ℕ)^4469*100000000000000^3445 ≤ 34394696893873^3445*2000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      878470249 2000000000 34394696893873 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4392351301/10000000000 : ℝ)^4469 ≤ (34394697462731/100000000000000 : ℝ)^3445 := by
    have hnat : (4392351301 : ℕ)^4469*100000000000000^3445 ≤ 34394697462731^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4392351301 10000000000 34394697462731 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2037721269/5000000000 : ℝ), (878470249/2000000000 : ℝ), (4392351301/10000000000 : ℝ)] ![(31210605634679/100000000000000 : ℝ), (34394696893873/100000000000000 : ℝ), (34394697462731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2037721269/5000000000 : ℝ)|^4469 ≤ (31210605634679/100000000000000 : ℝ)^3445
        have hw : |(2037721269/5000000000 : ℝ)|=(2037721269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(878470249/2000000000 : ℝ)|^4469 ≤ (34394696893873/100000000000000 : ℝ)^3445
        have hw : |(878470249/2000000000 : ℝ)|=(878470249/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4392351301/10000000000 : ℝ)|^4469 ≤ (34394697462731/100000000000000 : ℝ)^3445
        have hw : |(4392351301/10000000000 : ℝ)|=(4392351301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_box_8 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2037671823/10000000000 : ℝ)*x 0 + (128220107/250000000 : ℝ)*x 1 + (5426179483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2037671823/10000000000 : ℝ)^4469 ≤ (12699296325037/100000000000000 : ℝ)^3445 := by
    have hnat : (2037671823 : ℕ)^4469*100000000000000^3445 ≤ 12699296325037^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2037671823 10000000000 12699296325037 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (128220107/250000000 : ℝ)^4469 ≤ (5256911218031/12500000000000 : ℝ)^3445 := by
    have hnat : (128220107 : ℕ)^4469*12500000000000^3445 ≤ 5256911218031^3445*250000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128220107 250000000 5256911218031 12500000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5426179483/10000000000 : ℝ)^4469 ≤ (9049082782371/20000000000000 : ℝ)^3445 := by
    have hnat : (5426179483 : ℕ)^4469*20000000000000^3445 ≤ 9049082782371^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426179483 10000000000 9049082782371 20000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2037671823/10000000000 : ℝ), (128220107/250000000 : ℝ), (5426179483/10000000000 : ℝ)] ![(12699296325037/100000000000000 : ℝ), (5256911218031/12500000000000 : ℝ), (9049082782371/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2037671823/10000000000 : ℝ)|^4469 ≤ (12699296325037/100000000000000 : ℝ)^3445
        have hw : |(-2037671823/10000000000 : ℝ)|=(2037671823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(128220107/250000000 : ℝ)|^4469 ≤ (5256911218031/12500000000000 : ℝ)^3445
        have hw : |(128220107/250000000 : ℝ)|=(128220107/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5426179483/10000000000 : ℝ)|^4469 ≤ (9049082782371/20000000000000 : ℝ)^3445
        have hw : |(5426179483/10000000000 : ℝ)|=(5426179483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_box_9 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256025607/10000000000 : ℝ)*x 0 + (-466879553/2500000000 : ℝ)*x 1 + (5426179181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256025607/10000000000 : ℝ)^4469 ≤ (43413523440747/100000000000000 : ℝ)^3445 := by
    have hnat : (5256025607 : ℕ)^4469*100000000000000^3445 ≤ 43413523440747^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256025607 10000000000 43413523440747 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (466879553/2500000000 : ℝ)^4469 ≤ (2835266474247/25000000000000 : ℝ)^3445 := by
    have hnat : (466879553 : ℕ)^4469*25000000000000^3445 ≤ 2835266474247^3445*2500000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      466879553 2500000000 2835266474247 25000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5426179181/10000000000 : ℝ)^4469 ≤ (1131135266129/2500000000000 : ℝ)^3445 := by
    have hnat : (5426179181 : ℕ)^4469*2500000000000^3445 ≤ 1131135266129^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426179181 10000000000 1131135266129 2500000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256025607/10000000000 : ℝ), (-466879553/2500000000 : ℝ), (5426179181/10000000000 : ℝ)] ![(43413523440747/100000000000000 : ℝ), (2835266474247/25000000000000 : ℝ), (1131135266129/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256025607/10000000000 : ℝ)|^4469 ≤ (43413523440747/100000000000000 : ℝ)^3445
        have hw : |(5256025607/10000000000 : ℝ)|=(5256025607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-466879553/2500000000 : ℝ)|^4469 ≤ (2835266474247/25000000000000 : ℝ)^3445
        have hw : |(-466879553/2500000000 : ℝ)|=(466879553/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5426179181/10000000000 : ℝ)|^4469 ≤ (1131135266129/2500000000000 : ℝ)^3445
        have hw : |(5426179181/10000000000 : ℝ)|=(5426179181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_box_10 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256025047/10000000000 : ℝ)*x 0 + (2713089979/5000000000 : ℝ)*x 1 + (-1867517907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256025047/10000000000 : ℝ)^4469 ≤ (10853379360099/25000000000000 : ℝ)^3445 := by
    have hnat : (5256025047 : ℕ)^4469*25000000000000^3445 ≤ 10853379360099^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256025047 10000000000 10853379360099 25000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2713089979/5000000000 : ℝ)^4469 ≤ (45245419049867/100000000000000 : ℝ)^3445 := by
    have hnat : (2713089979 : ℕ)^4469*100000000000000^3445 ≤ 45245419049867^3445*5000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713089979 5000000000 45245419049867 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1867517907/10000000000 : ℝ)^4469 ≤ (1134106349423/10000000000000 : ℝ)^3445 := by
    have hnat : (1867517907 : ℕ)^4469*10000000000000^3445 ≤ 1134106349423^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1867517907 10000000000 1134106349423 10000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256025047/10000000000 : ℝ), (2713089979/5000000000 : ℝ), (-1867517907/10000000000 : ℝ)] ![(10853379360099/25000000000000 : ℝ), (45245419049867/100000000000000 : ℝ), (1134106349423/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256025047/10000000000 : ℝ)|^4469 ≤ (10853379360099/25000000000000 : ℝ)^3445
        have hw : |(5256025047/10000000000 : ℝ)|=(5256025047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2713089979/5000000000 : ℝ)|^4469 ≤ (45245419049867/100000000000000 : ℝ)^3445
        have hw : |(2713089979/5000000000 : ℝ)|=(2713089979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1867517907/10000000000 : ℝ)|^4469 ≤ (1134106349423/10000000000000 : ℝ)^3445
        have hw : |(-1867517907/10000000000 : ℝ)|=(1867517907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_box_11 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (907389017/2000000000 : ℝ)*x 0 + (4161146481/10000000000 : ℝ)*x 1 + (4161145829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (907389017/2000000000 : ℝ)^4469 ≤ (35870637497799/100000000000000 : ℝ)^3445 := by
    have hnat : (907389017 : ℕ)^4469*100000000000000^3445 ≤ 35870637497799^3445*2000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      907389017 2000000000 35870637497799 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4161146481/10000000000 : ℝ)^4469 ≤ (40080855631/125000000000 : ℝ)^3445 := by
    have hnat : (4161146481 : ℕ)^4469*125000000000^3445 ≤ 40080855631^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4161146481 10000000000 40080855631 125000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4161145829/10000000000 : ℝ)^4469 ≤ (8016169496819/25000000000000 : ℝ)^3445 := by
    have hnat : (4161145829 : ℕ)^4469*25000000000000^3445 ≤ 8016169496819^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4161145829 10000000000 8016169496819 25000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(907389017/2000000000 : ℝ), (4161146481/10000000000 : ℝ), (4161145829/10000000000 : ℝ)] ![(35870637497799/100000000000000 : ℝ), (40080855631/125000000000 : ℝ), (8016169496819/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(907389017/2000000000 : ℝ)|^4469 ≤ (35870637497799/100000000000000 : ℝ)^3445
        have hw : |(907389017/2000000000 : ℝ)|=(907389017/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4161146481/10000000000 : ℝ)|^4469 ≤ (40080855631/125000000000 : ℝ)^3445
        have hw : |(4161146481/10000000000 : ℝ)|=(4161146481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4161145829/10000000000 : ℝ)|^4469 ≤ (8016169496819/25000000000000 : ℝ)^3445
        have hw : |(4161145829/10000000000 : ℝ)|=(4161145829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_box_12 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-89106591/500000000 : ℝ)*x 0 + (5515774049/10000000000 : ℝ)*x 1 + (5227681511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (89106591/500000000 : ℝ)^4469 ≤ (5336510883107/50000000000000 : ℝ)^3445 := by
    have hnat : (89106591 : ℕ)^4469*50000000000000^3445 ≤ 5336510883107^3445*500000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89106591 500000000 5336510883107 50000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5515774049/10000000000 : ℝ)^4469 ≤ (23108457804197/50000000000000 : ℝ)^3445 := by
    have hnat : (5515774049 : ℕ)^4469*50000000000000^3445 ≤ 23108457804197^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5515774049 10000000000 23108457804197 50000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5227681511/10000000000 : ℝ)^4469 ≤ (8622012521307/20000000000000 : ℝ)^3445 := by
    have hnat : (5227681511 : ℕ)^4469*20000000000000^3445 ≤ 8622012521307^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227681511 10000000000 8622012521307 20000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-89106591/500000000 : ℝ), (5515774049/10000000000 : ℝ), (5227681511/10000000000 : ℝ)] ![(5336510883107/50000000000000 : ℝ), (23108457804197/50000000000000 : ℝ), (8622012521307/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-89106591/500000000 : ℝ)|^4469 ≤ (5336510883107/50000000000000 : ℝ)^3445
        have hw : |(-89106591/500000000 : ℝ)|=(89106591/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5515774049/10000000000 : ℝ)|^4469 ≤ (23108457804197/50000000000000 : ℝ)^3445
        have hw : |(5515774049/10000000000 : ℝ)|=(5515774049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5227681511/10000000000 : ℝ)|^4469 ≤ (8622012521307/20000000000000 : ℝ)^3445
        have hw : |(5227681511/10000000000 : ℝ)|=(5227681511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_box_13 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1078902149/2000000000 : ℝ)*x 0 + (-243620163/1250000000 : ℝ)*x 1 + (326730093/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078902149/2000000000 : ℝ)^4469 ≤ (11225788721351/25000000000000 : ℝ)^3445 := by
    have hnat : (1078902149 : ℕ)^4469*25000000000000^3445 ≤ 11225788721351^3445*2000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078902149 2000000000 11225788721351 25000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (243620163/1250000000 : ℝ)^4469 ≤ (1198678274537/10000000000000 : ℝ)^3445 := by
    have hnat : (243620163 : ℕ)^4469*10000000000000^3445 ≤ 1198678274537^3445*1250000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      243620163 1250000000 1198678274537 10000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (326730093/625000000 : ℝ)^4469 ≤ (43110062360487/100000000000000 : ℝ)^3445 := by
    have hnat : (326730093 : ℕ)^4469*100000000000000^3445 ≤ 43110062360487^3445*625000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326730093 625000000 43110062360487 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1078902149/2000000000 : ℝ), (-243620163/1250000000 : ℝ), (326730093/625000000 : ℝ)] ![(11225788721351/25000000000000 : ℝ), (1198678274537/10000000000000 : ℝ), (43110062360487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1078902149/2000000000 : ℝ)|^4469 ≤ (11225788721351/25000000000000 : ℝ)^3445
        have hw : |(1078902149/2000000000 : ℝ)|=(1078902149/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-243620163/1250000000 : ℝ)|^4469 ≤ (1198678274537/10000000000000 : ℝ)^3445
        have hw : |(-243620163/1250000000 : ℝ)|=(243620163/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(326730093/625000000 : ℝ)|^4469 ≤ (43110062360487/100000000000000 : ℝ)^3445
        have hw : |(326730093/625000000 : ℝ)|=(326730093/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_box_14 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1078902163/2000000000 : ℝ)*x 0 + (1045536319/2000000000 : ℝ)*x 1 + (-389792213/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078902163/2000000000 : ℝ)^4469 ≤ (11225788910317/25000000000000 : ℝ)^3445 := by
    have hnat : (1078902163 : ℕ)^4469*25000000000000^3445 ≤ 11225788910317^3445*2000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078902163 2000000000 11225788910317 25000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1045536319/2000000000 : ℝ)^4469 ≤ (21555031752571/50000000000000 : ℝ)^3445 := by
    have hnat : (1045536319 : ℕ)^4469*50000000000000^3445 ≤ 21555031752571^3445*2000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045536319 2000000000 21555031752571 50000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (389792213/2000000000 : ℝ)^4469 ≤ (11986780838511/100000000000000 : ℝ)^3445 := by
    have hnat : (389792213 : ℕ)^4469*100000000000000^3445 ≤ 11986780838511^3445*2000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389792213 2000000000 11986780838511 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1078902163/2000000000 : ℝ), (1045536319/2000000000 : ℝ), (-389792213/2000000000 : ℝ)] ![(11225788910317/25000000000000 : ℝ), (21555031752571/50000000000000 : ℝ), (11986780838511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1078902163/2000000000 : ℝ)|^4469 ≤ (11225788910317/25000000000000 : ℝ)^3445
        have hw : |(1078902163/2000000000 : ℝ)|=(1078902163/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1045536319/2000000000 : ℝ)|^4469 ≤ (21555031752571/50000000000000 : ℝ)^3445
        have hw : |(1045536319/2000000000 : ℝ)|=(1045536319/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-389792213/2000000000 : ℝ)|^4469 ≤ (11986780838511/100000000000000 : ℝ)^3445
        have hw : |(-389792213/2000000000 : ℝ)|=(389792213/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_box_15 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4036761579/10000000000 : ℝ)*x 0 + (2205613861/5000000000 : ℝ)*x 1 + (2205613361/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4036761579/10000000000 : ℝ)^4469 ≤ (15413435337701/50000000000000 : ℝ)^3445 := by
    have hnat : (4036761579 : ℕ)^4469*50000000000000^3445 ≤ 15413435337701^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4036761579 10000000000 15413435337701 50000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2205613861/5000000000 : ℝ)^4469 ≤ (4323321217499/12500000000000 : ℝ)^3445 := by
    have hnat : (2205613861 : ℕ)^4469*12500000000000^3445 ≤ 4323321217499^3445*5000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205613861 5000000000 4323321217499 12500000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2205613361/5000000000 : ℝ)^4469 ≤ (1080829986527/3125000000000 : ℝ)^3445 := by
    have hnat : (2205613361 : ℕ)^4469*3125000000000^3445 ≤ 1080829986527^3445*5000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205613361 5000000000 1080829986527 3125000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4036761579/10000000000 : ℝ), (2205613861/5000000000 : ℝ), (2205613361/5000000000 : ℝ)] ![(15413435337701/50000000000000 : ℝ), (4323321217499/12500000000000 : ℝ), (1080829986527/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4036761579/10000000000 : ℝ)|^4469 ≤ (15413435337701/50000000000000 : ℝ)^3445
        have hw : |(4036761579/10000000000 : ℝ)|=(4036761579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2205613861/5000000000 : ℝ)|^4469 ≤ (4323321217499/12500000000000 : ℝ)^3445
        have hw : |(2205613861/5000000000 : ℝ)|=(2205613861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2205613361/5000000000 : ℝ)|^4469 ≤ (1080829986527/3125000000000 : ℝ)^3445
        have hw : |(2205613361/5000000000 : ℝ)|=(2205613361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1486_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161305179/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15477/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10811/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(15927/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29253/50000 : ℝ) ∧ (16007/20000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (85833/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15477/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10811/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15477/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10811/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15477/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10811/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15477/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10811/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15477/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10811/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15477/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10811/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10811/100000 : ℝ) ^ (4467/1024 : ℝ) ≤ (3050693303274779/50000000000000000000 : ℝ) := by
    have hpowers : (10811/100000 : ℝ)^4467 ≤ (3050693303274779/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10811 : ℕ)^4467*50000000000000000000^1024 ≤ 3050693303274779^1024*100000^4467 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10811 100000 3050693303274779 50000000000000000000 4467 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10811/100000 : ℝ)) (X := (3050693303274779/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4467 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15477/100000 : ℝ) ^ (4467/1024 : ℝ) ≤ (29185480874841021/100000000000000000000 : ℝ) := by
    have hpowers : (15477/100000 : ℝ)^4467 ≤ (29185480874841021/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15477 : ℕ)^4467*100000000000000000000^1024 ≤ 29185480874841021^1024*100000^4467 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15477 100000 29185480874841021 100000000000000000000 4467 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15477/100000 : ℝ)) (X := (29185480874841021/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4467 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25003050693303274779/25000000000000000000 : ℝ) ≤ (10000279719099551/10000000000000000 : ℝ) ^ (4467/1024 : ℝ) := by
    have hpowers : (25003050693303274779/25000000000000000000 : ℝ)^1024 ≤ (10000279719099551/10000000000000000 : ℝ)^4467 := by
      have hnat : (25003050693303274779 : ℕ)^1024*10000000000000000^4467 ≤ 10000279719099551^4467*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003050693303274779 25000000000000000000 10000279719099551 10000000000000000 1024 4467 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000279719099551/10000000000000000 : ℝ)) (X := (25003050693303274779/25000000000000000000 : ℝ)) (by norm_num) 4467 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100035286867481390579/100000000000000000000 : ℝ) ≤ (10000808794258491/10000000000000000 : ℝ) ^ (4467/1024 : ℝ) := by
    have hpowers : (100035286867481390579/100000000000000000000 : ℝ)^1024 ≤ (10000808794258491/10000000000000000 : ℝ)^4467 := by
      have hnat : (100035286867481390579 : ℕ)^1024*10000000000000000^4467 ≤ 10000808794258491^4467*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100035286867481390579 100000000000000000000 10000808794258491 10000000000000000 1024 4467 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000808794258491/10000000000000000 : ℝ)) (X := (100035286867481390579/100000000000000000000 : ℝ)) (by norm_num) 4467 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029185480874841021/50000000000000000000 : ℝ) ≤ (10001337869417431/10000000000000000 : ℝ) ^ (4467/1024 : ℝ) := by
    have hpowers : (50029185480874841021/50000000000000000000 : ℝ)^1024 ≤ (10001337869417431/10000000000000000 : ℝ)^4467 := by
      have hnat : (50029185480874841021 : ℕ)^1024*10000000000000000^4467 ≤ 10001337869417431^4467*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029185480874841021 50000000000000000000 10001337869417431 10000000000000000 1024 4467 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001337869417431/10000000000000000 : ℝ)) (X := (50029185480874841021/50000000000000000000 : ℝ)) (by norm_num) 4467 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3050693303274779/50000000000000000000 : ℝ) ≤ ((23324932753115952143/23330000000000000000 : ℝ)+2*(26453757947/23330000000000 : ℝ)*(10811/100000 : ℝ))^(4467/1024 : ℝ) := by
    rw [show (23324932753115952143/23330000000000000000 : ℝ)+2*(26453757947/23330000000000 : ℝ)*(10811/100000 : ℝ)=(10000279719099551/10000000000000000 : ℝ) by norm_num, show 1+2*(3050693303274779/50000000000000000000 : ℝ)=(25003050693303274779/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29185480874841021/100000000000000000000 : ℝ)+(3050693303274779/50000000000000000000 : ℝ) ≤ ((23324932753115952143/23330000000000000000 : ℝ)+(26453757947/23330000000000 : ℝ)*((15477/100000 : ℝ)+(10811/100000 : ℝ)))^(4467/1024 : ℝ) := by
    rw [show (23324932753115952143/23330000000000000000 : ℝ)+(26453757947/23330000000000 : ℝ)*((15477/100000 : ℝ)+(10811/100000 : ℝ))=(10000808794258491/10000000000000000 : ℝ) by norm_num, show 1+(29185480874841021/100000000000000000000 : ℝ)+(3050693303274779/50000000000000000000 : ℝ)=(100035286867481390579/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29185480874841021/100000000000000000000 : ℝ) ≤ ((23324932753115952143/23330000000000000000 : ℝ)+2*(26453757947/23330000000000 : ℝ)*(15477/100000 : ℝ))^(4467/1024 : ℝ) := by
    rw [show (23324932753115952143/23330000000000000000 : ℝ)+2*(26453757947/23330000000000 : ℝ)*(15477/100000 : ℝ)=(10001337869417431/10000000000000000 : ℝ) by norm_num, show 1+2*(29185480874841021/100000000000000000000 : ℝ)=(50029185480874841021/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23324932753115952143/23330000000000000000 : ℝ)*(X 1 0+X 2 0)+(26453757947/23330000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4467/1024 : ℝ)) (lo := (10811/100000 : ℝ)) (hi := (15477/100000 : ℝ)) (c := (23324932753115952143/23330000000000000000 : ℝ)) (alpha := (26453757947/23330000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23324932753115952143/23330000000000000000 : ℝ)*(X 0 1+X 2 1)+(26453757947/23330000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4467/1024 : ℝ)) (lo := (10811/100000 : ℝ)) (hi := (15477/100000 : ℝ)) (c := (23324932753115952143/23330000000000000000 : ℝ)) (alpha := (26453757947/23330000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23324932753115952143/23330000000000000000 : ℝ)*(X 0 2+X 1 2)+(26453757947/23330000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4467/1024 : ℝ)) (lo := (10811/100000 : ℝ)) (hi := (15477/100000 : ℝ)) (c := (23324932753115952143/23330000000000000000 : ℝ)) (alpha := (26453757947/23330000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1688722283/10000000000 : ℝ)*X 0 0+(5405650259/10000000000 : ℝ)*X 0 1+(54056507/100000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2635177169/5000000000 : ℝ)*X 1 0+(-117261677/625000000 : ℝ)*X 1 1+(5405650523/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5270354871/10000000000 : ℝ)*X 2 0+(270282509/500000000 : ℝ)*X 2 1+(-1876186577/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2243169767/5000000000 : ℝ)*X 0 0+(837408043/2000000000 : ℝ)*X 0 1+(2093520483/5000000000 : ℝ)*X 0 2+(2243169767/5000000000 : ℝ)*X 1 0+(837408043/2000000000 : ℝ)*X 1 1+(2093520483/5000000000 : ℝ)*X 1 2+(2243169767/5000000000 : ℝ)*X 2 0+(837408043/2000000000 : ℝ)*X 2 1+(2093520483/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1065492767/5000000000 : ℝ)*X 0 0+(5242681727/10000000000 : ℝ)*X 0 1+(2621341209/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((336502933/625000000 : ℝ)*X 1 0+(-1942994187/10000000000 : ℝ)*X 1 1+(1310670589/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5384046909/10000000000 : ℝ)*X 2 0+(2621341029/5000000000 : ℝ)*X 2 1+(-1942994613/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2037721269/5000000000 : ℝ)*X 0 0+(878470249/2000000000 : ℝ)*X 0 1+(4392351301/10000000000 : ℝ)*X 0 2+(2037721269/5000000000 : ℝ)*X 1 0+(878470249/2000000000 : ℝ)*X 1 1+(4392351301/10000000000 : ℝ)*X 1 2+(2037721269/5000000000 : ℝ)*X 2 0+(878470249/2000000000 : ℝ)*X 2 1+(4392351301/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2037671823/10000000000 : ℝ)*X 0 0+(128220107/250000000 : ℝ)*X 0 1+(5426179483/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5256025607/10000000000 : ℝ)*X 1 0+(-466879553/2500000000 : ℝ)*X 1 1+(5426179181/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5256025047/10000000000 : ℝ)*X 2 0+(2713089979/5000000000 : ℝ)*X 2 1+(-1867517907/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((907389017/2000000000 : ℝ)*X 0 0+(4161146481/10000000000 : ℝ)*X 0 1+(4161145829/10000000000 : ℝ)*X 0 2+(907389017/2000000000 : ℝ)*X 1 0+(4161146481/10000000000 : ℝ)*X 1 1+(4161145829/10000000000 : ℝ)*X 1 2+(907389017/2000000000 : ℝ)*X 2 0+(4161146481/10000000000 : ℝ)*X 2 1+(4161145829/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-89106591/500000000 : ℝ)*X 0 0+(5515774049/10000000000 : ℝ)*X 0 1+(5227681511/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1078902149/2000000000 : ℝ)*X 1 0+(-243620163/1250000000 : ℝ)*X 1 1+(326730093/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1078902163/2000000000 : ℝ)*X 2 0+(1045536319/2000000000 : ℝ)*X 2 1+(-389792213/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4036761579/10000000000 : ℝ)*X 0 0+(2205613861/5000000000 : ℝ)*X 0 1+(2205613361/5000000000 : ℝ)*X 0 2+(4036761579/10000000000 : ℝ)*X 1 0+(2205613861/5000000000 : ℝ)*X 1 1+(2205613361/5000000000 : ℝ)*X 1 2+(4036761579/10000000000 : ℝ)*X 2 0+(2205613861/5000000000 : ℝ)*X 2 1+(2205613361/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-15927/25000 : ℝ) ≤ (-92891117784505986030329387603637/145812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3370651/4000000000000 : ℝ)*(upper1) + (13914097/10000000000000 : ℝ)*(lower4) + (3996991/10000000000000 : ℝ)*(upper5) + (546173026205153/25000000000000 : ℝ)*(major0) + (546173026205153/25000000000000 : ℝ)*(major1) + (546173026205153/25000000000000 : ℝ)*(major2) + (7120796727/100000000000000 : ℝ)*(sp2) + (554006211/25000000000000 : ℝ)*(sp3) + (1518114340020317/50000000000000 : ℝ)*(sp4) + (189761565925241/6250000000000 : ℝ)*(sp5) + (759057006258477/25000000000000 : ℝ)*(sp6) + (42324441777877/3125000000000 : ℝ)*(sp7) + (6465790001/100000000000000 : ℝ)*(sp12) + (2504551339/5000000000000 : ℝ)*(sp13) + (1354384352916909/100000000000000 : ℝ)*(f.failure) + (759058786457659/25000000000000 : ℝ)*(f.sum) + (1210948276589/291625000000000000000000000 : ℝ)*base65 + (5448172605131242879/583250000000000000000000000000000 : ℝ)*base67 + (3578518662713242879/583250000000000000000000000000000 : ℝ)*base69 + (4327570595421992879/583250000000000000000000000000000 : ℝ)*base71 + (1471354083361/583250000000000000000000000 : ℝ)*base73 + (2240256795799007121/583250000000000000000000000000000 : ℝ)*base76 + (5960208590848742879/583250000000000000000000000000000 : ℝ)*base77 + (6570692897260992879/583250000000000000000000000000000 : ℝ)*base79 + (6368079503377/2333000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (21628289/10000000000000000000000 : ℝ)*base90 + (21628289/10000000000000000000000 : ℝ)*base92 + (21628289/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (29253/50000 : ℝ) ≤ (34124900112282900517257351515151/58325000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2301729/6250000000000 : ℝ)*(lower1) + (1563433/1250000000000 : ℝ)*(lower3) + (34395953/50000000000000 : ℝ)*(upper4) + (2505149/3125000000000 : ℝ)*(upper5) + (112958209155673/5000000000000 : ℝ)*(major0) + (112958209155673/5000000000000 : ℝ)*(major1) + (112958209155673/5000000000000 : ℝ)*(major2) + (309827284830839/10000000000000 : ℝ)*(sp0) + (193641924897833/6250000000000 : ℝ)*(sp1) + (309822187789651/10000000000000 : ℝ)*(sp2) + (700275711763953/50000000000000 : ℝ)*(sp3) + (1024971531/50000000000000 : ℝ)*(sp5) + (273073033/20000000000000 : ℝ)*(sp7) + (1274260297/2500000000000 : ℝ)*(sp10) + (1400552788893071/100000000000000 : ℝ)*(f.failure) + (309827284830839/10000000000000 : ℝ)*(f.sum) + (740317511827/583250000000000000000000000 : ℝ)*base65 + (725221789860292761/116650000000000000000000000000000 : ℝ)*base68 + (1189501228949692761/116650000000000000000000000000000 : ℝ)*base70 + (1567544178281142761/116650000000000000000000000000000 : ℝ)*base72 + (3129340873563/466600000000000000000000000 : ℝ)*base73 + (1490564102356092761/116650000000000000000000000000000 : ℝ)*base76 + (1640934778911642761/116650000000000000000000000000000 : ℝ)*base78 + (1360800960029792761/116650000000000000000000000000000 : ℝ)*base80 + (1478006442717/2333000000000000000000000000 : ℝ)*base81 + (29514709/10000000000000000000000 : ℝ)*base89 + (29514709/10000000000000000000000 : ℝ)*base91 + (29514709/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (16007/20000 : ℝ) ≤ (933636677578354939074517438661997/1166500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (80373651/100000000000000 : ℝ)*(upper1) + (5302091/100000000000000 : ℝ)*(upper4) + (16729549/50000000000000 : ℝ)*(lower5) + (2456012709967007/100000000000000 : ℝ)*(major0) + (2456012709967007/100000000000000 : ℝ)*(major1) + (2456012709967007/100000000000000 : ℝ)*(major2) + (1797618823/100000000000000 : ℝ)*(sp1) + (136911894219/100000000000000 : ℝ)*(sp2) + (13841507299/100000000000000 : ℝ)*(sp3) + (1355440219/100000000000000 : ℝ)*(sp4) + (1681378642302631/50000000000000 : ℝ)*(sp8) + (3362756842426659/100000000000000 : ℝ)*(sp9) + (1681310864075631/50000000000000 : ℝ)*(sp10) + (380643448357427/25000000000000 : ℝ)*(sp11) + (95161727183563/6250000000000 : ℝ)*(f.failure) + (1681379320022741/50000000000000 : ℝ)*(f.sum) + (1905378355377/291625000000000000000000000 : ℝ)*base65 + (2139782752351946001/2333000000000000000000000000000000 : ℝ)*base67 + (1206255885832053999/2333000000000000000000000000000000 : ℝ)*base70 + (4347457195560946001/2333000000000000000000000000000000 : ℝ)*base71 + (12540910979721/2333000000000000000000000000 : ℝ)*base73 + (15367966275292053999/2333000000000000000000000000000000 : ℝ)*base76 + (10347725847852946001/2333000000000000000000000000000000 : ℝ)*base77 + (8469639057632946001/2333000000000000000000000000000000 : ℝ)*base79 + (5170456832181/2333000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (1822777/625000000000000000000 : ℝ)*base89 + (1822777/625000000000000000000 : ℝ)*base91 + (1822777/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-85833/100000 : ℝ) ≤ (-125151743527722214374046934535057/145812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (76980889/50000000000000 : ℝ)*(lower2) + (16915967/10000000000000 : ℝ)*(upper3) + (470769/2000000000000 : ℝ)*(upper5) + (311807516904867/12500000000000 : ℝ)*(major0) + (311807516904867/12500000000000 : ℝ)*(major1) + (311807516904867/12500000000000 : ℝ)*(major2) + (411775427/50000000000000 : ℝ)*(sp0) + (7991199443/6250000000000 : ℝ)*(sp5) + (3942594401/100000000000000 : ℝ)*(sp6) + (1643002157/4000000000000 : ℝ)*(sp7) + (867776700938857/25000000000000 : ℝ)*(sp12) + (1735489884057597/50000000000000 : ℝ)*(sp13) + (86777592117797/2500000000000 : ℝ)*(sp14) + (773190884047709/50000000000000 : ℝ)*(sp15) + (773211421574671/50000000000000 : ℝ)*(f.failure) + (1735553813653141/50000000000000 : ℝ)*(f.sum) + (2162804342603/1166500000000000000000000000 : ℝ)*base66 + (920394106621095019/291625000000000000000000000000000 : ℝ)*base68 + (3868119819864845019/291625000000000000000000000000000 : ℝ)*base70 + (2586686947817470019/291625000000000000000000000000000 : ℝ)*base72 + (604002323553/2333000000000000000000000000 : ℝ)*base74 + (2434252914094345019/291625000000000000000000000000000 : ℝ)*base76 + (731538510370654981/291625000000000000000000000000000 : ℝ)*base77 + (1028318011991404981/291625000000000000000000000000000 : ℝ)*base79 + (17290596957/3645312500000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (32478891/5000000000000000000000 : ℝ)*base90 + (32478891/5000000000000000000000 : ℝ)*base92 + (32478891/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1486_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161305179/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15477/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10811/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15927/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(29253/50000 : ℝ) else (16007/20000 : ℝ) ≤ X j i ∧ X j i ≤ (85833/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1486_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1486_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161305179/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7739/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1081/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15927/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(29253/50000 : ℝ) else (16007/20000 : ℝ) ≤ X j i ∧ X j i ≤ (85833/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1486_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1486_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161305179/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7739/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1081/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15927/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(29253/50000 : ℝ) else (16007/20000 : ℝ) ≤ X j i ∧ X j i ≤ (85833/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1486_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
