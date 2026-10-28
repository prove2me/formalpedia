-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1248_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:22:22.023201+00:00
-- url     : https://prove2.me/submissions/734b00a5-4413-4d9a-afcc-871c0d53a5a2

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
theorem support_rectangle_w1248_s6_0 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1058592331/5000000000 : ℝ)*x 0 + (539127257/1000000000 : ℝ)*x 1 + (1053423897/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058592331/5000000000 : ℝ)^8441 ≤ (12875535266659/100000000000000 : ℝ)^6393 := by
    have hnat : (1058592331 : ℕ)^8441*100000000000000^6393 ≤ 12875535266659^6393*5000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058592331 5000000000 12875535266659 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539127257/1000000000 : ℝ)^8441 ≤ (44232194942909/100000000000000 : ℝ)^6393 := by
    have hnat : (539127257 : ℕ)^8441*100000000000000^6393 ≤ 44232194942909^6393*1000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539127257 1000000000 44232194942909 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053423897/2000000000 : ℝ)^8441 ≤ (857845395637/2000000000000 : ℝ)^6393 := by
    have hnat : (1053423897 : ℕ)^8441*2000000000000^6393 ≤ 857845395637^6393*2000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053423897 2000000000 857845395637 2000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1058592331/5000000000 : ℝ), (539127257/1000000000 : ℝ), (1053423897/2000000000 : ℝ)] ![(12875535266659/100000000000000 : ℝ), (44232194942909/100000000000000 : ℝ), (857845395637/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1058592331/5000000000 : ℝ)|^8441 ≤ (12875535266659/100000000000000 : ℝ)^6393
        have hw : |(-1058592331/5000000000 : ℝ)|=(1058592331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539127257/1000000000 : ℝ)|^8441 ≤ (44232194942909/100000000000000 : ℝ)^6393
        have hw : |(539127257/1000000000 : ℝ)|=(539127257/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053423897/2000000000 : ℝ)|^8441 ≤ (857845395637/2000000000000 : ℝ)^6393
        have hw : |(1053423897/2000000000 : ℝ)|=(1053423897/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s6_1 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344325139/10000000000 : ℝ)*x 0 + (-2180134617/10000000000 : ℝ)*x 1 + (5267119481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344325139/10000000000 : ℝ)^8441 ≤ (21862169320119/50000000000000 : ℝ)^6393 := by
    have hnat : (5344325139 : ℕ)^8441*50000000000000^6393 ≤ 21862169320119^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344325139 10000000000 21862169320119 50000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2180134617/10000000000 : ℝ)^8441 ≤ (6691695804801/50000000000000 : ℝ)^6393 := by
    have hnat : (2180134617 : ℕ)^8441*50000000000000^6393 ≤ 6691695804801^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180134617 10000000000 6691695804801 50000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267119481/10000000000 : ℝ)^8441 ≤ (42892269738841/100000000000000 : ℝ)^6393 := by
    have hnat : (5267119481 : ℕ)^8441*100000000000000^6393 ≤ 42892269738841^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267119481 10000000000 42892269738841 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344325139/10000000000 : ℝ), (-2180134617/10000000000 : ℝ), (5267119481/10000000000 : ℝ)] ![(21862169320119/50000000000000 : ℝ), (6691695804801/50000000000000 : ℝ), (42892269738841/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344325139/10000000000 : ℝ)|^8441 ≤ (21862169320119/50000000000000 : ℝ)^6393
        have hw : |(5344325139/10000000000 : ℝ)|=(5344325139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2180134617/10000000000 : ℝ)|^8441 ≤ (6691695804801/50000000000000 : ℝ)^6393
        have hw : |(-2180134617/10000000000 : ℝ)|=(2180134617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267119481/10000000000 : ℝ)|^8441 ≤ (42892269738841/100000000000000 : ℝ)^6393
        have hw : |(5267119481/10000000000 : ℝ)|=(5267119481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s6_2 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672162573/5000000000 : ℝ)*x 0 + (131677987/250000000 : ℝ)*x 1 + (-2180134609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672162573/5000000000 : ℝ)^8441 ≤ (8744867743171/20000000000000 : ℝ)^6393 := by
    have hnat : (2672162573 : ℕ)^8441*20000000000000^6393 ≤ 8744867743171^6393*5000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672162573 5000000000 8744867743171 20000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131677987/250000000 : ℝ)^8441 ≤ (42892269728089/100000000000000 : ℝ)^6393 := by
    have hnat : (131677987 : ℕ)^8441*100000000000000^6393 ≤ 42892269728089^6393*250000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131677987 250000000 42892269728089 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2180134609/10000000000 : ℝ)^8441 ≤ (13383391544759/100000000000000 : ℝ)^6393 := by
    have hnat : (2180134609 : ℕ)^8441*100000000000000^6393 ≤ 13383391544759^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180134609 10000000000 13383391544759 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672162573/5000000000 : ℝ), (131677987/250000000 : ℝ), (-2180134609/10000000000 : ℝ)] ![(8744867743171/20000000000000 : ℝ), (42892269728089/100000000000000 : ℝ), (13383391544759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672162573/5000000000 : ℝ)|^8441 ≤ (8744867743171/20000000000000 : ℝ)^6393
        have hw : |(2672162573/5000000000 : ℝ)|=(2672162573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131677987/250000000 : ℝ)|^8441 ≤ (42892269728089/100000000000000 : ℝ)^6393
        have hw : |(131677987/250000000 : ℝ)|=(131677987/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2180134609/10000000000 : ℝ)|^8441 ≤ (13383391544759/100000000000000 : ℝ)^6393
        have hw : |(-2180134609/10000000000 : ℝ)|=(2180134609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s6_3 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (543742721/1250000000 : ℝ)*x 0 + (4225643013/10000000000 : ℝ)*x 1 + (4477788127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543742721/1250000000 : ℝ)^8441 ≤ (1665871429777/5000000000000 : ℝ)^6393 := by
    have hnat : (543742721 : ℕ)^8441*5000000000000^6393 ≤ 1665871429777^6393*1250000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543742721 1250000000 1665871429777 5000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4225643013/10000000000 : ℝ)^8441 ≤ (400827430031/1250000000000 : ℝ)^6393 := by
    have hnat : (4225643013 : ℕ)^8441*1250000000000^6393 ≤ 400827430031^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4225643013 10000000000 400827430031 1250000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4477788127/10000000000 : ℝ)^8441 ≤ (34616376991407/100000000000000 : ℝ)^6393 := by
    have hnat : (4477788127 : ℕ)^8441*100000000000000^6393 ≤ 34616376991407^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4477788127 10000000000 34616376991407 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(543742721/1250000000 : ℝ), (4225643013/10000000000 : ℝ), (4477788127/10000000000 : ℝ)] ![(1665871429777/5000000000000 : ℝ), (400827430031/1250000000000 : ℝ), (34616376991407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(543742721/1250000000 : ℝ)|^8441 ≤ (1665871429777/5000000000000 : ℝ)^6393
        have hw : |(543742721/1250000000 : ℝ)|=(543742721/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4225643013/10000000000 : ℝ)|^8441 ≤ (400827430031/1250000000000 : ℝ)^6393
        have hw : |(4225643013/10000000000 : ℝ)|=(4225643013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4477788127/10000000000 : ℝ)|^8441 ≤ (34616376991407/100000000000000 : ℝ)^6393
        have hw : |(4477788127/10000000000 : ℝ)|=(4477788127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s6_4 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2117189171/10000000000 : ℝ)*x 0 + (5267433389/10000000000 : ℝ)*x 1 + (5390957651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2117189171/10000000000 : ℝ)^8441 ≤ (12875571472291/100000000000000 : ℝ)^6393 := by
    have hnat : (2117189171 : ℕ)^8441*100000000000000^6393 ≤ 12875571472291^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117189171 10000000000 12875571472291 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267433389/10000000000 : ℝ)^8441 ≤ (2144782247747/5000000000000 : ℝ)^6393 := by
    have hnat : (5267433389 : ℕ)^8441*5000000000000^6393 ≤ 2144782247747^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267433389 10000000000 2144782247747 5000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390957651/10000000000 : ℝ)^8441 ≤ (22114391777139/50000000000000 : ℝ)^6393 := by
    have hnat : (5390957651 : ℕ)^8441*50000000000000^6393 ≤ 22114391777139^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390957651 10000000000 22114391777139 50000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2117189171/10000000000 : ℝ), (5267433389/10000000000 : ℝ), (5390957651/10000000000 : ℝ)] ![(12875571472291/100000000000000 : ℝ), (2144782247747/5000000000000 : ℝ), (22114391777139/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2117189171/10000000000 : ℝ)|^8441 ≤ (12875571472291/100000000000000 : ℝ)^6393
        have hw : |(-2117189171/10000000000 : ℝ)|=(2117189171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267433389/10000000000 : ℝ)|^8441 ≤ (2144782247747/5000000000000 : ℝ)^6393
        have hw : |(5267433389/10000000000 : ℝ)|=(5267433389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390957651/10000000000 : ℝ)|^8441 ≤ (22114391777139/50000000000000 : ℝ)^6393
        have hw : |(5390957651/10000000000 : ℝ)|=(5390957651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s6_5 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312633923/10000000000 : ℝ)*x 0 + (-514074287/2500000000 : ℝ)*x 1 + (1347739299/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312633923/10000000000 : ℝ)^8441 ≤ (21691161792837/50000000000000 : ℝ)^6393 := by
    have hnat : (5312633923 : ℕ)^8441*50000000000000^6393 ≤ 21691161792837^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312633923 10000000000 21691161792837 50000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (514074287/2500000000 : ℝ)^8441 ≤ (2477779554677/20000000000000 : ℝ)^6393 := by
    have hnat : (514074287 : ℕ)^8441*20000000000000^6393 ≤ 2477779554677^6393*2500000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514074287 2500000000 2477779554677 20000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347739299/2500000000 : ℝ)^8441 ≤ (5528597328187/12500000000000 : ℝ)^6393 := by
    have hnat : (1347739299 : ℕ)^8441*12500000000000^6393 ≤ 5528597328187^6393*2500000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347739299 2500000000 5528597328187 12500000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312633923/10000000000 : ℝ), (-514074287/2500000000 : ℝ), (1347739299/2500000000 : ℝ)] ![(21691161792837/50000000000000 : ℝ), (2477779554677/20000000000000 : ℝ), (5528597328187/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312633923/10000000000 : ℝ)|^8441 ≤ (21691161792837/50000000000000 : ℝ)^6393
        have hw : |(5312633923/10000000000 : ℝ)|=(5312633923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-514074287/2500000000 : ℝ)|^8441 ≤ (2477779554677/20000000000000 : ℝ)^6393
        have hw : |(-514074287/2500000000 : ℝ)|=(514074287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347739299/2500000000 : ℝ)|^8441 ≤ (5528597328187/12500000000000 : ℝ)^6393
        have hw : |(1347739299/2500000000 : ℝ)|=(1347739299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s6_6 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (53126339/100000000 : ℝ)*x 0 + (5390957377/10000000000 : ℝ)*x 1 + (-2056296933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53126339/100000000 : ℝ)^8441 ≤ (10845580834423/25000000000000 : ℝ)^6393 := by
    have hnat : (53126339 : ℕ)^8441*25000000000000^6393 ≤ 10845580834423^6393*100000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53126339 100000000 10845580834423 25000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390957377/10000000000 : ℝ)^8441 ≤ (691074696659/1562500000000 : ℝ)^6393 := by
    have hnat : (5390957377 : ℕ)^8441*1562500000000^6393 ≤ 691074696659^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390957377 10000000000 691074696659 1562500000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2056296933/10000000000 : ℝ)^8441 ≤ (12388896063077/100000000000000 : ℝ)^6393 := by
    have hnat : (2056296933 : ℕ)^8441*100000000000000^6393 ≤ 12388896063077^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2056296933 10000000000 12388896063077 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53126339/100000000 : ℝ), (5390957377/10000000000 : ℝ), (-2056296933/10000000000 : ℝ)] ![(10845580834423/25000000000000 : ℝ), (691074696659/1562500000000 : ℝ), (12388896063077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53126339/100000000 : ℝ)|^8441 ≤ (10845580834423/25000000000000 : ℝ)^6393
        have hw : |(53126339/100000000 : ℝ)|=(53126339/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390957377/10000000000 : ℝ)|^8441 ≤ (691074696659/1562500000000 : ℝ)^6393
        have hw : |(5390957377/10000000000 : ℝ)|=(5390957377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2056296933/10000000000 : ℝ)|^8441 ≤ (12388896063077/100000000000000 : ℝ)^6393
        have hw : |(-2056296933/10000000000 : ℝ)|=(2056296933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s6_7 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4349951203/10000000000 : ℝ)*x 0 + (223857529/500000000 : ℝ)*x 1 + (2113141477/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4349951203/10000000000 : ℝ)^8441 ≤ (33317524011117/100000000000000 : ℝ)^6393 := by
    have hnat : (4349951203 : ℕ)^8441*100000000000000^6393 ≤ 33317524011117^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4349951203 10000000000 33317524011117 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (223857529/500000000 : ℝ)^8441 ≤ (34609869560451/100000000000000 : ℝ)^6393 := by
    have hnat : (223857529 : ℕ)^8441*100000000000000^6393 ≤ 34609869560451^6393*500000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223857529 500000000 34609869560451 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2113141477/5000000000 : ℝ)^8441 ≤ (32072606413829/100000000000000 : ℝ)^6393 := by
    have hnat : (2113141477 : ℕ)^8441*100000000000000^6393 ≤ 32072606413829^6393*5000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113141477 5000000000 32072606413829 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4349951203/10000000000 : ℝ), (223857529/500000000 : ℝ), (2113141477/5000000000 : ℝ)] ![(33317524011117/100000000000000 : ℝ), (34609869560451/100000000000000 : ℝ), (32072606413829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4349951203/10000000000 : ℝ)|^8441 ≤ (33317524011117/100000000000000 : ℝ)^6393
        have hw : |(4349951203/10000000000 : ℝ)|=(4349951203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(223857529/500000000 : ℝ)|^8441 ≤ (34609869560451/100000000000000 : ℝ)^6393
        have hw : |(223857529/500000000 : ℝ)|=(223857529/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2113141477/5000000000 : ℝ)|^8441 ≤ (32072606413829/100000000000000 : ℝ)^6393
        have hw : |(2113141477/5000000000 : ℝ)|=(2113141477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1248_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2367907/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14133/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5731/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5741/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (441/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14133/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5731/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14133/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5731/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14133/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5731/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14133/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5731/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14133/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5731/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14133/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5731/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5731/50000 : ℝ) ^ (1055/256 : ℝ) ≤ (13277732994323973/100000000000000000000 : ℝ) := by
    have hpowers : (5731/50000 : ℝ)^1055 ≤ (13277732994323973/100000000000000000000 : ℝ)^256 := by
      have hnat : (5731 : ℕ)^1055*100000000000000000000^256 ≤ 13277732994323973^256*50000^1055 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5731 50000 13277732994323973 100000000000000000000 1055 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5731/50000 : ℝ)) (X := (13277732994323973/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1055 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14133/100000 : ℝ) ^ (1055/256 : ℝ) ≤ (31480101773232627/100000000000000000000 : ℝ) := by
    have hpowers : (14133/100000 : ℝ)^1055 ≤ (31480101773232627/100000000000000000000 : ℝ)^256 := by
      have hnat : (14133 : ℕ)^1055*100000000000000000000^256 ≤ 31480101773232627^256*100000^1055 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14133 100000 31480101773232627 100000000000000000000 1055 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14133/100000 : ℝ)) (X := (31480101773232627/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1055 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013277732994323973/50000000000000000000 : ℝ) ≤ (10000644314292279/10000000000000000 : ℝ) ^ (1055/256 : ℝ) := by
    have hpowers : (50013277732994323973/50000000000000000000 : ℝ)^256 ≤ (10000644314292279/10000000000000000 : ℝ)^1055 := by
      have hnat : (50013277732994323973 : ℕ)^256*10000000000000000^1055 ≤ 10000644314292279^1055*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013277732994323973 50000000000000000000 10000644314292279 10000000000000000 256 1055 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000644314292279/10000000000000000 : ℝ)) (X := (50013277732994323973/50000000000000000000 : ℝ)) (by norm_num) 1055 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (500223789173837783/500000000000000000 : ℝ) ≤ (10001085882866341/10000000000000000 : ℝ) ^ (1055/256 : ℝ) := by
    have hpowers : (500223789173837783/500000000000000000 : ℝ)^256 ≤ (10001085882866341/10000000000000000 : ℝ)^1055 := by
      have hnat : (500223789173837783 : ℕ)^256*10000000000000000^1055 ≤ 10001085882866341^1055*500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500223789173837783 500000000000000000 10001085882866341 10000000000000000 256 1055 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001085882866341/10000000000000000 : ℝ)) (X := (500223789173837783/500000000000000000 : ℝ)) (by norm_num) 1055 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031480101773232627/50000000000000000000 : ℝ) ≤ (10001527451440403/10000000000000000 : ℝ) ^ (1055/256 : ℝ) := by
    have hpowers : (50031480101773232627/50000000000000000000 : ℝ)^256 ≤ (10001527451440403/10000000000000000 : ℝ)^1055 := by
      have hnat : (50031480101773232627 : ℕ)^256*10000000000000000^1055 ≤ 10001527451440403^1055*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031480101773232627 50000000000000000000 10001527451440403 10000000000000000 256 1055 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001527451440403/10000000000000000 : ℝ)) (X := (50031480101773232627/50000000000000000000 : ℝ)) (by norm_num) 1055 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13277732994323973/100000000000000000000 : ℝ) ≤ ((26701598445482879921/26710000000000000000 : ℝ)+2*(220784287031/133550000000000 : ℝ)*(5731/50000 : ℝ))^(1055/256 : ℝ) := by
    rw [show (26701598445482879921/26710000000000000000 : ℝ)+2*(220784287031/133550000000000 : ℝ)*(5731/50000 : ℝ)=(10000644314292279/10000000000000000 : ℝ) by norm_num, show 1+2*(13277732994323973/100000000000000000000 : ℝ)=(50013277732994323973/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31480101773232627/100000000000000000000 : ℝ)+(13277732994323973/100000000000000000000 : ℝ) ≤ ((26701598445482879921/26710000000000000000 : ℝ)+(220784287031/133550000000000 : ℝ)*((14133/100000 : ℝ)+(5731/50000 : ℝ)))^(1055/256 : ℝ) := by
    rw [show (26701598445482879921/26710000000000000000 : ℝ)+(220784287031/133550000000000 : ℝ)*((14133/100000 : ℝ)+(5731/50000 : ℝ))=(10001085882866341/10000000000000000 : ℝ) by norm_num, show 1+(31480101773232627/100000000000000000000 : ℝ)+(13277732994323973/100000000000000000000 : ℝ)=(500223789173837783/500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31480101773232627/100000000000000000000 : ℝ) ≤ ((26701598445482879921/26710000000000000000 : ℝ)+2*(220784287031/133550000000000 : ℝ)*(14133/100000 : ℝ))^(1055/256 : ℝ) := by
    rw [show (26701598445482879921/26710000000000000000 : ℝ)+2*(220784287031/133550000000000 : ℝ)*(14133/100000 : ℝ)=(10001527451440403/10000000000000000 : ℝ) by norm_num, show 1+2*(31480101773232627/100000000000000000000 : ℝ)=(50031480101773232627/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26701598445482879921/26710000000000000000 : ℝ)*(X 1 0+X 2 0)+(220784287031/133550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1055/256 : ℝ)) (lo := (5731/50000 : ℝ)) (hi := (14133/100000 : ℝ)) (c := (26701598445482879921/26710000000000000000 : ℝ)) (alpha := (220784287031/133550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26701598445482879921/26710000000000000000 : ℝ)*(X 0 1+X 2 1)+(220784287031/133550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1055/256 : ℝ)) (lo := (5731/50000 : ℝ)) (hi := (14133/100000 : ℝ)) (c := (26701598445482879921/26710000000000000000 : ℝ)) (alpha := (220784287031/133550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26701598445482879921/26710000000000000000 : ℝ)*(X 0 2+X 1 2)+(220784287031/133550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1055/256 : ℝ)) (lo := (5731/50000 : ℝ)) (hi := (14133/100000 : ℝ)) (c := (26701598445482879921/26710000000000000000 : ℝ)) (alpha := (220784287031/133550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1058592331/5000000000 : ℝ)*X 0 0+(539127257/1000000000 : ℝ)*X 0 1+(1053423897/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344325139/10000000000 : ℝ)*X 1 0+(-2180134617/10000000000 : ℝ)*X 1 1+(5267119481/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672162573/5000000000 : ℝ)*X 2 0+(131677987/250000000 : ℝ)*X 2 1+(-2180134609/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((543742721/1250000000 : ℝ)*X 0 0+(4225643013/10000000000 : ℝ)*X 0 1+(4477788127/10000000000 : ℝ)*X 0 2+(543742721/1250000000 : ℝ)*X 1 0+(4225643013/10000000000 : ℝ)*X 1 1+(4477788127/10000000000 : ℝ)*X 1 2+(543742721/1250000000 : ℝ)*X 2 0+(4225643013/10000000000 : ℝ)*X 2 1+(4477788127/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2117189171/10000000000 : ℝ)*X 0 0+(5267433389/10000000000 : ℝ)*X 0 1+(5390957651/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312633923/10000000000 : ℝ)*X 1 0+(-514074287/2500000000 : ℝ)*X 1 1+(1347739299/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((53126339/100000000 : ℝ)*X 2 0+(5390957377/10000000000 : ℝ)*X 2 1+(-2056296933/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4349951203/10000000000 : ℝ)*X 0 0+(223857529/500000000 : ℝ)*X 0 1+(2113141477/5000000000 : ℝ)*X 0 2+(4349951203/10000000000 : ℝ)*X 1 0+(223857529/500000000 : ℝ)*X 1 1+(2113141477/5000000000 : ℝ)*X 1 2+(4349951203/10000000000 : ℝ)*X 2 0+(223857529/500000000 : ℝ)*X 2 1+(2113141477/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (907842937054114556726810307/267100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (133757259/20000000000000 : ℝ)*(base19) + (629644227/100000000000000 : ℝ)*(base23) + (1327851/5000000000000 : ℝ)*(lower2) + (82758409/100000000000000 : ℝ)*(upper3) + (15339241/25000000000000 : ℝ)*(upper5) + (1202059849652111/20000000000000 : ℝ)*(major0) + (1202059849652111/20000000000000 : ℝ)*(major1) + (1202059849652111/20000000000000 : ℝ)*(major2) + (8054590994209273/100000000000000 : ℝ)*(sp0) + (322184357693033/4000000000000 : ℝ)*(sp1) + (4027304490733947/50000000000000 : ℝ)*(sp2) + (3965979062252457/100000000000000 : ℝ)*(sp3) + (18616902847/100000000000000 : ℝ)*(sp4) + (1213732533/12500000000000 : ℝ)*(sp7) + (1982994386056361/50000000000000 : ℝ)*(f.failure) + (201365240277803/2500000000000 : ℝ)*(f.sum) + (11035591519473/2671000000000000000000000000 : ℝ)*base66 + (2708153589258563231/534200000000000000000000000000000 : ℝ)*base67 + (1599073522412036769/534200000000000000000000000000000 : ℝ)*base70 + (606851131714763231/534200000000000000000000000000000 : ℝ)*base71 + (8234220303363/1335500000000000000000000000 : ℝ)*base73 + (1946636229301363231/534200000000000000000000000000000 : ℝ)*base75 + (2715577909221036769/534200000000000000000000000000000 : ℝ)*base78 + (5346847829835163231/534200000000000000000000000000000 : ℝ)*base79 + (4604340208397/2671000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (1012677/78125000000000000000 : ℝ)*base89 + (1012677/78125000000000000000 : ℝ)*base91 + (1012677/78125000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (136751797398121550022531/13355000000000000000000000000 : ℝ) := by norm_num
    linear_combination (947294603/100000000000000 : ℝ)*(base19) + (38106489/6250000000000 : ℝ)*(base23) + (174099337/100000000000000 : ℝ)*(lower2) + (17065741/25000000000000 : ℝ)*(upper3) + (5697469/50000000000000 : ℝ)*(lower4) + (183308819/100000000000000 : ℝ)*(upper5) + (6040875937153909/100000000000000 : ℝ)*(major0) + (6040875937153909/100000000000000 : ℝ)*(major1) + (6040875937153909/100000000000000 : ℝ)*(major2) + (311540881/50000000000000 : ℝ)*(sp2) + (404779313026401/5000000000000 : ℝ)*(sp4) + (8095585313233417/100000000000000 : ℝ)*(sp5) + (1619117005548487/20000000000000 : ℝ)*(sp6) + (79723305449099/2000000000000 : ℝ)*(sp7) + (79723305449099/2000000000000 : ℝ)*(f.failure) + (404779313026401/5000000000000 : ℝ)*(f.sum) + (21743082662323/3338750000000000000000000000 : ℝ)*base66 + (1602344302998561189/2671000000000000000000000000000000 : ℝ)*base67 + (19490736451341438811/2671000000000000000000000000000000 : ℝ)*base70 + (5062413898167561189/2671000000000000000000000000000000 : ℝ)*base71 + (12930410517769/6677500000000000000000000000 : ℝ)*base73 + (21415794919906561189/2671000000000000000000000000000000 : ℝ)*base75 + (14566040889563438811/2671000000000000000000000000000000 : ℝ)*base78 + (53324251877226438811/2671000000000000000000000000000000 : ℝ)*base80 + (119885455144973/13355000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (9543/3125000000000000000 : ℝ)*base89 + (9543/3125000000000000000 : ℝ)*base91 + (9543/3125000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1248_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2367907/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14133/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5731/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5741/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (441/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1248_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1248_s7_0 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2117200841/10000000000 : ℝ)*x 0 + (539108079/1000000000 : ℝ)*x 1 + (658412577/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2117200841/10000000000 : ℝ)^8441 ≤ (6437832589133/50000000000000 : ℝ)^6393 := by
    have hnat : (2117200841 : ℕ)^8441*50000000000000^6393 ≤ 6437832589133^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117200841 10000000000 6437832589133 50000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539108079/1000000000 : ℝ)^8441 ≤ (5528764682633/12500000000000 : ℝ)^6393 := by
    have hnat : (539108079 : ℕ)^8441*12500000000000^6393 ≤ 5528764682633^6393*1000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539108079 1000000000 5528764682633 12500000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658412577/1250000000 : ℝ)^8441 ≤ (10723554334773/25000000000000 : ℝ)^6393 := by
    have hnat : (658412577 : ℕ)^8441*25000000000000^6393 ≤ 10723554334773^6393*1250000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658412577 1250000000 10723554334773 25000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2117200841/10000000000 : ℝ), (539108079/1000000000 : ℝ), (658412577/1250000000 : ℝ)] ![(6437832589133/50000000000000 : ℝ), (5528764682633/12500000000000 : ℝ), (10723554334773/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2117200841/10000000000 : ℝ)|^8441 ≤ (6437832589133/50000000000000 : ℝ)^6393
        have hw : |(-2117200841/10000000000 : ℝ)|=(2117200841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539108079/1000000000 : ℝ)|^8441 ≤ (5528764682633/12500000000000 : ℝ)^6393
        have hw : |(539108079/1000000000 : ℝ)|=(539108079/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658412577/1250000000 : ℝ)|^8441 ≤ (10723554334773/25000000000000 : ℝ)^6393
        have hw : |(658412577/1250000000 : ℝ)|=(658412577/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s7_1 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668034539/1250000000 : ℝ)*x 0 + (-544989797/2500000000 : ℝ)*x 1 + (5267300777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668034539/1250000000 : ℝ)^8441 ≤ (43723811193053/100000000000000 : ℝ)^6393 := by
    have hnat : (668034539 : ℕ)^8441*100000000000000^6393 ≤ 43723811193053^6393*1250000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668034539 1250000000 43723811193053 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (544989797/2500000000 : ℝ)^8441 ≤ (3345492428377/25000000000000 : ℝ)^6393 := by
    have hnat : (544989797 : ℕ)^8441*25000000000000^6393 ≤ 3345492428377^6393*2500000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544989797 2500000000 3345492428377 25000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267300777/10000000000 : ℝ)^8441 ≤ (21447109535103/50000000000000 : ℝ)^6393 := by
    have hnat : (5267300777 : ℕ)^8441*50000000000000^6393 ≤ 21447109535103^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267300777 10000000000 21447109535103 50000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668034539/1250000000 : ℝ), (-544989797/2500000000 : ℝ), (5267300777/10000000000 : ℝ)] ![(43723811193053/100000000000000 : ℝ), (3345492428377/25000000000000 : ℝ), (21447109535103/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668034539/1250000000 : ℝ)|^8441 ≤ (43723811193053/100000000000000 : ℝ)^6393
        have hw : |(668034539/1250000000 : ℝ)|=(668034539/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-544989797/2500000000 : ℝ)|^8441 ≤ (3345492428377/25000000000000 : ℝ)^6393
        have hw : |(-544989797/2500000000 : ℝ)|=(544989797/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267300777/10000000000 : ℝ)|^8441 ≤ (21447109535103/50000000000000 : ℝ)^6393
        have hw : |(5267300777/10000000000 : ℝ)|=(5267300777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s7_2 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (167008633/312500000 : ℝ)*x 0 + (329206301/625000000 : ℝ)*x 1 + (-544989803/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167008633/312500000 : ℝ)^8441 ≤ (43723810588121/100000000000000 : ℝ)^6393 := by
    have hnat : (167008633 : ℕ)^8441*100000000000000^6393 ≤ 43723810588121^6393*312500000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167008633 312500000 43723810588121 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329206301/625000000 : ℝ)^8441 ≤ (5361777436193/12500000000000 : ℝ)^6393 := by
    have hnat : (329206301 : ℕ)^8441*12500000000000^6393 ≤ 5361777436193^6393*625000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329206301 625000000 5361777436193 12500000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (544989803/2500000000 : ℝ)^8441 ≤ (209093279813/1562500000000 : ℝ)^6393 := by
    have hnat : (544989803 : ℕ)^8441*1562500000000^6393 ≤ 209093279813^6393*2500000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544989803 2500000000 209093279813 1562500000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167008633/312500000 : ℝ), (329206301/625000000 : ℝ), (-544989803/2500000000 : ℝ)] ![(43723810588121/100000000000000 : ℝ), (5361777436193/12500000000000 : ℝ), (209093279813/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167008633/312500000 : ℝ)|^8441 ≤ (43723810588121/100000000000000 : ℝ)^6393
        have hw : |(167008633/312500000 : ℝ)|=(167008633/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329206301/625000000 : ℝ)|^8441 ≤ (5361777436193/12500000000000 : ℝ)^6393
        have hw : |(329206301/625000000 : ℝ)|=(329206301/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-544989803/2500000000 : ℝ)|^8441 ≤ (209093279813/1562500000000 : ℝ)^6393
        have hw : |(-544989803/2500000000 : ℝ)|=(544989803/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s7_3 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4349951473/10000000000 : ℝ)*x 0 + (2113010057/5000000000 : ℝ)*x 1 + (4477408337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4349951473/10000000000 : ℝ)^8441 ≤ (8329381685403/25000000000000 : ℝ)^6393 := by
    have hnat : (4349951473 : ℕ)^8441*25000000000000^6393 ≤ 8329381685403^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4349951473 10000000000 8329381685403 25000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2113010057/5000000000 : ℝ)^8441 ≤ (16034986400247/50000000000000 : ℝ)^6393 := by
    have hnat : (2113010057 : ℕ)^8441*50000000000000^6393 ≤ 16034986400247^6393*5000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113010057 5000000000 16034986400247 50000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4477408337/10000000000 : ℝ)^8441 ≤ (34612500445847/100000000000000 : ℝ)^6393 := by
    have hnat : (4477408337 : ℕ)^8441*100000000000000^6393 ≤ 34612500445847^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4477408337 10000000000 34612500445847 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4349951473/10000000000 : ℝ), (2113010057/5000000000 : ℝ), (4477408337/10000000000 : ℝ)] ![(8329381685403/25000000000000 : ℝ), (16034986400247/50000000000000 : ℝ), (34612500445847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4349951473/10000000000 : ℝ)|^8441 ≤ (8329381685403/25000000000000 : ℝ)^6393
        have hw : |(4349951473/10000000000 : ℝ)|=(4349951473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2113010057/5000000000 : ℝ)|^8441 ≤ (16034986400247/50000000000000 : ℝ)^6393
        have hw : |(2113010057/5000000000 : ℝ)|=(2113010057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4477408337/10000000000 : ℝ)|^8441 ≤ (34612500445847/100000000000000 : ℝ)^6393
        have hw : |(4477408337/10000000000 : ℝ)|=(4477408337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s7_4 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2117205849/10000000000 : ℝ)*x 0 + (1316903183/2500000000 : ℝ)*x 1 + (539076727/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2117205849/10000000000 : ℝ)^8441 ≤ (12875705390787/100000000000000 : ℝ)^6393 := by
    have hnat : (2117205849 : ℕ)^8441*100000000000000^6393 ≤ 12875705390787^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117205849 10000000000 12875705390787 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316903183/2500000000 : ℝ)^8441 ≤ (42897573323953/100000000000000 : ℝ)^6393 := by
    have hnat : (1316903183 : ℕ)^8441*100000000000000^6393 ≤ 42897573323953^6393*2500000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316903183 2500000000 42897573323953 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539076727/1000000000 : ℝ)^8441 ≤ (4422672126579/10000000000000 : ℝ)^6393 := by
    have hnat : (539076727 : ℕ)^8441*10000000000000^6393 ≤ 4422672126579^6393*1000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539076727 1000000000 4422672126579 10000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2117205849/10000000000 : ℝ), (1316903183/2500000000 : ℝ), (539076727/1000000000 : ℝ)] ![(12875705390787/100000000000000 : ℝ), (42897573323953/100000000000000 : ℝ), (4422672126579/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2117205849/10000000000 : ℝ)|^8441 ≤ (12875705390787/100000000000000 : ℝ)^6393
        have hw : |(-2117205849/10000000000 : ℝ)|=(2117205849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316903183/2500000000 : ℝ)|^8441 ≤ (42897573323953/100000000000000 : ℝ)^6393
        have hw : |(1316903183/2500000000 : ℝ)|=(1316903183/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539076727/1000000000 : ℝ)|^8441 ≤ (4422672126579/10000000000000 : ℝ)^6393
        have hw : |(539076727/1000000000 : ℝ)|=(539076727/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s7_5 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312680489/10000000000 : ℝ)*x 0 + (-1028246351/5000000000 : ℝ)*x 1 + (2695383619/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312680489/10000000000 : ℝ)^8441 ≤ (10845706413163/25000000000000 : ℝ)^6393 := by
    have hnat : (5312680489 : ℕ)^8441*25000000000000^6393 ≤ 10845706413163^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312680489 10000000000 10845706413163 25000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1028246351/5000000000 : ℝ)^8441 ≤ (1548806676767/12500000000000 : ℝ)^6393 := by
    have hnat : (1028246351 : ℕ)^8441*12500000000000^6393 ≤ 1548806676767^6393*5000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028246351 5000000000 1548806676767 12500000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695383619/5000000000 : ℝ)^8441 ≤ (22113360459577/50000000000000 : ℝ)^6393 := by
    have hnat : (2695383619 : ℕ)^8441*50000000000000^6393 ≤ 22113360459577^6393*5000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695383619 5000000000 22113360459577 50000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312680489/10000000000 : ℝ), (-1028246351/5000000000 : ℝ), (2695383619/5000000000 : ℝ)] ![(10845706413163/25000000000000 : ℝ), (1548806676767/12500000000000 : ℝ), (22113360459577/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312680489/10000000000 : ℝ)|^8441 ≤ (10845706413163/25000000000000 : ℝ)^6393
        have hw : |(5312680489/10000000000 : ℝ)|=(5312680489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1028246351/5000000000 : ℝ)|^8441 ≤ (1548806676767/12500000000000 : ℝ)^6393
        have hw : |(-1028246351/5000000000 : ℝ)|=(1028246351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695383619/5000000000 : ℝ)|^8441 ≤ (22113360459577/50000000000000 : ℝ)^6393
        have hw : |(2695383619/5000000000 : ℝ)|=(2695383619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s7_6 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312680489/10000000000 : ℝ)*x 0 + (2695383633/5000000000 : ℝ)*x 1 + (-2056492663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312680489/10000000000 : ℝ)^8441 ≤ (10845706413163/25000000000000 : ℝ)^6393 := by
    have hnat : (5312680489 : ℕ)^8441*25000000000000^6393 ≤ 10845706413163^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312680489 10000000000 10845706413163 25000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695383633/5000000000 : ℝ)^8441 ≤ (2211336061123/5000000000000 : ℝ)^6393 := by
    have hnat : (2695383633 : ℕ)^8441*5000000000000^6393 ≤ 2211336061123^6393*5000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695383633 5000000000 2211336061123 5000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2056492663/10000000000 : ℝ)^8441 ≤ (3097613275971/25000000000000 : ℝ)^6393 := by
    have hnat : (2056492663 : ℕ)^8441*25000000000000^6393 ≤ 3097613275971^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2056492663 10000000000 3097613275971 25000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312680489/10000000000 : ℝ), (2695383633/5000000000 : ℝ), (-2056492663/10000000000 : ℝ)] ![(10845706413163/25000000000000 : ℝ), (2211336061123/5000000000000 : ℝ), (3097613275971/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312680489/10000000000 : ℝ)|^8441 ≤ (10845706413163/25000000000000 : ℝ)^6393
        have hw : |(5312680489/10000000000 : ℝ)|=(5312680489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695383633/5000000000 : ℝ)|^8441 ≤ (2211336061123/5000000000000 : ℝ)^6393
        have hw : |(2695383633/5000000000 : ℝ)|=(2695383633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2056492663/10000000000 : ℝ)|^8441 ≤ (3097613275971/25000000000000 : ℝ)^6393
        have hw : |(-2056492663/10000000000 : ℝ)|=(2056492663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s7_7 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2174980311/5000000000 : ℝ)*x 0 + (895354811/2000000000 : ℝ)*x 1 + (2113328491/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2174980311/5000000000 : ℝ)^8441 ≤ (16658809632477/50000000000000 : ℝ)^6393 := by
    have hnat : (2174980311 : ℕ)^8441*50000000000000^6393 ≤ 16658809632477^6393*5000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174980311 5000000000 16658809632477 50000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (895354811/2000000000 : ℝ)^8441 ≤ (34606026515857/100000000000000 : ℝ)^6393 := by
    have hnat : (895354811 : ℕ)^8441*100000000000000^6393 ≤ 34606026515857^6393*2000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895354811 2000000000 34606026515857 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2113328491/5000000000 : ℝ)^8441 ≤ (32076354202997/100000000000000 : ℝ)^6393 := by
    have hnat : (2113328491 : ℕ)^8441*100000000000000^6393 ≤ 32076354202997^6393*5000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113328491 5000000000 32076354202997 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2174980311/5000000000 : ℝ), (895354811/2000000000 : ℝ), (2113328491/5000000000 : ℝ)] ![(16658809632477/50000000000000 : ℝ), (34606026515857/100000000000000 : ℝ), (32076354202997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2174980311/5000000000 : ℝ)|^8441 ≤ (16658809632477/50000000000000 : ℝ)^6393
        have hw : |(2174980311/5000000000 : ℝ)|=(2174980311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(895354811/2000000000 : ℝ)|^8441 ≤ (34606026515857/100000000000000 : ℝ)^6393
        have hw : |(895354811/2000000000 : ℝ)|=(895354811/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2113328491/5000000000 : ℝ)|^8441 ≤ (32076354202997/100000000000000 : ℝ)^6393
        have hw : |(2113328491/5000000000 : ℝ)|=(2113328491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1248_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2367907/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (441/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5741/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5743/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3527/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (441/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5741/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (441/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5741/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (441/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5741/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (441/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5741/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (441/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5741/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (441/3125 : ℝ)*(X 0 2+X 1 2) := by
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
  have hpowlo : (5741/50000 : ℝ) ^ (1055/256 : ℝ) ≤ (13373471897112989/100000000000000000000 : ℝ) := by
    have hpowers : (5741/50000 : ℝ)^1055 ≤ (13373471897112989/100000000000000000000 : ℝ)^256 := by
      have hnat : (5741 : ℕ)^1055*100000000000000000000^256 ≤ 13373471897112989^256*50000^1055 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5741 50000 13373471897112989 100000000000000000000 1055 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5741/50000 : ℝ)) (X := (13373471897112989/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1055 256 (by norm_num) hpowers
    exact h
  have hpowhi : (441/3125 : ℝ) ^ (1055/256 : ℝ) ≤ (31287780905434797/100000000000000000000 : ℝ) := by
    have hpowers : (441/3125 : ℝ)^1055 ≤ (31287780905434797/100000000000000000000 : ℝ)^256 := by
      have hnat : (441 : ℕ)^1055*100000000000000000000^256 ≤ 31287780905434797^256*3125^1055 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        441 3125 31287780905434797 100000000000000000000 1055 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (441/3125 : ℝ)) (X := (31287780905434797/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1055 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013373471897112989/50000000000000000000 : ℝ) ≤ (10000648959640771/10000000000000000 : ℝ) ^ (1055/256 : ℝ) := by
    have hpowers : (50013373471897112989/50000000000000000000 : ℝ)^256 ≤ (10000648959640771/10000000000000000 : ℝ)^1055 := by
      have hnat : (50013373471897112989 : ℕ)^256*10000000000000000^1055 ≤ 10000648959640771^1055*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013373471897112989 50000000000000000000 10000648959640771 10000000000000000 256 1055 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000648959640771/10000000000000000 : ℝ)) (X := (50013373471897112989/50000000000000000000 : ℝ)) (by norm_num) 1055 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022330626401273893/50000000000000000000 : ℝ) ≤ (5000541770029649/5000000000000000 : ℝ) ^ (1055/256 : ℝ) := by
    have hpowers : (50022330626401273893/50000000000000000000 : ℝ)^256 ≤ (5000541770029649/5000000000000000 : ℝ)^1055 := by
      have hnat : (50022330626401273893 : ℕ)^256*5000000000000000^1055 ≤ 5000541770029649^1055*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022330626401273893 50000000000000000000 5000541770029649 5000000000000000 256 1055 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000541770029649/5000000000000000 : ℝ)) (X := (50022330626401273893/50000000000000000000 : ℝ)) (by norm_num) 1055 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031287780905434797/50000000000000000000 : ℝ) ≤ (400060724819113/400000000000000 : ℝ) ^ (1055/256 : ℝ) := by
    have hpowers : (50031287780905434797/50000000000000000000 : ℝ)^256 ≤ (400060724819113/400000000000000 : ℝ)^1055 := by
      have hnat : (50031287780905434797 : ℕ)^256*400000000000000^1055 ≤ 400060724819113^1055*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031287780905434797 50000000000000000000 400060724819113 400000000000000 256 1055 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400060724819113/400000000000000 : ℝ)) (X := (50031287780905434797/50000000000000000000 : ℝ)) (by norm_num) 1055 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13373471897112989/100000000000000000000 : ℝ) ≤ ((13145863529562086851/13150000000000000000 : ℝ)+2*(434580418527/263000000000000 : ℝ)*(5741/50000 : ℝ))^(1055/256 : ℝ) := by
    rw [show (13145863529562086851/13150000000000000000 : ℝ)+2*(434580418527/263000000000000 : ℝ)*(5741/50000 : ℝ)=(10000648959640771/10000000000000000 : ℝ) by norm_num, show 1+2*(13373471897112989/100000000000000000000 : ℝ)=(50013373471897112989/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31287780905434797/100000000000000000000 : ℝ)+(13373471897112989/100000000000000000000 : ℝ) ≤ ((13145863529562086851/13150000000000000000 : ℝ)+(434580418527/263000000000000 : ℝ)*((441/3125 : ℝ)+(5741/50000 : ℝ)))^(1055/256 : ℝ) := by
    rw [show (13145863529562086851/13150000000000000000 : ℝ)+(434580418527/263000000000000 : ℝ)*((441/3125 : ℝ)+(5741/50000 : ℝ))=(5000541770029649/5000000000000000 : ℝ) by norm_num, show 1+(31287780905434797/100000000000000000000 : ℝ)+(13373471897112989/100000000000000000000 : ℝ)=(50022330626401273893/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31287780905434797/100000000000000000000 : ℝ) ≤ ((13145863529562086851/13150000000000000000 : ℝ)+2*(434580418527/263000000000000 : ℝ)*(441/3125 : ℝ))^(1055/256 : ℝ) := by
    rw [show (13145863529562086851/13150000000000000000 : ℝ)+2*(434580418527/263000000000000 : ℝ)*(441/3125 : ℝ)=(400060724819113/400000000000000 : ℝ) by norm_num, show 1+2*(31287780905434797/100000000000000000000 : ℝ)=(50031287780905434797/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13145863529562086851/13150000000000000000 : ℝ)*(X 1 0+X 2 0)+(434580418527/263000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1055/256 : ℝ)) (lo := (5741/50000 : ℝ)) (hi := (441/3125 : ℝ)) (c := (13145863529562086851/13150000000000000000 : ℝ)) (alpha := (434580418527/263000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13145863529562086851/13150000000000000000 : ℝ)*(X 0 1+X 2 1)+(434580418527/263000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1055/256 : ℝ)) (lo := (5741/50000 : ℝ)) (hi := (441/3125 : ℝ)) (c := (13145863529562086851/13150000000000000000 : ℝ)) (alpha := (434580418527/263000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13145863529562086851/13150000000000000000 : ℝ)*(X 0 2+X 1 2)+(434580418527/263000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1055/256 : ℝ)) (lo := (5741/50000 : ℝ)) (hi := (441/3125 : ℝ)) (c := (13145863529562086851/13150000000000000000 : ℝ)) (alpha := (434580418527/263000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2117200841/10000000000 : ℝ)*X 0 0+(539108079/1000000000 : ℝ)*X 0 1+(658412577/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668034539/1250000000 : ℝ)*X 1 0+(-544989797/2500000000 : ℝ)*X 1 1+(5267300777/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((167008633/312500000 : ℝ)*X 2 0+(329206301/625000000 : ℝ)*X 2 1+(-544989803/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4349951473/10000000000 : ℝ)*X 0 0+(2113010057/5000000000 : ℝ)*X 0 1+(4477408337/10000000000 : ℝ)*X 0 2+(4349951473/10000000000 : ℝ)*X 1 0+(2113010057/5000000000 : ℝ)*X 1 1+(4477408337/10000000000 : ℝ)*X 1 2+(4349951473/10000000000 : ℝ)*X 2 0+(2113010057/5000000000 : ℝ)*X 2 1+(4477408337/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2117205849/10000000000 : ℝ)*X 0 0+(1316903183/2500000000 : ℝ)*X 0 1+(539076727/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312680489/10000000000 : ℝ)*X 1 0+(-1028246351/5000000000 : ℝ)*X 1 1+(2695383619/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312680489/10000000000 : ℝ)*X 2 0+(2695383633/5000000000 : ℝ)*X 2 1+(-2056492663/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2174980311/5000000000 : ℝ)*X 0 0+(895354811/2000000000 : ℝ)*X 0 1+(2113328491/5000000000 : ℝ)*X 0 2+(2174980311/5000000000 : ℝ)*X 1 0+(895354811/2000000000 : ℝ)*X 1 1+(2113328491/5000000000 : ℝ)*X 1 2+(2174980311/5000000000 : ℝ)*X 2 0+(895354811/2000000000 : ℝ)*X 2 1+(2113328491/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22383137980671606884823/6575000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1017/62500000000 : ℝ)*(base8) + (49925411/25000000000000 : ℝ)*(lower2) + (26377737/100000000000000 : ℝ)*(lower3) + (244943291/100000000000000 : ℝ)*(lower4) + (18555991/100000000000000 : ℝ)*(lower5) + (3014199437912667/50000000000000 : ℝ)*(major0) + (3014199437912667/50000000000000 : ℝ)*(major1) + (3014199437912667/50000000000000 : ℝ)*(major2) + (63116037539323/781250000000 : ℝ)*(sp0) + (4039432773656271/50000000000000 : ℝ)*(sp1) + (4039432773656271/50000000000000 : ℝ)*(sp2) + (994480526517427/25000000000000 : ℝ)*(sp3) + (6370325999/50000000000000 : ℝ)*(sp4) + (4992396213/50000000000000 : ℝ)*(sp7) + (1988966045431067/50000000000000 : ℝ)*(f.failure) + (4039432773656271/50000000000000 : ℝ)*(f.sum) + (27688103112241/6575000000000000000000000000 : ℝ)*base66 + (5228834859902508383/657500000000000000000000000000000 : ℝ)*base68 + (774728698592491617/657500000000000000000000000000000 : ℝ)*base69 + (1911142054382491617/657500000000000000000000000000000 : ℝ)*base71 + (6365610314059/6575000000000000000000000000 : ℝ)*base73 + (1005912650182508383/657500000000000000000000000000000 : ℝ)*base76 + (2338189850822491617/657500000000000000000000000000000 : ℝ)*base77 + (1474334949122508383/657500000000000000000000000000000 : ℝ)*base80 + (57854048848709/6575000000000000000000000000 : ℝ)*base81 + (620731/78125000000000000000 : ℝ)*base90 + (620731/78125000000000000000 : ℝ)*base92 + (620731/78125000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (653281825300929696487141377/82187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1434974349/100000000000000 : ℝ)*(base19) + (1602533531/100000000000000 : ℝ)*(base23) + (71802947/50000000000000 : ℝ)*(upper3) + (14317747/20000000000000 : ℝ)*(lower4) + (84405889/50000000000000 : ℝ)*(upper5) + (757375361131191/12500000000000 : ℝ)*(major0) + (757375361131191/12500000000000 : ℝ)*(major1) + (757375361131191/12500000000000 : ℝ)*(major2) + (39834589057/100000000000000 : ℝ)*(sp1) + (45351254369/100000000000000 : ℝ)*(sp2) + (4059939445778577/50000000000000 : ℝ)*(sp4) + (8119837621993747/100000000000000 : ℝ)*(sp5) + (8119831937769253/100000000000000 : ℝ)*(sp6) + (199906331079301/5000000000000 : ℝ)*(sp7) + (199906331079301/5000000000000 : ℝ)*(f.failure) + (4059939445778577/50000000000000 : ℝ)*(f.sum) + (26144458455211/3287500000000000000000000000 : ℝ)*base66 + (460912392502419541/164375000000000000000000000000000 : ℝ)*base67 + (216397118692419541/164375000000000000000000000000000 : ℝ)*base69 + (1732200009108205459/164375000000000000000000000000000 : ℝ)*base72 + (19112694178311/3287500000000000000000000000 : ℝ)*base74 + (4183964409826794541/164375000000000000000000000000000 : ℝ)*base75 + (764647190971955459/164375000000000000000000000000000 : ℝ)*base78 + (317108484213669541/164375000000000000000000000000000 : ℝ)*base79 + (22630360747347/6575000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (18007/7812500000000000000 : ℝ)*base89 + (18007/7812500000000000000 : ℝ)*base91 + (18007/7812500000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1248_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2367907/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (441/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5741/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5743/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3527/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1248_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1248_s8_0 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068853429/2000000000 : ℝ)*x 0 + (329208489/625000000 : ℝ)*x 1 + (-2179924913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068853429/2000000000 : ℝ)^8441 ≤ (1748948486717/4000000000000 : ℝ)^6393 := by
    have hnat : (1068853429 : ℕ)^8441*4000000000000^6393 ≤ 1748948486717^6393*2000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068853429 2000000000 1748948486717 4000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329208489/625000000 : ℝ)^8441 ≤ (21447297952569/50000000000000 : ℝ)^6393 := by
    have hnat : (329208489 : ℕ)^8441*50000000000000^6393 ≤ 21447297952569^6393*625000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329208489 625000000 21447297952569 50000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2179924913/10000000000 : ℝ)^8441 ≤ (13381691910307/100000000000000 : ℝ)^6393 := by
    have hnat : (2179924913 : ℕ)^8441*100000000000000^6393 ≤ 13381691910307^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179924913 10000000000 13381691910307 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068853429/2000000000 : ℝ), (329208489/625000000 : ℝ), (-2179924913/10000000000 : ℝ)] ![(1748948486717/4000000000000 : ℝ), (21447297952569/50000000000000 : ℝ), (13381691910307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068853429/2000000000 : ℝ)|^8441 ≤ (1748948486717/4000000000000 : ℝ)^6393
        have hw : |(1068853429/2000000000 : ℝ)|=(1068853429/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329208489/625000000 : ℝ)|^8441 ≤ (21447297952569/50000000000000 : ℝ)^6393
        have hw : |(329208489/625000000 : ℝ)|=(329208489/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2179924913/10000000000 : ℝ)|^8441 ≤ (13381691910307/100000000000000 : ℝ)^6393
        have hw : |(-2179924913/10000000000 : ℝ)|=(2179924913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s8_1 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-211720833/1000000000 : ℝ)*x 0 + (1053529537/2000000000 : ℝ)*x 1 + (336920671/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211720833/1000000000 : ℝ)^8441 ≤ (1609465664047/12500000000000 : ℝ)^6393 := by
    have hnat : (211720833 : ℕ)^8441*12500000000000^6393 ≤ 1609465664047^6393*1000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211720833 1000000000 1609465664047 12500000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053529537/2000000000 : ℝ)^8441 ≤ (428979491553/1000000000000 : ℝ)^6393 := by
    have hnat : (1053529537 : ℕ)^8441*1000000000000^6393 ≤ 428979491553^6393*2000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053529537 2000000000 428979491553 1000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (336920671/625000000 : ℝ)^8441 ≤ (44226325516531/100000000000000 : ℝ)^6393 := by
    have hnat : (336920671 : ℕ)^8441*100000000000000^6393 ≤ 44226325516531^6393*625000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336920671 625000000 44226325516531 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-211720833/1000000000 : ℝ), (1053529537/2000000000 : ℝ), (336920671/625000000 : ℝ)] ![(1609465664047/12500000000000 : ℝ), (428979491553/1000000000000 : ℝ), (44226325516531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-211720833/1000000000 : ℝ)|^8441 ≤ (1609465664047/12500000000000 : ℝ)^6393
        have hw : |(-211720833/1000000000 : ℝ)|=(211720833/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053529537/2000000000 : ℝ)|^8441 ≤ (428979491553/1000000000000 : ℝ)^6393
        have hw : |(1053529537/2000000000 : ℝ)|=(1053529537/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(336920671/625000000 : ℝ)|^8441 ≤ (44226325516531/100000000000000 : ℝ)^6393
        have hw : |(336920671/625000000 : ℝ)|=(336920671/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s8_2 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062537897/2000000000 : ℝ)*x 0 + (-1028265063/5000000000 : ℝ)*x 1 + (13476827/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062537897/2000000000 : ℝ)^8441 ≤ (43382922646211/100000000000000 : ℝ)^6393 := by
    have hnat : (1062537897 : ℕ)^8441*100000000000000^6393 ≤ 43382922646211^6393*2000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062537897 2000000000 43382922646211 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1028265063/5000000000 : ℝ)^8441 ≤ (12390751129119/100000000000000 : ℝ)^6393 := by
    have hnat : (1028265063 : ℕ)^8441*100000000000000^6393 ≤ 12390751129119^6393*5000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028265063 5000000000 12390751129119 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13476827/25000000 : ℝ)^8441 ≤ (44226326209801/100000000000000 : ℝ)^6393 := by
    have hnat : (13476827 : ℕ)^8441*100000000000000^6393 ≤ 44226326209801^6393*25000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13476827 25000000 44226326209801 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062537897/2000000000 : ℝ), (-1028265063/5000000000 : ℝ), (13476827/25000000 : ℝ)] ![(43382922646211/100000000000000 : ℝ), (12390751129119/100000000000000 : ℝ), (44226326209801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062537897/2000000000 : ℝ)|^8441 ≤ (43382922646211/100000000000000 : ℝ)^6393
        have hw : |(1062537897/2000000000 : ℝ)|=(1062537897/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1028265063/5000000000 : ℝ)|^8441 ≤ (12390751129119/100000000000000 : ℝ)^6393
        have hw : |(-1028265063/5000000000 : ℝ)|=(1028265063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(13476827/25000000 : ℝ)|^8441 ≤ (44226326209801/100000000000000 : ℝ)^6393
        have hw : |(13476827/25000000 : ℝ)|=(13476827/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s8_3 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312689437/10000000000 : ℝ)*x 0 + (5390730923/10000000000 : ℝ)*x 1 + (-257066253/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312689437/10000000000 : ℝ)^8441 ≤ (21691461064341/50000000000000 : ℝ)^6393 := by
    have hnat : (5312689437 : ℕ)^8441*50000000000000^6393 ≤ 21691461064341^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312689437 10000000000 21691461064341 50000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390730923/10000000000 : ℝ)^8441 ≤ (44226327542179/100000000000000 : ℝ)^6393 := by
    have hnat : (5390730923 : ℕ)^8441*100000000000000^6393 ≤ 44226327542179^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390730923 10000000000 44226327542179 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (257066253/1250000000 : ℝ)^8441 ≤ (1548843789711/12500000000000 : ℝ)^6393 := by
    have hnat : (257066253 : ℕ)^8441*12500000000000^6393 ≤ 1548843789711^6393*1250000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257066253 1250000000 1548843789711 12500000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312689437/10000000000 : ℝ), (5390730923/10000000000 : ℝ), (-257066253/1250000000 : ℝ)] ![(21691461064341/50000000000000 : ℝ), (44226327542179/100000000000000 : ℝ), (1548843789711/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312689437/10000000000 : ℝ)|^8441 ≤ (21691461064341/50000000000000 : ℝ)^6393
        have hw : |(5312689437/10000000000 : ℝ)|=(5312689437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390730923/10000000000 : ℝ)|^8441 ≤ (44226327542179/100000000000000 : ℝ)^6393
        have hw : |(5390730923/10000000000 : ℝ)|=(5390730923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-257066253/1250000000 : ℝ)|^8441 ≤ (1548843789711/12500000000000 : ℝ)^6393
        have hw : |(-257066253/1250000000 : ℝ)|=(257066253/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s8_4 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (543745299/1250000000 : ℝ)*x 0 + (895340273/2000000000 : ℝ)*x 1 + (1056682309/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543745299/1250000000 : ℝ)^8441 ≤ (266541097319/800000000000 : ℝ)^6393 := by
    have hnat : (543745299 : ℕ)^8441*800000000000^6393 ≤ 266541097319^6393*1250000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543745299 1250000000 266541097319 800000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (895340273/2000000000 : ℝ)^8441 ≤ (34605284609153/100000000000000 : ℝ)^6393 := by
    have hnat : (895340273 : ℕ)^8441*100000000000000^6393 ≤ 34605284609153^6393*2000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895340273 2000000000 34605284609153 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056682309/2500000000 : ℝ)^8441 ≤ (4009634775731/12500000000000 : ℝ)^6393 := by
    have hnat : (1056682309 : ℕ)^8441*12500000000000^6393 ≤ 4009634775731^6393*2500000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056682309 2500000000 4009634775731 12500000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(543745299/1250000000 : ℝ), (895340273/2000000000 : ℝ), (1056682309/2500000000 : ℝ)] ![(266541097319/800000000000 : ℝ), (34605284609153/100000000000000 : ℝ), (4009634775731/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(543745299/1250000000 : ℝ)|^8441 ≤ (266541097319/800000000000 : ℝ)^6393
        have hw : |(543745299/1250000000 : ℝ)|=(543745299/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(895340273/2000000000 : ℝ)|^8441 ≤ (34605284609153/100000000000000 : ℝ)^6393
        have hw : |(895340273/2000000000 : ℝ)|=(895340273/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1056682309/2500000000 : ℝ)|^8441 ≤ (4009634775731/12500000000000 : ℝ)^6393
        have hw : |(1056682309/2500000000 : ℝ)|=(1056682309/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1248_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2367907/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3527/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5743/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5743/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14107/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3527/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5743/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3527/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5743/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3527/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5743/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3527/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5743/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3527/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5743/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3527/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5743/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5743/50000 : ℝ) ^ (1055/256 : ℝ) ≤ (1339268224415557/10000000000000000000 : ℝ) := by
    have hpowers : (5743/50000 : ℝ)^1055 ≤ (1339268224415557/10000000000000000000 : ℝ)^256 := by
      have hnat : (5743 : ℕ)^1055*10000000000000000000^256 ≤ 1339268224415557^256*50000^1055 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5743 50000 1339268224415557 10000000000000000000 1055 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5743/50000 : ℝ)) (X := (1339268224415557/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1055 256 (by norm_num) hpowers
    exact h
  have hpowhi : (3527/25000 : ℝ) ^ (1055/256 : ℝ) ≤ (31251249483793371/100000000000000000000 : ℝ) := by
    have hpowers : (3527/25000 : ℝ)^1055 ≤ (31251249483793371/100000000000000000000 : ℝ)^256 := by
      have hnat : (3527 : ℕ)^1055*100000000000000000000^256 ≤ 31251249483793371^256*25000^1055 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3527 25000 31251249483793371 100000000000000000000 1055 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3527/25000 : ℝ)) (X := (31251249483793371/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1055 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001339268224415557/5000000000000000000 : ℝ) ≤ (1250081236468181/1250000000000000 : ℝ) ^ (1055/256 : ℝ) := by
    have hpowers : (5001339268224415557/5000000000000000000 : ℝ)^256 ≤ (1250081236468181/1250000000000000 : ℝ)^1055 := by
      have hnat : (5001339268224415557 : ℕ)^256*1250000000000000^1055 ≤ 1250081236468181^1055*5000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001339268224415557 5000000000000000000 1250081236468181 1250000000000000 256 1055 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250081236468181/1250000000000000 : ℝ)) (X := (5001339268224415557/5000000000000000000 : ℝ)) (by norm_num) 1055 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044643931727948941/100000000000000000000 : ℝ) ≤ (400043324795941/400000000000000 : ℝ) ^ (1055/256 : ℝ) := by
    have hpowers : (100044643931727948941/100000000000000000000 : ℝ)^256 ≤ (400043324795941/400000000000000 : ℝ)^1055 := by
      have hnat : (100044643931727948941 : ℕ)^256*400000000000000^1055 ≤ 400043324795941^1055*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044643931727948941 100000000000000000000 400043324795941 400000000000000 256 1055 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400043324795941/400000000000000 : ℝ)) (X := (100044643931727948941/100000000000000000000 : ℝ)) (by norm_num) 1055 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031251249483793371/50000000000000000000 : ℝ) ≤ (5000758174025801/5000000000000000 : ℝ) ^ (1055/256 : ℝ) := by
    have hpowers : (50031251249483793371/50000000000000000000 : ℝ)^256 ≤ (5000758174025801/5000000000000000 : ℝ)^1055 := by
      have hnat : (50031251249483793371 : ℕ)^256*5000000000000000^1055 ≤ 5000758174025801^1055*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031251249483793371 50000000000000000000 5000758174025801 5000000000000000 256 1055 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000758174025801/5000000000000000 : ℝ)) (X := (50031251249483793371/50000000000000000000 : ℝ)) (by norm_num) 1055 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1339268224415557/10000000000000000000 : ℝ) ≤ ((2184312658252006651/2185000000000000000 : ℝ)+2*(144409384359/87400000000000 : ℝ)*(5743/50000 : ℝ))^(1055/256 : ℝ) := by
    rw [show (2184312658252006651/2185000000000000000 : ℝ)+2*(144409384359/87400000000000 : ℝ)*(5743/50000 : ℝ)=(1250081236468181/1250000000000000 : ℝ) by norm_num, show 1+2*(1339268224415557/10000000000000000000 : ℝ)=(5001339268224415557/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31251249483793371/100000000000000000000 : ℝ)+(1339268224415557/10000000000000000000 : ℝ) ≤ ((2184312658252006651/2185000000000000000 : ℝ)+(144409384359/87400000000000 : ℝ)*((3527/25000 : ℝ)+(5743/50000 : ℝ)))^(1055/256 : ℝ) := by
    rw [show (2184312658252006651/2185000000000000000 : ℝ)+(144409384359/87400000000000 : ℝ)*((3527/25000 : ℝ)+(5743/50000 : ℝ))=(400043324795941/400000000000000 : ℝ) by norm_num, show 1+(31251249483793371/100000000000000000000 : ℝ)+(1339268224415557/10000000000000000000 : ℝ)=(100044643931727948941/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31251249483793371/100000000000000000000 : ℝ) ≤ ((2184312658252006651/2185000000000000000 : ℝ)+2*(144409384359/87400000000000 : ℝ)*(3527/25000 : ℝ))^(1055/256 : ℝ) := by
    rw [show (2184312658252006651/2185000000000000000 : ℝ)+2*(144409384359/87400000000000 : ℝ)*(3527/25000 : ℝ)=(5000758174025801/5000000000000000 : ℝ) by norm_num, show 1+2*(31251249483793371/100000000000000000000 : ℝ)=(50031251249483793371/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2184312658252006651/2185000000000000000 : ℝ)*(X 1 0+X 2 0)+(144409384359/87400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1055/256 : ℝ)) (lo := (5743/50000 : ℝ)) (hi := (3527/25000 : ℝ)) (c := (2184312658252006651/2185000000000000000 : ℝ)) (alpha := (144409384359/87400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2184312658252006651/2185000000000000000 : ℝ)*(X 0 1+X 2 1)+(144409384359/87400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1055/256 : ℝ)) (lo := (5743/50000 : ℝ)) (hi := (3527/25000 : ℝ)) (c := (2184312658252006651/2185000000000000000 : ℝ)) (alpha := (144409384359/87400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2184312658252006651/2185000000000000000 : ℝ)*(X 0 2+X 1 2)+(144409384359/87400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1055/256 : ℝ)) (lo := (5743/50000 : ℝ)) (hi := (3527/25000 : ℝ)) (c := (2184312658252006651/2185000000000000000 : ℝ)) (alpha := (144409384359/87400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((1068853429/2000000000 : ℝ)*X 2 0+(329208489/625000000 : ℝ)*X 2 1+(-2179924913/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s8_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-211720833/1000000000 : ℝ)*X 0 0+(1053529537/2000000000 : ℝ)*X 0 1+(336920671/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s8_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1062537897/2000000000 : ℝ)*X 1 0+(-1028265063/5000000000 : ℝ)*X 1 1+(13476827/25000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s8_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5312689437/10000000000 : ℝ)*X 2 0+(5390730923/10000000000 : ℝ)*X 2 1+(-257066253/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s8_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((543745299/1250000000 : ℝ)*X 0 0+(895340273/2000000000 : ℝ)*X 0 1+(1056682309/2500000000 : ℝ)*X 0 2+(543745299/1250000000 : ℝ)*X 1 0+(895340273/2000000000 : ℝ)*X 1 1+(1056682309/2500000000 : ℝ)*X 1 2+(543745299/1250000000 : ℝ)*X 2 0+(895340273/2000000000 : ℝ)*X 2 1+(1056682309/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s8_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (139937493085594539801/17480000000000000000000000 : ℝ) := by norm_num
    linear_combination (324129687/100000000000000 : ℝ)*(base19) + (671935697/100000000000000 : ℝ)*(base23) + (80893203/100000000000000 : ℝ)*(lower1) + (7531513/6250000000000 : ℝ)*(upper3) + (16775609/10000000000000 : ℝ)*(lower4) + (71090163/100000000000000 : ℝ)*(upper5) + (303125598716717/5000000000000 : ℝ)*(major0) + (303125598716717/5000000000000 : ℝ)*(major1) + (303125598716717/5000000000000 : ℝ)*(major2) + (17740502247/100000000000000 : ℝ)*(sp0) + (1015572692014543/12500000000000 : ℝ)*(sp1) + (8124581211986657/100000000000000 : ℝ)*(sp2) + (8124563123678399/100000000000000 : ℝ)*(sp3) + (250027634106233/6250000000000 : ℝ)*(sp4) + (250027634106233/6250000000000 : ℝ)*(f.failure) + (1015572692014543/12500000000000 : ℝ)*(f.sum) + (824439206867/218500000000000000000000000 : ℝ)*base65 + (91595450049040233/10925000000000000000000000000000 : ℝ)*base68 + (165531530653640233/10925000000000000000000000000000 : ℝ)*base70 + (946705202579534767/10925000000000000000000000000000 : ℝ)*base71 + (30348168859/4370000000000000000000000 : ℝ)*base73 + (1164144117248440233/10925000000000000000000000000000 : ℝ)*base76 + (64085983556509767/10925000000000000000000000000000 : ℝ)*base77 + (159572865523334767/10925000000000000000000000000000 : ℝ)*base79 + (2644486148271/437000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (13147/4882812500000000000 : ℝ)*base90 + (13147/4882812500000000000 : ℝ)*base92 + (13147/4882812500000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1248_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2367907/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3527/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5743/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5743/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14107/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1248_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1248_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2367907/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14133/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5731/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5743/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14107/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1248_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1248_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1248_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2367907/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14133/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5731/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5743/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14107/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1248_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
