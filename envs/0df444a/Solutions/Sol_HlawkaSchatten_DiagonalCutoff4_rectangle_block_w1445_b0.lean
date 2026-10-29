-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1445_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:57:35.14151+00:00
-- url     : https://prove2.me/submissions/755b23d2-455b-4124-8f1a-aa5d49ec30aa

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
theorem support_rectangle_w1445_s0_0 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-69991603/400000000 : ℝ)*x 0 + (74420079/125000000 : ℝ)*x 1 + (1208720799/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (69991603/400000000 : ℝ)^4405 ≤ (2580179312333/25000000000000 : ℝ)^3381 := by
    have hnat : (69991603 : ℕ)^4405*25000000000000^3381 ≤ 2580179312333^3381*400000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69991603 400000000 2580179312333 25000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (74420079/125000000 : ℝ)^4405 ≤ (50882448052213/100000000000000 : ℝ)^3381 := by
    have hnat : (74420079 : ℕ)^4405*100000000000000^3381 ≤ 50882448052213^3381*125000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74420079 125000000 50882448052213 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1208720799/2500000000 : ℝ)^4405 ≤ (19398417342569/50000000000000 : ℝ)^3381 := by
    have hnat : (1208720799 : ℕ)^4405*50000000000000^3381 ≤ 19398417342569^3381*2500000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1208720799 2500000000 19398417342569 50000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-69991603/400000000 : ℝ), (74420079/125000000 : ℝ), (1208720799/2500000000 : ℝ)] ![(2580179312333/25000000000000 : ℝ), (50882448052213/100000000000000 : ℝ), (19398417342569/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-69991603/400000000 : ℝ)|^4405 ≤ (2580179312333/25000000000000 : ℝ)^3381
        have hw : |(-69991603/400000000 : ℝ)|=(69991603/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(74420079/125000000 : ℝ)|^4405 ≤ (50882448052213/100000000000000 : ℝ)^3381
        have hw : |(74420079/125000000 : ℝ)|=(74420079/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1208720799/2500000000 : ℝ)|^4405 ≤ (19398417342569/50000000000000 : ℝ)^3381
        have hw : |(1208720799/2500000000 : ℝ)|=(1208720799/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_s0_1 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2745160853/5000000000 : ℝ)*x 0 + (-1190528023/5000000000 : ℝ)*x 1 + (2417441527/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2745160853/5000000000 : ℝ)^4405 ≤ (11446429879449/25000000000000 : ℝ)^3381 := by
    have hnat : (2745160853 : ℕ)^4405*25000000000000^3381 ≤ 11446429879449^3381*5000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2745160853 5000000000 11446429879449 25000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1190528023/5000000000 : ℝ)^4405 ≤ (1927180909601/12500000000000 : ℝ)^3381 := by
    have hnat : (1190528023 : ℕ)^4405*12500000000000^3381 ≤ 1927180909601^3381*5000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1190528023 5000000000 1927180909601 12500000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2417441527/5000000000 : ℝ)^4405 ≤ (38796833200573/100000000000000 : ℝ)^3381 := by
    have hnat : (2417441527 : ℕ)^4405*100000000000000^3381 ≤ 38796833200573^3381*5000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2417441527 5000000000 38796833200573 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2745160853/5000000000 : ℝ), (-1190528023/5000000000 : ℝ), (2417441527/5000000000 : ℝ)] ![(11446429879449/25000000000000 : ℝ), (1927180909601/12500000000000 : ℝ), (38796833200573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2745160853/5000000000 : ℝ)|^4405 ≤ (11446429879449/25000000000000 : ℝ)^3381
        have hw : |(2745160853/5000000000 : ℝ)|=(2745160853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1190528023/5000000000 : ℝ)|^4405 ≤ (1927180909601/12500000000000 : ℝ)^3381
        have hw : |(-1190528023/5000000000 : ℝ)|=(1190528023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2417441527/5000000000 : ℝ)|^4405 ≤ (38796833200573/100000000000000 : ℝ)^3381
        have hw : |(2417441527/5000000000 : ℝ)|=(2417441527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_s0_2 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1098064319/2000000000 : ℝ)*x 0 + (4834883017/10000000000 : ℝ)*x 1 + (-1190528117/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1098064319/2000000000 : ℝ)^4405 ≤ (11446429577943/25000000000000 : ℝ)^3381 := by
    have hnat : (1098064319 : ℕ)^4405*25000000000000^3381 ≤ 11446429577943^3381*2000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098064319 2000000000 11446429577943 25000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4834883017/10000000000 : ℝ)^4405 ≤ (38796832813749/100000000000000 : ℝ)^3381 := by
    have hnat : (4834883017 : ℕ)^4405*100000000000000^3381 ≤ 38796832813749^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4834883017 10000000000 38796832813749 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1190528117/5000000000 : ℝ)^4405 ≤ (7708724431401/50000000000000 : ℝ)^3381 := by
    have hnat : (1190528117 : ℕ)^4405*50000000000000^3381 ≤ 7708724431401^3381*5000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1190528117 5000000000 7708724431401 50000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1098064319/2000000000 : ℝ), (4834883017/10000000000 : ℝ), (-1190528117/5000000000 : ℝ)] ![(11446429577943/25000000000000 : ℝ), (38796832813749/100000000000000 : ℝ), (7708724431401/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1098064319/2000000000 : ℝ)|^4405 ≤ (11446429577943/25000000000000 : ℝ)^3381
        have hw : |(1098064319/2000000000 : ℝ)|=(1098064319/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4834883017/10000000000 : ℝ)|^4405 ≤ (38796832813749/100000000000000 : ℝ)^3381
        have hw : |(4834883017/10000000000 : ℝ)|=(4834883017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1190528117/5000000000 : ℝ)|^4405 ≤ (7708724431401/50000000000000 : ℝ)^3381
        have hw : |(-1190528117/5000000000 : ℝ)|=(1190528117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_s0_3 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4163715043/10000000000 : ℝ)*x 0 + (3102996091/10000000000 : ℝ)*x 1 + (346085223/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4163715043/10000000000 : ℝ)^4405 ≤ (15966274983069/50000000000000 : ℝ)^3381 := by
    have hnat : (4163715043 : ℕ)^4405*50000000000000^3381 ≤ 15966274983069^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4163715043 10000000000 15966274983069 50000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3102996091/10000000000 : ℝ)^4405 ≤ (21769954971119/100000000000000 : ℝ)^3381 := by
    have hnat : (3102996091 : ℕ)^4405*100000000000000^3381 ≤ 21769954971119^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3102996091 10000000000 21769954971119 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (346085223/625000000 : ℝ)^4405 ≤ (46297495048149/100000000000000 : ℝ)^3381 := by
    have hnat : (346085223 : ℕ)^4405*100000000000000^3381 ≤ 46297495048149^3381*625000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      346085223 625000000 46297495048149 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4163715043/10000000000 : ℝ), (3102996091/10000000000 : ℝ), (346085223/625000000 : ℝ)] ![(15966274983069/50000000000000 : ℝ), (21769954971119/100000000000000 : ℝ), (46297495048149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4163715043/10000000000 : ℝ)|^4405 ≤ (15966274983069/50000000000000 : ℝ)^3381
        have hw : |(4163715043/10000000000 : ℝ)|=(4163715043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3102996091/10000000000 : ℝ)|^4405 ≤ (21769954971119/100000000000000 : ℝ)^3381
        have hw : |(3102996091/10000000000 : ℝ)|=(3102996091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(346085223/625000000 : ℝ)|^4405 ≤ (46297495048149/100000000000000 : ℝ)^3381
        have hw : |(346085223/625000000 : ℝ)|=(346085223/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_s0_4 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-175373157/1000000000 : ℝ)*x 0 + (4863470737/10000000000 : ℝ)*x 1 + (2961998929/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (175373157/1000000000 : ℝ)^4405 ≤ (1035101662603/10000000000000 : ℝ)^3381 := by
    have hnat : (175373157 : ℕ)^4405*10000000000000^3381 ≤ 1035101662603^3381*1000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175373157 1000000000 1035101662603 10000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4863470737/10000000000 : ℝ)^4405 ≤ (4886996966539/12500000000000 : ℝ)^3381 := by
    have hnat : (4863470737 : ℕ)^4405*12500000000000^3381 ≤ 4886996966539^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4863470737 10000000000 4886996966539 12500000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2961998929/5000000000 : ℝ)^4405 ≤ (50553007619671/100000000000000 : ℝ)^3381 := by
    have hnat : (2961998929 : ℕ)^4405*100000000000000^3381 ≤ 50553007619671^3381*5000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2961998929 5000000000 50553007619671 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-175373157/1000000000 : ℝ), (4863470737/10000000000 : ℝ), (2961998929/5000000000 : ℝ)] ![(1035101662603/10000000000000 : ℝ), (4886996966539/12500000000000 : ℝ), (50553007619671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-175373157/1000000000 : ℝ)|^4405 ≤ (1035101662603/10000000000000 : ℝ)^3381
        have hw : |(-175373157/1000000000 : ℝ)|=(175373157/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4863470737/10000000000 : ℝ)|^4405 ≤ (4886996966539/12500000000000 : ℝ)^3381
        have hw : |(4863470737/10000000000 : ℝ)|=(4863470737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2961998929/5000000000 : ℝ)|^4405 ≤ (50553007619671/100000000000000 : ℝ)^3381
        have hw : |(2961998929/5000000000 : ℝ)|=(2961998929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_s0_5 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (103698153/200000000 : ℝ)*x 0 + (-40373169/312500000 : ℝ)*x 1 + (5923997927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (103698153/200000000 : ℝ)^4405 ≤ (21247847315913/50000000000000 : ℝ)^3381 := by
    have hnat : (103698153 : ℕ)^4405*50000000000000^3381 ≤ 21247847315913^3381*200000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103698153 200000000 21247847315913 50000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40373169/312500000 : ℝ)^4405 ≤ (868912120939/12500000000000 : ℝ)^3381 := by
    have hnat : (40373169 : ℕ)^4405*12500000000000^3381 ≤ 868912120939^3381*312500000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40373169 312500000 868912120939 12500000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5923997927/10000000000 : ℝ)^4405 ≤ (6319126048353/12500000000000 : ℝ)^3381 := by
    have hnat : (5923997927 : ℕ)^4405*12500000000000^3381 ≤ 6319126048353^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5923997927 10000000000 6319126048353 12500000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(103698153/200000000 : ℝ), (-40373169/312500000 : ℝ), (5923997927/10000000000 : ℝ)] ![(21247847315913/50000000000000 : ℝ), (868912120939/12500000000000 : ℝ), (6319126048353/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(103698153/200000000 : ℝ)|^4405 ≤ (21247847315913/50000000000000 : ℝ)^3381
        have hw : |(103698153/200000000 : ℝ)|=(103698153/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-40373169/312500000 : ℝ)|^4405 ≤ (868912120939/12500000000000 : ℝ)^3381
        have hw : |(-40373169/312500000 : ℝ)|=(40373169/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5923997927/10000000000 : ℝ)|^4405 ≤ (6319126048353/12500000000000 : ℝ)^3381
        have hw : |(5923997927/10000000000 : ℝ)|=(5923997927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_s0_6 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5184907679/10000000000 : ℝ)*x 0 + (5923997773/10000000000 : ℝ)*x 1 + (-1291941609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5184907679/10000000000 : ℝ)^4405 ≤ (42495694941499/100000000000000 : ℝ)^3381 := by
    have hnat : (5184907679 : ℕ)^4405*100000000000000^3381 ≤ 42495694941499^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184907679 10000000000 42495694941499 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5923997773/10000000000 : ℝ)^4405 ≤ (12638251668657/25000000000000 : ℝ)^3381 := by
    have hnat : (5923997773 : ℕ)^4405*25000000000000^3381 ≤ 12638251668657^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5923997773 10000000000 12638251668657 25000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1291941609/10000000000 : ℝ)^4405 ≤ (6951298376541/100000000000000 : ℝ)^3381 := by
    have hnat : (1291941609 : ℕ)^4405*100000000000000^3381 ≤ 6951298376541^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1291941609 10000000000 6951298376541 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5184907679/10000000000 : ℝ), (5923997773/10000000000 : ℝ), (-1291941609/10000000000 : ℝ)] ![(42495694941499/100000000000000 : ℝ), (12638251668657/25000000000000 : ℝ), (6951298376541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5184907679/10000000000 : ℝ)|^4405 ≤ (42495694941499/100000000000000 : ℝ)^3381
        have hw : |(5184907679/10000000000 : ℝ)|=(5184907679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5923997773/10000000000 : ℝ)|^4405 ≤ (12638251668657/25000000000000 : ℝ)^3381
        have hw : |(5923997773/10000000000 : ℝ)|=(5923997773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1291941609/10000000000 : ℝ)|^4405 ≤ (6951298376541/100000000000000 : ℝ)^3381
        have hw : |(-1291941609/10000000000 : ℝ)|=(1291941609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_s0_7 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4172290989/10000000000 : ℝ)*x 0 + (5475156017/10000000000 : ℝ)*x 1 + (3167425033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4172290989/10000000000 : ℝ)^4405 ≤ (6403653542899/20000000000000 : ℝ)^3381 := by
    have hnat : (4172290989 : ℕ)^4405*20000000000000^3381 ≤ 6403653542899^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172290989 10000000000 6403653542899 20000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5475156017/10000000000 : ℝ)^4405 ≤ (9124202407927/20000000000000 : ℝ)^3381 := by
    have hnat : (5475156017 : ℕ)^4405*20000000000000^3381 ≤ 9124202407927^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5475156017 10000000000 9124202407927 20000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3167425033/10000000000 : ℝ)^4405 ≤ (22360720225759/100000000000000 : ℝ)^3381 := by
    have hnat : (3167425033 : ℕ)^4405*100000000000000^3381 ≤ 22360720225759^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3167425033 10000000000 22360720225759 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4172290989/10000000000 : ℝ), (5475156017/10000000000 : ℝ), (3167425033/10000000000 : ℝ)] ![(6403653542899/20000000000000 : ℝ), (9124202407927/20000000000000 : ℝ), (22360720225759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4172290989/10000000000 : ℝ)|^4405 ≤ (6403653542899/20000000000000 : ℝ)^3381
        have hw : |(4172290989/10000000000 : ℝ)|=(4172290989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5475156017/10000000000 : ℝ)|^4405 ≤ (9124202407927/20000000000000 : ℝ)^3381
        have hw : |(5475156017/10000000000 : ℝ)|=(5475156017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3167425033/10000000000 : ℝ)|^4405 ≤ (22360720225759/100000000000000 : ℝ)^3381
        have hw : |(3167425033/10000000000 : ℝ)|=(3167425033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1445_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79400569/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (27/1250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6537/25000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (1101/256 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^1101 ≤ (0 : ℝ)^256 := by
      have hnat : (0 : ℕ)^1101*1^256 ≤ 0^256*1^1101 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 1101 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 1101 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (1101/256 : ℝ) ≤ (242916539159901293/12500000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^1101 ≤ (242916539159901293/12500000000000000000 : ℝ)^256 := by
      have hnat : (2 : ℕ)^1101*12500000000000000000^256 ≤ 242916539159901293^256*5^1101 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 242916539159901293 12500000000000000000 1101 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (242916539159901293/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 1101 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (1101/256 : ℝ) := by
    have hpowers : (1 : ℝ)^256 ≤ (1 : ℝ)^1101 := by
      have hnat : (1 : ℕ)^256*1^1101 ≤ 1^1101*1^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 256 1101 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 1101 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (12742916539159901293/12500000000000000000 : ℝ) ≤ (627803275373981/625000000000000 : ℝ) ^ (1101/256 : ℝ) := by
    have hpowers : (12742916539159901293/12500000000000000000 : ℝ)^256 ≤ (627803275373981/625000000000000 : ℝ)^1101 := by
      have hnat : (12742916539159901293 : ℕ)^256*625000000000000^1101 ≤ 627803275373981^1101*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12742916539159901293 12500000000000000000 627803275373981 625000000000000 256 1101 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (627803275373981/625000000000000 : ℝ)) (X := (12742916539159901293/12500000000000000000 : ℝ)) (by norm_num) 1101 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (6492916539159901293/6250000000000000000 : ℝ) ≤ (315303275373981/312500000000000 : ℝ) ^ (1101/256 : ℝ) := by
    have hpowers : (6492916539159901293/6250000000000000000 : ℝ)^256 ≤ (315303275373981/312500000000000 : ℝ)^1101 := by
      have hnat : (6492916539159901293 : ℕ)^256*312500000000000^1101 ≤ 315303275373981^1101*6250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6492916539159901293 6250000000000000000 315303275373981 312500000000000 256 1101 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (315303275373981/312500000000000 : ℝ)) (X := (6492916539159901293/6250000000000000000 : ℝ)) (by norm_num) 1101 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(2803275373981/250000000000000 : ℝ)*(0 : ℝ))^(1101/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(2803275373981/250000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(242916539159901293/12500000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(2803275373981/250000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(1101/256 : ℝ) := by
    rw [show (1 : ℝ)+(2803275373981/250000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(627803275373981/625000000000000 : ℝ) by norm_num, show 1+(242916539159901293/12500000000000000000 : ℝ)+(0 : ℝ)=(12742916539159901293/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(242916539159901293/12500000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(2803275373981/250000000000000 : ℝ)*(2/5 : ℝ))^(1101/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(2803275373981/250000000000000 : ℝ)*(2/5 : ℝ)=(315303275373981/312500000000000 : ℝ) by norm_num, show 1+2*(242916539159901293/12500000000000000000 : ℝ)=(6492916539159901293/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(2803275373981/250000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1101/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2803275373981/250000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(2803275373981/250000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1101/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2803275373981/250000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(2803275373981/250000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1101/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2803275373981/250000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-69991603/400000000 : ℝ)*X 0 0+(74420079/125000000 : ℝ)*X 0 1+(1208720799/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2745160853/5000000000 : ℝ)*X 1 0+(-1190528023/5000000000 : ℝ)*X 1 1+(2417441527/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1098064319/2000000000 : ℝ)*X 2 0+(4834883017/10000000000 : ℝ)*X 2 1+(-1190528117/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4163715043/10000000000 : ℝ)*X 0 0+(3102996091/10000000000 : ℝ)*X 0 1+(346085223/625000000 : ℝ)*X 0 2+(4163715043/10000000000 : ℝ)*X 1 0+(3102996091/10000000000 : ℝ)*X 1 1+(346085223/625000000 : ℝ)*X 1 2+(4163715043/10000000000 : ℝ)*X 2 0+(3102996091/10000000000 : ℝ)*X 2 1+(346085223/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-175373157/1000000000 : ℝ)*X 0 0+(4863470737/10000000000 : ℝ)*X 0 1+(2961998929/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((103698153/200000000 : ℝ)*X 1 0+(-40373169/312500000 : ℝ)*X 1 1+(5923997927/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5184907679/10000000000 : ℝ)*X 2 0+(5923997773/10000000000 : ℝ)*X 2 1+(-1291941609/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4172290989/10000000000 : ℝ)*X 0 0+(5475156017/10000000000 : ℝ)*X 0 1+(3167425033/10000000000 : ℝ)*X 0 2+(4172290989/10000000000 : ℝ)*X 1 0+(5475156017/10000000000 : ℝ)*X 1 1+(3167425033/10000000000 : ℝ)*X 1 2+(4172290989/10000000000 : ℝ)*X 2 0+(5475156017/10000000000 : ℝ)*X 2 1+(3167425033/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15838691063917808309859/3125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14459631/10000000000000 : ℝ)*(base1) + (572127437/50000000000000 : ℝ)*(base19) + (563091457/50000000000000 : ℝ)*(base23) + (14944057/10000000000000 : ℝ)*(upper3) + (4659549/5000000000000 : ℝ)*(upper5) + (81541912915777/12500000000000 : ℝ)*(major0) + (81541912915777/12500000000000 : ℝ)*(major1) + (81541912915777/12500000000000 : ℝ)*(major2) + (223469934196977/25000000000000 : ℝ)*(sp0) + (893881743978023/100000000000000 : ℝ)*(sp1) + (13966902532031/1562500000000 : ℝ)*(sp2) + (205392874765981/50000000000000 : ℝ)*(sp3) + (3296041299/100000000000000 : ℝ)*(sp4) + (827672609/50000000000000 : ℝ)*(sp7) + (410787549473491/100000000000000 : ℝ)*(f.failure) + (893882888232897/100000000000000 : ℝ)*(f.sum) + (2595803819431/781250000000000000000000000 : ℝ)*base65 + (11531941394431/1562500000000000000000000000 : ℝ)*base67 + (10787213926763/3125000000000000000000000000 : ℝ)*base70 + (2159417054487/3125000000000000000000000000 : ℝ)*base71 + (5174446200681/781250000000000000000000000 : ℝ)*base73 + (3617815035737/3125000000000000000000000000 : ℝ)*base75 + (10842886826763/3125000000000000000000000000 : ℝ)*base78 + (13024791601763/3125000000000000000000000000 : ℝ)*base80 + (236411032507/97656250000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (35816379/5000000000000000000000 : ℝ)*base89 + (35816379/5000000000000000000000 : ℝ)*base91 + (35816379/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (767560695773801800167/156250000000000000000000000 : ℝ) := by norm_num
    linear_combination (561741133/50000000000000 : ℝ)*(base19) + (1133257881/100000000000000 : ℝ)*(base23) + (1230553/1000000000000 : ℝ)*(base32) + (85700723/50000000000000 : ℝ)*(upper3) + (19322489/20000000000000 : ℝ)*(upper5) + (137625283224201/20000000000000 : ℝ)*(major0) + (137625283224201/20000000000000 : ℝ)*(major1) + (137625283224201/20000000000000 : ℝ)*(major2) + (2690591787/100000000000000 : ℝ)*(sp1) + (2767016567/100000000000000 : ℝ)*(sp2) + (942926796409713/100000000000000 : ℝ)*(sp4) + (47146149116783/5000000000000 : ℝ)*(sp5) + (188584579227053/20000000000000 : ℝ)*(sp6) + (433325749030709/100000000000000 : ℝ)*(sp7) + (54165734010751/12500000000000 : ℝ)*(f.failure) + (942926796409713/100000000000000 : ℝ)*(f.sum) + (2651859563319/2500000000000000000000000000 : ℝ)*base66 + (87582227755819/5000000000000000000000000000 : ℝ)*base68 + (12269920840819/5000000000000000000000000000 : ℝ)*base70 + (42887299200819/5000000000000000000000000000 : ℝ)*base72 + (23985811513319/2500000000000000000000000000 : ℝ)*base74 + (21038218660819/5000000000000000000000000000 : ℝ)*base76 + (32341482590819/5000000000000000000000000000 : ℝ)*base78 + (46955422770819/5000000000000000000000000000 : ℝ)*base80 + (6628824079181/2500000000000000000000000000 : ℝ)*base81 + (267319/625000000000000000000 : ℝ)*base89 + (267319/625000000000000000000 : ℝ)*base91 + (267319/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1445_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79400569/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (27/1250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6537/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1445_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1445_s1_0 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1919884063/10000000000 : ℝ)*x 0 + (349930027/625000000 : ℝ)*x 1 + (2540268933/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1919884063/10000000000 : ℝ)^4405 ≤ (2911663941499/25000000000000 : ℝ)^3381 := by
    have hnat : (1919884063 : ℕ)^4405*25000000000000^3381 ≤ 2911663941499^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1919884063 10000000000 2911663941499 25000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (349930027/625000000 : ℝ)^4405 ≤ (46968734588503/100000000000000 : ℝ)^3381 := by
    have hnat : (349930027 : ℕ)^4405*100000000000000^3381 ≤ 46968734588503^3381*625000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      349930027 625000000 46968734588503 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2540268933/5000000000 : ℝ)^4405 ≤ (4138460963237/10000000000000 : ℝ)^3381 := by
    have hnat : (2540268933 : ℕ)^4405*10000000000000^3381 ≤ 4138460963237^3381*5000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2540268933 5000000000 4138460963237 10000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1919884063/10000000000 : ℝ), (349930027/625000000 : ℝ), (2540268933/5000000000 : ℝ)] ![(2911663941499/25000000000000 : ℝ), (46968734588503/100000000000000 : ℝ), (4138460963237/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1919884063/10000000000 : ℝ)|^4405 ≤ (2911663941499/25000000000000 : ℝ)^3381
        have hw : |(-1919884063/10000000000 : ℝ)|=(1919884063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(349930027/625000000 : ℝ)|^4405 ≤ (46968734588503/100000000000000 : ℝ)^3381
        have hw : |(349930027/625000000 : ℝ)|=(349930027/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2540268933/5000000000 : ℝ)|^4405 ≤ (4138460963237/10000000000000 : ℝ)^3381
        have hw : |(2540268933/5000000000 : ℝ)|=(2540268933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_s1_1 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5395210719/10000000000 : ℝ)*x 0 + (-219421589/1000000000 : ℝ)*x 1 + (2540269679/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5395210719/10000000000 : ℝ)^4405 ≤ (44755052825271/100000000000000 : ℝ)^3381 := by
    have hnat : (5395210719 : ℕ)^4405*100000000000000^3381 ≤ 44755052825271^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395210719 10000000000 44755052825271 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (219421589/1000000000 : ℝ)^4405 ≤ (13860321697243/100000000000000 : ℝ)^3381 := by
    have hnat : (219421589 : ℕ)^4405*100000000000000^3381 ≤ 13860321697243^3381*1000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219421589 1000000000 13860321697243 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2540269679/5000000000 : ℝ)^4405 ≤ (20692312733333/50000000000000 : ℝ)^3381 := by
    have hnat : (2540269679 : ℕ)^4405*50000000000000^3381 ≤ 20692312733333^3381*5000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2540269679 5000000000 20692312733333 50000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5395210719/10000000000 : ℝ), (-219421589/1000000000 : ℝ), (2540269679/5000000000 : ℝ)] ![(44755052825271/100000000000000 : ℝ), (13860321697243/100000000000000 : ℝ), (20692312733333/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5395210719/10000000000 : ℝ)|^4405 ≤ (44755052825271/100000000000000 : ℝ)^3381
        have hw : |(5395210719/10000000000 : ℝ)|=(5395210719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-219421589/1000000000 : ℝ)|^4405 ≤ (13860321697243/100000000000000 : ℝ)^3381
        have hw : |(-219421589/1000000000 : ℝ)|=(219421589/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2540269679/5000000000 : ℝ)|^4405 ≤ (20692312733333/50000000000000 : ℝ)^3381
        have hw : |(2540269679/5000000000 : ℝ)|=(2540269679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_s1_2 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (674401489/1250000000 : ℝ)*x 0 + (5080538019/10000000000 : ℝ)*x 1 + (-43884321/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (674401489/1250000000 : ℝ)^4405 ≤ (44755065718891/100000000000000 : ℝ)^3381 := by
    have hnat : (674401489 : ℕ)^4405*100000000000000^3381 ≤ 44755065718891^3381*1250000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674401489 1250000000 44755065718891 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5080538019/10000000000 : ℝ)^4405 ≤ (646634550877/1562500000000 : ℝ)^3381 := by
    have hnat : (5080538019 : ℕ)^4405*1562500000000^3381 ≤ 646634550877^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5080538019 10000000000 646634550877 1562500000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43884321/200000000 : ℝ)^4405 ≤ (13860323014027/100000000000000 : ℝ)^3381 := by
    have hnat : (43884321 : ℕ)^4405*100000000000000^3381 ≤ 13860323014027^3381*200000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43884321 200000000 13860323014027 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(674401489/1250000000 : ℝ), (5080538019/10000000000 : ℝ), (-43884321/200000000 : ℝ)] ![(44755065718891/100000000000000 : ℝ), (646634550877/1562500000000 : ℝ), (13860323014027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(674401489/1250000000 : ℝ)|^4405 ≤ (44755065718891/100000000000000 : ℝ)^3381
        have hw : |(674401489/1250000000 : ℝ)|=(674401489/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5080538019/10000000000 : ℝ)|^4405 ≤ (646634550877/1562500000000 : ℝ)^3381
        have hw : |(5080538019/10000000000 : ℝ)|=(5080538019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-43884321/200000000 : ℝ)|^4405 ≤ (13860323014027/100000000000000 : ℝ)^3381
        have hw : |(-43884321/200000000 : ℝ)|=(43884321/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_s1_3 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4273726699/10000000000 : ℝ)*x 0 + (3742759177/10000000000 : ℝ)*x 1 + (974136237/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4273726699/10000000000 : ℝ)^4405 ≤ (1651808012267/5000000000000 : ℝ)^3381 := by
    have hnat : (4273726699 : ℕ)^4405*5000000000000^3381 ≤ 1651808012267^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4273726699 10000000000 1651808012267 5000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3742759177/10000000000 : ℝ)^4405 ≤ (2779232935781/10000000000000 : ℝ)^3381 := by
    have hnat : (3742759177 : ℕ)^4405*10000000000000^3381 ≤ 2779232935781^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3742759177 10000000000 2779232935781 10000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (974136237/2000000000 : ℝ)^4405 ≤ (1566860415149/4000000000000 : ℝ)^3381 := by
    have hnat : (974136237 : ℕ)^4405*4000000000000^3381 ≤ 1566860415149^3381*2000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      974136237 2000000000 1566860415149 4000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4273726699/10000000000 : ℝ), (3742759177/10000000000 : ℝ), (974136237/2000000000 : ℝ)] ![(1651808012267/5000000000000 : ℝ), (2779232935781/10000000000000 : ℝ), (1566860415149/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4273726699/10000000000 : ℝ)|^4405 ≤ (1651808012267/5000000000000 : ℝ)^3381
        have hw : |(4273726699/10000000000 : ℝ)|=(4273726699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3742759177/10000000000 : ℝ)|^4405 ≤ (2779232935781/10000000000000 : ℝ)^3381
        have hw : |(3742759177/10000000000 : ℝ)|=(3742759177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(974136237/2000000000 : ℝ)|^4405 ≤ (1566860415149/4000000000000 : ℝ)^3381
        have hw : |(974136237/2000000000 : ℝ)|=(974136237/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_s1_4 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-384052169/2000000000 : ℝ)*x 0 + (2543270089/5000000000 : ℝ)*x 1 + (2796388817/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (384052169/2000000000 : ℝ)^4405 ≤ (5824816901299/50000000000000 : ℝ)^3381 := by
    have hnat : (384052169 : ℕ)^4405*50000000000000^3381 ≤ 5824816901299^3381*2000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      384052169 2000000000 5824816901299 50000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2543270089/5000000000 : ℝ)^4405 ≤ (10362080588227/25000000000000 : ℝ)^3381 := by
    have hnat : (2543270089 : ℕ)^4405*25000000000000^3381 ≤ 10362080588227^3381*5000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2543270089 5000000000 10362080588227 25000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2796388817/5000000000 : ℝ)^4405 ≤ (2931377739023/6250000000000 : ℝ)^3381 := by
    have hnat : (2796388817 : ℕ)^4405*6250000000000^3381 ≤ 2931377739023^3381*5000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2796388817 5000000000 2931377739023 6250000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-384052169/2000000000 : ℝ), (2543270089/5000000000 : ℝ), (2796388817/5000000000 : ℝ)] ![(5824816901299/50000000000000 : ℝ), (10362080588227/25000000000000 : ℝ), (2931377739023/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-384052169/2000000000 : ℝ)|^4405 ≤ (5824816901299/50000000000000 : ℝ)^3381
        have hw : |(-384052169/2000000000 : ℝ)|=(384052169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2543270089/5000000000 : ℝ)|^4405 ≤ (10362080588227/25000000000000 : ℝ)^3381
        have hw : |(2543270089/5000000000 : ℝ)|=(2543270089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2796388817/5000000000 : ℝ)|^4405 ≤ (2931377739023/6250000000000 : ℝ)^3381
        have hw : |(2796388817/5000000000 : ℝ)|=(2796388817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_s1_5 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (105192469/200000000 : ℝ)*x 0 + (-1681977053/10000000000 : ℝ)*x 1 + (2796388831/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105192469/200000000 : ℝ)^4405 ≤ (8659054454517/20000000000000 : ℝ)^3381 := by
    have hnat : (105192469 : ℕ)^4405*20000000000000^3381 ≤ 8659054454517^3381*200000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105192469 200000000 8659054454517 20000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1681977053/10000000000 : ℝ)^4405 ≤ (980268358591/10000000000000 : ℝ)^3381 := by
    have hnat : (1681977053 : ℕ)^4405*10000000000000^3381 ≤ 980268358591^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1681977053 10000000000 980268358591 10000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2796388831/5000000000 : ℝ)^4405 ≤ (46902044130299/100000000000000 : ℝ)^3381 := by
    have hnat : (2796388831 : ℕ)^4405*100000000000000^3381 ≤ 46902044130299^3381*5000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2796388831 5000000000 46902044130299 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105192469/200000000 : ℝ), (-1681977053/10000000000 : ℝ), (2796388831/5000000000 : ℝ)] ![(8659054454517/20000000000000 : ℝ), (980268358591/10000000000000 : ℝ), (46902044130299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105192469/200000000 : ℝ)|^4405 ≤ (8659054454517/20000000000000 : ℝ)^3381
        have hw : |(105192469/200000000 : ℝ)|=(105192469/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1681977053/10000000000 : ℝ)|^4405 ≤ (980268358591/10000000000000 : ℝ)^3381
        have hw : |(-1681977053/10000000000 : ℝ)|=(1681977053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2796388831/5000000000 : ℝ)|^4405 ≤ (46902044130299/100000000000000 : ℝ)^3381
        have hw : |(2796388831/5000000000 : ℝ)|=(2796388831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_s1_6 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1051924673/2000000000 : ℝ)*x 0 + (2796388811/5000000000 : ℝ)*x 1 + (-1681977231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051924673/2000000000 : ℝ)^4405 ≤ (43295271360983/100000000000000 : ℝ)^3381 := by
    have hnat : (1051924673 : ℕ)^4405*100000000000000^3381 ≤ 43295271360983^3381*2000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051924673 2000000000 43295271360983 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2796388811/5000000000 : ℝ)^4405 ≤ (9380408738651/20000000000000 : ℝ)^3381 := by
    have hnat : (2796388811 : ℕ)^4405*20000000000000^3381 ≤ 9380408738651^3381*5000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2796388811 5000000000 9380408738651 20000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1681977231/10000000000 : ℝ)^4405 ≤ (4901342468751/50000000000000 : ℝ)^3381 := by
    have hnat : (1681977231 : ℕ)^4405*50000000000000^3381 ≤ 4901342468751^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1681977231 10000000000 4901342468751 50000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051924673/2000000000 : ℝ), (2796388811/5000000000 : ℝ), (-1681977231/10000000000 : ℝ)] ![(43295271360983/100000000000000 : ℝ), (9380408738651/20000000000000 : ℝ), (4901342468751/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051924673/2000000000 : ℝ)|^4405 ≤ (43295271360983/100000000000000 : ℝ)^3381
        have hw : |(1051924673/2000000000 : ℝ)|=(1051924673/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2796388811/5000000000 : ℝ)|^4405 ≤ (9380408738651/20000000000000 : ℝ)^3381
        have hw : |(2796388811/5000000000 : ℝ)|=(2796388811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1681977231/10000000000 : ℝ)|^4405 ≤ (4901342468751/50000000000000 : ℝ)^3381
        have hw : |(-1681977231/10000000000 : ℝ)|=(1681977231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_s1_7 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2137273531/5000000000 : ℝ)*x 0 + (4857621351/10000000000 : ℝ)*x 1 + (751207341/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2137273531/5000000000 : ℝ)^4405 ≤ (660888451397/2000000000000 : ℝ)^3381 := by
    have hnat : (2137273531 : ℕ)^4405*2000000000000^3381 ≤ 660888451397^3381*5000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2137273531 5000000000 660888451397 2000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4857621351/10000000000 : ℝ)^4405 ≤ (39034724103229/100000000000000 : ℝ)^3381 := by
    have hnat : (4857621351 : ℕ)^4405*100000000000000^3381 ≤ 39034724103229^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4857621351 10000000000 39034724103229 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (751207341/2000000000 : ℝ)^4405 ≤ (6980213328679/25000000000000 : ℝ)^3381 := by
    have hnat : (751207341 : ℕ)^4405*25000000000000^3381 ≤ 6980213328679^3381*2000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      751207341 2000000000 6980213328679 25000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2137273531/5000000000 : ℝ), (4857621351/10000000000 : ℝ), (751207341/2000000000 : ℝ)] ![(660888451397/2000000000000 : ℝ), (39034724103229/100000000000000 : ℝ), (6980213328679/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2137273531/5000000000 : ℝ)|^4405 ≤ (660888451397/2000000000000 : ℝ)^3381
        have hw : |(2137273531/5000000000 : ℝ)|=(2137273531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4857621351/10000000000 : ℝ)|^4405 ≤ (39034724103229/100000000000000 : ℝ)^3381
        have hw : |(4857621351/10000000000 : ℝ)|=(4857621351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(751207341/2000000000 : ℝ)|^4405 ≤ (6980213328679/25000000000000 : ℝ)^3381
        have hw : |(751207341/2000000000 : ℝ)|=(751207341/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1445_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79400569/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6537/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (27/1250 : ℝ)*pair X i i ≤ pair X i h) :
    (3891/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18741/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6537/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (27/1250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6537/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (27/1250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6537/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (27/1250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6537/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (27/1250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6537/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (27/1250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6537/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (27/1250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (27/1250 : ℝ) ^ (1101/256 : ℝ) ≤ (6868310525109/100000000000000000000 : ℝ) := by
    have hpowers : (27/1250 : ℝ)^1101 ≤ (6868310525109/100000000000000000000 : ℝ)^256 := by
      have hnat : (27 : ℕ)^1101*100000000000000000000^256 ≤ 6868310525109^256*1250^1101 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27 1250 6868310525109 100000000000000000000 1101 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27/1250 : ℝ)) (X := (6868310525109/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1101 256 (by norm_num) hpowers
    exact h
  have hpowhi : (6537/25000 : ℝ) ^ (1101/256 : ℝ) ≤ (156135021073790733/50000000000000000000 : ℝ) := by
    have hpowers : (6537/25000 : ℝ)^1101 ≤ (156135021073790733/50000000000000000000 : ℝ)^256 := by
      have hnat : (6537 : ℕ)^1101*50000000000000000000^256 ≤ 156135021073790733^256*25000^1101 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6537 25000 156135021073790733 50000000000000000000 1101 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6537/25000 : ℝ)) (X := (156135021073790733/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1101 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000006868310525109/50000000000000000000 : ℝ) ≤ (10000000319398257/10000000000000000 : ℝ) ^ (1101/256 : ℝ) := by
    have hpowers : (50000006868310525109/50000000000000000000 : ℝ)^256 ≤ (10000000319398257/10000000000000000 : ℝ)^1101 := by
      have hnat : (50000006868310525109 : ℕ)^256*10000000000000000^1101 ≤ 10000000319398257^1101*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000006868310525109 50000000000000000000 10000000319398257 10000000000000000 256 1101 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000319398257/10000000000000000 : ℝ)) (X := (50000006868310525109/50000000000000000000 : ℝ)) (by norm_num) 1101 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (4012491076418324263/4000000000000000000 : ℝ) ≤ (10007252249442427/10000000000000000 : ℝ) ^ (1101/256 : ℝ) := by
    have hpowers : (4012491076418324263/4000000000000000000 : ℝ)^256 ≤ (10007252249442427/10000000000000000 : ℝ)^1101 := by
      have hnat : (4012491076418324263 : ℕ)^256*10000000000000000^1101 ≤ 10007252249442427^1101*4000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4012491076418324263 4000000000000000000 10007252249442427 10000000000000000 256 1101 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007252249442427/10000000000000000 : ℝ)) (X := (4012491076418324263/4000000000000000000 : ℝ)) (by norm_num) 1101 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25156135021073790733/25000000000000000000 : ℝ) ≤ (10014504179486597/10000000000000000 : ℝ) ^ (1101/256 : ℝ) := by
    have hpowers : (25156135021073790733/25000000000000000000 : ℝ)^256 ≤ (10014504179486597/10000000000000000 : ℝ)^1101 := by
      have hnat : (25156135021073790733 : ℕ)^256*10000000000000000^1101 ≤ 10014504179486597^1101*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25156135021073790733 25000000000000000000 10014504179486597 10000000000000000 256 1101 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10014504179486597/10000000000000000 : ℝ)) (X := (25156135021073790733/25000000000000000000 : ℝ)) (by norm_num) 1101 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6868310525109/100000000000000000000 : ℝ) ≤ ((19987389943661214543/19990000000000000000 : ℝ)+2*(725193004417/239880000000000 : ℝ)*(27/1250 : ℝ))^(1101/256 : ℝ) := by
    rw [show (19987389943661214543/19990000000000000000 : ℝ)+2*(725193004417/239880000000000 : ℝ)*(27/1250 : ℝ)=(10000000319398257/10000000000000000 : ℝ) by norm_num, show 1+2*(6868310525109/100000000000000000000 : ℝ)=(50000006868310525109/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(156135021073790733/50000000000000000000 : ℝ)+(6868310525109/100000000000000000000 : ℝ) ≤ ((19987389943661214543/19990000000000000000 : ℝ)+(725193004417/239880000000000 : ℝ)*((6537/25000 : ℝ)+(27/1250 : ℝ)))^(1101/256 : ℝ) := by
    rw [show (19987389943661214543/19990000000000000000 : ℝ)+(725193004417/239880000000000 : ℝ)*((6537/25000 : ℝ)+(27/1250 : ℝ))=(10007252249442427/10000000000000000 : ℝ) by norm_num, show 1+(156135021073790733/50000000000000000000 : ℝ)+(6868310525109/100000000000000000000 : ℝ)=(4012491076418324263/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(156135021073790733/50000000000000000000 : ℝ) ≤ ((19987389943661214543/19990000000000000000 : ℝ)+2*(725193004417/239880000000000 : ℝ)*(6537/25000 : ℝ))^(1101/256 : ℝ) := by
    rw [show (19987389943661214543/19990000000000000000 : ℝ)+2*(725193004417/239880000000000 : ℝ)*(6537/25000 : ℝ)=(10014504179486597/10000000000000000 : ℝ) by norm_num, show 1+2*(156135021073790733/50000000000000000000 : ℝ)=(25156135021073790733/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19987389943661214543/19990000000000000000 : ℝ)*(X 1 0+X 2 0)+(725193004417/239880000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1101/256 : ℝ)) (lo := (27/1250 : ℝ)) (hi := (6537/25000 : ℝ)) (c := (19987389943661214543/19990000000000000000 : ℝ)) (alpha := (725193004417/239880000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19987389943661214543/19990000000000000000 : ℝ)*(X 0 1+X 2 1)+(725193004417/239880000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1101/256 : ℝ)) (lo := (27/1250 : ℝ)) (hi := (6537/25000 : ℝ)) (c := (19987389943661214543/19990000000000000000 : ℝ)) (alpha := (725193004417/239880000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19987389943661214543/19990000000000000000 : ℝ)*(X 0 2+X 1 2)+(725193004417/239880000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1101/256 : ℝ)) (lo := (27/1250 : ℝ)) (hi := (6537/25000 : ℝ)) (c := (19987389943661214543/19990000000000000000 : ℝ)) (alpha := (725193004417/239880000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1919884063/10000000000 : ℝ)*X 0 0+(349930027/625000000 : ℝ)*X 0 1+(2540268933/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5395210719/10000000000 : ℝ)*X 1 0+(-219421589/1000000000 : ℝ)*X 1 1+(2540269679/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((674401489/1250000000 : ℝ)*X 2 0+(5080538019/10000000000 : ℝ)*X 2 1+(-43884321/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4273726699/10000000000 : ℝ)*X 0 0+(3742759177/10000000000 : ℝ)*X 0 1+(974136237/2000000000 : ℝ)*X 0 2+(4273726699/10000000000 : ℝ)*X 1 0+(3742759177/10000000000 : ℝ)*X 1 1+(974136237/2000000000 : ℝ)*X 1 2+(4273726699/10000000000 : ℝ)*X 2 0+(3742759177/10000000000 : ℝ)*X 2 1+(974136237/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-384052169/2000000000 : ℝ)*X 0 0+(2543270089/5000000000 : ℝ)*X 0 1+(2796388817/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((105192469/200000000 : ℝ)*X 1 0+(-1681977053/10000000000 : ℝ)*X 1 1+(2796388831/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1051924673/2000000000 : ℝ)*X 2 0+(2796388811/5000000000 : ℝ)*X 2 1+(-1681977231/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2137273531/5000000000 : ℝ)*X 0 0+(4857621351/10000000000 : ℝ)*X 0 1+(751207341/2000000000 : ℝ)*X 0 2+(2137273531/5000000000 : ℝ)*X 1 0+(4857621351/10000000000 : ℝ)*X 1 1+(751207341/2000000000 : ℝ)*X 1 2+(2137273531/5000000000 : ℝ)*X 2 0+(4857621351/10000000000 : ℝ)*X 2 1+(751207341/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5026046181660103724898607719/999500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (49614079/6250000000000 : ℝ)*(base19) + (1177692811/100000000000000 : ℝ)*(base23) + (35710179/50000000000000 : ℝ)*(upper3) + (23054567/100000000000000 : ℝ)*(upper4) + (1804727/3125000000000 : ℝ)*(upper5) + (1407921270361789/100000000000000 : ℝ)*(major0) + (1407921270361789/100000000000000 : ℝ)*(major1) + (1407921270361789/100000000000000 : ℝ)*(major2) + (385847316331409/20000000000000 : ℝ)*(sp0) + (964623818316539/50000000000000 : ℝ)*(sp1) + (192924725276553/10000000000000 : ℝ)*(sp2) + (17731793718669/2000000000000 : ℝ)*(sp3) + (740550081/6250000000000 : ℝ)*(sp4) + (42567131/1000000000000 : ℝ)*(sp7) + (17731878852931/2000000000000 : ℝ)*(f.failure) + (1929248430458341/100000000000000 : ℝ)*(f.sum) + (54006935329217/11994000000000000000000000000 : ℝ)*base66 + (7249528866412142281/5997000000000000000000000000000000 : ℝ)*base67 + (2286723658069857719/5997000000000000000000000000000000 : ℝ)*base70 + (34189584935725857719/5997000000000000000000000000000000 : ℝ)*base72 + (18795510817993/11994000000000000000000000000 : ℝ)*base73 + (2172020114800142281/5997000000000000000000000000000000 : ℝ)*base75 + (8368543687108142281/5997000000000000000000000000000000 : ℝ)*base77 + (34657192527238142281/5997000000000000000000000000000000 : ℝ)*base79 + (52278029674487/11994000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (282261/100000000000000000000 : ℝ)*base90 + (282261/100000000000000000000 : ℝ)*base92 + (282261/100000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2661473833788364185600717699/499750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16881071/50000000000000 : ℝ)*(base1) + (299398867/25000000000000 : ℝ)*(base19) + (288587301/25000000000000 : ℝ)*(base23) + (34336399/25000000000000 : ℝ)*(upper3) + (13039589/12500000000000 : ℝ)*(upper5) + (1441570244096169/100000000000000 : ℝ)*(major0) + (1441570244096169/100000000000000 : ℝ)*(major1) + (1441570244096169/100000000000000 : ℝ)*(major2) + (7362001933/100000000000000 : ℝ)*(sp1) + (6922707939/100000000000000 : ℝ)*(sp2) + (987678511788227/50000000000000 : ℝ)*(sp4) + (1975348430216911/100000000000000 : ℝ)*(sp5) + (1975348912757169/100000000000000 : ℝ)*(sp6) + (907783287095527/100000000000000 : ℝ)*(sp7) + (907783320857669/100000000000000 : ℝ)*(f.failure) + (1975356989814313/100000000000000 : ℝ)*(f.sum) + (6370986820421/3998000000000000000000000000 : ℝ)*base66 + (5846701816495135767/1999000000000000000000000000000000 : ℝ)*base67 + (6847835835077135767/1999000000000000000000000000000000 : ℝ)*base69 + (7180598598842864233/1999000000000000000000000000000000 : ℝ)*base72 + (17429545840139/3998000000000000000000000000 : ℝ)*base73 + (12217567106337135767/1999000000000000000000000000000000 : ℝ)*base75 + (7750051789433135767/1999000000000000000000000000000000 : ℝ)*base77 + (11643529658642135767/1999000000000000000000000000000000 : ℝ)*base79 + (121643232583/3998000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (36613661/5000000000000000000000 : ℝ)*base89 + (36613661/5000000000000000000000 : ℝ)*base91 + (36613661/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1445_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79400569/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6537/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (27/1250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3891/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18741/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1445_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1445_s2_0 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1951840141/10000000000 : ℝ)*x 0 + (1363663287/2500000000 : ℝ)*x 1 + (2602088771/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1951840141/10000000000 : ℝ)^4405 ≤ (11899859181817/100000000000000 : ℝ)^3381 := by
    have hnat : (1951840141 : ℕ)^4405*100000000000000^3381 ≤ 11899859181817^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1951840141 10000000000 11899859181817 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1363663287/2500000000 : ℝ)^4405 ≤ (45398559570067/100000000000000 : ℝ)^3381 := by
    have hnat : (1363663287 : ℕ)^4405*100000000000000^3381 ≤ 45398559570067^3381*2500000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1363663287 2500000000 45398559570067 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2602088771/5000000000 : ℝ)^4405 ≤ (667212206707/1562500000000 : ℝ)^3381 := by
    have hnat : (2602088771 : ℕ)^4405*1562500000000^3381 ≤ 667212206707^3381*5000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2602088771 5000000000 667212206707 1562500000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1951840141/10000000000 : ℝ), (1363663287/2500000000 : ℝ), (2602088771/5000000000 : ℝ)] ![(11899859181817/100000000000000 : ℝ), (45398559570067/100000000000000 : ℝ), (667212206707/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1951840141/10000000000 : ℝ)|^4405 ≤ (11899859181817/100000000000000 : ℝ)^3381
        have hw : |(-1951840141/10000000000 : ℝ)|=(1951840141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1363663287/2500000000 : ℝ)|^4405 ≤ (45398559570067/100000000000000 : ℝ)^3381
        have hw : |(1363663287/2500000000 : ℝ)|=(1363663287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2602088771/5000000000 : ℝ)|^4405 ≤ (667212206707/1562500000000 : ℝ)^3381
        have hw : |(2602088771/5000000000 : ℝ)|=(2602088771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_s2_1 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5359136261/10000000000 : ℝ)*x 0 + (-2080619793/10000000000 : ℝ)*x 1 + (1040835453/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5359136261/10000000000 : ℝ)^4405 ≤ (22182782643857/50000000000000 : ℝ)^3381 := by
    have hnat : (5359136261 : ℕ)^4405*50000000000000^3381 ≤ 22182782643857^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5359136261 10000000000 22182782643857 50000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2080619793/10000000000 : ℝ)^4405 ≤ (12932856423333/100000000000000 : ℝ)^3381 := by
    have hnat : (2080619793 : ℕ)^4405*100000000000000^3381 ≤ 12932856423333^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080619793 10000000000 12932856423333 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1040835453/2000000000 : ℝ)^4405 ≤ (2668848641751/6250000000000 : ℝ)^3381 := by
    have hnat : (1040835453 : ℕ)^4405*6250000000000^3381 ≤ 2668848641751^3381*2000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040835453 2000000000 2668848641751 6250000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5359136261/10000000000 : ℝ), (-2080619793/10000000000 : ℝ), (1040835453/2000000000 : ℝ)] ![(22182782643857/50000000000000 : ℝ), (12932856423333/100000000000000 : ℝ), (2668848641751/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5359136261/10000000000 : ℝ)|^4405 ≤ (22182782643857/50000000000000 : ℝ)^3381
        have hw : |(5359136261/10000000000 : ℝ)|=(5359136261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2080619793/10000000000 : ℝ)|^4405 ≤ (12932856423333/100000000000000 : ℝ)^3381
        have hw : |(-2080619793/10000000000 : ℝ)|=(2080619793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1040835453/2000000000 : ℝ)|^4405 ≤ (2668848641751/6250000000000 : ℝ)^3381
        have hw : |(1040835453/2000000000 : ℝ)|=(1040835453/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_s2_2 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5359135691/10000000000 : ℝ)*x 0 + (5204177821/10000000000 : ℝ)*x 1 + (-2080619819/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5359135691/10000000000 : ℝ)^4405 ≤ (22182779569907/50000000000000 : ℝ)^3381 := by
    have hnat : (5359135691 : ℕ)^4405*50000000000000^3381 ≤ 22182779569907^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5359135691 10000000000 22182779569907 50000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5204177821/10000000000 : ℝ)^4405 ≤ (2135079210593/5000000000000 : ℝ)^3381 := by
    have hnat : (5204177821 : ℕ)^4405*5000000000000^3381 ≤ 2135079210593^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5204177821 10000000000 2135079210593 5000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2080619819/10000000000 : ℝ)^4405 ≤ (12932856633893/100000000000000 : ℝ)^3381 := by
    have hnat : (2080619819 : ℕ)^4405*100000000000000^3381 ≤ 12932856633893^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080619819 10000000000 12932856633893 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5359135691/10000000000 : ℝ), (5204177821/10000000000 : ℝ), (-2080619819/10000000000 : ℝ)] ![(22182779569907/50000000000000 : ℝ), (2135079210593/5000000000000 : ℝ), (12932856633893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5359135691/10000000000 : ℝ)|^4405 ≤ (22182779569907/50000000000000 : ℝ)^3381
        have hw : |(5359135691/10000000000 : ℝ)|=(5359135691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5204177821/10000000000 : ℝ)|^4405 ≤ (2135079210593/5000000000000 : ℝ)^3381
        have hw : |(5204177821/10000000000 : ℝ)|=(5204177821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2080619819/10000000000 : ℝ)|^4405 ≤ (12932856633893/100000000000000 : ℝ)^3381
        have hw : |(-2080619819/10000000000 : ℝ)|=(2080619819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_s2_3 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5370403/12500000 : ℝ)*x 0 + (806301461/2000000000 : ℝ)*x 1 + (4576549147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370403/12500000 : ℝ)^4405 ≤ (1039497164807/3125000000000 : ℝ)^3381 := by
    have hnat : (5370403 : ℕ)^4405*3125000000000^3381 ≤ 1039497164807^3381*12500000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370403 12500000 1039497164807 3125000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (806301461/2000000000 : ℝ)^4405 ≤ (7654481743463/25000000000000 : ℝ)^3381 := by
    have hnat : (806301461 : ℕ)^4405*25000000000000^3381 ≤ 7654481743463^3381*2000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      806301461 2000000000 7654481743463 25000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4576549147/10000000000 : ℝ)^4405 ≤ (7223632748631/20000000000000 : ℝ)^3381 := by
    have hnat : (4576549147 : ℕ)^4405*20000000000000^3381 ≤ 7223632748631^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4576549147 10000000000 7223632748631 20000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370403/12500000 : ℝ), (806301461/2000000000 : ℝ), (4576549147/10000000000 : ℝ)] ![(1039497164807/3125000000000 : ℝ), (7654481743463/25000000000000 : ℝ), (7223632748631/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370403/12500000 : ℝ)|^4405 ≤ (1039497164807/3125000000000 : ℝ)^3381
        have hw : |(5370403/12500000 : ℝ)|=(5370403/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(806301461/2000000000 : ℝ)|^4405 ≤ (7654481743463/25000000000000 : ℝ)^3381
        have hw : |(806301461/2000000000 : ℝ)|=(806301461/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4576549147/10000000000 : ℝ)|^4405 ≤ (7223632748631/20000000000000 : ℝ)^3381
        have hw : |(4576549147/10000000000 : ℝ)|=(4576549147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_s2_4 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1951882447/10000000000 : ℝ)*x 0 + (1301397111/2500000000 : ℝ)*x 1 + (5453231087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1951882447/10000000000 : ℝ)^4405 ≤ (11900195230123/100000000000000 : ℝ)^3381 := by
    have hnat : (1951882447 : ℕ)^4405*100000000000000^3381 ≤ 11900195230123^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1951882447 10000000000 11900195230123 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1301397111/2500000000 : ℝ)^4405 ≤ (42716664907939/100000000000000 : ℝ)^3381 := by
    have hnat : (1301397111 : ℕ)^4405*100000000000000^3381 ≤ 42716664907939^3381*2500000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1301397111 2500000000 42716664907939 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5453231087/10000000000 : ℝ)^4405 ≤ (4538313984059/10000000000000 : ℝ)^3381 := by
    have hnat : (5453231087 : ℕ)^4405*10000000000000^3381 ≤ 4538313984059^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5453231087 10000000000 4538313984059 10000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1951882447/10000000000 : ℝ), (1301397111/2500000000 : ℝ), (5453231087/10000000000 : ℝ)] ![(11900195230123/100000000000000 : ℝ), (42716664907939/100000000000000 : ℝ), (4538313984059/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1951882447/10000000000 : ℝ)|^4405 ≤ (11900195230123/100000000000000 : ℝ)^3381
        have hw : |(-1951882447/10000000000 : ℝ)|=(1951882447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1301397111/2500000000 : ℝ)|^4405 ≤ (42716664907939/100000000000000 : ℝ)^3381
        have hw : |(1301397111/2500000000 : ℝ)|=(1301397111/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5453231087/10000000000 : ℝ)|^4405 ≤ (4538313984059/10000000000000 : ℝ)^3381
        have hw : |(5453231087/10000000000 : ℝ)|=(5453231087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_s2_5 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661738409/1250000000 : ℝ)*x 0 + (-1831564763/10000000000 : ℝ)*x 1 + (5453232253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661738409/1250000000 : ℝ)^4405 ≤ (10915829891369/25000000000000 : ℝ)^3381 := by
    have hnat : (661738409 : ℕ)^4405*25000000000000^3381 ≤ 10915829891369^3381*1250000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661738409 1250000000 10915829891369 25000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1831564763/10000000000 : ℝ)^4405 ≤ (10953527932599/100000000000000 : ℝ)^3381 := by
    have hnat : (1831564763 : ℕ)^4405*100000000000000^3381 ≤ 10953527932599^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1831564763 10000000000 10953527932599 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5453232253/10000000000 : ℝ)^4405 ≤ (45383152483293/100000000000000 : ℝ)^3381 := by
    have hnat : (5453232253 : ℕ)^4405*100000000000000^3381 ≤ 45383152483293^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5453232253 10000000000 45383152483293 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661738409/1250000000 : ℝ), (-1831564763/10000000000 : ℝ), (5453232253/10000000000 : ℝ)] ![(10915829891369/25000000000000 : ℝ), (10953527932599/100000000000000 : ℝ), (45383152483293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661738409/1250000000 : ℝ)|^4405 ≤ (10915829891369/25000000000000 : ℝ)^3381
        have hw : |(661738409/1250000000 : ℝ)|=(661738409/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1831564763/10000000000 : ℝ)|^4405 ≤ (10953527932599/100000000000000 : ℝ)^3381
        have hw : |(-1831564763/10000000000 : ℝ)|=(1831564763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5453232253/10000000000 : ℝ)|^4405 ≤ (45383152483293/100000000000000 : ℝ)^3381
        have hw : |(5453232253/10000000000 : ℝ)|=(5453232253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_s2_6 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646953253/5000000000 : ℝ)*x 0 + (681654003/1250000000 : ℝ)*x 1 + (-915783069/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646953253/5000000000 : ℝ)^4405 ≤ (43663311334147/100000000000000 : ℝ)^3381 := by
    have hnat : (2646953253 : ℕ)^4405*100000000000000^3381 ≤ 43663311334147^3381*5000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646953253 5000000000 43663311334147 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (681654003/1250000000 : ℝ)^4405 ≤ (11345787500073/25000000000000 : ℝ)^3381 := by
    have hnat : (681654003 : ℕ)^4405*25000000000000^3381 ≤ 11345787500073^3381*1250000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681654003 1250000000 11345787500073 25000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (915783069/5000000000 : ℝ)^4405 ≤ (5476769323097/50000000000000 : ℝ)^3381 := by
    have hnat : (915783069 : ℕ)^4405*50000000000000^3381 ≤ 5476769323097^3381*5000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      915783069 5000000000 5476769323097 50000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646953253/5000000000 : ℝ), (681654003/1250000000 : ℝ), (-915783069/5000000000 : ℝ)] ![(43663311334147/100000000000000 : ℝ), (11345787500073/25000000000000 : ℝ), (5476769323097/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646953253/5000000000 : ℝ)|^4405 ≤ (43663311334147/100000000000000 : ℝ)^3381
        have hw : |(2646953253/5000000000 : ℝ)|=(2646953253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(681654003/1250000000 : ℝ)|^4405 ≤ (11345787500073/25000000000000 : ℝ)^3381
        have hw : |(681654003/1250000000 : ℝ)|=(681654003/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-915783069/5000000000 : ℝ)|^4405 ≤ (5476769323097/50000000000000 : ℝ)^3381
        have hw : |(-915783069/5000000000 : ℝ)|=(915783069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_s2_7 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (537051883/1250000000 : ℝ)*x 0 + (4573480643/10000000000 : ℝ)*x 1 + (4034600797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537051883/1250000000 : ℝ)^4405 ≤ (831621100281/2500000000000 : ℝ)^3381 := by
    have hnat : (537051883 : ℕ)^4405*2500000000000^3381 ≤ 831621100281^3381*1250000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537051883 1250000000 831621100281 2500000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4573480643/10000000000 : ℝ)^4405 ≤ (9021653953393/25000000000000 : ℝ)^3381 := by
    have hnat : (4573480643 : ℕ)^4405*25000000000000^3381 ≤ 9021653953393^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4573480643 10000000000 9021653953393 25000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4034600797/10000000000 : ℝ)^4405 ≤ (30648540159427/100000000000000 : ℝ)^3381 := by
    have hnat : (4034600797 : ℕ)^4405*100000000000000^3381 ≤ 30648540159427^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4034600797 10000000000 30648540159427 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537051883/1250000000 : ℝ), (4573480643/10000000000 : ℝ), (4034600797/10000000000 : ℝ)] ![(831621100281/2500000000000 : ℝ), (9021653953393/25000000000000 : ℝ), (30648540159427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537051883/1250000000 : ℝ)|^4405 ≤ (831621100281/2500000000000 : ℝ)^3381
        have hw : |(537051883/1250000000 : ℝ)|=(537051883/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4573480643/10000000000 : ℝ)|^4405 ≤ (9021653953393/25000000000000 : ℝ)^3381
        have hw : |(4573480643/10000000000 : ℝ)|=(4573480643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4034600797/10000000000 : ℝ)|^4405 ≤ (30648540159427/100000000000000 : ℝ)^3381
        have hw : |(4034600797/10000000000 : ℝ)|=(4034600797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1445_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79400569/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18741/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3891/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10451/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1969/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18741/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3891/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18741/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3891/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18741/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3891/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18741/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3891/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18741/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3891/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18741/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3891/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3891/50000 : ℝ) ^ (1101/256 : ℝ) ≤ (1701476435871611/100000000000000000000 : ℝ) := by
    have hpowers : (3891/50000 : ℝ)^1101 ≤ (1701476435871611/100000000000000000000 : ℝ)^256 := by
      have hnat : (3891 : ℕ)^1101*100000000000000000000^256 ≤ 1701476435871611^256*50000^1101 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3891 50000 1701476435871611 100000000000000000000 1101 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3891/50000 : ℝ)) (X := (1701476435871611/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1101 256 (by norm_num) hpowers
    exact h
  have hpowhi : (18741/100000 : ℝ) ^ (1101/256 : ℝ) ≤ (74548814269610267/100000000000000000000 : ℝ) := by
    have hpowers : (18741/100000 : ℝ)^1101 ≤ (74548814269610267/100000000000000000000 : ℝ)^256 := by
      have hnat : (18741 : ℕ)^1101*100000000000000000000^256 ≤ 74548814269610267^256*100000^1101 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18741 100000 74548814269610267 100000000000000000000 1101 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18741/100000 : ℝ)) (X := (74548814269610267/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1101 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001701476435871611/50000000000000000000 : ℝ) ≤ (5000039561514957/5000000000000000 : ℝ) ^ (1101/256 : ℝ) := by
    have hpowers : (50001701476435871611/50000000000000000000 : ℝ)^256 ≤ (5000039561514957/5000000000000000 : ℝ)^1101 := by
      have hnat : (50001701476435871611 : ℕ)^256*5000000000000000^1101 ≤ 5000039561514957^1101*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001701476435871611 50000000000000000000 5000039561514957 5000000000000000 256 1101 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000039561514957/5000000000000000 : ℝ)) (X := (50001701476435871611/50000000000000000000 : ℝ)) (by norm_num) 1101 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50038125145352740939/50000000000000000000 : ℝ) ≤ (100017724219187/100000000000000 : ℝ) ^ (1101/256 : ℝ) := by
    have hpowers : (50038125145352740939/50000000000000000000 : ℝ)^256 ≤ (100017724219187/100000000000000 : ℝ)^1101 := by
      have hnat : (50038125145352740939 : ℕ)^256*100000000000000^1101 ≤ 100017724219187^1101*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50038125145352740939 50000000000000000000 100017724219187 100000000000000 256 1101 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100017724219187/100000000000000 : ℝ)) (X := (50038125145352740939/50000000000000000000 : ℝ)) (by norm_num) 1101 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50074548814269610267/50000000000000000000 : ℝ) ≤ (5001732860403743/5000000000000000 : ℝ) ^ (1101/256 : ℝ) := by
    have hpowers : (50074548814269610267/50000000000000000000 : ℝ)^256 ≤ (5001732860403743/5000000000000000 : ℝ)^1101 := by
      have hnat : (50074548814269610267 : ℕ)^256*5000000000000000^1101 ≤ 5001732860403743^1101*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50074548814269610267 50000000000000000000 5001732860403743 5000000000000000 256 1101 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001732860403743/5000000000000000 : ℝ)) (X := (50074548814269610267/50000000000000000000 : ℝ)) (by norm_num) 1101 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1701476435871611/100000000000000000000 : ℝ) ≤ ((18260752100896627037/18265000000000000000 : ℝ)+2*(846649444393/547950000000000 : ℝ)*(3891/50000 : ℝ))^(1101/256 : ℝ) := by
    rw [show (18260752100896627037/18265000000000000000 : ℝ)+2*(846649444393/547950000000000 : ℝ)*(3891/50000 : ℝ)=(5000039561514957/5000000000000000 : ℝ) by norm_num, show 1+2*(1701476435871611/100000000000000000000 : ℝ)=(50001701476435871611/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(74548814269610267/100000000000000000000 : ℝ)+(1701476435871611/100000000000000000000 : ℝ) ≤ ((18260752100896627037/18265000000000000000 : ℝ)+(846649444393/547950000000000 : ℝ)*((18741/100000 : ℝ)+(3891/50000 : ℝ)))^(1101/256 : ℝ) := by
    rw [show (18260752100896627037/18265000000000000000 : ℝ)+(846649444393/547950000000000 : ℝ)*((18741/100000 : ℝ)+(3891/50000 : ℝ))=(100017724219187/100000000000000 : ℝ) by norm_num, show 1+(74548814269610267/100000000000000000000 : ℝ)+(1701476435871611/100000000000000000000 : ℝ)=(50038125145352740939/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(74548814269610267/100000000000000000000 : ℝ) ≤ ((18260752100896627037/18265000000000000000 : ℝ)+2*(846649444393/547950000000000 : ℝ)*(18741/100000 : ℝ))^(1101/256 : ℝ) := by
    rw [show (18260752100896627037/18265000000000000000 : ℝ)+2*(846649444393/547950000000000 : ℝ)*(18741/100000 : ℝ)=(5001732860403743/5000000000000000 : ℝ) by norm_num, show 1+2*(74548814269610267/100000000000000000000 : ℝ)=(50074548814269610267/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18260752100896627037/18265000000000000000 : ℝ)*(X 1 0+X 2 0)+(846649444393/547950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1101/256 : ℝ)) (lo := (3891/50000 : ℝ)) (hi := (18741/100000 : ℝ)) (c := (18260752100896627037/18265000000000000000 : ℝ)) (alpha := (846649444393/547950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18260752100896627037/18265000000000000000 : ℝ)*(X 0 1+X 2 1)+(846649444393/547950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1101/256 : ℝ)) (lo := (3891/50000 : ℝ)) (hi := (18741/100000 : ℝ)) (c := (18260752100896627037/18265000000000000000 : ℝ)) (alpha := (846649444393/547950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18260752100896627037/18265000000000000000 : ℝ)*(X 0 2+X 1 2)+(846649444393/547950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1101/256 : ℝ)) (lo := (3891/50000 : ℝ)) (hi := (18741/100000 : ℝ)) (c := (18260752100896627037/18265000000000000000 : ℝ)) (alpha := (846649444393/547950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1951840141/10000000000 : ℝ)*X 0 0+(1363663287/2500000000 : ℝ)*X 0 1+(2602088771/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5359136261/10000000000 : ℝ)*X 1 0+(-2080619793/10000000000 : ℝ)*X 1 1+(1040835453/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5359135691/10000000000 : ℝ)*X 2 0+(5204177821/10000000000 : ℝ)*X 2 1+(-2080619819/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5370403/12500000 : ℝ)*X 0 0+(806301461/2000000000 : ℝ)*X 0 1+(4576549147/10000000000 : ℝ)*X 0 2+(5370403/12500000 : ℝ)*X 1 0+(806301461/2000000000 : ℝ)*X 1 1+(4576549147/10000000000 : ℝ)*X 1 2+(5370403/12500000 : ℝ)*X 2 0+(806301461/2000000000 : ℝ)*X 2 1+(4576549147/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1951882447/10000000000 : ℝ)*X 0 0+(1301397111/2500000000 : ℝ)*X 0 1+(5453231087/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((661738409/1250000000 : ℝ)*X 1 0+(-1831564763/10000000000 : ℝ)*X 1 1+(5453232253/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2646953253/5000000000 : ℝ)*X 2 0+(681654003/1250000000 : ℝ)*X 2 1+(-915783069/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((537051883/1250000000 : ℝ)*X 0 0+(4573480643/10000000000 : ℝ)*X 0 1+(4034600797/10000000000 : ℝ)*X 0 2+(537051883/1250000000 : ℝ)*X 1 0+(4573480643/10000000000 : ℝ)*X 1 1+(4034600797/10000000000 : ℝ)*X 1 2+(537051883/1250000000 : ℝ)*X 2 0+(4573480643/10000000000 : ℝ)*X 2 1+(4034600797/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1270233882319191307638503631/114156250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1640109069/100000000000000 : ℝ)*(base19) + (187852609/20000000000000 : ℝ)*(base23) + (74012061/50000000000000 : ℝ)*(lower2) + (383992693/100000000000000 : ℝ)*(upper3) + (16371783/25000000000000 : ℝ)*(upper5) + (728397109272321/25000000000000 : ℝ)*(major0) + (728397109272321/25000000000000 : ℝ)*(major1) + (728397109272321/25000000000000 : ℝ)*(major2) + (499053062983639/12500000000000 : ℝ)*(sp0) + (249527161719151/6250000000000 : ℝ)*(sp1) + (99810882208811/2500000000000 : ℝ)*(sp2) + (458682337514593/25000000000000 : ℝ)*(sp3) + (5861873187/50000000000000 : ℝ)*(sp4) + (2185119931/20000000000000 : ℝ)*(sp7) + (458685068914507/25000000000000 : ℝ)*(f.failure) + (798487245523097/20000000000000 : ℝ)*(f.sum) + (29934762656329/9132500000000000000000000000 : ℝ)*base65 + (2410391374743182123/456625000000000000000000000000000 : ℝ)*base68 + (2964822118207182123/456625000000000000000000000000000 : ℝ)*base70 + (951951269698442877/456625000000000000000000000000000 : ℝ)*base71 + (27794724350103/18265000000000000000000000000 : ℝ)*base73 + (960521931418932123/456625000000000000000000000000000 : ℝ)*base76 + (1895190292800557123/456625000000000000000000000000000 : ℝ)*base78 + (3801803827121182123/456625000000000000000000000000000 : ℝ)*base80 + (1101675774273/18265000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (18154483/1250000000000000000000 : ℝ)*base89 + (18154483/1250000000000000000000 : ℝ)*base91 + (18154483/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (146817709696327886682304207/11415625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (946804007/100000000000000 : ℝ)*(base19) + (187887763/25000000000000 : ℝ)*(base23) + (87993369/25000000000000 : ℝ)*(upper3) + (272399301/100000000000000 : ℝ)*(lower4) + (36836042228387/1250000000000 : ℝ)*(major0) + (36836042228387/1250000000000 : ℝ)*(major1) + (36836042228387/1250000000000 : ℝ)*(major2) + (22057541233/100000000000000 : ℝ)*(sp1) + (2374091197/20000000000000 : ℝ)*(sp2) + (2583955197/100000000000000 : ℝ)*(sp3) + (40380596147847/1000000000000 : ℝ)*(sp4) + (201901830521973/5000000000000 : ℝ)*(sp5) + (63094484262151/1562500000000 : ℝ)*(sp6) + (231963016137257/12500000000000 : ℝ)*(sp7) + (1855706713053253/100000000000000 : ℝ)*(f.failure) + (40380596147847/1000000000000 : ℝ)*(f.sum) + (3707359983439/2739750000000000000000000000 : ℝ)*base65 + (376639005970979207/68493750000000000000000000000000 : ℝ)*base67 + (176512107894533293/68493750000000000000000000000000 : ℝ)*base70 + (957316660554629207/68493750000000000000000000000000 : ℝ)*base71 + (1199277141749/684937500000000000000000000 : ℝ)*base74 + (553405969043127043/68493750000000000000000000000000 : ℝ)*base76 + (373957980188333293/68493750000000000000000000000000 : ℝ)*base78 + (339970950681139543/68493750000000000000000000000000 : ℝ)*base80 + (4668444153521/2739750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (15500957/5000000000000000000000 : ℝ)*base89 + (15500957/5000000000000000000000 : ℝ)*base91 + (15500957/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1445_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79400569/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18741/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3891/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10451/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1969/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1445_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1445_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79400569/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10451/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1969/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1445_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1445_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1445_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79400569/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10451/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1969/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1445_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
