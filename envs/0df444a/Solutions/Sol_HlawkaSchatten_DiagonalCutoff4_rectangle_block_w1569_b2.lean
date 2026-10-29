-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1569_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:27:12.00244+00:00
-- url     : https://prove2.me/submissions/97920e7b-a201-48c7-a52b-ae17ed3f4dc0

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
theorem support_rectangle_w1569_s6_0 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337062917/2500000000 : ℝ)*x 0 + (1305008337/2500000000 : ℝ)*x 1 + (-378461413/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337062917/2500000000 : ℝ)^4635 ≤ (44785631566029/100000000000000 : ℝ)^3611 := by
    have hnat : (1337062917 : ℕ)^4635*100000000000000^3611 ≤ 44785631566029^3611*2500000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337062917 2500000000 44785631566029 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1305008337/2500000000 : ℝ)^4635 ≤ (21706092372291/50000000000000 : ℝ)^3611 := by
    have hnat : (1305008337 : ℕ)^4635*50000000000000^3611 ≤ 21706092372291^3611*2500000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305008337 2500000000 21706092372291 50000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (378461413/2000000000 : ℝ)^4635 ≤ (2360436736541/20000000000000 : ℝ)^3611 := by
    have hnat : (378461413 : ℕ)^4635*20000000000000^3611 ≤ 2360436736541^3611*2000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      378461413 2000000000 2360436736541 20000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337062917/2500000000 : ℝ), (1305008337/2500000000 : ℝ), (-378461413/2000000000 : ℝ)] ![(44785631566029/100000000000000 : ℝ), (21706092372291/50000000000000 : ℝ), (2360436736541/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337062917/2500000000 : ℝ)|^4635 ≤ (44785631566029/100000000000000 : ℝ)^3611
        have hw : |(1337062917/2500000000 : ℝ)|=(1337062917/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1305008337/2500000000 : ℝ)|^4635 ≤ (21706092372291/50000000000000 : ℝ)^3611
        have hw : |(1305008337/2500000000 : ℝ)|=(1305008337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-378461413/2000000000 : ℝ)|^4635 ≤ (2360436736541/20000000000000 : ℝ)^3611
        have hw : |(-378461413/2000000000 : ℝ)|=(378461413/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_s6_1 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-111688033/625000000 : ℝ)*x 0 + (2610552737/5000000000 : ℝ)*x 1 + (2712415909/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (111688033/625000000 : ℝ)^4635 ≤ (438637960113/4000000000000 : ℝ)^3611 := by
    have hnat : (111688033 : ℕ)^4635*4000000000000^3611 ≤ 438637960113^3611*625000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111688033 625000000 438637960113 4000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2610552737/5000000000 : ℝ)^4635 ≤ (21711814915679/50000000000000 : ℝ)^3611 := by
    have hnat : (2610552737 : ℕ)^4635*50000000000000^3611 ≤ 21711814915679^3611*5000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610552737 5000000000 21711814915679 50000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2712415909/5000000000 : ℝ)^4635 ≤ (11402605287169/25000000000000 : ℝ)^3611 := by
    have hnat : (2712415909 : ℕ)^4635*25000000000000^3611 ≤ 11402605287169^3611*5000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712415909 5000000000 11402605287169 25000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-111688033/625000000 : ℝ), (2610552737/5000000000 : ℝ), (2712415909/5000000000 : ℝ)] ![(438637960113/4000000000000 : ℝ), (21711814915679/50000000000000 : ℝ), (11402605287169/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-111688033/625000000 : ℝ)|^4635 ≤ (438637960113/4000000000000 : ℝ)^3611
        have hw : |(-111688033/625000000 : ℝ)|=(111688033/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2610552737/5000000000 : ℝ)|^4635 ≤ (21711814915679/50000000000000 : ℝ)^3611
        have hw : |(2610552737/5000000000 : ℝ)|=(2610552737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2712415909/5000000000 : ℝ)|^4635 ≤ (11402605287169/25000000000000 : ℝ)^3611
        have hw : |(2712415909/5000000000 : ℝ)|=(2712415909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_s6_2 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293788299/10000000000 : ℝ)*x 0 + (-1687509489/10000000000 : ℝ)*x 1 + (1084966369/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293788299/10000000000 : ℝ)^4635 ≤ (44201077671563/100000000000000 : ℝ)^3611 := by
    have hnat : (5293788299 : ℕ)^4635*100000000000000^3611 ≤ 44201077671563^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293788299 10000000000 44201077671563 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1687509489/10000000000 : ℝ)^4635 ≤ (10188500872621/100000000000000 : ℝ)^3611 := by
    have hnat : (1687509489 : ℕ)^4635*100000000000000^3611 ≤ 10188500872621^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1687509489 10000000000 10188500872621 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1084966369/2000000000 : ℝ)^4635 ≤ (45610421440059/100000000000000 : ℝ)^3611 := by
    have hnat : (1084966369 : ℕ)^4635*100000000000000^3611 ≤ 45610421440059^3611*2000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084966369 2000000000 45610421440059 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293788299/10000000000 : ℝ), (-1687509489/10000000000 : ℝ), (1084966369/2000000000 : ℝ)] ![(44201077671563/100000000000000 : ℝ), (10188500872621/100000000000000 : ℝ), (45610421440059/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293788299/10000000000 : ℝ)|^4635 ≤ (44201077671563/100000000000000 : ℝ)^3611
        have hw : |(5293788299/10000000000 : ℝ)|=(5293788299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1687509489/10000000000 : ℝ)|^4635 ≤ (10188500872621/100000000000000 : ℝ)^3611
        have hw : |(-1687509489/10000000000 : ℝ)|=(1687509489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1084966369/2000000000 : ℝ)|^4635 ≤ (45610421440059/100000000000000 : ℝ)^3611
        have hw : |(1084966369/2000000000 : ℝ)|=(1084966369/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_s6_3 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293788323/10000000000 : ℝ)*x 0 + (339051989/625000000 : ℝ)*x 1 + (-421877371/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293788323/10000000000 : ℝ)^4635 ≤ (2210053896439/5000000000000 : ℝ)^3611 := by
    have hnat : (5293788323 : ℕ)^4635*5000000000000^3611 ≤ 2210053896439^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293788323 10000000000 2210053896439 5000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339051989/625000000 : ℝ)^4635 ≤ (11402605303357/25000000000000 : ℝ)^3611 := by
    have hnat : (339051989 : ℕ)^4635*25000000000000^3611 ≤ 11402605303357^3611*625000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339051989 625000000 11402605303357 25000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (421877371/2500000000 : ℝ)^4635 ≤ (636781302117/6250000000000 : ℝ)^3611 := by
    have hnat : (421877371 : ℕ)^4635*6250000000000^3611 ≤ 636781302117^3611*2500000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421877371 2500000000 636781302117 6250000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293788323/10000000000 : ℝ), (339051989/625000000 : ℝ), (-421877371/2500000000 : ℝ)] ![(2210053896439/5000000000000 : ℝ), (11402605303357/25000000000000 : ℝ), (636781302117/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293788323/10000000000 : ℝ)|^4635 ≤ (2210053896439/5000000000000 : ℝ)^3611
        have hw : |(5293788323/10000000000 : ℝ)|=(5293788323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(339051989/625000000 : ℝ)|^4635 ≤ (11402605303357/25000000000000 : ℝ)^3611
        have hw : |(339051989/625000000 : ℝ)|=(339051989/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-421877371/2500000000 : ℝ)|^4635 ≤ (636781302117/6250000000000 : ℝ)^3611
        have hw : |(-421877371/2500000000 : ℝ)|=(421877371/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_s6_4 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (424400997/1000000000 : ℝ)*x 0 + (4489877401/10000000000 : ℝ)*x 1 + (2004648153/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (424400997/1000000000 : ℝ)^4635 ≤ (6656592664897/20000000000000 : ℝ)^3611 := by
    have hnat : (424400997 : ℕ)^4635*20000000000000^3611 ≤ 6656592664897^3611*1000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424400997 1000000000 6656592664897 20000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4489877401/10000000000 : ℝ)^4635 ≤ (8944495634427/25000000000000 : ℝ)^3611 := by
    have hnat : (4489877401 : ℕ)^4635*25000000000000^3611 ≤ 8944495634427^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489877401 10000000000 8944495634427 25000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2004648153/5000000000 : ℝ)^4635 ≤ (30939054120141/100000000000000 : ℝ)^3611 := by
    have hnat : (2004648153 : ℕ)^4635*100000000000000^3611 ≤ 30939054120141^3611*5000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2004648153 5000000000 30939054120141 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(424400997/1000000000 : ℝ), (4489877401/10000000000 : ℝ), (2004648153/5000000000 : ℝ)] ![(6656592664897/20000000000000 : ℝ), (8944495634427/25000000000000 : ℝ), (30939054120141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(424400997/1000000000 : ℝ)|^4635 ≤ (6656592664897/20000000000000 : ℝ)^3611
        have hw : |(424400997/1000000000 : ℝ)|=(424400997/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4489877401/10000000000 : ℝ)|^4635 ≤ (8944495634427/25000000000000 : ℝ)^3611
        have hw : |(4489877401/10000000000 : ℝ)|=(4489877401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2004648153/5000000000 : ℝ)|^4635 ≤ (30939054120141/100000000000000 : ℝ)^3611
        have hw : |(2004648153/5000000000 : ℝ)|=(2004648153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1569_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167947699/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5559/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5559/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3871/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5559/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5559/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5559/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5559/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5559/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5559/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5559/50000 : ℝ) ^ (4633/1024 : ℝ) ≤ (2414346803371701/50000000000000000000 : ℝ) := by
    have hpowers : (5559/50000 : ℝ)^4633 ≤ (2414346803371701/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5559 : ℕ)^4633*50000000000000000000^1024 ≤ 2414346803371701^1024*50000^4633 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5559 50000 2414346803371701 50000000000000000000 4633 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5559/50000 : ℝ)) (X := (2414346803371701/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4633 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3097/20000 : ℝ) ^ (4633/1024 : ℝ) ≤ (5404591749700993/25000000000000000000 : ℝ) := by
    have hpowers : (3097/20000 : ℝ)^4633 ≤ (5404591749700993/25000000000000000000 : ℝ)^1024 := by
      have hnat : (3097 : ℕ)^4633*25000000000000000000^1024 ≤ 5404591749700993^1024*20000^4633 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3097 20000 5404591749700993 25000000000000000000 4633 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3097/20000 : ℝ)) (X := (5404591749700993/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4633 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002414346803371701/25000000000000000000 : ℝ) ≤ (5000106721266489/5000000000000000 : ℝ) ^ (4633/1024 : ℝ) := by
    have hpowers : (25002414346803371701/25000000000000000000 : ℝ)^1024 ≤ (5000106721266489/5000000000000000 : ℝ)^4633 := by
      have hnat : (25002414346803371701 : ℕ)^1024*5000000000000000^4633 ≤ 5000106721266489^4633*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002414346803371701 25000000000000000000 5000106721266489 5000000000000000 1024 4633 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000106721266489/5000000000000000 : ℝ)) (X := (25002414346803371701/25000000000000000000 : ℝ)) (by norm_num) 4633 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50013223530302773687/50000000000000000000 : ℝ) ≤ (10000584480916249/10000000000000000 : ℝ) ^ (4633/1024 : ℝ) := by
    have hpowers : (50013223530302773687/50000000000000000000 : ℝ)^1024 ≤ (10000584480916249/10000000000000000 : ℝ)^4633 := by
      have hnat : (50013223530302773687 : ℕ)^1024*10000000000000000^4633 ≤ 10000584480916249^4633*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013223530302773687 50000000000000000000 10000584480916249 10000000000000000 1024 4633 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000584480916249/10000000000000000 : ℝ)) (X := (50013223530302773687/50000000000000000000 : ℝ)) (by norm_num) 4633 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12505404591749700993/12500000000000000000 : ℝ) ≤ (31252985997811/31250000000000 : ℝ) ^ (4633/1024 : ℝ) := by
    have hpowers : (12505404591749700993/12500000000000000000 : ℝ)^1024 ≤ (31252985997811/31250000000000 : ℝ)^4633 := by
      have hnat : (12505404591749700993 : ℕ)^1024*31250000000000^4633 ≤ 31252985997811^4633*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505404591749700993 12500000000000000000 31252985997811 31250000000000 1024 4633 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (31252985997811/31250000000000 : ℝ)) (X := (12505404591749700993/12500000000000000000 : ℝ)) (by norm_num) 4633 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2414346803371701/50000000000000000000 : ℝ) ≤ ((4366268169405110097/4367000000000000000 : ℝ)+2*(371038383271/436700000000000 : ℝ)*(5559/50000 : ℝ))^(4633/1024 : ℝ) := by
    rw [show (4366268169405110097/4367000000000000000 : ℝ)+2*(371038383271/436700000000000 : ℝ)*(5559/50000 : ℝ)=(5000106721266489/5000000000000000 : ℝ) by norm_num, show 1+2*(2414346803371701/50000000000000000000 : ℝ)=(25002414346803371701/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5404591749700993/25000000000000000000 : ℝ)+(2414346803371701/50000000000000000000 : ℝ) ≤ ((4366268169405110097/4367000000000000000 : ℝ)+(371038383271/436700000000000 : ℝ)*((3097/20000 : ℝ)+(5559/50000 : ℝ)))^(4633/1024 : ℝ) := by
    rw [show (4366268169405110097/4367000000000000000 : ℝ)+(371038383271/436700000000000 : ℝ)*((3097/20000 : ℝ)+(5559/50000 : ℝ))=(10000584480916249/10000000000000000 : ℝ) by norm_num, show 1+(5404591749700993/25000000000000000000 : ℝ)+(2414346803371701/50000000000000000000 : ℝ)=(50013223530302773687/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5404591749700993/25000000000000000000 : ℝ) ≤ ((4366268169405110097/4367000000000000000 : ℝ)+2*(371038383271/436700000000000 : ℝ)*(3097/20000 : ℝ))^(4633/1024 : ℝ) := by
    rw [show (4366268169405110097/4367000000000000000 : ℝ)+2*(371038383271/436700000000000 : ℝ)*(3097/20000 : ℝ)=(31252985997811/31250000000000 : ℝ) by norm_num, show 1+2*(5404591749700993/25000000000000000000 : ℝ)=(12505404591749700993/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4366268169405110097/4367000000000000000 : ℝ)*(X 1 0+X 2 0)+(371038383271/436700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4633/1024 : ℝ)) (lo := (5559/50000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (4366268169405110097/4367000000000000000 : ℝ)) (alpha := (371038383271/436700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4366268169405110097/4367000000000000000 : ℝ)*(X 0 1+X 2 1)+(371038383271/436700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4633/1024 : ℝ)) (lo := (5559/50000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (4366268169405110097/4367000000000000000 : ℝ)) (alpha := (371038383271/436700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4366268169405110097/4367000000000000000 : ℝ)*(X 0 2+X 1 2)+(371038383271/436700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4633/1024 : ℝ)) (lo := (5559/50000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (4366268169405110097/4367000000000000000 : ℝ)) (alpha := (371038383271/436700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((1337062917/2500000000 : ℝ)*X 2 0+(1305008337/2500000000 : ℝ)*X 2 1+(-378461413/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s6_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-111688033/625000000 : ℝ)*X 0 0+(2610552737/5000000000 : ℝ)*X 0 1+(2712415909/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s6_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5293788299/10000000000 : ℝ)*X 1 0+(-1687509489/10000000000 : ℝ)*X 1 1+(1084966369/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s6_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5293788323/10000000000 : ℝ)*X 2 0+(339051989/625000000 : ℝ)*X 2 1+(-421877371/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s6_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((424400997/1000000000 : ℝ)*X 0 0+(4489877401/10000000000 : ℝ)*X 0 1+(2004648153/5000000000 : ℝ)*X 0 2+(424400997/1000000000 : ℝ)*X 1 0+(4489877401/10000000000 : ℝ)*X 1 1+(2004648153/5000000000 : ℝ)*X 1 2+(424400997/1000000000 : ℝ)*X 2 0+(4489877401/10000000000 : ℝ)*X 2 1+(2004648153/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s6_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10779407722359345923182209/3970000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (51072751/12500000000000 : ℝ)*(base19) + (482328387/100000000000000 : ℝ)*(base23) + (141742087/100000000000000 : ℝ)*(lower1) + (29222057/50000000000000 : ℝ)*(upper3) + (2204129/10000000000000 : ℝ)*(lower4) + (54466681/100000000000000 : ℝ)*(upper5) + (698934941237511/20000000000000 : ℝ)*(major0) + (698934941237511/20000000000000 : ℝ)*(major1) + (698934941237511/20000000000000 : ℝ)*(major2) + (479036449/50000000000000 : ℝ)*(sp0) + (4908538017517979/100000000000000 : ℝ)*(sp1) + (4908537608935971/100000000000000 : ℝ)*(sp2) + (2454268288558347/50000000000000 : ℝ)*(sp3) + (1040405652174953/50000000000000 : ℝ)*(sp4) + (1040405652174953/50000000000000 : ℝ)*(f.failure) + (4908538017517979/100000000000000 : ℝ)*(f.sum) + (62260015741/79400000000000000000000000 : ℝ)*base66 + (132745555956147403/7940000000000000000000000000000 : ℝ)*base68 + (18512939098212597/7940000000000000000000000000000 : ℝ)*base69 + (413916635844327403/7940000000000000000000000000000 : ℝ)*base72 + (22525749223/24812500000000000000000000 : ℝ)*base74 + (747559446154592597/7940000000000000000000000000000 : ℝ)*base75 + (83288905861492597/7940000000000000000000000000000 : ℝ)*base77 + (17339854850692597/7940000000000000000000000000000 : ℝ)*base79 + (2022718873681/397000000000000000000000000 : ℝ)*base81 + (48216853/5000000000000000000000 : ℝ)*base90 + (48216853/5000000000000000000000 : ℝ)*base92 + (48216853/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1569_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167947699/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5559/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5559/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1569_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1569_box_0 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-39575481/250000000 : ℝ)*x 0 + (5396698453/10000000000 : ℝ)*x 1 + (1079339523/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (39575481/250000000 : ℝ)^4635 ≤ (9385947573181/100000000000000 : ℝ)^3611 := by
    have hnat : (39575481 : ℕ)^4635*100000000000000^3611 ≤ 9385947573181^3611*250000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39575481 250000000 9385947573181 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396698453/10000000000 : ℝ)^4635 ≤ (22653515360601/50000000000000 : ℝ)^3611 := by
    have hnat : (5396698453 : ℕ)^4635*50000000000000^3611 ≤ 22653515360601^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396698453 10000000000 22653515360601 50000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1079339523/2000000000 : ℝ)^4635 ≤ (4530702169087/10000000000000 : ℝ)^3611 := by
    have hnat : (1079339523 : ℕ)^4635*10000000000000^3611 ≤ 4530702169087^3611*2000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079339523 2000000000 4530702169087 10000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-39575481/250000000 : ℝ), (5396698453/10000000000 : ℝ), (1079339523/2000000000 : ℝ)] ![(9385947573181/100000000000000 : ℝ), (22653515360601/50000000000000 : ℝ), (4530702169087/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-39575481/250000000 : ℝ)|^4635 ≤ (9385947573181/100000000000000 : ℝ)^3611
        have hw : |(-39575481/250000000 : ℝ)|=(39575481/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396698453/10000000000 : ℝ)|^4635 ≤ (22653515360601/50000000000000 : ℝ)^3611
        have hw : |(5396698453/10000000000 : ℝ)|=(5396698453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1079339523/2000000000 : ℝ)|^4635 ≤ (4530702169087/10000000000000 : ℝ)^3611
        have hw : |(1079339523/2000000000 : ℝ)|=(1079339523/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_box_1 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5271143263/10000000000 : ℝ)*x 0 + (-219693509/1250000000 : ℝ)*x 1 + (1349174519/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5271143263/10000000000 : ℝ)^4635 ≤ (8791705923617/20000000000000 : ℝ)^3611 := by
    have hnat : (5271143263 : ℕ)^4635*20000000000000^3611 ≤ 8791705923617^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271143263 10000000000 8791705923617 20000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (219693509/1250000000 : ℝ)^4635 ≤ (5367221857131/50000000000000 : ℝ)^3611 := by
    have hnat : (219693509 : ℕ)^4635*50000000000000^3611 ≤ 5367221857131^3611*1250000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219693509 1250000000 5367221857131 50000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1349174519/2500000000 : ℝ)^4635 ≤ (4530702665863/10000000000000 : ℝ)^3611 := by
    have hnat : (1349174519 : ℕ)^4635*10000000000000^3611 ≤ 4530702665863^3611*2500000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349174519 2500000000 4530702665863 10000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5271143263/10000000000 : ℝ), (-219693509/1250000000 : ℝ), (1349174519/2500000000 : ℝ)] ![(8791705923617/20000000000000 : ℝ), (5367221857131/50000000000000 : ℝ), (4530702665863/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5271143263/10000000000 : ℝ)|^4635 ≤ (8791705923617/20000000000000 : ℝ)^3611
        have hw : |(5271143263/10000000000 : ℝ)|=(5271143263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-219693509/1250000000 : ℝ)|^4635 ≤ (5367221857131/50000000000000 : ℝ)^3611
        have hw : |(-219693509/1250000000 : ℝ)|=(219693509/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1349174519/2500000000 : ℝ)|^4635 ≤ (4530702665863/10000000000000 : ℝ)^3611
        have hw : |(1349174519/2500000000 : ℝ)|=(1349174519/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_box_2 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1054228747/2000000000 : ℝ)*x 0 + (5396698027/10000000000 : ℝ)*x 1 + (-878773747/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054228747/2000000000 : ℝ)^4635 ≤ (43958534670541/100000000000000 : ℝ)^3611 := by
    have hnat : (1054228747 : ℕ)^4635*100000000000000^3611 ≤ 43958534670541^3611*2000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054228747 2000000000 43958534670541 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396698027/10000000000 : ℝ)^4635 ≤ (45307026130603/100000000000000 : ℝ)^3611 := by
    have hnat : (5396698027 : ℕ)^4635*100000000000000^3611 ≤ 45307026130603^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396698027 10000000000 45307026130603 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (878773747/5000000000 : ℝ)^4635 ≤ (10734439182967/100000000000000 : ℝ)^3611 := by
    have hnat : (878773747 : ℕ)^4635*100000000000000^3611 ≤ 10734439182967^3611*5000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      878773747 5000000000 10734439182967 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1054228747/2000000000 : ℝ), (5396698027/10000000000 : ℝ), (-878773747/5000000000 : ℝ)] ![(43958534670541/100000000000000 : ℝ), (45307026130603/100000000000000 : ℝ), (10734439182967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1054228747/2000000000 : ℝ)|^4635 ≤ (43958534670541/100000000000000 : ℝ)^3611
        have hw : |(1054228747/2000000000 : ℝ)|=(1054228747/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396698027/10000000000 : ℝ)|^4635 ≤ (45307026130603/100000000000000 : ℝ)^3611
        have hw : |(5396698027/10000000000 : ℝ)|=(5396698027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-878773747/5000000000 : ℝ)|^4635 ≤ (10734439182967/100000000000000 : ℝ)^3611
        have hw : |(-878773747/5000000000 : ℝ)|=(878773747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_box_3 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4444669043/10000000000 : ℝ)*x 0 + (2075112543/5000000000 : ℝ)*x 1 + (259389137/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4444669043/10000000000 : ℝ)^4635 ≤ (17658119737831/50000000000000 : ℝ)^3611 := by
    have hnat : (4444669043 : ℕ)^4635*50000000000000^3611 ≤ 17658119737831^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4444669043 10000000000 17658119737831 50000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2075112543/5000000000 : ℝ)^4635 ≤ (6468374945069/20000000000000 : ℝ)^3611 := by
    have hnat : (2075112543 : ℕ)^4635*20000000000000^3611 ≤ 6468374945069^3611*5000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2075112543 5000000000 6468374945069 20000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (259389137/625000000 : ℝ)^4635 ≤ (16170942894147/50000000000000 : ℝ)^3611 := by
    have hnat : (259389137 : ℕ)^4635*50000000000000^3611 ≤ 16170942894147^3611*625000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259389137 625000000 16170942894147 50000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4444669043/10000000000 : ℝ), (2075112543/5000000000 : ℝ), (259389137/625000000 : ℝ)] ![(17658119737831/50000000000000 : ℝ), (6468374945069/20000000000000 : ℝ), (16170942894147/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4444669043/10000000000 : ℝ)|^4635 ≤ (17658119737831/50000000000000 : ℝ)^3611
        have hw : |(4444669043/10000000000 : ℝ)|=(4444669043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2075112543/5000000000 : ℝ)|^4635 ≤ (6468374945069/20000000000000 : ℝ)^3611
        have hw : |(2075112543/5000000000 : ℝ)|=(2075112543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(259389137/625000000 : ℝ)|^4635 ≤ (16170942894147/50000000000000 : ℝ)^3611
        have hw : |(259389137/625000000 : ℝ)|=(259389137/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_box_4 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-998169839/5000000000 : ℝ)*x 0 + (5245037363/10000000000 : ℝ)*x 1 + (1049007609/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (998169839/5000000000 : ℝ)^4635 ≤ (1264143427033/10000000000000 : ℝ)^3611 := by
    have hnat : (998169839 : ℕ)^4635*10000000000000^3611 ≤ 1264143427033^3611*5000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      998169839 5000000000 1264143427033 10000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245037363/10000000000 : ℝ)^4635 ≤ (4367927921027/10000000000000 : ℝ)^3611 := by
    have hnat : (5245037363 : ℕ)^4635*10000000000000^3611 ≤ 4367927921027^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245037363 10000000000 4367927921027 10000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049007609/2000000000 : ℝ)^4635 ≤ (4367928650037/10000000000000 : ℝ)^3611 := by
    have hnat : (1049007609 : ℕ)^4635*10000000000000^3611 ≤ 4367928650037^3611*2000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049007609 2000000000 4367928650037 10000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-998169839/5000000000 : ℝ), (5245037363/10000000000 : ℝ), (1049007609/2000000000 : ℝ)] ![(1264143427033/10000000000000 : ℝ), (4367927921027/10000000000000 : ℝ), (4367928650037/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-998169839/5000000000 : ℝ)|^4635 ≤ (1264143427033/10000000000000 : ℝ)^3611
        have hw : |(-998169839/5000000000 : ℝ)|=(998169839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245037363/10000000000 : ℝ)|^4635 ≤ (4367927921027/10000000000000 : ℝ)^3611
        have hw : |(5245037363/10000000000 : ℝ)|=(5245037363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049007609/2000000000 : ℝ)|^4635 ≤ (4367928650037/10000000000000 : ℝ)^3611
        have hw : |(1049007609/2000000000 : ℝ)|=(1049007609/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_box_5 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5376278501/10000000000 : ℝ)*x 0 + (-910449889/5000000000 : ℝ)*x 1 + (1049007567/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5376278501/10000000000 : ℝ)^4635 ≤ (45087102407843/100000000000000 : ℝ)^3611 := by
    have hnat : (5376278501 : ℕ)^4635*100000000000000^3611 ≤ 45087102407843^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376278501 10000000000 45087102407843 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (910449889/5000000000 : ℝ)^4635 ≤ (11233613324483/100000000000000 : ℝ)^3611 := by
    have hnat : (910449889 : ℕ)^4635*100000000000000^3611 ≤ 11233613324483^3611*5000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      910449889 5000000000 11233613324483 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049007567/2000000000 : ℝ)^4635 ≤ (21839642127809/50000000000000 : ℝ)^3611 := by
    have hnat : (1049007567 : ℕ)^4635*50000000000000^3611 ≤ 21839642127809^3611*2000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049007567 2000000000 21839642127809 50000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5376278501/10000000000 : ℝ), (-910449889/5000000000 : ℝ), (1049007567/2000000000 : ℝ)] ![(45087102407843/100000000000000 : ℝ), (11233613324483/100000000000000 : ℝ), (21839642127809/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5376278501/10000000000 : ℝ)|^4635 ≤ (45087102407843/100000000000000 : ℝ)^3611
        have hw : |(5376278501/10000000000 : ℝ)|=(5376278501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-910449889/5000000000 : ℝ)|^4635 ≤ (11233613324483/100000000000000 : ℝ)^3611
        have hw : |(-910449889/5000000000 : ℝ)|=(910449889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049007567/2000000000 : ℝ)|^4635 ≤ (21839642127809/50000000000000 : ℝ)^3611
        have hw : |(1049007567/2000000000 : ℝ)|=(1049007567/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_box_6 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (268813929/500000000 : ℝ)*x 0 + (1049007603/2000000000 : ℝ)*x 1 + (-455224857/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268813929/500000000 : ℝ)^4635 ≤ (11271775814559/25000000000000 : ℝ)^3611 := by
    have hnat : (268813929 : ℕ)^4635*25000000000000^3611 ≤ 11271775814559^3611*500000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268813929 500000000 11271775814559 25000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049007603/2000000000 : ℝ)^4635 ≤ (43679286179691/100000000000000 : ℝ)^3611 := by
    have hnat : (1049007603 : ℕ)^4635*100000000000000^3611 ≤ 43679286179691^3611*2000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049007603 2000000000 43679286179691 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (455224857/2500000000 : ℝ)^4635 ≤ (11233610552927/100000000000000 : ℝ)^3611 := by
    have hnat : (455224857 : ℕ)^4635*100000000000000^3611 ≤ 11233610552927^3611*2500000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      455224857 2500000000 11233610552927 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268813929/500000000 : ℝ), (1049007603/2000000000 : ℝ), (-455224857/2500000000 : ℝ)] ![(11271775814559/25000000000000 : ℝ), (43679286179691/100000000000000 : ℝ), (11233610552927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268813929/500000000 : ℝ)|^4635 ≤ (11271775814559/25000000000000 : ℝ)^3611
        have hw : |(268813929/500000000 : ℝ)|=(268813929/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049007603/2000000000 : ℝ)|^4635 ≤ (43679286179691/100000000000000 : ℝ)^3611
        have hw : |(1049007603/2000000000 : ℝ)|=(1049007603/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-455224857/2500000000 : ℝ)|^4635 ≤ (11233610552927/100000000000000 : ℝ)^3611
        have hw : |(-455224857/2500000000 : ℝ)|=(455224857/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_box_7 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (161621579/400000000 : ℝ)*x 0 + (4352163271/10000000000 : ℝ)*x 1 + (4352162517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (161621579/400000000 : ℝ)^4635 ≤ (31248863749009/100000000000000 : ℝ)^3611 := by
    have hnat : (161621579 : ℕ)^4635*100000000000000^3611 ≤ 31248863749009^3611*400000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161621579 400000000 31248863749009 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4352163271/10000000000 : ℝ)^4635 ≤ (17187785971459/50000000000000 : ℝ)^3611 := by
    have hnat : (4352163271 : ℕ)^4635*50000000000000^3611 ≤ 17187785971459^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4352163271 10000000000 17187785971459 50000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4352162517/10000000000 : ℝ)^4635 ≤ (34375564298607/100000000000000 : ℝ)^3611 := by
    have hnat : (4352162517 : ℕ)^4635*100000000000000^3611 ≤ 34375564298607^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4352162517 10000000000 34375564298607 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(161621579/400000000 : ℝ), (4352163271/10000000000 : ℝ), (4352162517/10000000000 : ℝ)] ![(31248863749009/100000000000000 : ℝ), (17187785971459/50000000000000 : ℝ), (34375564298607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(161621579/400000000 : ℝ)|^4635 ≤ (31248863749009/100000000000000 : ℝ)^3611
        have hw : |(161621579/400000000 : ℝ)|=(161621579/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4352163271/10000000000 : ℝ)|^4635 ≤ (17187785971459/50000000000000 : ℝ)^3611
        have hw : |(4352163271/10000000000 : ℝ)|=(4352163271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4352162517/10000000000 : ℝ)|^4635 ≤ (34375564298607/100000000000000 : ℝ)^3611
        have hw : |(4352162517/10000000000 : ℝ)|=(4352162517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_box_8 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-95436681/500000000 : ℝ)*x 0 + (5138195751/10000000000 : ℝ)*x 1 + (1354243059/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (95436681/500000000 : ℝ)^4635 ≤ (11933849370241/100000000000000 : ℝ)^3611 := by
    have hnat : (95436681 : ℕ)^4635*100000000000000^3611 ≤ 11933849370241^3611*500000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95436681 500000000 11933849370241 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5138195751/10000000000 : ℝ)^4635 ≤ (21270266138243/50000000000000 : ℝ)^3611 := by
    have hnat : (5138195751 : ℕ)^4635*50000000000000^3611 ≤ 21270266138243^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5138195751 10000000000 21270266138243 50000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1354243059/2500000000 : ℝ)^4635 ≤ (45525618337793/100000000000000 : ℝ)^3611 := by
    have hnat : (1354243059 : ℕ)^4635*100000000000000^3611 ≤ 45525618337793^3611*2500000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354243059 2500000000 45525618337793 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-95436681/500000000 : ℝ), (5138195751/10000000000 : ℝ), (1354243059/2500000000 : ℝ)] ![(11933849370241/100000000000000 : ℝ), (21270266138243/50000000000000 : ℝ), (45525618337793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-95436681/500000000 : ℝ)|^4635 ≤ (11933849370241/100000000000000 : ℝ)^3611
        have hw : |(-95436681/500000000 : ℝ)|=(95436681/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5138195751/10000000000 : ℝ)|^4635 ≤ (21270266138243/50000000000000 : ℝ)^3611
        have hw : |(5138195751/10000000000 : ℝ)|=(5138195751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1354243059/2500000000 : ℝ)|^4635 ≤ (45525618337793/100000000000000 : ℝ)^3611
        have hw : |(1354243059/2500000000 : ℝ)|=(1354243059/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_box_9 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628542963/5000000000 : ℝ)*x 0 + (-1748847427/10000000000 : ℝ)*x 1 + (5416971113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628542963/5000000000 : ℝ)^4635 ≤ (1369003493711/3125000000000 : ℝ)^3611 := by
    have hnat : (2628542963 : ℕ)^4635*3125000000000^3611 ≤ 1369003493711^3611*5000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628542963 5000000000 1369003493711 3125000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1748847427/10000000000 : ℝ)^4635 ≤ (10666281965851/100000000000000 : ℝ)^3611 := by
    have hnat : (1748847427 : ℕ)^4635*100000000000000^3611 ≤ 10666281965851^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1748847427 10000000000 10666281965851 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416971113/10000000000 : ℝ)^4635 ≤ (11381401555853/25000000000000 : ℝ)^3611 := by
    have hnat : (5416971113 : ℕ)^4635*25000000000000^3611 ≤ 11381401555853^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416971113 10000000000 11381401555853 25000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628542963/5000000000 : ℝ), (-1748847427/10000000000 : ℝ), (5416971113/10000000000 : ℝ)] ![(1369003493711/3125000000000 : ℝ), (10666281965851/100000000000000 : ℝ), (11381401555853/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628542963/5000000000 : ℝ)|^4635 ≤ (1369003493711/3125000000000 : ℝ)^3611
        have hw : |(2628542963/5000000000 : ℝ)|=(2628542963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1748847427/10000000000 : ℝ)|^4635 ≤ (10666281965851/100000000000000 : ℝ)^3611
        have hw : |(-1748847427/10000000000 : ℝ)|=(1748847427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416971113/10000000000 : ℝ)|^4635 ≤ (11381401555853/25000000000000 : ℝ)^3611
        have hw : |(5416971113/10000000000 : ℝ)|=(5416971113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_box_10 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (210283453/400000000 : ℝ)*x 0 + (5416971577/10000000000 : ℝ)*x 1 + (-1748846243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210283453/400000000 : ℝ)^4635 ≤ (43808116066557/100000000000000 : ℝ)^3611 := by
    have hnat : (210283453 : ℕ)^4635*100000000000000^3611 ≤ 43808116066557^3611*400000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210283453 400000000 43808116066557 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5416971577/10000000000 : ℝ)^4635 ≤ (45525611228819/100000000000000 : ℝ)^3611 := by
    have hnat : (5416971577 : ℕ)^4635*100000000000000^3611 ≤ 45525611228819^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416971577 10000000000 45525611228819 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1748846243/10000000000 : ℝ)^4635 ≤ (2133254539361/20000000000000 : ℝ)^3611 := by
    have hnat : (1748846243 : ℕ)^4635*20000000000000^3611 ≤ 2133254539361^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1748846243 10000000000 2133254539361 20000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210283453/400000000 : ℝ), (5416971577/10000000000 : ℝ), (-1748846243/10000000000 : ℝ)] ![(43808116066557/100000000000000 : ℝ), (45525611228819/100000000000000 : ℝ), (2133254539361/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210283453/400000000 : ℝ)|^4635 ≤ (43808116066557/100000000000000 : ℝ)^3611
        have hw : |(210283453/400000000 : ℝ)|=(210283453/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5416971577/10000000000 : ℝ)|^4635 ≤ (45525611228819/100000000000000 : ℝ)^3611
        have hw : |(5416971577/10000000000 : ℝ)|=(5416971577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1748846243/10000000000 : ℝ)|^4635 ≤ (2133254539361/20000000000000 : ℝ)^3611
        have hw : |(-1748846243/10000000000 : ℝ)|=(1748846243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_box_11 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4497546393/10000000000 : ℝ)*x 0 + (824639653/2000000000 : ℝ)*x 1 + (206159857/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4497546393/10000000000 : ℝ)^4635 ≤ (35856442306473/100000000000000 : ℝ)^3611 := by
    have hnat : (4497546393 : ℕ)^4635*100000000000000^3611 ≤ 35856442306473^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497546393 10000000000 35856442306473 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (824639653/2000000000 : ℝ)^4635 ≤ (32071784455809/100000000000000 : ℝ)^3611 := by
    have hnat : (824639653 : ℕ)^4635*100000000000000^3611 ≤ 32071784455809^3611*2000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      824639653 2000000000 32071784455809 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (206159857/500000000 : ℝ)^4635 ≤ (32071773223639/100000000000000 : ℝ)^3611 := by
    have hnat : (206159857 : ℕ)^4635*100000000000000^3611 ≤ 32071773223639^3611*500000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206159857 500000000 32071773223639 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4497546393/10000000000 : ℝ), (824639653/2000000000 : ℝ), (206159857/500000000 : ℝ)] ![(35856442306473/100000000000000 : ℝ), (32071784455809/100000000000000 : ℝ), (32071773223639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4497546393/10000000000 : ℝ)|^4635 ≤ (35856442306473/100000000000000 : ℝ)^3611
        have hw : |(4497546393/10000000000 : ℝ)|=(4497546393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(824639653/2000000000 : ℝ)|^4635 ≤ (32071784455809/100000000000000 : ℝ)^3611
        have hw : |(824639653/2000000000 : ℝ)|=(824639653/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(206159857/500000000 : ℝ)|^4635 ≤ (32071773223639/100000000000000 : ℝ)^3611
        have hw : |(206159857/500000000 : ℝ)|=(206159857/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_box_12 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-835145813/5000000000 : ℝ)*x 0 + (5500280533/10000000000 : ℝ)*x 1 + (5229988111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (835145813/5000000000 : ℝ)^4635 ≤ (10055260672267/100000000000000 : ℝ)^3611 := by
    have hnat : (835145813 : ℕ)^4635*100000000000000^3611 ≤ 10055260672267^3611*5000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      835145813 5000000000 10055260672267 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5500280533/10000000000 : ℝ)^4635 ≤ (23213130266453/50000000000000 : ℝ)^3611 := by
    have hnat : (5500280533 : ℕ)^4635*50000000000000^3611 ≤ 23213130266453^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5500280533 10000000000 23213130266453 50000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5229988111/10000000000 : ℝ)^4635 ≤ (21759239390853/50000000000000 : ℝ)^3611 := by
    have hnat : (5229988111 : ℕ)^4635*50000000000000^3611 ≤ 21759239390853^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229988111 10000000000 21759239390853 50000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-835145813/5000000000 : ℝ), (5500280533/10000000000 : ℝ), (5229988111/10000000000 : ℝ)] ![(10055260672267/100000000000000 : ℝ), (23213130266453/50000000000000 : ℝ), (21759239390853/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-835145813/5000000000 : ℝ)|^4635 ≤ (10055260672267/100000000000000 : ℝ)^3611
        have hw : |(-835145813/5000000000 : ℝ)|=(835145813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5500280533/10000000000 : ℝ)|^4635 ≤ (23213130266453/50000000000000 : ℝ)^3611
        have hw : |(5500280533/10000000000 : ℝ)|=(5500280533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5229988111/10000000000 : ℝ)|^4635 ≤ (21759239390853/50000000000000 : ℝ)^3611
        have hw : |(5229988111/10000000000 : ℝ)|=(5229988111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_box_13 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (673339077/1250000000 : ℝ)*x 0 + (-1827016063/10000000000 : ℝ)*x 1 + (5229988161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (673339077/1250000000 : ℝ)^4635 ≤ (45199451061929/100000000000000 : ℝ)^3611 := by
    have hnat : (673339077 : ℕ)^4635*100000000000000^3611 ≤ 45199451061929^3611*1250000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673339077 1250000000 45199451061929 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1827016063/10000000000 : ℝ)^4635 ≤ (5641034799117/50000000000000 : ℝ)^3611 := by
    have hnat : (1827016063 : ℕ)^4635*50000000000000^3611 ≤ 5641034799117^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1827016063 10000000000 5641034799117 50000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5229988161/10000000000 : ℝ)^4635 ≤ (8703695863147/20000000000000 : ℝ)^3611 := by
    have hnat : (5229988161 : ℕ)^4635*20000000000000^3611 ≤ 8703695863147^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229988161 10000000000 8703695863147 20000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(673339077/1250000000 : ℝ), (-1827016063/10000000000 : ℝ), (5229988161/10000000000 : ℝ)] ![(45199451061929/100000000000000 : ℝ), (5641034799117/50000000000000 : ℝ), (8703695863147/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(673339077/1250000000 : ℝ)|^4635 ≤ (45199451061929/100000000000000 : ℝ)^3611
        have hw : |(673339077/1250000000 : ℝ)|=(673339077/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1827016063/10000000000 : ℝ)|^4635 ≤ (5641034799117/50000000000000 : ℝ)^3611
        have hw : |(-1827016063/10000000000 : ℝ)|=(1827016063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5229988161/10000000000 : ℝ)|^4635 ≤ (8703695863147/20000000000000 : ℝ)^3611
        have hw : |(5229988161/10000000000 : ℝ)|=(5229988161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_box_14 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5386712561/10000000000 : ℝ)*x 0 + (2614994071/5000000000 : ℝ)*x 1 + (-365403233/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5386712561/10000000000 : ℝ)^4635 ≤ (45199450469557/100000000000000 : ℝ)^3611 := by
    have hnat : (5386712561 : ℕ)^4635*100000000000000^3611 ≤ 45199450469557^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386712561 10000000000 45199450469557 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2614994071/5000000000 : ℝ)^4635 ≤ (10879619778201/25000000000000 : ℝ)^3611 := by
    have hnat : (2614994071 : ℕ)^4635*25000000000000^3611 ≤ 10879619778201^3611*5000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614994071 5000000000 10879619778201 25000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (365403233/2000000000 : ℝ)^4635 ≤ (11282070406713/100000000000000 : ℝ)^3611 := by
    have hnat : (365403233 : ℕ)^4635*100000000000000^3611 ≤ 11282070406713^3611*2000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      365403233 2000000000 11282070406713 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5386712561/10000000000 : ℝ), (2614994071/5000000000 : ℝ), (-365403233/2000000000 : ℝ)] ![(45199450469557/100000000000000 : ℝ), (10879619778201/25000000000000 : ℝ), (11282070406713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5386712561/10000000000 : ℝ)|^4635 ≤ (45199450469557/100000000000000 : ℝ)^3611
        have hw : |(5386712561/10000000000 : ℝ)|=(5386712561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2614994071/5000000000 : ℝ)|^4635 ≤ (10879619778201/25000000000000 : ℝ)^3611
        have hw : |(2614994071/5000000000 : ℝ)|=(2614994071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-365403233/2000000000 : ℝ)|^4635 ≤ (11282070406713/100000000000000 : ℝ)^3611
        have hw : |(-365403233/2000000000 : ℝ)|=(365403233/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_box_15 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3999573497/10000000000 : ℝ)*x 0 + (4372177453/10000000000 : ℝ)*x 1 + (4372176381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3999573497/10000000000 : ℝ)^4635 ≤ (6168556271289/20000000000000 : ℝ)^3611 := by
    have hnat : (3999573497 : ℕ)^4635*20000000000000^3611 ≤ 6168556271289^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3999573497 10000000000 6168556271289 20000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4372177453/10000000000 : ℝ)^4635 ≤ (3457861475681/10000000000000 : ℝ)^3611 := by
    have hnat : (4372177453 : ℕ)^4635*10000000000000^3611 ≤ 3457861475681^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4372177453 10000000000 3457861475681 10000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4372176381/10000000000 : ℝ)^4635 ≤ (8644650968589/25000000000000 : ℝ)^3611 := by
    have hnat : (4372176381 : ℕ)^4635*25000000000000^3611 ≤ 8644650968589^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4372176381 10000000000 8644650968589 25000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3999573497/10000000000 : ℝ), (4372177453/10000000000 : ℝ), (4372176381/10000000000 : ℝ)] ![(6168556271289/20000000000000 : ℝ), (3457861475681/10000000000000 : ℝ), (8644650968589/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3999573497/10000000000 : ℝ)|^4635 ≤ (6168556271289/20000000000000 : ℝ)^3611
        have hw : |(3999573497/10000000000 : ℝ)|=(3999573497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4372177453/10000000000 : ℝ)|^4635 ≤ (3457861475681/10000000000000 : ℝ)^3611
        have hw : |(4372177453/10000000000 : ℝ)|=(4372177453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4372176381/10000000000 : ℝ)|^4635 ≤ (8644650968589/25000000000000 : ℝ)^3611
        have hw : |(4372176381/10000000000 : ℝ)|=(4372176381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1569_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167947699/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5559/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(63827/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29449/50000 : ℝ) ∧ (8091/10000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (2159/2500 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5559/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5559/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5559/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5559/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5559/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5559/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5559/50000 : ℝ) ^ (4633/1024 : ℝ) ≤ (2414346803371701/50000000000000000000 : ℝ) := by
    have hpowers : (5559/50000 : ℝ)^4633 ≤ (2414346803371701/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5559 : ℕ)^4633*50000000000000000000^1024 ≤ 2414346803371701^1024*50000^4633 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5559 50000 2414346803371701 50000000000000000000 4633 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5559/50000 : ℝ)) (X := (2414346803371701/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4633 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3871/25000 : ℝ) ^ (4633/1024 : ℝ) ≤ (21612051253673497/100000000000000000000 : ℝ) := by
    have hpowers : (3871/25000 : ℝ)^4633 ≤ (21612051253673497/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3871 : ℕ)^4633*100000000000000000000^1024 ≤ 21612051253673497^1024*25000^4633 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3871 25000 21612051253673497 100000000000000000000 4633 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3871/25000 : ℝ)) (X := (21612051253673497/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4633 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002414346803371701/25000000000000000000 : ℝ) ≤ (5000106721266489/5000000000000000 : ℝ) ^ (4633/1024 : ℝ) := by
    have hpowers : (25002414346803371701/25000000000000000000 : ℝ)^1024 ≤ (5000106721266489/5000000000000000 : ℝ)^4633 := by
      have hnat : (25002414346803371701 : ℕ)^1024*5000000000000000^4633 ≤ 5000106721266489^4633*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002414346803371701 25000000000000000000 5000106721266489 5000000000000000 1024 4633 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000106721266489/5000000000000000 : ℝ)) (X := (25002414346803371701/25000000000000000000 : ℝ)) (by norm_num) 4633 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100026440744860416899/100000000000000000000 : ℝ) ≤ (10000584341352443/10000000000000000 : ℝ) ^ (4633/1024 : ℝ) := by
    have hpowers : (100026440744860416899/100000000000000000000 : ℝ)^1024 ≤ (10000584341352443/10000000000000000 : ℝ)^4633 := by
      have hnat : (100026440744860416899 : ℕ)^1024*10000000000000000^4633 ≤ 10000584341352443^4633*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100026440744860416899 100000000000000000000 10000584341352443 10000000000000000 1024 4633 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000584341352443/10000000000000000 : ℝ)) (X := (100026440744860416899/100000000000000000000 : ℝ)) (by norm_num) 4633 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50021612051253673497/50000000000000000000 : ℝ) ≤ (2500238810042977/2500000000000000 : ℝ) ^ (4633/1024 : ℝ) := by
    have hpowers : (50021612051253673497/50000000000000000000 : ℝ)^1024 ≤ (2500238810042977/2500000000000000 : ℝ)^4633 := by
      have hnat : (50021612051253673497 : ℕ)^1024*2500000000000000^4633 ≤ 2500238810042977^4633*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021612051253673497 50000000000000000000 2500238810042977 2500000000000000 1024 4633 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500238810042977/2500000000000000 : ℝ)) (X := (50021612051253673497/50000000000000000000 : ℝ)) (by norm_num) 4633 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2414346803371701/50000000000000000000 : ℝ) ≤ ((341036598312104361/341093750000000000 : ℝ)+2*(74179763893/87320000000000 : ℝ)*(5559/50000 : ℝ))^(4633/1024 : ℝ) := by
    rw [show (341036598312104361/341093750000000000 : ℝ)+2*(74179763893/87320000000000 : ℝ)*(5559/50000 : ℝ)=(5000106721266489/5000000000000000 : ℝ) by norm_num, show 1+2*(2414346803371701/50000000000000000000 : ℝ)=(25002414346803371701/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(21612051253673497/100000000000000000000 : ℝ)+(2414346803371701/50000000000000000000 : ℝ) ≤ ((341036598312104361/341093750000000000 : ℝ)+(74179763893/87320000000000 : ℝ)*((3871/25000 : ℝ)+(5559/50000 : ℝ)))^(4633/1024 : ℝ) := by
    rw [show (341036598312104361/341093750000000000 : ℝ)+(74179763893/87320000000000 : ℝ)*((3871/25000 : ℝ)+(5559/50000 : ℝ))=(10000584341352443/10000000000000000 : ℝ) by norm_num, show 1+(21612051253673497/100000000000000000000 : ℝ)+(2414346803371701/50000000000000000000 : ℝ)=(100026440744860416899/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(21612051253673497/100000000000000000000 : ℝ) ≤ ((341036598312104361/341093750000000000 : ℝ)+2*(74179763893/87320000000000 : ℝ)*(3871/25000 : ℝ))^(4633/1024 : ℝ) := by
    rw [show (341036598312104361/341093750000000000 : ℝ)+2*(74179763893/87320000000000 : ℝ)*(3871/25000 : ℝ)=(2500238810042977/2500000000000000 : ℝ) by norm_num, show 1+2*(21612051253673497/100000000000000000000 : ℝ)=(50021612051253673497/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (341036598312104361/341093750000000000 : ℝ)*(X 1 0+X 2 0)+(74179763893/87320000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4633/1024 : ℝ)) (lo := (5559/50000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (341036598312104361/341093750000000000 : ℝ)) (alpha := (74179763893/87320000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (341036598312104361/341093750000000000 : ℝ)*(X 0 1+X 2 1)+(74179763893/87320000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4633/1024 : ℝ)) (lo := (5559/50000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (341036598312104361/341093750000000000 : ℝ)) (alpha := (74179763893/87320000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (341036598312104361/341093750000000000 : ℝ)*(X 0 2+X 1 2)+(74179763893/87320000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4633/1024 : ℝ)) (lo := (5559/50000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (341036598312104361/341093750000000000 : ℝ)) (alpha := (74179763893/87320000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-39575481/250000000 : ℝ)*X 0 0+(5396698453/10000000000 : ℝ)*X 0 1+(1079339523/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5271143263/10000000000 : ℝ)*X 1 0+(-219693509/1250000000 : ℝ)*X 1 1+(1349174519/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1054228747/2000000000 : ℝ)*X 2 0+(5396698027/10000000000 : ℝ)*X 2 1+(-878773747/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4444669043/10000000000 : ℝ)*X 0 0+(2075112543/5000000000 : ℝ)*X 0 1+(259389137/625000000 : ℝ)*X 0 2+(4444669043/10000000000 : ℝ)*X 1 0+(2075112543/5000000000 : ℝ)*X 1 1+(259389137/625000000 : ℝ)*X 1 2+(4444669043/10000000000 : ℝ)*X 2 0+(2075112543/5000000000 : ℝ)*X 2 1+(259389137/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-998169839/5000000000 : ℝ)*X 0 0+(5245037363/10000000000 : ℝ)*X 0 1+(1049007609/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5376278501/10000000000 : ℝ)*X 1 0+(-910449889/5000000000 : ℝ)*X 1 1+(1049007567/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((268813929/500000000 : ℝ)*X 2 0+(1049007603/2000000000 : ℝ)*X 2 1+(-455224857/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((161621579/400000000 : ℝ)*X 0 0+(4352163271/10000000000 : ℝ)*X 0 1+(4352162517/10000000000 : ℝ)*X 0 2+(161621579/400000000 : ℝ)*X 1 0+(4352163271/10000000000 : ℝ)*X 1 1+(4352162517/10000000000 : ℝ)*X 1 2+(161621579/400000000 : ℝ)*X 2 0+(4352163271/10000000000 : ℝ)*X 2 1+(4352162517/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-95436681/500000000 : ℝ)*X 0 0+(5138195751/10000000000 : ℝ)*X 0 1+(1354243059/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2628542963/5000000000 : ℝ)*X 1 0+(-1748847427/10000000000 : ℝ)*X 1 1+(5416971113/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((210283453/400000000 : ℝ)*X 2 0+(5416971577/10000000000 : ℝ)*X 2 1+(-1748846243/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4497546393/10000000000 : ℝ)*X 0 0+(824639653/2000000000 : ℝ)*X 0 1+(206159857/500000000 : ℝ)*X 0 2+(4497546393/10000000000 : ℝ)*X 1 0+(824639653/2000000000 : ℝ)*X 1 1+(206159857/500000000 : ℝ)*X 1 2+(4497546393/10000000000 : ℝ)*X 2 0+(824639653/2000000000 : ℝ)*X 2 1+(206159857/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-835145813/5000000000 : ℝ)*X 0 0+(5500280533/10000000000 : ℝ)*X 0 1+(5229988111/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((673339077/1250000000 : ℝ)*X 1 0+(-1827016063/10000000000 : ℝ)*X 1 1+(5229988161/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5386712561/10000000000 : ℝ)*X 2 0+(2614994071/5000000000 : ℝ)*X 2 1+(-365403233/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3999573497/10000000000 : ℝ)*X 0 0+(4372177453/10000000000 : ℝ)*X 0 1+(4372176381/10000000000 : ℝ)*X 0 2+(3999573497/10000000000 : ℝ)*X 1 0+(4372177453/10000000000 : ℝ)*X 1 1+(4372176381/10000000000 : ℝ)*X 1 2+(3999573497/10000000000 : ℝ)*X 2 0+(4372177453/10000000000 : ℝ)*X 2 1+(4372176381/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-63827/100000 : ℝ) ≤ (-108850489727804269238516220261/170546875000000000000000000000 : ℝ) := by norm_num
    linear_combination (47221849/100000000000000 : ℝ)*(upper1) + (114930991/100000000000000 : ℝ)*(lower2) + (2675287/50000000000000 : ℝ)*(upper5) + (92254026000243/4000000000000 : ℝ)*(major0) + (92254026000243/4000000000000 : ℝ)*(major1) + (92254026000243/4000000000000 : ℝ)*(major2) + (1034677229/100000000000000 : ℝ)*(sp1) + (326071711540961/10000000000000 : ℝ)*(sp4) + (25474373249969/781250000000 : ℝ)*(sp5) + (1630322886966421/50000000000000 : ℝ)*(sp6) + (343312266263739/25000000000000 : ℝ)*(sp7) + (73905273/2000000000000 : ℝ)*(sp12) + (75036740419/100000000000000 : ℝ)*(sp14) + (6218428311/100000000000000 : ℝ)*(sp15) + (343313820870817/25000000000000 : ℝ)*(f.failure) + (163036040533663/5000000000000 : ℝ)*(f.sum) + (37242098307533/4366000000000000000000000000 : ℝ)*base65 + (49082947091830767/5457500000000000000000000000000 : ℝ)*base67 + (21575468888750767/5457500000000000000000000000000 : ℝ)*base69 + (5084110715471733/5457500000000000000000000000000 : ℝ)*base72 + (1162740669821/174640000000000000000000000 : ℝ)*base73 + (38187528449020767/5457500000000000000000000000000 : ℝ)*base75 + (24380598003828267/5457500000000000000000000000000 : ℝ)*base77 + (17238318831629233/5457500000000000000000000000000 : ℝ)*base80 + (35913271083063/4366000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (16400083/2500000000000000000000 : ℝ)*base89 + (16400083/2500000000000000000000 : ℝ)*base91 + (16400083/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (29449/50000 : ℝ) ≤ (642896265026198820493846083/1091500000000000000000000000 : ℝ) := by norm_num
    linear_combination (836871/12500000000000 : ℝ)*(upper0) + (55610993/20000000000000 : ℝ)*(lower1) + (131316693/50000000000000 : ℝ)*(upper4) + (1193258154369113/50000000000000 : ℝ)*(major0) + (1193258154369113/50000000000000 : ℝ)*(major1) + (1193258154369113/50000000000000 : ℝ)*(major2) + (1666202781959593/50000000000000 : ℝ)*(sp0) + (1666172092989943/50000000000000 : ℝ)*(sp1) + (3332410369832541/100000000000000 : ℝ)*(sp2) + (1420982496636257/100000000000000 : ℝ)*(sp3) + (1032508613/100000000000000 : ℝ)*(sp6) + (5300724531/100000000000000 : ℝ)*(sp7) + (364901373/6250000000000 : ℝ)*(sp8) + (67216361269/100000000000000 : ℝ)*(sp9) + (355246949340197/25000000000000 : ℝ)*(f.failure) + (1666205701170577/50000000000000 : ℝ)*(f.sum) + (4546815252199/2183000000000000000000000000 : ℝ)*base66 + (35113118844866547/68218750000000000000000000000000 : ℝ)*base67 + (51698547775133453/68218750000000000000000000000000 : ℝ)*base70 + (479525048876914703/68218750000000000000000000000000 : ℝ)*base72 + (605192012791/87320000000000000000000000 : ℝ)*base74 + (67786600012835297/68218750000000000000000000000000 : ℝ)*base75 + (73395965387804047/68218750000000000000000000000000 : ℝ)*base77 + (518082451261633453/68218750000000000000000000000000 : ℝ)*base80 + (288952670861/218300000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (4356703/2500000000000000000000 : ℝ)*base89 + (4356703/2500000000000000000000 : ℝ)*base91 + (4356703/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (8091/10000 : ℝ) ≤ (1379938674581394914484577802673/1705468750000000000000000000000 : ℝ) := by norm_num
    linear_combination (9211033/20000000000000 : ℝ)*(upper1) + (84170051/25000000000000 : ℝ)*(lower3) + (99945103/25000000000000 : ℝ)*(upper4) + (98555847/50000000000000 : ℝ)*(lower5) + (514617431914337/20000000000000 : ℝ)*(major0) + (514617431914337/20000000000000 : ℝ)*(major1) + (514617431914337/20000000000000 : ℝ)*(major2) + (9913376023/100000000000000 : ℝ)*(sp0) + (182575626791/100000000000000 : ℝ)*(sp2) + (44253041297/50000000000000 : ℝ)*(sp3) + (1793558544355381/50000000000000 : ℝ)*(sp8) + (1793563501043393/50000000000000 : ℝ)*(sp9) + (717388885291999/20000000000000 : ℝ)*(sp10) + (765993976387403/50000000000000 : ℝ)*(sp11) + (7660382294287/500000000000 : ℝ)*(f.failure) + (1793563501043393/50000000000000 : ℝ)*(f.sum) + (3708116188147/873200000000000000000000000 : ℝ)*base66 + (13789884130260253/27287500000000000000000000000000 : ℝ)*base67 + (191163641113635253/27287500000000000000000000000000 : ℝ)*base69 + (283317965281277247/27287500000000000000000000000000 : ℝ)*base72 + (8772007352673/4366000000000000000000000000 : ℝ)*base73 + (184594070697652247/27287500000000000000000000000000 : ℝ)*base76 + (164363537169927247/27287500000000000000000000000000 : ℝ)*base78 + (155742954379152247/27287500000000000000000000000000 : ℝ)*base80 + (18016158890029/4366000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (4387/50000000000000000000 : ℝ)*base90 + (4387/50000000000000000000 : ℝ)*base92 + (4387/50000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-2159/2500 : ℝ) ≤ (-29456049314577108331161635031237/34109375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (364233/3125000000000 : ℝ)*(lower0) + (1226203/5000000000000 : ℝ)*(upper1) + (5832339/12500000000000 : ℝ)*(lower2) + (51913459/25000000000000 : ℝ)*(upper3) + (653384540518639/25000000000000 : ℝ)*(major0) + (653384540518639/25000000000000 : ℝ)*(major1) + (653384540518639/25000000000000 : ℝ)*(major2) + (991491487/100000000000000 : ℝ)*(sp4) + (110383429103/100000000000000 : ℝ)*(sp5) + (46164810533/100000000000000 : ℝ)*(sp6) + (924924819007209/25000000000000 : ℝ)*(sp12) + (3699589884091221/100000000000000 : ℝ)*(sp13) + (369965410270979/10000000000000 : ℝ)*(sp14) + (389040483679767/25000000000000 : ℝ)*(sp15) + (389040483679767/25000000000000 : ℝ)*(f.failure) + (924925066880081/25000000000000 : ℝ)*(f.sum) + (304041271139/272875000000000000000000000 : ℝ)*base65 + (40208063128940321/8527343750000000000000000000000 : ℝ)*base68 + (169354146176771267/17054687500000000000000000000000 : ℝ)*base70 + (131843638689490017/17054687500000000000000000000000 : ℝ)*base72 + (6806910560447/2183000000000000000000000000 : ℝ)*base74 + (344416662542995659/34109375000000000000000000000000 : ℝ)*base76 + (171073386100120659/34109375000000000000000000000000 : ℝ)*base78 + (46576962418021267/17054687500000000000000000000000 : ℝ)*base80 + (913259223729/272875000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (20506133/2500000000000000000000 : ℝ)*base89 + (20506133/2500000000000000000000 : ℝ)*base91 + (20506133/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1569_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167947699/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5559/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63827/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29449/50000 : ℝ) else (8091/10000 : ℝ) ≤ X j i ∧ X j i ≤ (2159/2500 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1569_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1569_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167947699/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5559/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63827/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29449/50000 : ℝ) else (8091/10000 : ℝ) ≤ X j i ∧ X j i ≤ (2159/2500 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1569_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1569_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167947699/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5559/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63827/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29449/50000 : ℝ) else (8091/10000 : ℝ) ≤ X j i ∧ X j i ≤ (2159/2500 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1569_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
