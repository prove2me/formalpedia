-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1238_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:17:59.711995+00:00
-- url     : https://prove2.me/submissions/6bb43111-94fa-4560-bb07-54cd606d1126

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
theorem support_rectangle_w1238_s6_0 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1060892667/5000000000 : ℝ)*x 0 + (2695735953/5000000000 : ℝ)*x 1 + (526697443/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060892667/5000000000 : ℝ)^8431 ≤ (645122339961/5000000000000 : ℝ)^6383 := by
    have hnat : (1060892667 : ℕ)^8431*5000000000000^6383 ≤ 645122339961^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060892667 5000000000 645122339961 5000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695735953/5000000000 : ℝ)^8431 ≤ (5527580222779/12500000000000 : ℝ)^6383 := by
    have hnat : (2695735953 : ℕ)^8431*12500000000000^6383 ≤ 5527580222779^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695735953 5000000000 5527580222779 12500000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526697443/1000000000 : ℝ)^8431 ≤ (42876911403993/100000000000000 : ℝ)^6383 := by
    have hnat : (526697443 : ℕ)^8431*100000000000000^6383 ≤ 42876911403993^6383*1000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526697443 1000000000 42876911403993 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1060892667/5000000000 : ℝ), (2695735953/5000000000 : ℝ), (526697443/1000000000 : ℝ)] ![(645122339961/5000000000000 : ℝ), (5527580222779/12500000000000 : ℝ), (42876911403993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1060892667/5000000000 : ℝ)|^8431 ≤ (645122339961/5000000000000 : ℝ)^6383
        have hw : |(-1060892667/5000000000 : ℝ)|=(1060892667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695735953/5000000000 : ℝ)|^8431 ≤ (5527580222779/12500000000000 : ℝ)^6383
        have hw : |(2695735953/5000000000 : ℝ)|=(2695735953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526697443/1000000000 : ℝ)|^8431 ≤ (42876911403993/100000000000000 : ℝ)^6383
        have hw : |(526697443/1000000000 : ℝ)|=(526697443/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s6_1 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344381477/10000000000 : ℝ)*x 0 + (-2184912269/10000000000 : ℝ)*x 1 + (2633487249/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344381477/10000000000 : ℝ)^8431 ≤ (43711200169409/100000000000000 : ℝ)^6383 := by
    have hnat : (5344381477 : ℕ)^8431*100000000000000^6383 ≤ 43711200169409^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344381477 10000000000 43711200169409 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2184912269/10000000000 : ℝ)^8431 ≤ (13411887688151/100000000000000 : ℝ)^6383 := by
    have hnat : (2184912269 : ℕ)^8431*100000000000000^6383 ≤ 13411887688151^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184912269 10000000000 13411887688151 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633487249/5000000000 : ℝ)^8431 ≤ (1715076485407/4000000000000 : ℝ)^6383 := by
    have hnat : (2633487249 : ℕ)^8431*4000000000000^6383 ≤ 1715076485407^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633487249 5000000000 1715076485407 4000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344381477/10000000000 : ℝ), (-2184912269/10000000000 : ℝ), (2633487249/5000000000 : ℝ)] ![(43711200169409/100000000000000 : ℝ), (13411887688151/100000000000000 : ℝ), (1715076485407/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344381477/10000000000 : ℝ)|^8431 ≤ (43711200169409/100000000000000 : ℝ)^6383
        have hw : |(5344381477/10000000000 : ℝ)|=(5344381477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2184912269/10000000000 : ℝ)|^8431 ≤ (13411887688151/100000000000000 : ℝ)^6383
        have hw : |(-2184912269/10000000000 : ℝ)|=(2184912269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633487249/5000000000 : ℝ)|^8431 ≤ (1715076485407/4000000000000 : ℝ)^6383
        have hw : |(2633487249/5000000000 : ℝ)|=(2633487249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s6_2 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344381341/10000000000 : ℝ)*x 0 + (5266974507/10000000000 : ℝ)*x 1 + (-1092456219/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344381341/10000000000 : ℝ)^8431 ≤ (5463899837523/12500000000000 : ℝ)^6383 := by
    have hnat : (5344381341 : ℕ)^8431*12500000000000^6383 ≤ 5463899837523^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344381341 10000000000 5463899837523 12500000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266974507/10000000000 : ℝ)^8431 ≤ (42876912231949/100000000000000 : ℝ)^6383 := by
    have hnat : (5266974507 : ℕ)^8431*100000000000000^6383 ≤ 42876912231949^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266974507 10000000000 42876912231949 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1092456219/5000000000 : ℝ)^8431 ≤ (1676486132299/12500000000000 : ℝ)^6383 := by
    have hnat : (1092456219 : ℕ)^8431*12500000000000^6383 ≤ 1676486132299^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092456219 5000000000 1676486132299 12500000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344381341/10000000000 : ℝ), (5266974507/10000000000 : ℝ), (-1092456219/5000000000 : ℝ)] ![(5463899837523/12500000000000 : ℝ), (42876912231949/100000000000000 : ℝ), (1676486132299/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344381341/10000000000 : ℝ)|^8431 ≤ (5463899837523/12500000000000 : ℝ)^6383
        have hw : |(5344381341/10000000000 : ℝ)|=(5344381341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266974507/10000000000 : ℝ)|^8431 ≤ (42876912231949/100000000000000 : ℝ)^6383
        have hw : |(5266974507/10000000000 : ℝ)|=(5266974507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1092456219/5000000000 : ℝ)|^8431 ≤ (1676486132299/12500000000000 : ℝ)^6383
        have hw : |(-1092456219/5000000000 : ℝ)|=(1092456219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s6_3 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (870262403/2000000000 : ℝ)*x 0 + (4226914349/10000000000 : ℝ)*x 1 + (2239635519/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (870262403/2000000000 : ℝ)^8431 ≤ (2082335603227/6250000000000 : ℝ)^6383 := by
    have hnat : (870262403 : ℕ)^8431*6250000000000^6383 ≤ 2082335603227^6383*2000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870262403 2000000000 2082335603227 6250000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4226914349/10000000000 : ℝ)^8431 ≤ (6413014471567/20000000000000 : ℝ)^6383 := by
    have hnat : (4226914349 : ℕ)^8431*20000000000000^6383 ≤ 6413014471567^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4226914349 10000000000 6413014471567 20000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2239635519/5000000000 : ℝ)^8431 ≤ (1730877898971/5000000000000 : ℝ)^6383 := by
    have hnat : (2239635519 : ℕ)^8431*5000000000000^6383 ≤ 1730877898971^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2239635519 5000000000 1730877898971 5000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(870262403/2000000000 : ℝ), (4226914349/10000000000 : ℝ), (2239635519/5000000000 : ℝ)] ![(2082335603227/6250000000000 : ℝ), (6413014471567/20000000000000 : ℝ), (1730877898971/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(870262403/2000000000 : ℝ)|^8431 ≤ (2082335603227/6250000000000 : ℝ)^6383
        have hw : |(870262403/2000000000 : ℝ)|=(870262403/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4226914349/10000000000 : ℝ)|^8431 ≤ (6413014471567/20000000000000 : ℝ)^6383
        have hw : |(4226914349/10000000000 : ℝ)|=(4226914349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2239635519/5000000000 : ℝ)|^8431 ≤ (1730877898971/5000000000000 : ℝ)^6383
        have hw : |(2239635519/5000000000 : ℝ)|=(2239635519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s6_4 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-106089507/500000000 : ℝ)*x 0 + (5267288927/10000000000 : ℝ)*x 1 + (5391156189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106089507/500000000 : ℝ)^8431 ≤ (12902485401131/100000000000000 : ℝ)^6383 := by
    have hnat : (106089507 : ℕ)^8431*100000000000000^6383 ≤ 12902485401131^6383*500000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106089507 500000000 12902485401131 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267288927/10000000000 : ℝ)^8431 ≤ (5360036640061/12500000000000 : ℝ)^6383 := by
    have hnat : (5267288927 : ℕ)^8431*12500000000000^6383 ≤ 5360036640061^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267288927 10000000000 5360036640061 12500000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391156189/10000000000 : ℝ)^8431 ≤ (44217221469421/100000000000000 : ℝ)^6383 := by
    have hnat : (5391156189 : ℕ)^8431*100000000000000^6383 ≤ 44217221469421^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391156189 10000000000 44217221469421 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-106089507/500000000 : ℝ), (5267288927/10000000000 : ℝ), (5391156189/10000000000 : ℝ)] ![(12902485401131/100000000000000 : ℝ), (5360036640061/12500000000000 : ℝ), (44217221469421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-106089507/500000000 : ℝ)|^8431 ≤ (12902485401131/100000000000000 : ℝ)^6383
        have hw : |(-106089507/500000000 : ℝ)|=(106089507/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267288927/10000000000 : ℝ)|^8431 ≤ (5360036640061/12500000000000 : ℝ)^6383
        have hw : |(5267288927/10000000000 : ℝ)|=(5267288927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391156189/10000000000 : ℝ)|^8431 ≤ (44217221469421/100000000000000 : ℝ)^6383
        have hw : |(5391156189/10000000000 : ℝ)|=(5391156189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s6_5 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312624111/10000000000 : ℝ)*x 0 + (-2060731553/10000000000 : ℝ)*x 1 + (5391155229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312624111/10000000000 : ℝ)^8431 ≤ (43368448769017/100000000000000 : ℝ)^6383 := by
    have hnat : (5312624111 : ℕ)^8431*100000000000000^6383 ≤ 43368448769017^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312624111 10000000000 43368448769017 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2060731553/10000000000 : ℝ)^8431 ≤ (12414340151171/100000000000000 : ℝ)^6383 := by
    have hnat : (2060731553 : ℕ)^8431*100000000000000^6383 ≤ 12414340151171^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2060731553 10000000000 12414340151171 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391155229/10000000000 : ℝ)^8431 ≤ (44217211069381/100000000000000 : ℝ)^6383 := by
    have hnat : (5391155229 : ℕ)^8431*100000000000000^6383 ≤ 44217211069381^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391155229 10000000000 44217211069381 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312624111/10000000000 : ℝ), (-2060731553/10000000000 : ℝ), (5391155229/10000000000 : ℝ)] ![(43368448769017/100000000000000 : ℝ), (12414340151171/100000000000000 : ℝ), (44217211069381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312624111/10000000000 : ℝ)|^8431 ≤ (43368448769017/100000000000000 : ℝ)^6383
        have hw : |(5312624111/10000000000 : ℝ)|=(5312624111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2060731553/10000000000 : ℝ)|^8431 ≤ (12414340151171/100000000000000 : ℝ)^6383
        have hw : |(-2060731553/10000000000 : ℝ)|=(2060731553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391155229/10000000000 : ℝ)|^8431 ≤ (44217211069381/100000000000000 : ℝ)^6383
        have hw : |(5391155229/10000000000 : ℝ)|=(5391155229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s6_6 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062524727/2000000000 : ℝ)*x 0 + (539115589/1000000000 : ℝ)*x 1 + (-2060731297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062524727/2000000000 : ℝ)^8431 ≤ (5421055454569/12500000000000 : ℝ)^6383 := by
    have hnat : (1062524727 : ℕ)^8431*12500000000000^6383 ≤ 5421055454569^6383*2000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062524727 2000000000 5421055454569 12500000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539115589/1000000000 : ℝ)^8431 ≤ (22108609115121/50000000000000 : ℝ)^6383 := by
    have hnat : (539115589 : ℕ)^8431*50000000000000^6383 ≤ 22108609115121^6383*1000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539115589 1000000000 22108609115121 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2060731297/10000000000 : ℝ)^8431 ≤ (6207169057073/50000000000000 : ℝ)^6383 := by
    have hnat : (2060731297 : ℕ)^8431*50000000000000^6383 ≤ 6207169057073^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2060731297 10000000000 6207169057073 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062524727/2000000000 : ℝ), (539115589/1000000000 : ℝ), (-2060731297/10000000000 : ℝ)] ![(5421055454569/12500000000000 : ℝ), (22108609115121/50000000000000 : ℝ), (6207169057073/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062524727/2000000000 : ℝ)|^8431 ≤ (5421055454569/12500000000000 : ℝ)^6383
        have hw : |(1062524727/2000000000 : ℝ)|=(1062524727/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539115589/1000000000 : ℝ)|^8431 ≤ (22108609115121/50000000000000 : ℝ)^6383
        have hw : |(539115589/1000000000 : ℝ)|=(539115589/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2060731297/10000000000 : ℝ)|^8431 ≤ (6207169057073/50000000000000 : ℝ)^6383
        have hw : |(-2060731297/10000000000 : ℝ)|=(2060731297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s6_7 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1087830613/2500000000 : ℝ)*x 0 + (2239316363/5000000000 : ℝ)*x 1 + (2113777041/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087830613/2500000000 : ℝ)^8431 ≤ (16658737603531/50000000000000 : ℝ)^6383 := by
    have hnat : (1087830613 : ℕ)^8431*50000000000000^6383 ≤ 16658737603531^6383*2500000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087830613 2500000000 16658737603531 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2239316363/5000000000 : ℝ)^8431 ≤ (17305521099719/50000000000000 : ℝ)^6383 := by
    have hnat : (2239316363 : ℕ)^8431*50000000000000^6383 ≤ 17305521099719^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2239316363 5000000000 17305521099719 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2113777041/5000000000 : ℝ)^8431 ≤ (16035741284377/50000000000000 : ℝ)^6383 := by
    have hnat : (2113777041 : ℕ)^8431*50000000000000^6383 ≤ 16035741284377^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113777041 5000000000 16035741284377 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1087830613/2500000000 : ℝ), (2239316363/5000000000 : ℝ), (2113777041/5000000000 : ℝ)] ![(16658737603531/50000000000000 : ℝ), (17305521099719/50000000000000 : ℝ), (16035741284377/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1087830613/2500000000 : ℝ)|^8431 ≤ (16658737603531/50000000000000 : ℝ)^6383
        have hw : |(1087830613/2500000000 : ℝ)|=(1087830613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2239316363/5000000000 : ℝ)|^8431 ≤ (17305521099719/50000000000000 : ℝ)^6383
        have hw : |(2239316363/5000000000 : ℝ)|=(2239316363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2113777041/5000000000 : ℝ)|^8431 ≤ (16035741284377/50000000000000 : ℝ)^6383
        have hw : |(2113777041/5000000000 : ℝ)|=(2113777041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1238_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75675097/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14129/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11449/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11469/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14107/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14129/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11449/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14129/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11449/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14129/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11449/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14129/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11449/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14129/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11449/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14129/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11449/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11449/100000 : ℝ) ^ (4215/1024 : ℝ) ≤ (13356378465132421/100000000000000000000 : ℝ) := by
    have hpowers : (11449/100000 : ℝ)^4215 ≤ (13356378465132421/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11449 : ℕ)^4215*100000000000000000000^1024 ≤ 13356378465132421^1024*100000^4215 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11449 100000 13356378465132421 100000000000000000000 4215 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11449/100000 : ℝ)) (X := (13356378465132421/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14129/100000 : ℝ) ^ (4215/1024 : ℝ) ≤ (7936323480540729/25000000000000000000 : ℝ) := by
    have hpowers : (14129/100000 : ℝ)^4215 ≤ (7936323480540729/25000000000000000000 : ℝ)^1024 := by
      have hnat : (14129 : ℕ)^4215*25000000000000000000^1024 ≤ 7936323480540729^1024*100000^4215 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14129 100000 7936323480540729 25000000000000000000 4215 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14129/100000 : ℝ)) (X := (7936323480540729/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013356378465132421/50000000000000000000 : ℝ) ≤ (5000324449556683/5000000000000000 : ℝ) ^ (4215/1024 : ℝ) := by
    have hpowers : (50013356378465132421/50000000000000000000 : ℝ)^1024 ≤ (5000324449556683/5000000000000000 : ℝ)^4215 := by
      have hnat : (50013356378465132421 : ℕ)^1024*5000000000000000^4215 ≤ 5000324449556683^4215*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013356378465132421 50000000000000000000 5000324449556683 5000000000000000 1024 4215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000324449556683/5000000000000000 : ℝ)) (X := (50013356378465132421/50000000000000000000 : ℝ)) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045101672387295337/100000000000000000000 : ℝ) ≤ (312534235045907/312500000000000 : ℝ) ^ (4215/1024 : ℝ) := by
    have hpowers : (100045101672387295337/100000000000000000000 : ℝ)^1024 ≤ (312534235045907/312500000000000 : ℝ)^4215 := by
      have hnat : (100045101672387295337 : ℕ)^1024*312500000000000^4215 ≤ 312534235045907^4215*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045101672387295337 100000000000000000000 312534235045907 312500000000000 1024 4215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312534235045907/312500000000000 : ℝ)) (X := (100045101672387295337/100000000000000000000 : ℝ)) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507936323480540729/12500000000000000000 : ℝ) ≤ (5000771071912341/5000000000000000 : ℝ) ^ (4215/1024 : ℝ) := by
    have hpowers : (12507936323480540729/12500000000000000000 : ℝ)^1024 ≤ (5000771071912341/5000000000000000 : ℝ)^4215 := by
      have hnat : (12507936323480540729 : ℕ)^1024*5000000000000000^4215 ≤ 5000771071912341^4215*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507936323480540729 12500000000000000000 5000771071912341 5000000000000000 1024 4215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000771071912341/5000000000000000 : ℝ)) (X := (12507936323480540729/12500000000000000000 : ℝ)) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13356378465132421/100000000000000000000 : ℝ) ≤ ((6697878072730990999/6700000000000000000 : ℝ)+2*(223311177829/134000000000000 : ℝ)*(11449/100000 : ℝ))^(4215/1024 : ℝ) := by
    rw [show (6697878072730990999/6700000000000000000 : ℝ)+2*(223311177829/134000000000000 : ℝ)*(11449/100000 : ℝ)=(5000324449556683/5000000000000000 : ℝ) by norm_num, show 1+2*(13356378465132421/100000000000000000000 : ℝ)=(50013356378465132421/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7936323480540729/25000000000000000000 : ℝ)+(13356378465132421/100000000000000000000 : ℝ) ≤ ((6697878072730990999/6700000000000000000 : ℝ)+(223311177829/134000000000000 : ℝ)*((14129/100000 : ℝ)+(11449/100000 : ℝ)))^(4215/1024 : ℝ) := by
    rw [show (6697878072730990999/6700000000000000000 : ℝ)+(223311177829/134000000000000 : ℝ)*((14129/100000 : ℝ)+(11449/100000 : ℝ))=(312534235045907/312500000000000 : ℝ) by norm_num, show 1+(7936323480540729/25000000000000000000 : ℝ)+(13356378465132421/100000000000000000000 : ℝ)=(100045101672387295337/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7936323480540729/25000000000000000000 : ℝ) ≤ ((6697878072730990999/6700000000000000000 : ℝ)+2*(223311177829/134000000000000 : ℝ)*(14129/100000 : ℝ))^(4215/1024 : ℝ) := by
    rw [show (6697878072730990999/6700000000000000000 : ℝ)+2*(223311177829/134000000000000 : ℝ)*(14129/100000 : ℝ)=(5000771071912341/5000000000000000 : ℝ) by norm_num, show 1+2*(7936323480540729/25000000000000000000 : ℝ)=(12507936323480540729/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6697878072730990999/6700000000000000000 : ℝ)*(X 1 0+X 2 0)+(223311177829/134000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4215/1024 : ℝ)) (lo := (11449/100000 : ℝ)) (hi := (14129/100000 : ℝ)) (c := (6697878072730990999/6700000000000000000 : ℝ)) (alpha := (223311177829/134000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6697878072730990999/6700000000000000000 : ℝ)*(X 0 1+X 2 1)+(223311177829/134000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4215/1024 : ℝ)) (lo := (11449/100000 : ℝ)) (hi := (14129/100000 : ℝ)) (c := (6697878072730990999/6700000000000000000 : ℝ)) (alpha := (223311177829/134000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6697878072730990999/6700000000000000000 : ℝ)*(X 0 2+X 1 2)+(223311177829/134000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4215/1024 : ℝ)) (lo := (11449/100000 : ℝ)) (hi := (14129/100000 : ℝ)) (c := (6697878072730990999/6700000000000000000 : ℝ)) (alpha := (223311177829/134000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1060892667/5000000000 : ℝ)*X 0 0+(2695735953/5000000000 : ℝ)*X 0 1+(526697443/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344381477/10000000000 : ℝ)*X 1 0+(-2184912269/10000000000 : ℝ)*X 1 1+(2633487249/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344381341/10000000000 : ℝ)*X 2 0+(5266974507/10000000000 : ℝ)*X 2 1+(-1092456219/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((870262403/2000000000 : ℝ)*X 0 0+(4226914349/10000000000 : ℝ)*X 0 1+(2239635519/5000000000 : ℝ)*X 0 2+(870262403/2000000000 : ℝ)*X 1 0+(4226914349/10000000000 : ℝ)*X 1 1+(2239635519/5000000000 : ℝ)*X 1 2+(870262403/2000000000 : ℝ)*X 2 0+(4226914349/10000000000 : ℝ)*X 2 1+(2239635519/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-106089507/500000000 : ℝ)*X 0 0+(5267288927/10000000000 : ℝ)*X 0 1+(5391156189/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312624111/10000000000 : ℝ)*X 1 0+(-2060731553/10000000000 : ℝ)*X 1 1+(5391155229/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062524727/2000000000 : ℝ)*X 2 0+(539115589/1000000000 : ℝ)*X 2 1+(-2060731297/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1087830613/2500000000 : ℝ)*X 0 0+(2239316363/5000000000 : ℝ)*X 0 1+(2113777041/5000000000 : ℝ)*X 0 2+(1087830613/2500000000 : ℝ)*X 1 0+(2239316363/5000000000 : ℝ)*X 1 1+(2113777041/5000000000 : ℝ)*X 1 2+(1087830613/2500000000 : ℝ)*X 2 0+(2239316363/5000000000 : ℝ)*X 2 1+(2113777041/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3765733883740384965271914891/335000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (23279069/1250000000000 : ℝ)*(base19) + (1641507041/100000000000000 : ℝ)*(base23) + (14545559/100000000000000 : ℝ)*(lower2) + (6527813/2000000000000 : ℝ)*(upper3) + (2886231/50000000000000 : ℝ)*(lower4) + (5997553986244901/100000000000000 : ℝ)*(major0) + (5997553986244901/100000000000000 : ℝ)*(major1) + (5997553986244901/100000000000000 : ℝ)*(major2) + (4016179301296647/50000000000000 : ℝ)*(sp0) + (2008101458873183/25000000000000 : ℝ)*(sp1) + (8032406056311211/100000000000000 : ℝ)*(sp2) + (495333700957911/12500000000000 : ℝ)*(sp3) + (24547612479/50000000000000 : ℝ)*(sp4) + (6058461673/20000000000000 : ℝ)*(sp7) + (990674974992913/25000000000000 : ℝ)*(f.failure) + (2008101924454563/25000000000000 : ℝ)*(f.sum) + (54020472792871/6700000000000000000000000000 : ℝ)*base66 + (4557133085002903901/670000000000000000000000000000000 : ℝ)*base68 + (4400470619082903901/670000000000000000000000000000000 : ℝ)*base70 + (6207229541442903901/670000000000000000000000000000000 : ℝ)*base72 + (27452906579871/6700000000000000000000000000 : ℝ)*base74 + (10331251025262903901/670000000000000000000000000000000 : ℝ)*base76 + (3050584028732903901/670000000000000000000000000000000 : ℝ)*base78 + (12331048981492903901/670000000000000000000000000000000 : ℝ)*base80 + (33930887755271/6700000000000000000000000000 : ℝ)*base82 + (3087561/1250000000000000000000 : ℝ)*base89 + (3087561/1250000000000000000000 : ℝ)*base91 + (3087561/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (124547893780743741620052693/16750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2061143141/100000000000000 : ℝ)*(base19) + (550792821/50000000000000 : ℝ)*(base23) + (197742771/100000000000000 : ℝ)*(lower2) + (122327581/50000000000000 : ℝ)*(upper3) + (14449783/20000000000000 : ℝ)*(lower4) + (15128799/4000000000000 : ℝ)*(upper5) + (602799198530231/10000000000000 : ℝ)*(major0) + (602799198530231/10000000000000 : ℝ)*(major1) + (602799198530231/10000000000000 : ℝ)*(major2) + (1403806757/25000000000000 : ℝ)*(sp0) + (4036583616479657/50000000000000 : ℝ)*(sp4) + (4036585393521601/50000000000000 : ℝ)*(sp5) + (8073171746600701/100000000000000 : ℝ)*(sp6) + (497851359320219/12500000000000 : ℝ)*(sp7) + (497851359320219/12500000000000 : ℝ)*(f.failure) + (8073172848186343/100000000000000 : ℝ)*(f.sum) + (4418919228141/670000000000000000000000000 : ℝ)*base66 + (1559155561649340769/67000000000000000000000000000000 : ℝ)*base67 + (1195943693965340769/67000000000000000000000000000000 : ℝ)*base69 + (648551062473340769/67000000000000000000000000000000 : ℝ)*base71 + (4358979473679/670000000000000000000000000 : ℝ)*base73 + (637564697541340769/67000000000000000000000000000000 : ℝ)*base75 + (1070897306702340769/67000000000000000000000000000000 : ℝ)*base77 + (807732497098659231/67000000000000000000000000000000 : ℝ)*base80 + (2190665695609/670000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (10613757/625000000000000000000 : ℝ)*base90 + (10613757/625000000000000000000 : ℝ)*base92 + (10613757/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1238_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75675097/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14129/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11449/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11469/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14107/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1238_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1238_s7_0 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2121805447/10000000000 : ℝ)*x 0 + (336954511/625000000 : ℝ)*x 1 + (5267160637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2121805447/10000000000 : ℝ)^8431 ≤ (20160325543/156250000000 : ℝ)^6383 := by
    have hnat : (2121805447 : ℕ)^8431*156250000000^6383 ≤ 20160325543^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121805447 10000000000 20160325543 156250000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (336954511/625000000 : ℝ)^8431 ≤ (44218478004433/100000000000000 : ℝ)^6383 := by
    have hnat : (336954511 : ℕ)^8431*100000000000000^6383 ≤ 44218478004433^6383*625000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336954511 625000000 44218478004433 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267160637/10000000000 : ℝ)^8431 ≤ (8575782727749/20000000000000 : ℝ)^6383 := by
    have hnat : (5267160637 : ℕ)^8431*20000000000000^6383 ≤ 8575782727749^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267160637 10000000000 8575782727749 20000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2121805447/10000000000 : ℝ), (336954511/625000000 : ℝ), (5267160637/10000000000 : ℝ)] ![(20160325543/156250000000 : ℝ), (44218478004433/100000000000000 : ℝ), (8575782727749/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2121805447/10000000000 : ℝ)|^8431 ≤ (20160325543/156250000000 : ℝ)^6383
        have hw : |(-2121805447/10000000000 : ℝ)|=(2121805447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(336954511/625000000 : ℝ)|^8431 ≤ (44218478004433/100000000000000 : ℝ)^6383
        have hw : |(336954511/625000000 : ℝ)|=(336954511/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267160637/10000000000 : ℝ)|^8431 ≤ (8575782727749/20000000000000 : ℝ)^6383
        have hw : |(5267160637/10000000000 : ℝ)|=(5267160637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s7_1 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668041241/1250000000 : ℝ)*x 0 + (-546183521/2500000000 : ℝ)*x 1 + (1316790161/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668041241/1250000000 : ℝ)^8431 ≤ (43710643279821/100000000000000 : ℝ)^6383 := by
    have hnat : (668041241 : ℕ)^8431*100000000000000^6383 ≤ 43710643279821^6383*1250000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668041241 1250000000 43710643279821 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (546183521/2500000000 : ℝ)^8431 ≤ (13410442995017/100000000000000 : ℝ)^6383 := by
    have hnat : (546183521 : ℕ)^8431*100000000000000^6383 ≤ 13410442995017^6383*2500000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546183521 2500000000 13410442995017 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316790161/2500000000 : ℝ)^8431 ≤ (8575782742803/20000000000000 : ℝ)^6383 := by
    have hnat : (1316790161 : ℕ)^8431*20000000000000^6383 ≤ 8575782742803^6383*2500000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316790161 2500000000 8575782742803 20000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668041241/1250000000 : ℝ), (-546183521/2500000000 : ℝ), (1316790161/2500000000 : ℝ)] ![(43710643279821/100000000000000 : ℝ), (13410442995017/100000000000000 : ℝ), (8575782742803/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668041241/1250000000 : ℝ)|^8431 ≤ (43710643279821/100000000000000 : ℝ)^6383
        have hw : |(668041241/1250000000 : ℝ)|=(668041241/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-546183521/2500000000 : ℝ)|^8431 ≤ (13410442995017/100000000000000 : ℝ)^6383
        have hw : |(-546183521/2500000000 : ℝ)|=(546183521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316790161/2500000000 : ℝ)|^8431 ≤ (8575782742803/20000000000000 : ℝ)^6383
        have hw : |(1316790161/2500000000 : ℝ)|=(1316790161/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s7_2 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336082483/2500000000 : ℝ)*x 0 + (1316790161/2500000000 : ℝ)*x 1 + (-1092367039/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336082483/2500000000 : ℝ)^8431 ≤ (43710643323033/100000000000000 : ℝ)^6383 := by
    have hnat : (1336082483 : ℕ)^8431*100000000000000^6383 ≤ 43710643323033^6383*2500000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336082483 2500000000 43710643323033 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316790161/2500000000 : ℝ)^8431 ≤ (8575782742803/20000000000000 : ℝ)^6383 := by
    have hnat : (1316790161 : ℕ)^8431*20000000000000^6383 ≤ 8575782742803^6383*2500000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316790161 2500000000 8575782742803 20000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1092367039/5000000000 : ℝ)^8431 ≤ (13410442946371/100000000000000 : ℝ)^6383 := by
    have hnat : (1092367039 : ℕ)^8431*100000000000000^6383 ≤ 13410442946371^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092367039 5000000000 13410442946371 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336082483/2500000000 : ℝ), (1316790161/2500000000 : ℝ), (-1092367039/5000000000 : ℝ)] ![(43710643323033/100000000000000 : ℝ), (8575782742803/20000000000000 : ℝ), (13410442946371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336082483/2500000000 : ℝ)|^8431 ≤ (43710643323033/100000000000000 : ℝ)^6383
        have hw : |(1336082483/2500000000 : ℝ)|=(1336082483/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316790161/2500000000 : ℝ)|^8431 ≤ (8575782742803/20000000000000 : ℝ)^6383
        have hw : |(1316790161/2500000000 : ℝ)|=(1316790161/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1092367039/5000000000 : ℝ)|^8431 ≤ (13410442946371/100000000000000 : ℝ)^6383
        have hw : |(-1092367039/5000000000 : ℝ)|=(1092367039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s7_3 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2175661007/5000000000 : ℝ)*x 0 + (33025813/78125000 : ℝ)*x 1 + (4478878589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175661007/5000000000 : ℝ)^8431 ≤ (1041170961791/3125000000000 : ℝ)^6383 := by
    have hnat : (2175661007 : ℕ)^8431*3125000000000^6383 ≤ 1041170961791^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175661007 5000000000 1041170961791 3125000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33025813/78125000 : ℝ)^8431 ≤ (32068977317631/100000000000000 : ℝ)^6383 := by
    have hnat : (33025813 : ℕ)^8431*100000000000000^6383 ≤ 32068977317631^6383*78125000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33025813 78125000 32068977317631 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4478878589/10000000000 : ℝ)^8431 ≤ (135209187077/390625000000 : ℝ)^6383 := by
    have hnat : (4478878589 : ℕ)^8431*390625000000^6383 ≤ 135209187077^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4478878589 10000000000 135209187077 390625000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2175661007/5000000000 : ℝ), (33025813/78125000 : ℝ), (4478878589/10000000000 : ℝ)] ![(1041170961791/3125000000000 : ℝ), (32068977317631/100000000000000 : ℝ), (135209187077/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2175661007/5000000000 : ℝ)|^8431 ≤ (1041170961791/3125000000000 : ℝ)^6383
        have hw : |(2175661007/5000000000 : ℝ)|=(2175661007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(33025813/78125000 : ℝ)|^8431 ≤ (32068977317631/100000000000000 : ℝ)^6383
        have hw : |(33025813/78125000 : ℝ)|=(33025813/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4478878589/10000000000 : ℝ)|^8431 ≤ (135209187077/390625000000 : ℝ)^6383
        have hw : |(4478878589/10000000000 : ℝ)|=(4478878589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s7_4 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-424362013/2000000000 : ℝ)*x 0 + (1053495049/2000000000 : ℝ)*x 1 + (16846739/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (424362013/2000000000 : ℝ)^8431 ≤ (6451322719761/50000000000000 : ℝ)^6383 := by
    have hnat : (424362013 : ℕ)^8431*50000000000000^6383 ≤ 6451322719761^6383*2000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424362013 2000000000 6451322719761 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053495049/2000000000 : ℝ)^8431 ≤ (21441148293591/50000000000000 : ℝ)^6383 := by
    have hnat : (1053495049 : ℕ)^8431*50000000000000^6383 ≤ 21441148293591^6383*2000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053495049 2000000000 21441148293591 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16846739/31250000 : ℝ)^8431 ≤ (1381720561243/3125000000000 : ℝ)^6383 := by
    have hnat : (16846739 : ℕ)^8431*3125000000000^6383 ≤ 1381720561243^6383*31250000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16846739 31250000 1381720561243 3125000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-424362013/2000000000 : ℝ), (1053495049/2000000000 : ℝ), (16846739/31250000 : ℝ)] ![(6451322719761/50000000000000 : ℝ), (21441148293591/50000000000000 : ℝ), (1381720561243/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-424362013/2000000000 : ℝ)|^8431 ≤ (6451322719761/50000000000000 : ℝ)^6383
        have hw : |(-424362013/2000000000 : ℝ)|=(424362013/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053495049/2000000000 : ℝ)|^8431 ≤ (21441148293591/50000000000000 : ℝ)^6383
        have hw : |(1053495049/2000000000 : ℝ)|=(1053495049/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(16846739/31250000 : ℝ)|^8431 ≤ (1381720561243/3125000000000 : ℝ)^6383
        have hw : |(16846739/31250000 : ℝ)|=(16846739/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s7_5 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328167573/2500000000 : ℝ)*x 0 + (-2060936157/10000000000 : ℝ)*x 1 + (269547949/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328167573/2500000000 : ℝ)^8431 ≤ (43368946715859/100000000000000 : ℝ)^6383 := by
    have hnat : (1328167573 : ℕ)^8431*100000000000000^6383 ≤ 43368946715859^6383*2500000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328167573 2500000000 43368946715859 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2060936157/10000000000 : ℝ)^8431 ≤ (3103992059443/25000000000000 : ℝ)^6383 := by
    have hnat : (2060936157 : ℕ)^8431*25000000000000^6383 ≤ 3103992059443^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2060936157 10000000000 3103992059443 25000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269547949/500000000 : ℝ)^8431 ≤ (22107542521447/50000000000000 : ℝ)^6383 := by
    have hnat : (269547949 : ℕ)^8431*50000000000000^6383 ≤ 22107542521447^6383*500000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269547949 500000000 22107542521447 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328167573/2500000000 : ℝ), (-2060936157/10000000000 : ℝ), (269547949/500000000 : ℝ)] ![(43368946715859/100000000000000 : ℝ), (3103992059443/25000000000000 : ℝ), (22107542521447/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328167573/2500000000 : ℝ)|^8431 ≤ (43368946715859/100000000000000 : ℝ)^6383
        have hw : |(1328167573/2500000000 : ℝ)|=(1328167573/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2060936157/10000000000 : ℝ)|^8431 ≤ (3103992059443/25000000000000 : ℝ)^6383
        have hw : |(-2060936157/10000000000 : ℝ)|=(2060936157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269547949/500000000 : ℝ)|^8431 ≤ (22107542521447/50000000000000 : ℝ)^6383
        have hw : |(269547949/500000000 : ℝ)|=(269547949/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s7_6 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312670913/10000000000 : ℝ)*x 0 + (5390957413/10000000000 : ℝ)*x 1 + (-257617181/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312670913/10000000000 : ℝ)^8431 ≤ (10842238352951/25000000000000 : ℝ)^6383 := by
    have hnat : (5312670913 : ℕ)^8431*25000000000000^6383 ≤ 10842238352951^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312670913 10000000000 10842238352951 25000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390957413/10000000000 : ℝ)^8431 ≤ (8843013613439/20000000000000 : ℝ)^6383 := by
    have hnat : (5390957413 : ℕ)^8431*20000000000000^6383 ≤ 8843013613439^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390957413 10000000000 8843013613439 20000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (257617181/1250000000 : ℝ)^8431 ≤ (2483195702151/20000000000000 : ℝ)^6383 := by
    have hnat : (257617181 : ℕ)^8431*20000000000000^6383 ≤ 2483195702151^6383*1250000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257617181 1250000000 2483195702151 20000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312670913/10000000000 : ℝ), (5390957413/10000000000 : ℝ), (-257617181/1250000000 : ℝ)] ![(10842238352951/25000000000000 : ℝ), (8843013613439/20000000000000 : ℝ), (2483195702151/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312670913/10000000000 : ℝ)|^8431 ≤ (10842238352951/25000000000000 : ℝ)^6383
        have hw : |(5312670913/10000000000 : ℝ)|=(5312670913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390957413/10000000000 : ℝ)|^8431 ≤ (8843013613439/20000000000000 : ℝ)^6383
        have hw : |(5390957413/10000000000 : ℝ)|=(5390957413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-257617181/1250000000 : ℝ)|^8431 ≤ (2483195702151/20000000000000 : ℝ)^6383
        have hw : |(-257617181/1250000000 : ℝ)|=(257617181/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s7_7 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4351331521/10000000000 : ℝ)*x 0 + (2239122653/5000000000 : ℝ)*x 1 + (4227939577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4351331521/10000000000 : ℝ)^8431 ≤ (1665878346359/5000000000000 : ℝ)^6383 := by
    have hnat : (4351331521 : ℕ)^8431*5000000000000^6383 ≤ 1665878346359^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4351331521 10000000000 1665878346359 5000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2239122653/5000000000 : ℝ)^8431 ≤ (17303543813741/50000000000000 : ℝ)^6383 := by
    have hnat : (2239122653 : ℕ)^8431*50000000000000^6383 ≤ 17303543813741^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2239122653 5000000000 17303543813741 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4227939577/10000000000 : ℝ)^8431 ≤ (16037672715459/50000000000000 : ℝ)^6383 := by
    have hnat : (4227939577 : ℕ)^8431*50000000000000^6383 ≤ 16037672715459^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227939577 10000000000 16037672715459 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4351331521/10000000000 : ℝ), (2239122653/5000000000 : ℝ), (4227939577/10000000000 : ℝ)] ![(1665878346359/5000000000000 : ℝ), (17303543813741/50000000000000 : ℝ), (16037672715459/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4351331521/10000000000 : ℝ)|^8431 ≤ (1665878346359/5000000000000 : ℝ)^6383
        have hw : |(4351331521/10000000000 : ℝ)|=(4351331521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2239122653/5000000000 : ℝ)|^8431 ≤ (17303543813741/50000000000000 : ℝ)^6383
        have hw : |(2239122653/5000000000 : ℝ)|=(2239122653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4227939577/10000000000 : ℝ)|^8431 ≤ (16037672715459/50000000000000 : ℝ)^6383
        have hw : |(4227939577/10000000000 : ℝ)|=(4227939577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1238_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75675097/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14107/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11469/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11473/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14103/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14107/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11469/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14107/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11469/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14107/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11469/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14107/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11469/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14107/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11469/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14107/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11469/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11469/100000 : ℝ) ^ (4215/1024 : ℝ) ≤ (6726339721599633/50000000000000000000 : ℝ) := by
    have hpowers : (11469/100000 : ℝ)^4215 ≤ (6726339721599633/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11469 : ℕ)^4215*50000000000000000000^1024 ≤ 6726339721599633^1024*100000^4215 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11469 100000 6726339721599633 50000000000000000000 4215 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11469/100000 : ℝ)) (X := (6726339721599633/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14107/100000 : ℝ) ^ (4215/1024 : ℝ) ≤ (3942790337342249/12500000000000000000 : ℝ) := by
    have hpowers : (14107/100000 : ℝ)^4215 ≤ (3942790337342249/12500000000000000000 : ℝ)^1024 := by
      have hnat : (14107 : ℕ)^4215*12500000000000000000^1024 ≤ 3942790337342249^1024*100000^4215 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14107 100000 3942790337342249 12500000000000000000 4215 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14107/100000 : ℝ)) (X := (3942790337342249/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006726339721599633/25000000000000000000 : ℝ) ≤ (5000326788635969/5000000000000000 : ℝ) ^ (4215/1024 : ℝ) := by
    have hpowers : (25006726339721599633/25000000000000000000 : ℝ)^1024 ≤ (5000326788635969/5000000000000000 : ℝ)^4215 := by
      have hnat : (25006726339721599633 : ℕ)^1024*5000000000000000^4215 ≤ 5000326788635969^4215*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006726339721599633 25000000000000000000 5000326788635969 5000000000000000 1024 4215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000326788635969/5000000000000000 : ℝ)) (X := (25006726339721599633/25000000000000000000 : ℝ)) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022497501070968629/50000000000000000000 : ℝ) ≤ (500054646544277/500000000000000 : ℝ) ^ (4215/1024 : ℝ) := by
    have hpowers : (50022497501070968629/50000000000000000000 : ℝ)^1024 ≤ (500054646544277/500000000000000 : ℝ)^4215 := by
      have hnat : (50022497501070968629 : ℕ)^1024*500000000000000^4215 ≤ 500054646544277^4215*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022497501070968629 50000000000000000000 500054646544277 500000000000000 1024 4215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500054646544277/500000000000000 : ℝ)) (X := (50022497501070968629/50000000000000000000 : ℝ)) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253942790337342249/6250000000000000000 : ℝ) ≤ (5000766142249571/5000000000000000 : ℝ) ^ (4215/1024 : ℝ) := by
    have hpowers : (6253942790337342249/6250000000000000000 : ℝ)^1024 ≤ (5000766142249571/5000000000000000 : ℝ)^4215 := by
      have hnat : (6253942790337342249 : ℕ)^1024*5000000000000000^4215 ≤ 5000766142249571^4215*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253942790337342249 6250000000000000000 5000766142249571 5000000000000000 1024 4215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000766142249571/5000000000000000 : ℝ)) (X := (6253942790337342249/6250000000000000000 : ℝ)) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6726339721599633/50000000000000000000 : ℝ) ≤ ((3296455780456821221/3297500000000000000 : ℝ)+2*(219676806801/131900000000000 : ℝ)*(11469/100000 : ℝ))^(4215/1024 : ℝ) := by
    rw [show (3296455780456821221/3297500000000000000 : ℝ)+2*(219676806801/131900000000000 : ℝ)*(11469/100000 : ℝ)=(5000326788635969/5000000000000000 : ℝ) by norm_num, show 1+2*(6726339721599633/50000000000000000000 : ℝ)=(25006726339721599633/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3942790337342249/12500000000000000000 : ℝ)+(6726339721599633/50000000000000000000 : ℝ) ≤ ((3296455780456821221/3297500000000000000 : ℝ)+(219676806801/131900000000000 : ℝ)*((14107/100000 : ℝ)+(11469/100000 : ℝ)))^(4215/1024 : ℝ) := by
    rw [show (3296455780456821221/3297500000000000000 : ℝ)+(219676806801/131900000000000 : ℝ)*((14107/100000 : ℝ)+(11469/100000 : ℝ))=(500054646544277/500000000000000 : ℝ) by norm_num, show 1+(3942790337342249/12500000000000000000 : ℝ)+(6726339721599633/50000000000000000000 : ℝ)=(50022497501070968629/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3942790337342249/12500000000000000000 : ℝ) ≤ ((3296455780456821221/3297500000000000000 : ℝ)+2*(219676806801/131900000000000 : ℝ)*(14107/100000 : ℝ))^(4215/1024 : ℝ) := by
    rw [show (3296455780456821221/3297500000000000000 : ℝ)+2*(219676806801/131900000000000 : ℝ)*(14107/100000 : ℝ)=(5000766142249571/5000000000000000 : ℝ) by norm_num, show 1+2*(3942790337342249/12500000000000000000 : ℝ)=(6253942790337342249/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3296455780456821221/3297500000000000000 : ℝ)*(X 1 0+X 2 0)+(219676806801/131900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4215/1024 : ℝ)) (lo := (11469/100000 : ℝ)) (hi := (14107/100000 : ℝ)) (c := (3296455780456821221/3297500000000000000 : ℝ)) (alpha := (219676806801/131900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3296455780456821221/3297500000000000000 : ℝ)*(X 0 1+X 2 1)+(219676806801/131900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4215/1024 : ℝ)) (lo := (11469/100000 : ℝ)) (hi := (14107/100000 : ℝ)) (c := (3296455780456821221/3297500000000000000 : ℝ)) (alpha := (219676806801/131900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3296455780456821221/3297500000000000000 : ℝ)*(X 0 2+X 1 2)+(219676806801/131900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4215/1024 : ℝ)) (lo := (11469/100000 : ℝ)) (hi := (14107/100000 : ℝ)) (c := (3296455780456821221/3297500000000000000 : ℝ)) (alpha := (219676806801/131900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2121805447/10000000000 : ℝ)*X 0 0+(336954511/625000000 : ℝ)*X 0 1+(5267160637/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668041241/1250000000 : ℝ)*X 1 0+(-546183521/2500000000 : ℝ)*X 1 1+(1316790161/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336082483/2500000000 : ℝ)*X 2 0+(1316790161/2500000000 : ℝ)*X 2 1+(-1092367039/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2175661007/5000000000 : ℝ)*X 0 0+(33025813/78125000 : ℝ)*X 0 1+(4478878589/10000000000 : ℝ)*X 0 2+(2175661007/5000000000 : ℝ)*X 1 0+(33025813/78125000 : ℝ)*X 1 1+(4478878589/10000000000 : ℝ)*X 1 2+(2175661007/5000000000 : ℝ)*X 2 0+(33025813/78125000 : ℝ)*X 2 1+(4478878589/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-424362013/2000000000 : ℝ)*X 0 0+(1053495049/2000000000 : ℝ)*X 0 1+(16846739/31250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328167573/2500000000 : ℝ)*X 1 0+(-2060936157/10000000000 : ℝ)*X 1 1+(269547949/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312670913/10000000000 : ℝ)*X 2 0+(5390957413/10000000000 : ℝ)*X 2 1+(-257617181/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4351331521/10000000000 : ℝ)*X 0 0+(2239122653/5000000000 : ℝ)*X 0 1+(4227939577/10000000000 : ℝ)*X 0 2+(4351331521/10000000000 : ℝ)*X 1 0+(2239122653/5000000000 : ℝ)*X 1 1+(4227939577/10000000000 : ℝ)*X 1 2+(4351331521/10000000000 : ℝ)*X 2 0+(2239122653/5000000000 : ℝ)*X 2 1+(4227939577/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (839383900139654728602604959/82437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (39403443/2000000000000 : ℝ)*(base19) + (1843459287/100000000000000 : ℝ)*(base23) + (70942487/100000000000000 : ℝ)*(lower2) + (10048387/4000000000000 : ℝ)*(upper3) + (164259941/100000000000000 : ℝ)*(upper5) + (6016201070873693/100000000000000 : ℝ)*(major0) + (6016201070873693/100000000000000 : ℝ)*(major1) + (6016201070873693/100000000000000 : ℝ)*(major2) + (8057325927953237/100000000000000 : ℝ)*(sp0) + (2014344860697033/25000000000000 : ℝ)*(sp1) + (1611475913900199/20000000000000 : ℝ)*(sp2) + (397499148342097/10000000000000 : ℝ)*(sp3) + (27742503523/50000000000000 : ℝ)*(sp4) + (2890596399/10000000000000 : ℝ)*(sp7) + (3105484679207/78125000000 : ℝ)*(f.failure) + (4028690706480141/50000000000000 : ℝ)*(f.sum) + (9867415043849/3297500000000000000000000000 : ℝ)*base65 + (3605371622284135847/329750000000000000000000000000000 : ℝ)*base68 + (1300838104942385847/329750000000000000000000000000000 : ℝ)*base70 + (2191408193938135847/329750000000000000000000000000000 : ℝ)*base72 + (19925518055447/6595000000000000000000000000 : ℝ)*base74 + (4265939745327364153/329750000000000000000000000000000 : ℝ)*base75 + (302424715497135847/329750000000000000000000000000000 : ℝ)*base78 + (7845966777924635847/329750000000000000000000000000000 : ℝ)*base80 + (21769562295843/6595000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (49467/7812500000000000000 : ℝ)*base90 + (49467/7812500000000000000 : ℝ)*base92 + (49467/7812500000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (935527658721413698646768127/82437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (379315869/50000000000000 : ℝ)*(base19) + (8179131/500000000000 : ℝ)*(base23) + (221698037/50000000000000 : ℝ)*(upper3) + (68788051/50000000000000 : ℝ)*(lower4) + (3023405015758829/50000000000000 : ℝ)*(major0) + (3023405015758829/50000000000000 : ℝ)*(major1) + (3023405015758829/50000000000000 : ℝ)*(major2) + (77983852947/50000000000000 : ℝ)*(sp1) + (25216152811/25000000000000 : ℝ)*(sp2) + (59643449907/100000000000000 : ℝ)*(sp3) + (809837536315639/10000000000000 : ℝ)*(sp4) + (4049109318409379/50000000000000 : ℝ)*(sp5) + (4049136431359473/50000000000000 : ℝ)*(sp6) + (1997592339075731/50000000000000 : ℝ)*(sp7) + (399524432160137/10000000000000 : ℝ)*(f.failure) + (809837536315639/10000000000000 : ℝ)*(f.sum) + (4583793166827/1648750000000000000000000000 : ℝ)*base65 + (2174039849522714791/164875000000000000000000000000000 : ℝ)*base68 + (273128050400660209/164875000000000000000000000000000 : ℝ)*base69 + (1444054863392964791/164875000000000000000000000000000 : ℝ)*base72 + (2955176946231/824375000000000000000000000 : ℝ)*base73 + (1044598352217339791/164875000000000000000000000000000 : ℝ)*base76 + (378968981145714791/164875000000000000000000000000000 : ℝ)*base78 + (1017550668902785209/164875000000000000000000000000000 : ℝ)*base79 + (27105408725643/6595000000000000000000000000 : ℝ)*base81 + (2991711/500000000000000000000 : ℝ)*base90 + (2991711/500000000000000000000 : ℝ)*base92 + (2991711/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1238_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75675097/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14107/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11469/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11473/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14103/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1238_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1238_s8_0 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2121808097/10000000000 : ℝ)*x 0 + (1078246991/2000000000 : ℝ)*x 1 + (1316799039/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2121808097/10000000000 : ℝ)^8431 ≤ (12902629632447/100000000000000 : ℝ)^6383 := by
    have hnat : (2121808097 : ℕ)^8431*100000000000000^6383 ≤ 12902629632447^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121808097 10000000000 12902629632447 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078246991/2000000000 : ℝ)^8431 ≤ (22109037386521/50000000000000 : ℝ)^6383 := by
    have hnat : (1078246991 : ℕ)^8431*50000000000000^6383 ≤ 22109037386521^6383*2000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078246991 2000000000 22109037386521 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316799039/2500000000 : ℝ)^8431 ≤ (21439647783881/50000000000000 : ℝ)^6383 := by
    have hnat : (1316799039 : ℕ)^8431*50000000000000^6383 ≤ 21439647783881^6383*2500000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316799039 2500000000 21439647783881 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2121808097/10000000000 : ℝ), (1078246991/2000000000 : ℝ), (1316799039/2500000000 : ℝ)] ![(12902629632447/100000000000000 : ℝ), (22109037386521/50000000000000 : ℝ), (21439647783881/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2121808097/10000000000 : ℝ)|^8431 ≤ (12902629632447/100000000000000 : ℝ)^6383
        have hw : |(-2121808097/10000000000 : ℝ)|=(2121808097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078246991/2000000000 : ℝ)|^8431 ≤ (22109037386521/50000000000000 : ℝ)^6383
        have hw : |(1078246991/2000000000 : ℝ)|=(1078246991/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316799039/2500000000 : ℝ)|^8431 ≤ (21439647783881/50000000000000 : ℝ)^6383
        have hw : |(1316799039/2500000000 : ℝ)|=(1316799039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s8_1 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344320647/10000000000 : ℝ)*x 0 + (-2184699347/10000000000 : ℝ)*x 1 + (4114997/7812500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344320647/10000000000 : ℝ)^8431 ≤ (43710543016327/100000000000000 : ℝ)^6383 := by
    have hnat : (5344320647 : ℕ)^8431*100000000000000^6383 ≤ 43710543016327^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344320647 10000000000 43710543016327 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2184699347/10000000000 : ℝ)^8431 ≤ (6705080678919/50000000000000 : ℝ)^6383 := by
    have hnat : (2184699347 : ℕ)^8431*50000000000000^6383 ≤ 6705080678919^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184699347 10000000000 6705080678919 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4114997/7812500 : ℝ)^8431 ≤ (21439647805387/50000000000000 : ℝ)^6383 := by
    have hnat : (4114997 : ℕ)^8431*50000000000000^6383 ≤ 21439647805387^6383*7812500^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4114997 7812500 21439647805387 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344320647/10000000000 : ℝ), (-2184699347/10000000000 : ℝ), (4114997/7812500 : ℝ)] ![(43710543016327/100000000000000 : ℝ), (6705080678919/50000000000000 : ℝ), (21439647805387/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344320647/10000000000 : ℝ)|^8431 ≤ (43710543016327/100000000000000 : ℝ)^6383
        have hw : |(5344320647/10000000000 : ℝ)|=(5344320647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2184699347/10000000000 : ℝ)|^8431 ≤ (6705080678919/50000000000000 : ℝ)^6383
        have hw : |(-2184699347/10000000000 : ℝ)|=(2184699347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4114997/7812500 : ℝ)|^8431 ≤ (21439647805387/50000000000000 : ℝ)^6383
        have hw : |(4114997/7812500 : ℝ)|=(4114997/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s8_2 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668040081/1250000000 : ℝ)*x 0 + (658399521/1250000000 : ℝ)*x 1 + (-273087417/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668040081/1250000000 : ℝ)^8431 ≤ (4371054302713/10000000000000 : ℝ)^6383 := by
    have hnat : (668040081 : ℕ)^8431*10000000000000^6383 ≤ 4371054302713^6383*1250000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668040081 1250000000 4371054302713 10000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658399521/1250000000 : ℝ)^8431 ≤ (10719823924199/25000000000000 : ℝ)^6383 := by
    have hnat : (658399521 : ℕ)^8431*25000000000000^6383 ≤ 10719823924199^6383*1250000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658399521 1250000000 10719823924199 25000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (273087417/1250000000 : ℝ)^8431 ≤ (6705080634327/50000000000000 : ℝ)^6383 := by
    have hnat : (273087417 : ℕ)^8431*50000000000000^6383 ≤ 6705080634327^6383*1250000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273087417 1250000000 6705080634327 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668040081/1250000000 : ℝ), (658399521/1250000000 : ℝ), (-273087417/1250000000 : ℝ)] ![(4371054302713/10000000000000 : ℝ), (10719823924199/25000000000000 : ℝ), (6705080634327/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668040081/1250000000 : ℝ)|^8431 ≤ (4371054302713/10000000000000 : ℝ)^6383
        have hw : |(668040081/1250000000 : ℝ)|=(668040081/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658399521/1250000000 : ℝ)|^8431 ≤ (10719823924199/25000000000000 : ℝ)^6383
        have hw : |(658399521/1250000000 : ℝ)|=(658399521/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-273087417/1250000000 : ℝ)|^8431 ≤ (6705080634327/50000000000000 : ℝ)^6383
        have hw : |(-273087417/1250000000 : ℝ)|=(273087417/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s8_3 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4351323857/10000000000 : ℝ)*x 0 + (845475507/2000000000 : ℝ)*x 1 + (2239402321/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4351323857/10000000000 : ℝ)^8431 ≤ (33317489416647/100000000000000 : ℝ)^6383 := by
    have hnat : (4351323857 : ℕ)^8431*100000000000000^6383 ≤ 33317489416647^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4351323857 10000000000 33317489416647 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (845475507/2000000000 : ℝ)^8431 ≤ (32069713512913/100000000000000 : ℝ)^6383 := by
    have hnat : (845475507 : ℕ)^8431*100000000000000^6383 ≤ 32069713512913^6383*2000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845475507 2000000000 32069713512913 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2239402321/5000000000 : ℝ)^8431 ≤ (8653199264829/25000000000000 : ℝ)^6383 := by
    have hnat : (2239402321 : ℕ)^8431*25000000000000^6383 ≤ 8653199264829^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2239402321 5000000000 8653199264829 25000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4351323857/10000000000 : ℝ), (845475507/2000000000 : ℝ), (2239402321/5000000000 : ℝ)] ![(33317489416647/100000000000000 : ℝ), (32069713512913/100000000000000 : ℝ), (8653199264829/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4351323857/10000000000 : ℝ)|^8431 ≤ (33317489416647/100000000000000 : ℝ)^6383
        have hw : |(4351323857/10000000000 : ℝ)|=(4351323857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(845475507/2000000000 : ℝ)|^8431 ≤ (32069713512913/100000000000000 : ℝ)^6383
        have hw : |(845475507/2000000000 : ℝ)|=(845475507/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2239402321/5000000000 : ℝ)|^8431 ≤ (8653199264829/25000000000000 : ℝ)^6383
        have hw : |(2239402321/5000000000 : ℝ)|=(2239402321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s8_4 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-424362481/2000000000 : ℝ)*x 0 + (1316877199/2500000000 : ℝ)*x 1 + (2695460721/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (424362481/2000000000 : ℝ)^8431 ≤ (12902664234527/100000000000000 : ℝ)^6383 := by
    have hnat : (424362481 : ℕ)^8431*100000000000000^6383 ≤ 12902664234527^6383*2000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424362481 2000000000 12902664234527 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316877199/2500000000 : ℝ)^8431 ≤ (10720664340391/25000000000000 : ℝ)^6383 := by
    have hnat : (1316877199 : ℕ)^8431*25000000000000^6383 ≤ 10720664340391^6383*2500000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316877199 2500000000 10720664340391 25000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695460721/5000000000 : ℝ)^8431 ≤ (44214678384887/100000000000000 : ℝ)^6383 := by
    have hnat : (2695460721 : ℕ)^8431*100000000000000^6383 ≤ 44214678384887^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695460721 5000000000 44214678384887 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-424362481/2000000000 : ℝ), (1316877199/2500000000 : ℝ), (2695460721/5000000000 : ℝ)] ![(12902664234527/100000000000000 : ℝ), (10720664340391/25000000000000 : ℝ), (44214678384887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-424362481/2000000000 : ℝ)|^8431 ≤ (12902664234527/100000000000000 : ℝ)^6383
        have hw : |(-424362481/2000000000 : ℝ)|=(424362481/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316877199/2500000000 : ℝ)|^8431 ≤ (10720664340391/25000000000000 : ℝ)^6383
        have hw : |(1316877199/2500000000 : ℝ)|=(1316877199/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695460721/5000000000 : ℝ)|^8431 ≤ (44214678384887/100000000000000 : ℝ)^6383
        have hw : |(2695460721/5000000000 : ℝ)|=(2695460721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s8_5 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656340017/5000000000 : ℝ)*x 0 + (-1030487097/5000000000 : ℝ)*x 1 + (5390921343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656340017/5000000000 : ℝ)^8431 ≤ (10842262939799/25000000000000 : ℝ)^6383 := by
    have hnat : (2656340017 : ℕ)^8431*25000000000000^6383 ≤ 10842262939799^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656340017 5000000000 10842262939799 25000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1030487097/5000000000 : ℝ)^8431 ≤ (1552033864209/12500000000000 : ℝ)^6383 := by
    have hnat : (1030487097 : ℕ)^8431*12500000000000^6383 ≤ 1552033864209^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030487097 5000000000 1552033864209 12500000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390921343/10000000000 : ℝ)^8431 ≤ (22107338656199/50000000000000 : ℝ)^6383 := by
    have hnat : (5390921343 : ℕ)^8431*50000000000000^6383 ≤ 22107338656199^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390921343 10000000000 22107338656199 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656340017/5000000000 : ℝ), (-1030487097/5000000000 : ℝ), (5390921343/10000000000 : ℝ)] ![(10842262939799/25000000000000 : ℝ), (1552033864209/12500000000000 : ℝ), (22107338656199/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656340017/5000000000 : ℝ)|^8431 ≤ (10842262939799/25000000000000 : ℝ)^6383
        have hw : |(2656340017/5000000000 : ℝ)|=(2656340017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1030487097/5000000000 : ℝ)|^8431 ≤ (1552033864209/12500000000000 : ℝ)^6383
        have hw : |(-1030487097/5000000000 : ℝ)|=(1030487097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390921343/10000000000 : ℝ)|^8431 ≤ (22107338656199/50000000000000 : ℝ)^6383
        have hw : |(5390921343/10000000000 : ℝ)|=(5390921343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s8_6 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (53126807/100000000 : ℝ)*x 0 + (1078184157/2000000000 : ℝ)*x 1 + (-2060974051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53126807/100000000 : ℝ)^8431 ≤ (21684529470179/50000000000000 : ℝ)^6383 := by
    have hnat : (53126807 : ℕ)^8431*50000000000000^6383 ≤ 21684529470179^6383*100000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53126807 100000000 21684529470179 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078184157/2000000000 : ℝ)^8431 ≤ (44214671267459/100000000000000 : ℝ)^6383 := by
    have hnat : (1078184157 : ℕ)^8431*100000000000000^6383 ≤ 44214671267459^6383*2000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078184157 2000000000 44214671267459 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2060974051/10000000000 : ℝ)^8431 ≤ (12416269775759/100000000000000 : ℝ)^6383 := by
    have hnat : (2060974051 : ℕ)^8431*100000000000000^6383 ≤ 12416269775759^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2060974051 10000000000 12416269775759 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53126807/100000000 : ℝ), (1078184157/2000000000 : ℝ), (-2060974051/10000000000 : ℝ)] ![(21684529470179/50000000000000 : ℝ), (44214671267459/100000000000000 : ℝ), (12416269775759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53126807/100000000 : ℝ)|^8431 ≤ (21684529470179/50000000000000 : ℝ)^6383
        have hw : |(53126807/100000000 : ℝ)|=(53126807/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078184157/2000000000 : ℝ)|^8431 ≤ (44214671267459/100000000000000 : ℝ)^6383
        have hw : |(1078184157/2000000000 : ℝ)|=(1078184157/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2060974051/10000000000 : ℝ)|^8431 ≤ (12416269775759/100000000000000 : ℝ)^6383
        have hw : |(-2060974051/10000000000 : ℝ)|=(2060974051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s8_7 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4351332699/10000000000 : ℝ)*x 0 + (4478171311/10000000000 : ℝ)*x 1 + (4228013761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4351332699/10000000000 : ℝ)^8431 ≤ (3331757884099/10000000000000 : ℝ)^6383 := by
    have hnat : (4351332699 : ℕ)^8431*10000000000000^6383 ≤ 3331757884099^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4351332699 10000000000 3331757884099 10000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4478171311/10000000000 : ℝ)^8431 ≤ (34606332339383/100000000000000 : ℝ)^6383 := by
    have hnat : (4478171311 : ℕ)^8431*100000000000000^6383 ≤ 34606332339383^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4478171311 10000000000 34606332339383 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4228013761/10000000000 : ℝ)^8431 ≤ (32076088806487/100000000000000 : ℝ)^6383 := by
    have hnat : (4228013761 : ℕ)^8431*100000000000000^6383 ≤ 32076088806487^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4228013761 10000000000 32076088806487 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4351332699/10000000000 : ℝ), (4478171311/10000000000 : ℝ), (4228013761/10000000000 : ℝ)] ![(3331757884099/10000000000000 : ℝ), (34606332339383/100000000000000 : ℝ), (32076088806487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4351332699/10000000000 : ℝ)|^8431 ≤ (3331757884099/10000000000000 : ℝ)^6383
        have hw : |(4351332699/10000000000 : ℝ)|=(4351332699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4478171311/10000000000 : ℝ)|^8431 ≤ (34606332339383/100000000000000 : ℝ)^6383
        have hw : |(4478171311/10000000000 : ℝ)|=(4478171311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4228013761/10000000000 : ℝ)|^8431 ≤ (32076088806487/100000000000000 : ℝ)^6383
        have hw : |(4228013761/10000000000 : ℝ)|=(4228013761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1238_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75675097/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14103/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11473/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5737/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7051/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14103/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11473/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14103/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11473/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14103/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11473/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14103/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11473/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14103/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11473/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14103/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11473/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11473/100000 : ℝ) ^ (4215/1024 : ℝ) ≤ (1684000318173113/12500000000000000000 : ℝ) := by
    have hpowers : (11473/100000 : ℝ)^4215 ≤ (1684000318173113/12500000000000000000 : ℝ)^1024 := by
      have hnat : (11473 : ℕ)^4215*12500000000000000000^1024 ≤ 1684000318173113^1024*100000^4215 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11473 100000 1684000318173113 12500000000000000000 4215 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11473/100000 : ℝ)) (X := (1684000318173113/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14103/100000 : ℝ) ^ (4215/1024 : ℝ) ≤ (31505524653912793/100000000000000000000 : ℝ) := by
    have hpowers : (14103/100000 : ℝ)^4215 ≤ (31505524653912793/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14103 : ℕ)^4215*100000000000000000000^1024 ≤ 31505524653912793^1024*100000^4215 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14103 100000 31505524653912793 100000000000000000000 4215 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14103/100000 : ℝ)) (X := (31505524653912793/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251684000318173113/6250000000000000000 : ℝ) ≤ (10000654515958739/10000000000000000 : ℝ) ^ (4215/1024 : ℝ) := by
    have hpowers : (6251684000318173113/6250000000000000000 : ℝ)^1024 ≤ (10000654515958739/10000000000000000 : ℝ)^4215 := by
      have hnat : (6251684000318173113 : ℕ)^1024*10000000000000000^4215 ≤ 10000654515958739^4215*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251684000318173113 6250000000000000000 10000654515958739 10000000000000000 1024 4215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000654515958739/10000000000000000 : ℝ)) (X := (6251684000318173113/6250000000000000000 : ℝ)) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044977527199297697/100000000000000000000 : ℝ) ≤ (5000546253245269/5000000000000000 : ℝ) ^ (4215/1024 : ℝ) := by
    have hpowers : (100044977527199297697/100000000000000000000 : ℝ)^1024 ≤ (5000546253245269/5000000000000000 : ℝ)^4215 := by
      have hnat : (100044977527199297697 : ℕ)^1024*5000000000000000^4215 ≤ 5000546253245269^4215*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044977527199297697 100000000000000000000 5000546253245269 5000000000000000 1024 4215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000546253245269/5000000000000000 : ℝ)) (X := (100044977527199297697/100000000000000000000 : ℝ)) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031505524653912793/50000000000000000000 : ℝ) ≤ (10001530497022337/10000000000000000 : ℝ) ^ (4215/1024 : ℝ) := by
    have hpowers : (50031505524653912793/50000000000000000000 : ℝ)^1024 ≤ (10001530497022337/10000000000000000 : ℝ)^4215 := by
      have hnat : (50031505524653912793 : ℕ)^1024*10000000000000000^4215 ≤ 10001530497022337^4215*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031505524653912793 50000000000000000000 10001530497022337 10000000000000000 1024 4215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001530497022337/10000000000000000 : ℝ)) (X := (50031505524653912793/50000000000000000000 : ℝ)) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1684000318173113/12500000000000000000 : ℝ) ≤ ((6572917811557205929/6575000000000000000 : ℝ)+2*(437990531799/263000000000000 : ℝ)*(11473/100000 : ℝ))^(4215/1024 : ℝ) := by
    rw [show (6572917811557205929/6575000000000000000 : ℝ)+2*(437990531799/263000000000000 : ℝ)*(11473/100000 : ℝ)=(10000654515958739/10000000000000000 : ℝ) by norm_num, show 1+2*(1684000318173113/12500000000000000000 : ℝ)=(6251684000318173113/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31505524653912793/100000000000000000000 : ℝ)+(1684000318173113/12500000000000000000 : ℝ) ≤ ((6572917811557205929/6575000000000000000 : ℝ)+(437990531799/263000000000000 : ℝ)*((14103/100000 : ℝ)+(11473/100000 : ℝ)))^(4215/1024 : ℝ) := by
    rw [show (6572917811557205929/6575000000000000000 : ℝ)+(437990531799/263000000000000 : ℝ)*((14103/100000 : ℝ)+(11473/100000 : ℝ))=(5000546253245269/5000000000000000 : ℝ) by norm_num, show 1+(31505524653912793/100000000000000000000 : ℝ)+(1684000318173113/12500000000000000000 : ℝ)=(100044977527199297697/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31505524653912793/100000000000000000000 : ℝ) ≤ ((6572917811557205929/6575000000000000000 : ℝ)+2*(437990531799/263000000000000 : ℝ)*(14103/100000 : ℝ))^(4215/1024 : ℝ) := by
    rw [show (6572917811557205929/6575000000000000000 : ℝ)+2*(437990531799/263000000000000 : ℝ)*(14103/100000 : ℝ)=(10001530497022337/10000000000000000 : ℝ) by norm_num, show 1+2*(31505524653912793/100000000000000000000 : ℝ)=(50031505524653912793/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6572917811557205929/6575000000000000000 : ℝ)*(X 1 0+X 2 0)+(437990531799/263000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4215/1024 : ℝ)) (lo := (11473/100000 : ℝ)) (hi := (14103/100000 : ℝ)) (c := (6572917811557205929/6575000000000000000 : ℝ)) (alpha := (437990531799/263000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6572917811557205929/6575000000000000000 : ℝ)*(X 0 1+X 2 1)+(437990531799/263000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4215/1024 : ℝ)) (lo := (11473/100000 : ℝ)) (hi := (14103/100000 : ℝ)) (c := (6572917811557205929/6575000000000000000 : ℝ)) (alpha := (437990531799/263000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6572917811557205929/6575000000000000000 : ℝ)*(X 0 2+X 1 2)+(437990531799/263000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4215/1024 : ℝ)) (lo := (11473/100000 : ℝ)) (hi := (14103/100000 : ℝ)) (c := (6572917811557205929/6575000000000000000 : ℝ)) (alpha := (437990531799/263000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2121808097/10000000000 : ℝ)*X 0 0+(1078246991/2000000000 : ℝ)*X 0 1+(1316799039/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344320647/10000000000 : ℝ)*X 1 0+(-2184699347/10000000000 : ℝ)*X 1 1+(4114997/7812500 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668040081/1250000000 : ℝ)*X 2 0+(658399521/1250000000 : ℝ)*X 2 1+(-273087417/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4351323857/10000000000 : ℝ)*X 0 0+(845475507/2000000000 : ℝ)*X 0 1+(2239402321/5000000000 : ℝ)*X 0 2+(4351323857/10000000000 : ℝ)*X 1 0+(845475507/2000000000 : ℝ)*X 1 1+(2239402321/5000000000 : ℝ)*X 1 2+(4351323857/10000000000 : ℝ)*X 2 0+(845475507/2000000000 : ℝ)*X 2 1+(2239402321/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-424362481/2000000000 : ℝ)*X 0 0+(1316877199/2500000000 : ℝ)*X 0 1+(2695460721/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656340017/5000000000 : ℝ)*X 1 0+(-1030487097/5000000000 : ℝ)*X 1 1+(5390921343/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((53126807/100000000 : ℝ)*X 2 0+(1078184157/2000000000 : ℝ)*X 2 1+(-2060974051/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4351332699/10000000000 : ℝ)*X 0 0+(4478171311/10000000000 : ℝ)*X 0 1+(4228013761/10000000000 : ℝ)*X 0 2+(4351332699/10000000000 : ℝ)*X 1 0+(4478171311/10000000000 : ℝ)*X 1 1+(4228013761/10000000000 : ℝ)*X 1 2+(4351332699/10000000000 : ℝ)*X 2 0+(4478171311/10000000000 : ℝ)*X 2 1+(4228013761/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (645232730669788884128573331/82187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1526022881/100000000000000 : ℝ)*(base19) + (1422209489/100000000000000 : ℝ)*(base23) + (7035927/12500000000000 : ℝ)*(lower2) + (9617181/5000000000000 : ℝ)*(upper3) + (13409113/10000000000000 : ℝ)*(upper5) + (1504927472750813/25000000000000 : ℝ)*(major0) + (1504927472750813/25000000000000 : ℝ)*(major1) + (1504927472750813/25000000000000 : ℝ)*(major2) + (1612407539355303/20000000000000 : ℝ)*(sp0) + (4031039629796907/50000000000000 : ℝ)*(sp1) + (4031039681703603/50000000000000 : ℝ)*(sp2) + (62145568336033/1562500000000 : ℝ)*(sp3) + (43088840179/100000000000000 : ℝ)*(sp4) + (1118059617/5000000000000 : ℝ)*(sp7) + (994334683674613/25000000000000 : ℝ)*(f.failure) + (1612416157123339/20000000000000 : ℝ)*(f.sum) + (158331204333/51367187500000000000000000 : ℝ)*base65 + (284359624603470277/164375000000000000000000000000000 : ℝ)*base67 + (1535848439133404723/164375000000000000000000000000000 : ℝ)*base70 + (2813676709508404723/164375000000000000000000000000000 : ℝ)*base72 + (940760514907/205468750000000000000000000 : ℝ)*base73 + (2354314265799654723/164375000000000000000000000000000 : ℝ)*base76 + (1515284908435345277/164375000000000000000000000000000 : ℝ)*base77 + (2025929405794654723/164375000000000000000000000000000 : ℝ)*base80 + (3420410066963/3287500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (5212461/1250000000000000000000 : ℝ)*base89 + (5212461/1250000000000000000000 : ℝ)*base91 + (5212461/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1292536658699670536392771869/164375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (334410513/50000000000000 : ℝ)*(base19) + (984502143/50000000000000 : ℝ)*(base23) + (19750347/5000000000000 : ℝ)*(lower1) + (166960593/100000000000000 : ℝ)*(lower3) + (100218421/100000000000000 : ℝ)*(lower4) + (231497/781250000000 : ℝ)*(lower5) + (6050173906053787/100000000000000 : ℝ)*(major0) + (6050173906053787/100000000000000 : ℝ)*(major1) + (6050173906053787/100000000000000 : ℝ)*(major2) + (401988807/2500000000000 : ℝ)*(sp2) + (8102880651437887/100000000000000 : ℝ)*(sp4) + (8102879982616861/100000000000000 : ℝ)*(sp5) + (8102862602881321/100000000000000 : ℝ)*(sp6) + (3997466898558311/100000000000000 : ℝ)*(sp7) + (3997466898558311/100000000000000 : ℝ)*(f.failure) + (8102880651437887/100000000000000 : ℝ)*(f.sum) + (3444288397713/13150000000000000000000000000 : ℝ)*base65 + (3466464162817871877/657500000000000000000000000000000 : ℝ)*base68 + (1381282438757871877/657500000000000000000000000000000 : ℝ)*base70 + (21633909052992871877/657500000000000000000000000000000 : ℝ)*base72 + (17353850661237/13150000000000000000000000000 : ℝ)*base74 + (42012869948125371877/657500000000000000000000000000000 : ℝ)*base76 + (1667740467612128123/657500000000000000000000000000000 : ℝ)*base77 + (7949737040065371877/657500000000000000000000000000000 : ℝ)*base80 + (64287930479813/13150000000000000000000000000 : ℝ)*base81 + (4918833/5000000000000000000000 : ℝ)*base90 + (4918833/5000000000000000000000 : ℝ)*base92 + (4918833/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1238_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75675097/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14103/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11473/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5737/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7051/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1238_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1238_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75675097/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14129/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11449/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5737/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7051/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1238_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1238_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1238_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75675097/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14129/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11449/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5737/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7051/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1238_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
