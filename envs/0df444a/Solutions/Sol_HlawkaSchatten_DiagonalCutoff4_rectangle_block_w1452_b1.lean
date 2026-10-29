-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1452_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:59:41.988935+00:00
-- url     : https://prove2.me/submissions/7ebd4786-6999-4cce-9a12-dc7f73264def

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
theorem support_rectangle_w1452_s3_0 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-975847901/5000000000 : ℝ)*x 0 + (1353756717/2500000000 : ℝ)*x 1 + (2620006961/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (975847901/5000000000 : ℝ)^1103 ≤ (11910884431693/100000000000000 : ℝ)^847 := by
    have hnat : (975847901 : ℕ)^1103*100000000000000^847 ≤ 11910884431693^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      975847901 5000000000 11910884431693 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353756717/2500000000 : ℝ)^1103 ≤ (22493302029527/50000000000000 : ℝ)^847 := by
    have hnat : (1353756717 : ℕ)^1103*50000000000000^847 ≤ 22493302029527^847*2500000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353756717 2500000000 22493302029527 50000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2620006961/5000000000 : ℝ)^1103 ≤ (1724100460209/4000000000000 : ℝ)^847 := by
    have hnat : (2620006961 : ℕ)^1103*4000000000000^847 ≤ 1724100460209^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620006961 5000000000 1724100460209 4000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-975847901/5000000000 : ℝ), (1353756717/2500000000 : ℝ), (2620006961/5000000000 : ℝ)] ![(11910884431693/100000000000000 : ℝ), (22493302029527/50000000000000 : ℝ), (1724100460209/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-975847901/5000000000 : ℝ)|^1103 ≤ (11910884431693/100000000000000 : ℝ)^847
        have hw : |(-975847901/5000000000 : ℝ)|=(975847901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353756717/2500000000 : ℝ)|^1103 ≤ (22493302029527/50000000000000 : ℝ)^847
        have hw : |(1353756717/2500000000 : ℝ)|=(1353756717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2620006961/5000000000 : ℝ)|^1103 ≤ (1724100460209/4000000000000 : ℝ)^847
        have hw : |(2620006961/5000000000 : ℝ)|=(2620006961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s3_1 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2674451579/5000000000 : ℝ)*x 0 + (-1020466263/5000000000 : ℝ)*x 1 + (2620006993/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674451579/5000000000 : ℝ)^1103 ≤ (22136277999873/50000000000000 : ℝ)^847 := by
    have hnat : (2674451579 : ℕ)^1103*50000000000000^847 ≤ 22136277999873^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674451579 5000000000 22136277999873 50000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1020466263/5000000000 : ℝ)^1103 ≤ (126249318053/1000000000000 : ℝ)^847 := by
    have hnat : (1020466263 : ℕ)^1103*1000000000000^847 ≤ 126249318053^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1020466263 5000000000 126249318053 1000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2620006993/5000000000 : ℝ)^1103 ≤ (2155125609539/5000000000000 : ℝ)^847 := by
    have hnat : (2620006993 : ℕ)^1103*5000000000000^847 ≤ 2155125609539^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620006993 5000000000 2155125609539 5000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674451579/5000000000 : ℝ), (-1020466263/5000000000 : ℝ), (2620006993/5000000000 : ℝ)] ![(22136277999873/50000000000000 : ℝ), (126249318053/1000000000000 : ℝ), (2155125609539/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674451579/5000000000 : ℝ)|^1103 ≤ (22136277999873/50000000000000 : ℝ)^847
        have hw : |(2674451579/5000000000 : ℝ)|=(2674451579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1020466263/5000000000 : ℝ)|^1103 ≤ (126249318053/1000000000000 : ℝ)^847
        have hw : |(-1020466263/5000000000 : ℝ)|=(1020466263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2620006993/5000000000 : ℝ)|^1103 ≤ (2155125609539/5000000000000 : ℝ)^847
        have hw : |(2620006993/5000000000 : ℝ)|=(2620006993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s3_2 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2674451709/5000000000 : ℝ)*x 0 + (2620006897/5000000000 : ℝ)*x 1 + (-127558277/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674451709/5000000000 : ℝ)^1103 ≤ (2213627940109/5000000000000 : ℝ)^847 := by
    have hnat : (2674451709 : ℕ)^1103*5000000000000^847 ≤ 2213627940109^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674451709 5000000000 2213627940109 5000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2620006897/5000000000 : ℝ)^1103 ≤ (8620502026823/20000000000000 : ℝ)^847 := by
    have hnat : (2620006897 : ℕ)^1103*20000000000000^847 ≤ 8620502026823^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620006897 5000000000 8620502026823 20000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (127558277/625000000 : ℝ)^1103 ≤ (12624931048083/100000000000000 : ℝ)^847 := by
    have hnat : (127558277 : ℕ)^1103*100000000000000^847 ≤ 12624931048083^847*625000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127558277 625000000 12624931048083 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674451709/5000000000 : ℝ), (2620006897/5000000000 : ℝ), (-127558277/625000000 : ℝ)] ![(2213627940109/5000000000000 : ℝ), (8620502026823/20000000000000 : ℝ), (12624931048083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674451709/5000000000 : ℝ)|^1103 ≤ (2213627940109/5000000000000 : ℝ)^847
        have hw : |(2674451709/5000000000 : ℝ)|=(2674451709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2620006897/5000000000 : ℝ)|^1103 ≤ (8620502026823/20000000000000 : ℝ)^847
        have hw : |(2620006897/5000000000 : ℝ)|=(2620006897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-127558277/625000000 : ℝ)|^1103 ≤ (12624931048083/100000000000000 : ℝ)^847
        have hw : |(-127558277/625000000 : ℝ)|=(127558277/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s3_3 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2149044797/5000000000 : ℝ)*x 0 + (4110962107/10000000000 : ℝ)*x 1 + (2246383043/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2149044797/5000000000 : ℝ)^1103 ≤ (8324831875093/25000000000000 : ℝ)^847 := by
    have hnat : (2149044797 : ℕ)^1103*25000000000000^847 ≤ 8324831875093^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149044797 5000000000 8324831875093 25000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4110962107/10000000000 : ℝ)^1103 ≤ (31423930775627/100000000000000 : ℝ)^847 := by
    have hnat : (4110962107 : ℕ)^1103*100000000000000^847 ≤ 31423930775627^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4110962107 10000000000 31423930775627 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2246383043/5000000000 : ℝ)^1103 ≤ (1763837085213/5000000000000 : ℝ)^847 := by
    have hnat : (2246383043 : ℕ)^1103*5000000000000^847 ≤ 1763837085213^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246383043 5000000000 1763837085213 5000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2149044797/5000000000 : ℝ), (4110962107/10000000000 : ℝ), (2246383043/5000000000 : ℝ)] ![(8324831875093/25000000000000 : ℝ), (31423930775627/100000000000000 : ℝ), (1763837085213/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2149044797/5000000000 : ℝ)|^1103 ≤ (8324831875093/25000000000000 : ℝ)^847
        have hw : |(2149044797/5000000000 : ℝ)|=(2149044797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4110962107/10000000000 : ℝ)|^1103 ≤ (31423930775627/100000000000000 : ℝ)^847
        have hw : |(4110962107/10000000000 : ℝ)|=(4110962107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2246383043/5000000000 : ℝ)|^1103 ≤ (1763837085213/5000000000000 : ℝ)^847
        have hw : |(2246383043/5000000000 : ℝ)|=(2246383043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s3_4 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1951709901/10000000000 : ℝ)*x 0 + (524070717/1000000000 : ℝ)*x 1 + (1082866017/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1951709901/10000000000 : ℝ)^1103 ≤ (11910996481927/100000000000000 : ℝ)^847 := by
    have hnat : (1951709901 : ℕ)^1103*100000000000000^847 ≤ 11910996481927^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1951709901 10000000000 11910996481927 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524070717/1000000000 : ℝ)^1103 ≤ (21554968791947/50000000000000 : ℝ)^847 := by
    have hnat : (524070717 : ℕ)^1103*50000000000000^847 ≤ 21554968791947^847*1000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524070717 1000000000 21554968791947 50000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082866017/2000000000 : ℝ)^1103 ≤ (44979065926023/100000000000000 : ℝ)^847 := by
    have hnat : (1082866017 : ℕ)^1103*100000000000000^847 ≤ 44979065926023^847*2000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082866017 2000000000 44979065926023 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1951709901/10000000000 : ℝ), (524070717/1000000000 : ℝ), (1082866017/2000000000 : ℝ)] ![(11910996481927/100000000000000 : ℝ), (21554968791947/50000000000000 : ℝ), (44979065926023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1951709901/10000000000 : ℝ)|^1103 ≤ (11910996481927/100000000000000 : ℝ)^847
        have hw : |(-1951709901/10000000000 : ℝ)|=(1951709901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524070717/1000000000 : ℝ)|^1103 ≤ (21554968791947/50000000000000 : ℝ)^847
        have hw : |(524070717/1000000000 : ℝ)|=(524070717/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082866017/2000000000 : ℝ)|^1103 ≤ (44979065926023/100000000000000 : ℝ)^847
        have hw : |(1082866017/2000000000 : ℝ)|=(1082866017/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s3_5 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (106066101/200000000 : ℝ)*x 0 + (-233327063/1250000000 : ℝ)*x 1 + (5414330053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106066101/200000000 : ℝ)^1103 ≤ (21890853551283/50000000000000 : ℝ)^847 := by
    have hnat : (106066101 : ℕ)^1103*50000000000000^847 ≤ 21890853551283^847*200000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106066101 200000000 21890853551283 50000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (233327063/1250000000 : ℝ)^1103 ≤ (2247845459811/20000000000000 : ℝ)^847 := by
    have hnat : (233327063 : ℕ)^1103*20000000000000^847 ≤ 2247845459811^847*1250000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      233327063 1250000000 2247845459811 20000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414330053/10000000000 : ℝ)^1103 ≤ (22489532789919/50000000000000 : ℝ)^847 := by
    have hnat : (5414330053 : ℕ)^1103*50000000000000^847 ≤ 22489532789919^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414330053 10000000000 22489532789919 50000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106066101/200000000 : ℝ), (-233327063/1250000000 : ℝ), (5414330053/10000000000 : ℝ)] ![(21890853551283/50000000000000 : ℝ), (2247845459811/20000000000000 : ℝ), (22489532789919/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106066101/200000000 : ℝ)|^1103 ≤ (21890853551283/50000000000000 : ℝ)^847
        have hw : |(106066101/200000000 : ℝ)|=(106066101/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-233327063/1250000000 : ℝ)|^1103 ≤ (2247845459811/20000000000000 : ℝ)^847
        have hw : |(-233327063/1250000000 : ℝ)|=(233327063/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414330053/10000000000 : ℝ)|^1103 ≤ (22489532789919/50000000000000 : ℝ)^847
        have hw : |(5414330053/10000000000 : ℝ)|=(5414330053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s3_6 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5303303927/10000000000 : ℝ)*x 0 + (2707165469/5000000000 : ℝ)*x 1 + (-1866616823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303303927/10000000000 : ℝ)^1103 ≤ (4378169502949/10000000000000 : ℝ)^847 := by
    have hnat : (5303303927 : ℕ)^1103*10000000000000^847 ≤ 4378169502949^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303303927 10000000000 4378169502949 10000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707165469/5000000000 : ℝ)^1103 ≤ (44979075154007/100000000000000 : ℝ)^847 := by
    have hnat : (2707165469 : ℕ)^1103*100000000000000^847 ≤ 44979075154007^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707165469 5000000000 44979075154007 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1866616823/10000000000 : ℝ)^1103 ≤ (2247845960069/20000000000000 : ℝ)^847 := by
    have hnat : (1866616823 : ℕ)^1103*20000000000000^847 ≤ 2247845960069^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1866616823 10000000000 2247845960069 20000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303303927/10000000000 : ℝ), (2707165469/5000000000 : ℝ), (-1866616823/10000000000 : ℝ)] ![(4378169502949/10000000000000 : ℝ), (44979075154007/100000000000000 : ℝ), (2247845960069/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303303927/10000000000 : ℝ)|^1103 ≤ (4378169502949/10000000000000 : ℝ)^847
        have hw : |(5303303927/10000000000 : ℝ)|=(5303303927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707165469/5000000000 : ℝ)|^1103 ≤ (44979075154007/100000000000000 : ℝ)^847
        have hw : |(2707165469/5000000000 : ℝ)|=(2707165469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1866616823/10000000000 : ℝ)|^1103 ≤ (2247845960069/20000000000000 : ℝ)^847
        have hw : |(-1866616823/10000000000 : ℝ)|=(1866616823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s3_7 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4298120633/10000000000 : ℝ)*x 0 + (1122813701/2500000000 : ℝ)*x 1 + (4112482883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4298120633/10000000000 : ℝ)^1103 ≤ (16649820328027/50000000000000 : ℝ)^847 := by
    have hnat : (4298120633 : ℕ)^1103*50000000000000^847 ≤ 16649820328027^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4298120633 10000000000 16649820328027 50000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1122813701/2500000000 : ℝ)^1103 ≤ (7052257901783/20000000000000 : ℝ)^847 := by
    have hnat : (1122813701 : ℕ)^1103*20000000000000^847 ≤ 7052257901783^847*2500000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122813701 2500000000 7052257901783 20000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4112482883/10000000000 : ℝ)^1103 ≤ (6287813965411/20000000000000 : ℝ)^847 := by
    have hnat : (4112482883 : ℕ)^1103*20000000000000^847 ≤ 6287813965411^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4112482883 10000000000 6287813965411 20000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4298120633/10000000000 : ℝ), (1122813701/2500000000 : ℝ), (4112482883/10000000000 : ℝ)] ![(16649820328027/50000000000000 : ℝ), (7052257901783/20000000000000 : ℝ), (6287813965411/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4298120633/10000000000 : ℝ)|^1103 ≤ (16649820328027/50000000000000 : ℝ)^847
        have hw : |(4298120633/10000000000 : ℝ)|=(4298120633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1122813701/2500000000 : ℝ)|^1103 ≤ (7052257901783/20000000000000 : ℝ)^847
        have hw : |(1122813701/2500000000 : ℝ)|=(1122813701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4112482883/10000000000 : ℝ)|^1103 ≤ (6287813965411/20000000000000 : ℝ)^847
        have hw : |(4112482883/10000000000 : ℝ)|=(4112482883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1452_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9942431/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3933/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10487/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11229/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1867/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3933/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10487/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3933/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10487/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3933/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10487/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3933/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10487/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3933/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10487/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3933/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10487/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
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
  have hpowlo : (10487/100000 : ℝ) ^ (4411/1024 : ℝ) ≤ (6044224257531677/100000000000000000000 : ℝ) := by
    have hpowers : (10487/100000 : ℝ)^4411 ≤ (6044224257531677/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10487 : ℕ)^4411*100000000000000000000^1024 ≤ 6044224257531677^1024*100000^4411 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10487 100000 6044224257531677 100000000000000000000 4411 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10487/100000 : ℝ)) (X := (6044224257531677/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4411 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3933/25000 : ℝ) ^ (4411/1024 : ℝ) ≤ (33865128532979/97656250000000000 : ℝ) := by
    have hpowers : (3933/25000 : ℝ)^4411 ≤ (33865128532979/97656250000000000 : ℝ)^1024 := by
      have hnat : (3933 : ℕ)^4411*97656250000000000^1024 ≤ 33865128532979^1024*25000^4411 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3933 25000 33865128532979 97656250000000000 4411 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3933/25000 : ℝ)) (X := (33865128532979/97656250000000000 : ℝ)) (by norm_num) (by norm_num) 4411 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006044224257531677/50000000000000000000 : ℝ) ≤ (5000140308284079/5000000000000000 : ℝ) ^ (4411/1024 : ℝ) := by
    have hpowers : (50006044224257531677/50000000000000000000 : ℝ)^1024 ≤ (5000140308284079/5000000000000000 : ℝ)^4411 := by
      have hnat : (50006044224257531677 : ℕ)^1024*5000000000000000^4411 ≤ 5000140308284079^4411*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006044224257531677 50000000000000000000 5000140308284079 5000000000000000 1024 4411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000140308284079/5000000000000000 : ℝ)) (X := (50006044224257531677/50000000000000000000 : ℝ)) (by norm_num) 4411 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100040722115875302173/100000000000000000000 : ℝ) ≤ (5000472601777411/5000000000000000 : ℝ) ^ (4411/1024 : ℝ) := by
    have hpowers : (100040722115875302173/100000000000000000000 : ℝ)^1024 ≤ (5000472601777411/5000000000000000 : ℝ)^4411 := by
      have hnat : (100040722115875302173 : ℕ)^1024*5000000000000000^4411 ≤ 5000472601777411^4411*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100040722115875302173 100000000000000000000 5000472601777411 5000000000000000 1024 4411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000472601777411/5000000000000000 : ℝ)) (X := (100040722115875302173/100000000000000000000 : ℝ)) (by norm_num) 4411 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (48861990128532979/48828125000000000 : ℝ) ≤ (5000804895270743/5000000000000000 : ℝ) ^ (4411/1024 : ℝ) := by
    have hpowers : (48861990128532979/48828125000000000 : ℝ)^1024 ≤ (5000804895270743/5000000000000000 : ℝ)^4411 := by
      have hnat : (48861990128532979 : ℕ)^1024*5000000000000000^4411 ≤ 5000804895270743^4411*48828125000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        48861990128532979 48828125000000000 5000804895270743 5000000000000000 1024 4411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000804895270743/5000000000000000 : ℝ)) (X := (48861990128532979/48828125000000000 : ℝ)) (by norm_num) 4411 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6044224257531677/100000000000000000000 : ℝ) ≤ ((26218766393220848987/26225000000000000000 : ℝ)+2*(83073373333/65562500000000 : ℝ)*(10487/100000 : ℝ))^(4411/1024 : ℝ) := by
    rw [show (26218766393220848987/26225000000000000000 : ℝ)+2*(83073373333/65562500000000 : ℝ)*(10487/100000 : ℝ)=(5000140308284079/5000000000000000 : ℝ) by norm_num, show 1+2*(6044224257531677/100000000000000000000 : ℝ)=(50006044224257531677/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33865128532979/97656250000000000 : ℝ)+(6044224257531677/100000000000000000000 : ℝ) ≤ ((26218766393220848987/26225000000000000000 : ℝ)+(83073373333/65562500000000 : ℝ)*((3933/25000 : ℝ)+(10487/100000 : ℝ)))^(4411/1024 : ℝ) := by
    rw [show (26218766393220848987/26225000000000000000 : ℝ)+(83073373333/65562500000000 : ℝ)*((3933/25000 : ℝ)+(10487/100000 : ℝ))=(5000472601777411/5000000000000000 : ℝ) by norm_num, show 1+(33865128532979/97656250000000000 : ℝ)+(6044224257531677/100000000000000000000 : ℝ)=(100040722115875302173/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33865128532979/97656250000000000 : ℝ) ≤ ((26218766393220848987/26225000000000000000 : ℝ)+2*(83073373333/65562500000000 : ℝ)*(3933/25000 : ℝ))^(4411/1024 : ℝ) := by
    rw [show (26218766393220848987/26225000000000000000 : ℝ)+2*(83073373333/65562500000000 : ℝ)*(3933/25000 : ℝ)=(5000804895270743/5000000000000000 : ℝ) by norm_num, show 1+2*(33865128532979/97656250000000000 : ℝ)=(48861990128532979/48828125000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26218766393220848987/26225000000000000000 : ℝ)*(X 1 0+X 2 0)+(83073373333/65562500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4411/1024 : ℝ)) (lo := (10487/100000 : ℝ)) (hi := (3933/25000 : ℝ)) (c := (26218766393220848987/26225000000000000000 : ℝ)) (alpha := (83073373333/65562500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26218766393220848987/26225000000000000000 : ℝ)*(X 0 1+X 2 1)+(83073373333/65562500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4411/1024 : ℝ)) (lo := (10487/100000 : ℝ)) (hi := (3933/25000 : ℝ)) (c := (26218766393220848987/26225000000000000000 : ℝ)) (alpha := (83073373333/65562500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26218766393220848987/26225000000000000000 : ℝ)*(X 0 2+X 1 2)+(83073373333/65562500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4411/1024 : ℝ)) (lo := (10487/100000 : ℝ)) (hi := (3933/25000 : ℝ)) (c := (26218766393220848987/26225000000000000000 : ℝ)) (alpha := (83073373333/65562500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-975847901/5000000000 : ℝ)*X 0 0+(1353756717/2500000000 : ℝ)*X 0 1+(2620006961/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674451579/5000000000 : ℝ)*X 1 0+(-1020466263/5000000000 : ℝ)*X 1 1+(2620006993/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674451709/5000000000 : ℝ)*X 2 0+(2620006897/5000000000 : ℝ)*X 2 1+(-127558277/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2149044797/5000000000 : ℝ)*X 0 0+(4110962107/10000000000 : ℝ)*X 0 1+(2246383043/5000000000 : ℝ)*X 0 2+(2149044797/5000000000 : ℝ)*X 1 0+(4110962107/10000000000 : ℝ)*X 1 1+(2246383043/5000000000 : ℝ)*X 1 2+(2149044797/5000000000 : ℝ)*X 2 0+(4110962107/10000000000 : ℝ)*X 2 1+(2246383043/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1951709901/10000000000 : ℝ)*X 0 0+(524070717/1000000000 : ℝ)*X 0 1+(1082866017/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((106066101/200000000 : ℝ)*X 1 0+(-233327063/1250000000 : ℝ)*X 1 1+(5414330053/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5303303927/10000000000 : ℝ)*X 2 0+(2707165469/5000000000 : ℝ)*X 2 1+(-1866616823/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4298120633/10000000000 : ℝ)*X 0 0+(1122813701/2500000000 : ℝ)*X 0 1+(4112482883/10000000000 : ℝ)*X 0 2+(4298120633/10000000000 : ℝ)*X 1 0+(1122813701/2500000000 : ℝ)*X 1 1+(4112482883/10000000000 : ℝ)*X 1 2+(4298120633/10000000000 : ℝ)*X 2 0+(1122813701/2500000000 : ℝ)*X 2 1+(4112482883/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4203864381753307239450633417/1311250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (204514931/50000000000000 : ℝ)*(base19) + (307631221/50000000000000 : ℝ)*(base23) + (4438023/12500000000000 : ℝ)*(upper3) + (19124509/50000000000000 : ℝ)*(upper4) + (1426367/1000000000000 : ℝ)*(upper5) + (520814263478179/12500000000000 : ℝ)*(major0) + (520814263478179/12500000000000 : ℝ)*(major1) + (4166514107825433/100000000000000 : ℝ)*(major2) + (44639588901107/781250000000 : ℝ)*(sp0) + (1142775640122379/20000000000000 : ℝ)*(sp1) + (1142775598875863/20000000000000 : ℝ)*(sp2) + (2619147412493929/100000000000000 : ℝ)*(sp3) + (11230300061/100000000000000 : ℝ)*(sp4) + (104332429/5000000000000 : ℝ)*(sp7) + (2619149499142509/100000000000000 : ℝ)*(f.failure) + (5713878609641757/100000000000000 : ℝ)*(f.sum) + (10081508297251/5245000000000000000000000000 : ℝ)*base65 + (6645803052108357827/327812500000000000000000000000000 : ℝ)*base68 + (24820269179954213629/2622500000000000000000000000000000 : ℝ)*base70 + (6550651591044295327/327812500000000000000000000000000 : ℝ)*base72 + (3468782097049/5245000000000000000000000000 : ℝ)*base74 + (18193832092646713629/2622500000000000000000000000000000 : ℝ)*base76 + (6585663646817195327/327812500000000000000000000000000 : ℝ)*base78 + (7351949360458757827/327812500000000000000000000000000 : ℝ)*base80 + (27594008922599/13112500000000000000000000000 : ℝ)*base81 + (4899379/625000000000000000000 : ℝ)*base89 + (4899379/625000000000000000000 : ℝ)*base91 + (1350621/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (80470176478318969420232103/5245000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (153667271/100000000000000 : ℝ)*(base21) + (111910639/50000000000000 : ℝ)*(upper2) + (338229697/100000000000000 : ℝ)*(lower4) + (7759691/6250000000000 : ℝ)*(upper5) + (524981383225719/12500000000000 : ℝ)*(major0) + (524981383225719/12500000000000 : ℝ)*(major1) + (2099925532902877/50000000000000 : ℝ)*(major2) + (528657433/50000000000000 : ℝ)*(sp0) + (2758538253/100000000000000 : ℝ)*(sp2) + (157248183/10000000000000 : ℝ)*(sp3) + (2879797411009809/50000000000000 : ℝ)*(sp4) + (1439898969833621/25000000000000 : ℝ)*(sp5) + (8999364011139/156250000000 : ℝ)*(sp6) + (2640104168386369/100000000000000 : ℝ)*(sp7) + (13200528704341/500000000000 : ℝ)*(f.failure) + (1439898969833621/25000000000000 : ℝ)*(f.sum) + (236748886049583/26225000000000000000000000000 : ℝ)*base66 + (5477928325158028347/327812500000000000000000000000000 : ℝ)*base68 + (12727127362261785599/1311250000000000000000000000000000 : ℝ)*base69 + (4934877272528965847/327812500000000000000000000000000 : ℝ)*base72 + (27909127502121/13112500000000000000000000000 : ℝ)*base73 + (9599434639974285599/1311250000000000000000000000000000 : ℝ)*base75 + (354639130870390847/327812500000000000000000000000000 : ℝ)*base78 + (1847958021580703347/327812500000000000000000000000000 : ℝ)*base80 + (73333748523353/26225000000000000000000000000 : ℝ)*base81 + (42971/3125000000000000000 : ℝ)*base89 + (42971/3125000000000000000 : ℝ)*base91 + (19529/3125000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1452_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9942431/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3933/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10487/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11229/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1867/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1452_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1452_s4_0 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-244060987/1250000000 : ℝ)*x 0 + (2704099569/5000000000 : ℝ)*x 1 + (5246319613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (244060987/1250000000 : ℝ)^1103 ≤ (1489647486231/12500000000000 : ℝ)^847 := by
    have hnat : (244060987 : ℕ)^1103*12500000000000^847 ≤ 1489647486231^847*1250000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      244060987 1250000000 1489647486231 12500000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704099569/5000000000 : ℝ)^1103 ≤ (11228187760163/25000000000000 : ℝ)^847 := by
    have hnat : (2704099569 : ℕ)^1103*25000000000000^847 ≤ 11228187760163^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704099569 5000000000 11228187760163 25000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246319613/10000000000 : ℝ)^1103 ≤ (1079251726307/2500000000000 : ℝ)^847 := by
    have hnat : (5246319613 : ℕ)^1103*2500000000000^847 ≤ 1079251726307^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246319613 10000000000 1079251726307 2500000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-244060987/1250000000 : ℝ), (2704099569/5000000000 : ℝ), (5246319613/10000000000 : ℝ)] ![(1489647486231/12500000000000 : ℝ), (11228187760163/25000000000000 : ℝ), (1079251726307/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-244060987/1250000000 : ℝ)|^1103 ≤ (1489647486231/12500000000000 : ℝ)^847
        have hw : |(-244060987/1250000000 : ℝ)|=(244060987/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704099569/5000000000 : ℝ)|^1103 ≤ (11228187760163/25000000000000 : ℝ)^847
        have hw : |(2704099569/5000000000 : ℝ)|=(2704099569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246319613/10000000000 : ℝ)|^1103 ≤ (1079251726307/2500000000000 : ℝ)^847
        have hw : |(5246319613/10000000000 : ℝ)|=(5246319613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s4_1 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2673567881/5000000000 : ℝ)*x 0 + (-2034908173/10000000000 : ℝ)*x 1 + (5246319587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673567881/5000000000 : ℝ)^1103 ≤ (8850701382749/20000000000000 : ℝ)^847 := by
    have hnat : (2673567881 : ℕ)^1103*20000000000000^847 ≤ 8850701382749^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673567881 5000000000 8850701382749 20000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2034908173/10000000000 : ℝ)^1103 ≤ (12576424292931/100000000000000 : ℝ)^847 := by
    have hnat : (2034908173 : ℕ)^1103*100000000000000^847 ≤ 12576424292931^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2034908173 10000000000 12576424292931 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246319587/10000000000 : ℝ)^1103 ≤ (5396258596709/12500000000000 : ℝ)^847 := by
    have hnat : (5246319587 : ℕ)^1103*12500000000000^847 ≤ 5396258596709^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246319587 10000000000 5396258596709 12500000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673567881/5000000000 : ℝ), (-2034908173/10000000000 : ℝ), (5246319587/10000000000 : ℝ)] ![(8850701382749/20000000000000 : ℝ), (12576424292931/100000000000000 : ℝ), (5396258596709/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673567881/5000000000 : ℝ)|^1103 ≤ (8850701382749/20000000000000 : ℝ)^847
        have hw : |(2673567881/5000000000 : ℝ)|=(2673567881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2034908173/10000000000 : ℝ)|^1103 ≤ (12576424292931/100000000000000 : ℝ)^847
        have hw : |(-2034908173/10000000000 : ℝ)|=(2034908173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246319587/10000000000 : ℝ)|^1103 ≤ (5396258596709/12500000000000 : ℝ)^847
        have hw : |(5246319587/10000000000 : ℝ)|=(5246319587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s4_2 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (21388543/40000000 : ℝ)*x 0 + (524631959/1000000000 : ℝ)*x 1 + (-406981637/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21388543/40000000 : ℝ)^1103 ≤ (8850701356883/20000000000000 : ℝ)^847 := by
    have hnat : (21388543 : ℕ)^1103*20000000000000^847 ≤ 8850701356883^847*40000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21388543 40000000 8850701356883 20000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524631959/1000000000 : ℝ)^1103 ≤ (43170068805819/100000000000000 : ℝ)^847 := by
    have hnat : (524631959 : ℕ)^1103*100000000000000^847 ≤ 43170068805819^847*1000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524631959 1000000000 43170068805819 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (406981637/2000000000 : ℝ)^1103 ≤ (1257642438951/10000000000000 : ℝ)^847 := by
    have hnat : (406981637 : ℕ)^1103*10000000000000^847 ≤ 1257642438951^847*2000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      406981637 2000000000 1257642438951 10000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21388543/40000000 : ℝ), (524631959/1000000000 : ℝ), (-406981637/2000000000 : ℝ)] ![(8850701356883/20000000000000 : ℝ), (43170068805819/100000000000000 : ℝ), (1257642438951/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21388543/40000000 : ℝ)|^1103 ≤ (8850701356883/20000000000000 : ℝ)^847
        have hw : |(21388543/40000000 : ℝ)|=(21388543/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524631959/1000000000 : ℝ)|^1103 ≤ (43170068805819/100000000000000 : ℝ)^847
        have hw : |(524631959/1000000000 : ℝ)|=(524631959/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-406981637/2000000000 : ℝ)|^1103 ≤ (1257642438951/10000000000000 : ℝ)^847
        have hw : |(-406981637/2000000000 : ℝ)|=(406981637/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s4_3 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (171943047/400000000 : ℝ)*x 0 + (1031307359/2500000000 : ℝ)*x 1 + (2239191137/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (171943047/400000000 : ℝ)^1103 ≤ (416302959313/1250000000000 : ℝ)^847 := by
    have hnat : (171943047 : ℕ)^1103*1250000000000^847 ≤ 416302959313^847*400000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171943047 400000000 416302959313 1250000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1031307359/2500000000 : ℝ)^1103 ≤ (6313205191209/20000000000000 : ℝ)^847 := by
    have hnat : (1031307359 : ℕ)^1103*20000000000000^847 ≤ 6313205191209^847*2500000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031307359 2500000000 6313205191209 20000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2239191137/5000000000 : ℝ)^1103 ≤ (6861276811/19531250000 : ℝ)^847 := by
    have hnat : (2239191137 : ℕ)^1103*19531250000^847 ≤ 6861276811^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2239191137 5000000000 6861276811 19531250000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(171943047/400000000 : ℝ), (1031307359/2500000000 : ℝ), (2239191137/5000000000 : ℝ)] ![(416302959313/1250000000000 : ℝ), (6313205191209/20000000000000 : ℝ), (6861276811/19531250000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(171943047/400000000 : ℝ)|^1103 ≤ (416302959313/1250000000000 : ℝ)^847
        have hw : |(171943047/400000000 : ℝ)|=(171943047/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1031307359/2500000000 : ℝ)|^1103 ≤ (6313205191209/20000000000000 : ℝ)^847
        have hw : |(1031307359/2500000000 : ℝ)|=(1031307359/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2239191137/5000000000 : ℝ)|^1103 ≤ (6861276811/19531250000 : ℝ)^847
        have hw : |(2239191137/5000000000 : ℝ)|=(2239191137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s4_4 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-976249721/5000000000 : ℝ)*x 0 + (1049382559/2000000000 : ℝ)*x 1 + (2703801437/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (976249721/5000000000 : ℝ)^1103 ≤ (2383454332327/20000000000000 : ℝ)^847 := by
    have hnat : (976249721 : ℕ)^1103*20000000000000^847 ≤ 2383454332327^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      976249721 5000000000 2383454332327 20000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049382559/2000000000 : ℝ)^1103 ≤ (21588212757359/50000000000000 : ℝ)^847 := by
    have hnat : (1049382559 : ℕ)^1103*50000000000000^847 ≤ 21588212757359^847*2000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049382559 2000000000 21588212757359 50000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703801437/5000000000 : ℝ)^1103 ≤ (5613287851483/12500000000000 : ℝ)^847 := by
    have hnat : (2703801437 : ℕ)^1103*12500000000000^847 ≤ 5613287851483^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703801437 5000000000 5613287851483 12500000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-976249721/5000000000 : ℝ), (1049382559/2000000000 : ℝ), (2703801437/5000000000 : ℝ)] ![(2383454332327/20000000000000 : ℝ), (21588212757359/50000000000000 : ℝ), (5613287851483/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-976249721/5000000000 : ℝ)|^1103 ≤ (2383454332327/20000000000000 : ℝ)^847
        have hw : |(-976249721/5000000000 : ℝ)|=(976249721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049382559/2000000000 : ℝ)|^1103 ≤ (21588212757359/50000000000000 : ℝ)^847
        have hw : |(1049382559/2000000000 : ℝ)|=(1049382559/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703801437/5000000000 : ℝ)|^1103 ≤ (5613287851483/12500000000000 : ℝ)^847
        have hw : |(2703801437/5000000000 : ℝ)|=(2703801437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s4_5 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (663119831/1250000000 : ℝ)*x 0 + (-936812487/5000000000 : ℝ)*x 1 + (168987589/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663119831/1250000000 : ℝ)^1103 ≤ (21899742667607/50000000000000 : ℝ)^847 := by
    have hnat : (663119831 : ℕ)^1103*50000000000000^847 ≤ 21899742667607^847*1250000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663119831 1250000000 21899742667607 50000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (936812487/5000000000 : ℝ)^1103 ≤ (352944128733/3125000000000 : ℝ)^847 := by
    have hnat : (936812487 : ℕ)^1103*3125000000000^847 ≤ 352944128733^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      936812487 5000000000 352944128733 3125000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168987589/312500000 : ℝ)^1103 ≤ (22453151265347/50000000000000 : ℝ)^847 := by
    have hnat : (168987589 : ℕ)^1103*50000000000000^847 ≤ 22453151265347^847*312500000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168987589 312500000 22453151265347 50000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663119831/1250000000 : ℝ), (-936812487/5000000000 : ℝ), (168987589/312500000 : ℝ)] ![(21899742667607/50000000000000 : ℝ), (352944128733/3125000000000 : ℝ), (22453151265347/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663119831/1250000000 : ℝ)|^1103 ≤ (21899742667607/50000000000000 : ℝ)^847
        have hw : |(663119831/1250000000 : ℝ)|=(663119831/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-936812487/5000000000 : ℝ)|^1103 ≤ (352944128733/3125000000000 : ℝ)^847
        have hw : |(-936812487/5000000000 : ℝ)|=(936812487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(168987589/312500000 : ℝ)|^1103 ≤ (22453151265347/50000000000000 : ℝ)^847
        have hw : |(168987589/312500000 : ℝ)|=(168987589/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s4_6 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2652479361/5000000000 : ℝ)*x 0 + (1081520563/2000000000 : ℝ)*x 1 + (-1873624919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652479361/5000000000 : ℝ)^1103 ≤ (43799486130843/100000000000000 : ℝ)^847 := by
    have hnat : (2652479361 : ℕ)^1103*100000000000000^847 ≤ 43799486130843^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652479361 5000000000 43799486130843 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081520563/2000000000 : ℝ)^1103 ≤ (22453151086913/50000000000000 : ℝ)^847 := by
    have hnat : (1081520563 : ℕ)^1103*50000000000000^847 ≤ 22453151086913^847*2000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081520563 2000000000 22453151086913 50000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1873624919/10000000000 : ℝ)^1103 ≤ (11294211687711/100000000000000 : ℝ)^847 := by
    have hnat : (1873624919 : ℕ)^1103*100000000000000^847 ≤ 11294211687711^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1873624919 10000000000 11294211687711 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652479361/5000000000 : ℝ), (1081520563/2000000000 : ℝ), (-1873624919/10000000000 : ℝ)] ![(43799486130843/100000000000000 : ℝ), (22453151086913/50000000000000 : ℝ), (11294211687711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652479361/5000000000 : ℝ)|^1103 ≤ (43799486130843/100000000000000 : ℝ)^847
        have hw : |(2652479361/5000000000 : ℝ)|=(2652479361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081520563/2000000000 : ℝ)|^1103 ≤ (22453151086913/50000000000000 : ℝ)^847
        have hw : |(1081520563/2000000000 : ℝ)|=(1081520563/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1873624919/10000000000 : ℝ)|^1103 ≤ (11294211687711/100000000000000 : ℝ)^847
        have hw : |(-1873624919/10000000000 : ℝ)|=(1873624919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s4_7 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (537325179/1250000000 : ℝ)*x 0 + (4477088093/10000000000 : ℝ)*x 1 + (4126530457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537325179/1250000000 : ℝ)^1103 ≤ (2081530723387/6250000000000 : ℝ)^847 := by
    have hnat : (537325179 : ℕ)^1103*6250000000000^847 ≤ 2081530723387^847*1250000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537325179 1250000000 2081530723387 6250000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4477088093/10000000000 : ℝ)^1103 ≤ (35116517563381/100000000000000 : ℝ)^847 := by
    have hnat : (4477088093 : ℕ)^1103*100000000000000^847 ≤ 35116517563381^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4477088093 10000000000 35116517563381 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4126530457/10000000000 : ℝ)^1103 ≤ (631579816963/2000000000000 : ℝ)^847 := by
    have hnat : (4126530457 : ℕ)^1103*2000000000000^847 ≤ 631579816963^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4126530457 10000000000 631579816963 2000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537325179/1250000000 : ℝ), (4477088093/10000000000 : ℝ), (4126530457/10000000000 : ℝ)] ![(2081530723387/6250000000000 : ℝ), (35116517563381/100000000000000 : ℝ), (631579816963/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537325179/1250000000 : ℝ)|^1103 ≤ (2081530723387/6250000000000 : ℝ)^847
        have hw : |(537325179/1250000000 : ℝ)|=(537325179/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4477088093/10000000000 : ℝ)|^1103 ≤ (35116517563381/100000000000000 : ℝ)^847
        have hw : |(4477088093/10000000000 : ℝ)|=(4477088093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4126530457/10000000000 : ℝ)|^1103 ≤ (631579816963/2000000000000 : ℝ)^847
        have hw : |(4126530457/10000000000 : ℝ)|=(4126530457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1452_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9942431/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1867/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11229/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11363/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14793/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1867/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11229/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1867/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11229/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1867/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11229/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1867/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11229/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1867/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11229/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1867/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11229/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11229/100000 : ℝ) ^ (4411/1024 : ℝ) ≤ (8113961110643853/100000000000000000000 : ℝ) := by
    have hpowers : (11229/100000 : ℝ)^4411 ≤ (8113961110643853/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11229 : ℕ)^4411*100000000000000000000^1024 ≤ 8113961110643853^1024*100000^4411 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11229 100000 8113961110643853 100000000000000000000 4411 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11229/100000 : ℝ)) (X := (8113961110643853/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4411 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1867/12500 : ℝ) ^ (4411/1024 : ℝ) ≤ (2772793320087851/10000000000000000000 : ℝ) := by
    have hpowers : (1867/12500 : ℝ)^4411 ≤ (2772793320087851/10000000000000000000 : ℝ)^1024 := by
      have hnat : (1867 : ℕ)^4411*10000000000000000000^1024 ≤ 2772793320087851^1024*12500^4411 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1867 12500 2772793320087851 10000000000000000000 4411 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1867/12500 : ℝ)) (X := (2772793320087851/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4411 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008113961110643853/50000000000000000000 : ℝ) ≤ (10000376702723537/10000000000000000 : ℝ) ^ (4411/1024 : ℝ) := by
    have hpowers : (50008113961110643853/50000000000000000000 : ℝ)^1024 ≤ (10000376702723537/10000000000000000 : ℝ)^4411 := by
      have hnat : (50008113961110643853 : ℕ)^1024*10000000000000000^4411 ≤ 10000376702723537^4411*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008113961110643853 50000000000000000000 10000376702723537 10000000000000000 1024 4411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000376702723537/10000000000000000 : ℝ)) (X := (50008113961110643853/50000000000000000000 : ℝ)) (by norm_num) 4411 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100035841894311522363/100000000000000000000 : ℝ) ≤ (250020798600313/250000000000000 : ℝ) ^ (4411/1024 : ℝ) := by
    have hpowers : (100035841894311522363/100000000000000000000 : ℝ)^1024 ≤ (250020798600313/250000000000000 : ℝ)^4411 := by
      have hnat : (100035841894311522363 : ℕ)^1024*250000000000000^4411 ≤ 250020798600313^4411*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100035841894311522363 100000000000000000000 250020798600313 250000000000000 1024 4411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250020798600313/250000000000000 : ℝ)) (X := (100035841894311522363/100000000000000000000 : ℝ)) (by norm_num) 4411 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5002772793320087851/5000000000000000000 : ℝ) ≤ (10001287185301503/10000000000000000 : ℝ) ^ (4411/1024 : ℝ) := by
    have hpowers : (5002772793320087851/5000000000000000000 : ℝ)^1024 ≤ (10001287185301503/10000000000000000 : ℝ)^4411 := by
      have hnat : (5002772793320087851 : ℕ)^1024*10000000000000000^4411 ≤ 10001287185301503^4411*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002772793320087851 5000000000000000000 10001287185301503 10000000000000000 1024 4411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001287185301503/10000000000000000 : ℝ)) (X := (5002772793320087851/5000000000000000000 : ℝ)) (by norm_num) 4411 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8113961110643853/100000000000000000000 : ℝ) ≤ ((21994761203636897/22000000000000000 : ℝ)+2*(1350864359/1100000000000 : ℝ)*(11229/100000 : ℝ))^(4411/1024 : ℝ) := by
    rw [show (21994761203636897/22000000000000000 : ℝ)+2*(1350864359/1100000000000 : ℝ)*(11229/100000 : ℝ)=(10000376702723537/10000000000000000 : ℝ) by norm_num, show 1+2*(8113961110643853/100000000000000000000 : ℝ)=(50008113961110643853/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2772793320087851/10000000000000000000 : ℝ)+(8113961110643853/100000000000000000000 : ℝ) ≤ ((21994761203636897/22000000000000000 : ℝ)+(1350864359/1100000000000 : ℝ)*((1867/12500 : ℝ)+(11229/100000 : ℝ)))^(4411/1024 : ℝ) := by
    rw [show (21994761203636897/22000000000000000 : ℝ)+(1350864359/1100000000000 : ℝ)*((1867/12500 : ℝ)+(11229/100000 : ℝ))=(250020798600313/250000000000000 : ℝ) by norm_num, show 1+(2772793320087851/10000000000000000000 : ℝ)+(8113961110643853/100000000000000000000 : ℝ)=(100035841894311522363/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2772793320087851/10000000000000000000 : ℝ) ≤ ((21994761203636897/22000000000000000 : ℝ)+2*(1350864359/1100000000000 : ℝ)*(1867/12500 : ℝ))^(4411/1024 : ℝ) := by
    rw [show (21994761203636897/22000000000000000 : ℝ)+2*(1350864359/1100000000000 : ℝ)*(1867/12500 : ℝ)=(10001287185301503/10000000000000000 : ℝ) by norm_num, show 1+2*(2772793320087851/10000000000000000000 : ℝ)=(5002772793320087851/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (21994761203636897/22000000000000000 : ℝ)*(X 1 0+X 2 0)+(1350864359/1100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4411/1024 : ℝ)) (lo := (11229/100000 : ℝ)) (hi := (1867/12500 : ℝ)) (c := (21994761203636897/22000000000000000 : ℝ)) (alpha := (1350864359/1100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (21994761203636897/22000000000000000 : ℝ)*(X 0 1+X 2 1)+(1350864359/1100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4411/1024 : ℝ)) (lo := (11229/100000 : ℝ)) (hi := (1867/12500 : ℝ)) (c := (21994761203636897/22000000000000000 : ℝ)) (alpha := (1350864359/1100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (21994761203636897/22000000000000000 : ℝ)*(X 0 2+X 1 2)+(1350864359/1100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4411/1024 : ℝ)) (lo := (11229/100000 : ℝ)) (hi := (1867/12500 : ℝ)) (c := (21994761203636897/22000000000000000 : ℝ)) (alpha := (1350864359/1100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-244060987/1250000000 : ℝ)*X 0 0+(2704099569/5000000000 : ℝ)*X 0 1+(5246319613/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673567881/5000000000 : ℝ)*X 1 0+(-2034908173/10000000000 : ℝ)*X 1 1+(5246319587/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((21388543/40000000 : ℝ)*X 2 0+(524631959/1000000000 : ℝ)*X 2 1+(-406981637/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((171943047/400000000 : ℝ)*X 0 0+(1031307359/2500000000 : ℝ)*X 0 1+(2239191137/5000000000 : ℝ)*X 0 2+(171943047/400000000 : ℝ)*X 1 0+(1031307359/2500000000 : ℝ)*X 1 1+(2239191137/5000000000 : ℝ)*X 1 2+(171943047/400000000 : ℝ)*X 2 0+(1031307359/2500000000 : ℝ)*X 2 1+(2239191137/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-976249721/5000000000 : ℝ)*X 0 0+(1049382559/2000000000 : ℝ)*X 0 1+(2703801437/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((663119831/1250000000 : ℝ)*X 1 0+(-936812487/5000000000 : ℝ)*X 1 1+(168987589/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652479361/5000000000 : ℝ)*X 2 0+(1081520563/2000000000 : ℝ)*X 2 1+(-1873624919/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((537325179/1250000000 : ℝ)*X 0 0+(4477088093/10000000000 : ℝ)*X 0 1+(4126530457/10000000000 : ℝ)*X 0 2+(537325179/1250000000 : ℝ)*X 1 0+(4477088093/10000000000 : ℝ)*X 1 1+(4126530457/10000000000 : ℝ)*X 1 2+(537325179/1250000000 : ℝ)*X 2 0+(4477088093/10000000000 : ℝ)*X 2 1+(4126530457/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10468400909944881676212189/1100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1733801987/100000000000000 : ℝ)*(base19) + (787834389/50000000000000 : ℝ)*(base23) + (19285743/25000000000000 : ℝ)*(lower2) + (10683081/4000000000000 : ℝ)*(upper3) + (144525187/100000000000000 : ℝ)*(upper5) + (3519207573473/78125000000 : ℝ)*(major0) + (3519207573473/78125000000 : ℝ)*(major1) + (4504585694045441/100000000000000 : ℝ)*(major2) + (6177469837472907/100000000000000 : ℝ)*(sp0) + (61775016505819/1000000000000 : ℝ)*(sp1) + (6177501808715109/100000000000000 : ℝ)*(sp2) + (353956274301021/12500000000000 : ℝ)*(sp3) + (1677345549/5000000000000 : ℝ)*(sp4) + (1093254659/6250000000000 : ℝ)*(sp7) + (353958460810339/12500000000000 : ℝ)*(f.failure) + (6177503384383887/100000000000000 : ℝ)*(f.sum) + (749569676919/110000000000000000000000000 : ℝ)*base65 + (38953706823623/13750000000000000000000000000 : ℝ)*base67 + (46781974709236577/2200000000000000000000000000000 : ℝ)*base69 + (37668479171123/13750000000000000000000000000 : ℝ)*base71 + (60185204879/110000000000000000000000000 : ℝ)*base73 + (28527928373436577/2200000000000000000000000000000 : ℝ)*base75 + (25534115140937/3437500000000000000000000000 : ℝ)*base77 + (45267661418437/3437500000000000000000000000 : ℝ)*base79 + (69048026367/11000000000000000000000000 : ℝ)*base81 + (405891/78125000000000000000 : ℝ)*base90 + (405891/78125000000000000000 : ℝ)*base92 + (1187141/78125000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (476811094385133630759/55000000000000000000000000 : ℝ) := by norm_num
    linear_combination (62305629/5000000000000 : ℝ)*(base19) + (383938217/25000000000000 : ℝ)*(base23) + (25808569/20000000000000 : ℝ)*(upper3) + (22818877/25000000000000 : ℝ)*(lower4) + (3226069/1562500000000 : ℝ)*(upper5) + (2268939511764199/50000000000000 : ℝ)*(major0) + (2268939511764199/50000000000000 : ℝ)*(major1) + (2268939511764199/50000000000000 : ℝ)*(major2) + (6619430287/25000000000000 : ℝ)*(sp1) + (7587155621/25000000000000 : ℝ)*(sp2) + (6223161255569817/100000000000000 : ℝ)*(sp4) + (6223133531736089/100000000000000 : ℝ)*(sp5) + (1244625874238893/20000000000000 : ℝ)*(sp6) + (356574562813819/12500000000000 : ℝ)*(sp7) + (356574562813819/12500000000000 : ℝ)*(f.failure) + (6223161255569817/100000000000000 : ℝ)*(f.sum) + (21768418273/3437500000000000000000000 : ℝ)*base66 + (13712738712770503/1100000000000000000000000000000 : ℝ)*base67 + (1615851194670503/1100000000000000000000000000000 : ℝ)*base69 + (12075537054329497/1100000000000000000000000000000 : ℝ)*base72 + (7642782011/1718750000000000000000000 : ℝ)*base73 + (9626647424329497/1100000000000000000000000000000 : ℝ)*base76 + (3784995235470503/1100000000000000000000000000000 : ℝ)*base77 + (6457930509229497/1100000000000000000000000000000 : ℝ)*base80 + (208931810487/55000000000000000000000000 : ℝ)*base81 + (316489/78125000000000000000 : ℝ)*base89 + (316489/78125000000000000000 : ℝ)*base91 + (316489/78125000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1452_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9942431/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1867/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11229/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11363/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14793/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1452_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1452_s5_0 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-488150967/2500000000 : ℝ)*x 0 + (2703591317/5000000000 : ℝ)*x 1 + (5247259419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (488150967/2500000000 : ℝ)^1103 ≤ (11918101684729/100000000000000 : ℝ)^847 := by
    have hnat : (488150967 : ℕ)^1103*100000000000000^847 ≤ 11918101684729^847*2500000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      488150967 2500000000 11918101684729 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703591317/5000000000 : ℝ)^1103 ≤ (5612719787947/12500000000000 : ℝ)^847 := by
    have hnat : (2703591317 : ℕ)^1103*12500000000000^847 ≤ 5612719787947^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703591317 5000000000 5612719787947 12500000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247259419/10000000000 : ℝ)^1103 ≤ (43180139993709/100000000000000 : ℝ)^847 := by
    have hnat : (5247259419 : ℕ)^1103*100000000000000^847 ≤ 43180139993709^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247259419 10000000000 43180139993709 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-488150967/2500000000 : ℝ), (2703591317/5000000000 : ℝ), (5247259419/10000000000 : ℝ)] ![(11918101684729/100000000000000 : ℝ), (5612719787947/12500000000000 : ℝ), (43180139993709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-488150967/2500000000 : ℝ)|^1103 ≤ (11918101684729/100000000000000 : ℝ)^847
        have hw : |(-488150967/2500000000 : ℝ)|=(488150967/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703591317/5000000000 : ℝ)|^1103 ≤ (5612719787947/12500000000000 : ℝ)^847
        have hw : |(2703591317/5000000000 : ℝ)|=(2703591317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247259419/10000000000 : ℝ)|^1103 ≤ (43180139993709/100000000000000 : ℝ)^847
        have hw : |(5247259419/10000000000 : ℝ)|=(5247259419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s5_1 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2673435831/5000000000 : ℝ)*x 0 + (-1017005211/5000000000 : ℝ)*x 1 + (5247259419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673435831/5000000000 : ℝ)^1103 ≤ (44250660593621/100000000000000 : ℝ)^847 := by
    have hnat : (2673435831 : ℕ)^1103*100000000000000^847 ≤ 44250660593621^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673435831 5000000000 44250660593621 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1017005211/5000000000 : ℝ)^1103 ≤ (2513839880033/20000000000000 : ℝ)^847 := by
    have hnat : (1017005211 : ℕ)^1103*20000000000000^847 ≤ 2513839880033^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1017005211 5000000000 2513839880033 20000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247259419/10000000000 : ℝ)^1103 ≤ (43180139993709/100000000000000 : ℝ)^847 := by
    have hnat : (5247259419 : ℕ)^1103*100000000000000^847 ≤ 43180139993709^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247259419 10000000000 43180139993709 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673435831/5000000000 : ℝ), (-1017005211/5000000000 : ℝ), (5247259419/10000000000 : ℝ)] ![(44250660593621/100000000000000 : ℝ), (2513839880033/20000000000000 : ℝ), (43180139993709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673435831/5000000000 : ℝ)|^1103 ≤ (44250660593621/100000000000000 : ℝ)^847
        have hw : |(2673435831/5000000000 : ℝ)|=(2673435831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1017005211/5000000000 : ℝ)|^1103 ≤ (2513839880033/20000000000000 : ℝ)^847
        have hw : |(-1017005211/5000000000 : ℝ)|=(1017005211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247259419/10000000000 : ℝ)|^1103 ≤ (43180139993709/100000000000000 : ℝ)^847
        have hw : |(5247259419/10000000000 : ℝ)|=(5247259419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s5_2 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2673435831/5000000000 : ℝ)*x 0 + (5247259419/10000000000 : ℝ)*x 1 + (-1017005211/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673435831/5000000000 : ℝ)^1103 ≤ (44250660593621/100000000000000 : ℝ)^847 := by
    have hnat : (2673435831 : ℕ)^1103*100000000000000^847 ≤ 44250660593621^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673435831 5000000000 44250660593621 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247259419/10000000000 : ℝ)^1103 ≤ (43180139993709/100000000000000 : ℝ)^847 := by
    have hnat : (5247259419 : ℕ)^1103*100000000000000^847 ≤ 43180139993709^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247259419 10000000000 43180139993709 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1017005211/5000000000 : ℝ)^1103 ≤ (2513839880033/20000000000000 : ℝ)^847 := by
    have hnat : (1017005211 : ℕ)^1103*20000000000000^847 ≤ 2513839880033^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1017005211 5000000000 2513839880033 20000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673435831/5000000000 : ℝ), (5247259419/10000000000 : ℝ), (-1017005211/5000000000 : ℝ)] ![(44250660593621/100000000000000 : ℝ), (43180139993709/100000000000000 : ℝ), (2513839880033/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673435831/5000000000 : ℝ)|^1103 ≤ (44250660593621/100000000000000 : ℝ)^847
        have hw : |(2673435831/5000000000 : ℝ)|=(2673435831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247259419/10000000000 : ℝ)|^1103 ≤ (43180139993709/100000000000000 : ℝ)^847
        have hw : |(5247259419/10000000000 : ℝ)|=(5247259419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1017005211/5000000000 : ℝ)|^1103 ≤ (2513839880033/20000000000000 : ℝ)^847
        have hw : |(-1017005211/5000000000 : ℝ)|=(1017005211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s5_3 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (214932267/500000000 : ℝ)*x 0 + (33018841/80000000 : ℝ)*x 1 + (55953001/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214932267/500000000 : ℝ)^1103 ≤ (3330493458269/10000000000000 : ℝ)^847 := by
    have hnat : (214932267 : ℕ)^1103*10000000000000^847 ≤ 3330493458269^847*500000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214932267 500000000 3330493458269 10000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33018841/80000000 : ℝ)^1103 ≤ (394840118033/1250000000000 : ℝ)^847 := by
    have hnat : (33018841 : ℕ)^1103*1250000000000^847 ≤ 394840118033^847*80000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33018841 80000000 394840118033 1250000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (55953001/125000000 : ℝ)^1103 ≤ (17553927983109/50000000000000 : ℝ)^847 := by
    have hnat : (55953001 : ℕ)^1103*50000000000000^847 ≤ 17553927983109^847*125000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55953001 125000000 17553927983109 50000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214932267/500000000 : ℝ), (33018841/80000000 : ℝ), (55953001/125000000 : ℝ)] ![(3330493458269/10000000000000 : ℝ), (394840118033/1250000000000 : ℝ), (17553927983109/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214932267/500000000 : ℝ)|^1103 ≤ (3330493458269/10000000000000 : ℝ)^847
        have hw : |(214932267/500000000 : ℝ)|=(214932267/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(33018841/80000000 : ℝ)|^1103 ≤ (394840118033/1250000000000 : ℝ)^847
        have hw : |(33018841/80000000 : ℝ)|=(33018841/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(55953001/125000000 : ℝ)|^1103 ≤ (17553927983109/50000000000000 : ℝ)^847
        have hw : |(55953001/125000000 : ℝ)|=(55953001/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s5_4 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-488153771/2500000000 : ℝ)*x 0 + (5247838499/10000000000 : ℝ)*x 1 + (2703300261/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (488153771/2500000000 : ℝ)^1103 ≤ (5959095417577/50000000000000 : ℝ)^847 := by
    have hnat : (488153771 : ℕ)^1103*50000000000000^847 ≤ 5959095417577^847*2500000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      488153771 2500000000 5959095417577 50000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247838499/10000000000 : ℝ)^1103 ≤ (43186345674333/100000000000000 : ℝ)^847 := by
    have hnat : (5247838499 : ℕ)^1103*100000000000000^847 ≤ 43186345674333^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247838499 10000000000 43186345674333 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703300261/5000000000 : ℝ)^1103 ≤ (8979092695029/20000000000000 : ℝ)^847 := by
    have hnat : (2703300261 : ℕ)^1103*20000000000000^847 ≤ 8979092695029^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703300261 5000000000 8979092695029 20000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-488153771/2500000000 : ℝ), (5247838499/10000000000 : ℝ), (2703300261/5000000000 : ℝ)] ![(5959095417577/50000000000000 : ℝ), (43186345674333/100000000000000 : ℝ), (8979092695029/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-488153771/2500000000 : ℝ)|^1103 ≤ (5959095417577/50000000000000 : ℝ)^847
        have hw : |(-488153771/2500000000 : ℝ)|=(488153771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247838499/10000000000 : ℝ)|^1103 ≤ (43186345674333/100000000000000 : ℝ)^847
        have hw : |(5247838499/10000000000 : ℝ)|=(5247838499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703300261/5000000000 : ℝ)|^1103 ≤ (8979092695029/20000000000000 : ℝ)^847
        have hw : |(2703300261/5000000000 : ℝ)|=(2703300261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s5_5 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2652601949/5000000000 : ℝ)*x 0 + (-1874669521/10000000000 : ℝ)*x 1 + (1081320139/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652601949/5000000000 : ℝ)^1103 ≤ (43802122220013/100000000000000 : ℝ)^847 := by
    have hnat : (2652601949 : ℕ)^1103*100000000000000^847 ≤ 43802122220013^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652601949 5000000000 43802122220013 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1874669521/10000000000 : ℝ)^1103 ≤ (2825603105827/25000000000000 : ℝ)^847 := by
    have hnat : (1874669521 : ℕ)^1103*25000000000000^847 ≤ 2825603105827^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1874669521 10000000000 2825603105827 25000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081320139/2000000000 : ℝ)^1103 ≤ (22447732672949/50000000000000 : ℝ)^847 := by
    have hnat : (1081320139 : ℕ)^1103*50000000000000^847 ≤ 22447732672949^847*2000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081320139 2000000000 22447732672949 50000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652601949/5000000000 : ℝ), (-1874669521/10000000000 : ℝ), (1081320139/2000000000 : ℝ)] ![(43802122220013/100000000000000 : ℝ), (2825603105827/25000000000000 : ℝ), (22447732672949/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652601949/5000000000 : ℝ)|^1103 ≤ (43802122220013/100000000000000 : ℝ)^847
        have hw : |(2652601949/5000000000 : ℝ)|=(2652601949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1874669521/10000000000 : ℝ)|^1103 ≤ (2825603105827/25000000000000 : ℝ)^847
        have hw : |(-1874669521/10000000000 : ℝ)|=(1874669521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081320139/2000000000 : ℝ)|^1103 ≤ (22447732672949/50000000000000 : ℝ)^847
        have hw : |(1081320139/2000000000 : ℝ)|=(1081320139/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s5_6 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305204337/10000000000 : ℝ)*x 0 + (1081320139/2000000000 : ℝ)*x 1 + (-1874668919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305204337/10000000000 : ℝ)^1103 ≤ (43802126940097/100000000000000 : ℝ)^847 := by
    have hnat : (5305204337 : ℕ)^1103*100000000000000^847 ≤ 43802126940097^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305204337 10000000000 43802126940097 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081320139/2000000000 : ℝ)^1103 ≤ (22447732672949/50000000000000 : ℝ)^847 := by
    have hnat : (1081320139 : ℕ)^1103*50000000000000^847 ≤ 22447732672949^847*2000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081320139 2000000000 22447732672949 50000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1874668919/10000000000 : ℝ)^1103 ≤ (5651203848429/50000000000000 : ℝ)^847 := by
    have hnat : (1874668919 : ℕ)^1103*50000000000000^847 ≤ 5651203848429^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1874668919 10000000000 5651203848429 50000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305204337/10000000000 : ℝ), (1081320139/2000000000 : ℝ), (-1874668919/10000000000 : ℝ)] ![(43802126940097/100000000000000 : ℝ), (22447732672949/50000000000000 : ℝ), (5651203848429/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305204337/10000000000 : ℝ)|^1103 ≤ (43802126940097/100000000000000 : ℝ)^847
        have hw : |(5305204337/10000000000 : ℝ)|=(5305204337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081320139/2000000000 : ℝ)|^1103 ≤ (22447732672949/50000000000000 : ℝ)^847
        have hw : |(1081320139/2000000000 : ℝ)|=(1081320139/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1874668919/10000000000 : ℝ)|^1103 ≤ (5651203848429/50000000000000 : ℝ)^847
        have hw : |(-1874668919/10000000000 : ℝ)|=(1874668919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s5_7 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1074667469/2500000000 : ℝ)*x 0 + (2237488391/5000000000 : ℝ)*x 1 + (1032156209/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074667469/2500000000 : ℝ)^1103 ≤ (33305182138549/100000000000000 : ℝ)^847 := by
    have hnat : (1074667469 : ℕ)^1103*100000000000000^847 ≤ 33305182138549^847*2500000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074667469 2500000000 33305182138549 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2237488391/5000000000 : ℝ)^1103 ≤ (7018990714307/20000000000000 : ℝ)^847 := by
    have hnat : (2237488391 : ℕ)^1103*20000000000000^847 ≤ 7018990714307^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237488391 5000000000 7018990714307 20000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1032156209/2500000000 : ℝ)^1103 ≤ (31599864280779/100000000000000 : ℝ)^847 := by
    have hnat : (1032156209 : ℕ)^1103*100000000000000^847 ≤ 31599864280779^847*2500000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032156209 2500000000 31599864280779 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074667469/2500000000 : ℝ), (2237488391/5000000000 : ℝ), (1032156209/2500000000 : ℝ)] ![(33305182138549/100000000000000 : ℝ), (7018990714307/20000000000000 : ℝ), (31599864280779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074667469/2500000000 : ℝ)|^1103 ≤ (33305182138549/100000000000000 : ℝ)^847
        have hw : |(1074667469/2500000000 : ℝ)|=(1074667469/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2237488391/5000000000 : ℝ)|^1103 ≤ (7018990714307/20000000000000 : ℝ)^847
        have hw : |(2237488391/5000000000 : ℝ)|=(2237488391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1032156209/2500000000 : ℝ)|^1103 ≤ (31599864280779/100000000000000 : ℝ)^847
        have hw : |(1032156209/2500000000 : ℝ)|=(1032156209/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1452_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9942431/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14793/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11363/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11383/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3693/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14793/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11363/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14793/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11363/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14793/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11363/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14793/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11363/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14793/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11363/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14793/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11363/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11363/100000 : ℝ) ^ (4411/1024 : ℝ) ≤ (1067420292582543/12500000000000000000 : ℝ) := by
    have hpowers : (11363/100000 : ℝ)^4411 ≤ (1067420292582543/12500000000000000000 : ℝ)^1024 := by
      have hnat : (11363 : ℕ)^4411*12500000000000000000^1024 ≤ 1067420292582543^1024*100000^4411 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11363 100000 1067420292582543 12500000000000000000 4411 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11363/100000 : ℝ)) (X := (1067420292582543/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4411 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14793/100000 : ℝ) ^ (4411/1024 : ℝ) ≤ (13301177021927331/50000000000000000000 : ℝ) := by
    have hpowers : (14793/100000 : ℝ)^4411 ≤ (13301177021927331/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14793 : ℕ)^4411*50000000000000000000^1024 ≤ 13301177021927331^1024*100000^4411 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14793 100000 13301177021927331 50000000000000000000 4411 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14793/100000 : ℝ)) (X := (13301177021927331/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4411 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251067420292582543/6250000000000000000 : ℝ) ≤ (10000396451314099/10000000000000000 : ℝ) ^ (4411/1024 : ℝ) := by
    have hpowers : (6251067420292582543/6250000000000000000 : ℝ)^1024 ≤ (10000396451314099/10000000000000000 : ℝ)^4411 := by
      have hnat : (6251067420292582543 : ℕ)^1024*10000000000000000^4411 ≤ 10000396451314099^4411*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251067420292582543 6250000000000000000 10000396451314099 10000000000000000 1024 4411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000396451314099/10000000000000000 : ℝ)) (X := (6251067420292582543/6250000000000000000 : ℝ)) (by norm_num) 4411 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50017570858192257503/50000000000000000000 : ℝ) ≤ (125010196175337/125000000000000 : ℝ) ^ (4411/1024 : ℝ) := by
    have hpowers : (50017570858192257503/50000000000000000000 : ℝ)^1024 ≤ (125010196175337/125000000000000 : ℝ)^4411 := by
      have hnat : (50017570858192257503 : ℕ)^1024*125000000000000^4411 ≤ 125010196175337^4411*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017570858192257503 50000000000000000000 125010196175337 125000000000000 1024 4411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125010196175337/125000000000000 : ℝ)) (X := (50017570858192257503/50000000000000000000 : ℝ)) (by norm_num) 4411 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013301177021927331/25000000000000000000 : ℝ) ≤ (10001234936739821/10000000000000000 : ℝ) ^ (4411/1024 : ℝ) := by
    have hpowers : (25013301177021927331/25000000000000000000 : ℝ)^1024 ≤ (10001234936739821/10000000000000000 : ℝ)^4411 := by
      have hnat : (25013301177021927331 : ℕ)^1024*10000000000000000^4411 ≤ 10001234936739821^4411*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013301177021927331 25000000000000000000 10001234936739821 10000000000000000 1024 4411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001234936739821/10000000000000000 : ℝ)) (X := (25013301177021927331/25000000000000000000 : ℝ)) (by norm_num) 4411 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1067420292582543/12500000000000000000 : ℝ) ≤ ((1224708289932674303/1225000000000000000 : ℝ)+2*(59891816123/49000000000000 : ℝ)*(11363/100000 : ℝ))^(4411/1024 : ℝ) := by
    rw [show (1224708289932674303/1225000000000000000 : ℝ)+2*(59891816123/49000000000000 : ℝ)*(11363/100000 : ℝ)=(10000396451314099/10000000000000000 : ℝ) by norm_num, show 1+2*(1067420292582543/12500000000000000000 : ℝ)=(6251067420292582543/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13301177021927331/50000000000000000000 : ℝ)+(1067420292582543/12500000000000000000 : ℝ) ≤ ((1224708289932674303/1225000000000000000 : ℝ)+(59891816123/49000000000000 : ℝ)*((14793/100000 : ℝ)+(11363/100000 : ℝ)))^(4411/1024 : ℝ) := by
    rw [show (1224708289932674303/1225000000000000000 : ℝ)+(59891816123/49000000000000 : ℝ)*((14793/100000 : ℝ)+(11363/100000 : ℝ))=(125010196175337/125000000000000 : ℝ) by norm_num, show 1+(13301177021927331/50000000000000000000 : ℝ)+(1067420292582543/12500000000000000000 : ℝ)=(50017570858192257503/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13301177021927331/50000000000000000000 : ℝ) ≤ ((1224708289932674303/1225000000000000000 : ℝ)+2*(59891816123/49000000000000 : ℝ)*(14793/100000 : ℝ))^(4411/1024 : ℝ) := by
    rw [show (1224708289932674303/1225000000000000000 : ℝ)+2*(59891816123/49000000000000 : ℝ)*(14793/100000 : ℝ)=(10001234936739821/10000000000000000 : ℝ) by norm_num, show 1+2*(13301177021927331/50000000000000000000 : ℝ)=(25013301177021927331/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1224708289932674303/1225000000000000000 : ℝ)*(X 1 0+X 2 0)+(59891816123/49000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4411/1024 : ℝ)) (lo := (11363/100000 : ℝ)) (hi := (14793/100000 : ℝ)) (c := (1224708289932674303/1225000000000000000 : ℝ)) (alpha := (59891816123/49000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1224708289932674303/1225000000000000000 : ℝ)*(X 0 1+X 2 1)+(59891816123/49000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4411/1024 : ℝ)) (lo := (11363/100000 : ℝ)) (hi := (14793/100000 : ℝ)) (c := (1224708289932674303/1225000000000000000 : ℝ)) (alpha := (59891816123/49000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1224708289932674303/1225000000000000000 : ℝ)*(X 0 2+X 1 2)+(59891816123/49000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4411/1024 : ℝ)) (lo := (11363/100000 : ℝ)) (hi := (14793/100000 : ℝ)) (c := (1224708289932674303/1225000000000000000 : ℝ)) (alpha := (59891816123/49000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-488150967/2500000000 : ℝ)*X 0 0+(2703591317/5000000000 : ℝ)*X 0 1+(5247259419/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673435831/5000000000 : ℝ)*X 1 0+(-1017005211/5000000000 : ℝ)*X 1 1+(5247259419/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673435831/5000000000 : ℝ)*X 2 0+(5247259419/10000000000 : ℝ)*X 2 1+(-1017005211/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((214932267/500000000 : ℝ)*X 0 0+(33018841/80000000 : ℝ)*X 0 1+(55953001/125000000 : ℝ)*X 0 2+(214932267/500000000 : ℝ)*X 1 0+(33018841/80000000 : ℝ)*X 1 1+(55953001/125000000 : ℝ)*X 1 2+(214932267/500000000 : ℝ)*X 2 0+(33018841/80000000 : ℝ)*X 2 1+(55953001/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-488153771/2500000000 : ℝ)*X 0 0+(5247838499/10000000000 : ℝ)*X 0 1+(2703300261/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652601949/5000000000 : ℝ)*X 1 0+(-1874669521/10000000000 : ℝ)*X 1 1+(1081320139/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305204337/10000000000 : ℝ)*X 2 0+(1081320139/2000000000 : ℝ)*X 2 1+(-1874668919/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1074667469/2500000000 : ℝ)*X 0 0+(2237488391/5000000000 : ℝ)*X 0 1+(1032156209/2500000000 : ℝ)*X 0 2+(1074667469/2500000000 : ℝ)*X 1 0+(2237488391/5000000000 : ℝ)*X 1 1+(1032156209/2500000000 : ℝ)*X 1 2+(1074667469/2500000000 : ℝ)*X 2 0+(2237488391/5000000000 : ℝ)*X 2 1+(1032156209/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22262204358520527164436039/2187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1838138337/100000000000000 : ℝ)*(base19) + (1713148349/100000000000000 : ℝ)*(base23) + (33415271/50000000000000 : ℝ)*(lower2) + (126691993/50000000000000 : ℝ)*(upper3) + (20342703/12500000000000 : ℝ)*(upper5) + (1139923959949753/25000000000000 : ℝ)*(major0) + (1139923959949753/25000000000000 : ℝ)*(major1) + (4559695839799013/100000000000000 : ℝ)*(major2) + (6253041449877929/100000000000000 : ℝ)*(sp0) + (1250615707350917/20000000000000 : ℝ)*(sp1) + (6253078661744573/100000000000000 : ℝ)*(sp2) + (89571614261683/3125000000000 : ℝ)*(sp3) + (38925014993/100000000000000 : ℝ)*(sp4) + (19309097649/100000000000000 : ℝ)*(sp7) + (1433155482735753/50000000000000 : ℝ)*(f.failure) + (3126540187446461/50000000000000 : ℝ)*(f.sum) + (65834360371/28000000000000000000000000 : ℝ)*base66 + (348564456748665909/30625000000000000000000000000000 : ℝ)*base67 + (940096630650737061/122500000000000000000000000000000 : ℝ)*base70 + (108417759044290909/30625000000000000000000000000000 : ℝ)*base71 + (908800453/1120000000000000000000000 : ℝ)*base73 + (961642795894262939/122500000000000000000000000000000 : ℝ)*base75 + (41128491521477841/30625000000000000000000000000000 : ℝ)*base78 + (283262603456647159/30625000000000000000000000000000 : ℝ)*base79 + (225223939457/76562500000000000000000000 : ℝ)*base82 + (2935543/312500000000000000000 : ℝ)*base89 + (2935543/312500000000000000000 : ℝ)*base91 + (189457/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (43232554234440849707250837/3828125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (364442177/25000000000000 : ℝ)*(base19) + (602156473/25000000000000 : ℝ)*(base23) + (289598187/100000000000000 : ℝ)*(upper3) + (93564151/100000000000000 : ℝ)*(lower4) + (237794363/100000000000000 : ℝ)*(upper5) + (574123552548207/12500000000000 : ℝ)*(major0) + (574123552548207/12500000000000 : ℝ)*(major1) + (574123552548207/12500000000000 : ℝ)*(major2) + (30687675919/100000000000000 : ℝ)*(sp1) + (62936413941/100000000000000 : ℝ)*(sp2) + (15746842883989/250000000000 : ℝ)*(sp4) + (1574676252037743/25000000000000 : ℝ)*(sp5) + (787333976069471/12500000000000 : ℝ)*(sp6) + (288723931072897/10000000000000 : ℝ)*(sp7) + (288723931072897/10000000000000 : ℝ)*(f.failure) + (15746842883989/250000000000 : ℝ)*(f.sum) + (406547412211/306250000000000000000000000 : ℝ)*base65 + (54470893105399721/15312500000000000000000000000000 : ℝ)*base67 + (2924069411649721/15312500000000000000000000000000 : ℝ)*base69 + (98346947578524721/15312500000000000000000000000000 : ℝ)*base71 + (370903518047/612500000000000000000000000 : ℝ)*base73 + (248912439208837221/15312500000000000000000000000000 : ℝ)*base75 + (66519823257725279/15312500000000000000000000000000 : ℝ)*base78 + (111843543945712221/15312500000000000000000000000000 : ℝ)*base79 + (2396190679497/612500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (607393/62500000000000000000 : ℝ)*base90 + (607393/62500000000000000000 : ℝ)*base92 + (607393/62500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1452_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9942431/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14793/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11363/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11383/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3693/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1452_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1452_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9942431/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3933/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10487/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11383/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3693/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1452_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1452_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1452_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9942431/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3933/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10487/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11383/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3693/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1452_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
