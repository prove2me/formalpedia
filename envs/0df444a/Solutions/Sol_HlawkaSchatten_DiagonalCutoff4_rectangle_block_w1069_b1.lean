-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1069_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:09:06.571886+00:00
-- url     : https://prove2.me/submissions/8a5ccf14-0d4f-4218-bd1e-fdc14358dbb9

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
theorem support_rectangle_w1069_s3_0 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2197591633/10000000000 : ℝ)*x 0 + (2718591053/5000000000 : ℝ)*x 1 + (65308803/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2197591633/10000000000 : ℝ)^4131 ≤ (1333727034979/10000000000000 : ℝ)^3107 := by
    have hnat : (2197591633 : ℕ)^4131*10000000000000^3107 ≤ 1333727034979^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2197591633 10000000000 1333727034979 10000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2718591053/5000000000 : ℝ)^4131 ≤ (44479391057939/100000000000000 : ℝ)^3107 := by
    have hnat : (2718591053 : ℕ)^4131*100000000000000^3107 ≤ 44479391057939^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718591053 5000000000 44479391057939 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65308803/125000000 : ℝ)^4131 ≤ (5272917322523/12500000000000 : ℝ)^3107 := by
    have hnat : (65308803 : ℕ)^4131*12500000000000^3107 ≤ 5272917322523^3107*125000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65308803 125000000 5272917322523 12500000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2197591633/10000000000 : ℝ), (2718591053/5000000000 : ℝ), (65308803/125000000 : ℝ)] ![(1333727034979/10000000000000 : ℝ), (44479391057939/100000000000000 : ℝ), (5272917322523/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2197591633/10000000000 : ℝ)|^4131 ≤ (1333727034979/10000000000000 : ℝ)^3107
        have hw : |(-2197591633/10000000000 : ℝ)|=(2197591633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2718591053/5000000000 : ℝ)|^4131 ≤ (44479391057939/100000000000000 : ℝ)^3107
        have hw : |(2718591053/5000000000 : ℝ)|=(2718591053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(65308803/125000000 : ℝ)|^4131 ≤ (5272917322523/12500000000000 : ℝ)^3107
        have hw : |(65308803/125000000 : ℝ)|=(65308803/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s3_1 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338903383/2500000000 : ℝ)*x 0 + (-576597231/2500000000 : ℝ)*x 1 + (5224704343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338903383/2500000000 : ℝ)^4131 ≤ (43594391289777/100000000000000 : ℝ)^3107 := by
    have hnat : (1338903383 : ℕ)^4131*100000000000000^3107 ≤ 43594391289777^3107*2500000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338903383 2500000000 43594391289777 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (576597231/2500000000 : ℝ)^4131 ≤ (2844453802817/20000000000000 : ℝ)^3107 := by
    have hnat : (576597231 : ℕ)^4131*20000000000000^3107 ≤ 2844453802817^3107*2500000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      576597231 2500000000 2844453802817 20000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5224704343/10000000000 : ℝ)^4131 ≤ (21091669842933/50000000000000 : ℝ)^3107 := by
    have hnat : (5224704343 : ℕ)^4131*50000000000000^3107 ≤ 21091669842933^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5224704343 10000000000 21091669842933 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338903383/2500000000 : ℝ), (-576597231/2500000000 : ℝ), (5224704343/10000000000 : ℝ)] ![(43594391289777/100000000000000 : ℝ), (2844453802817/20000000000000 : ℝ), (21091669842933/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338903383/2500000000 : ℝ)|^4131 ≤ (43594391289777/100000000000000 : ℝ)^3107
        have hw : |(1338903383/2500000000 : ℝ)|=(1338903383/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-576597231/2500000000 : ℝ)|^4131 ≤ (2844453802817/20000000000000 : ℝ)^3107
        have hw : |(-576597231/2500000000 : ℝ)|=(576597231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5224704343/10000000000 : ℝ)|^4131 ≤ (21091669842933/50000000000000 : ℝ)^3107
        have hw : |(5224704343/10000000000 : ℝ)|=(5224704343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s3_2 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338903381/2500000000 : ℝ)*x 0 + (5224704721/10000000000 : ℝ)*x 1 + (-2306388439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338903381/2500000000 : ℝ)^4131 ≤ (8718878240639/20000000000000 : ℝ)^3107 := by
    have hnat : (1338903381 : ℕ)^4131*20000000000000^3107 ≤ 8718878240639^3107*2500000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338903381 2500000000 8718878240639 20000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5224704721/10000000000 : ℝ)^4131 ≤ (21091671871807/50000000000000 : ℝ)^3107 := by
    have hnat : (5224704721 : ℕ)^4131*50000000000000^3107 ≤ 21091671871807^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5224704721 10000000000 21091671871807 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2306388439/10000000000 : ℝ)^4131 ≤ (14222265037667/100000000000000 : ℝ)^3107 := by
    have hnat : (2306388439 : ℕ)^4131*100000000000000^3107 ≤ 14222265037667^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2306388439 10000000000 14222265037667 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338903381/2500000000 : ℝ), (5224704721/10000000000 : ℝ), (-2306388439/10000000000 : ℝ)] ![(8718878240639/20000000000000 : ℝ), (21091671871807/50000000000000 : ℝ), (14222265037667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338903381/2500000000 : ℝ)|^4131 ≤ (8718878240639/20000000000000 : ℝ)^3107
        have hw : |(1338903381/2500000000 : ℝ)|=(1338903381/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5224704721/10000000000 : ℝ)|^4131 ≤ (21091671871807/50000000000000 : ℝ)^3107
        have hw : |(5224704721/10000000000 : ℝ)|=(5224704721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2306388439/10000000000 : ℝ)|^4131 ≤ (14222265037667/100000000000000 : ℝ)^3107
        have hw : |(-2306388439/10000000000 : ℝ)|=(2306388439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s3_3 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1093070623/2500000000 : ℝ)*x 0 + (2084481233/5000000000 : ℝ)*x 1 + (4585636049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093070623/2500000000 : ℝ)^4131 ≤ (1331537504477/4000000000000 : ℝ)^3107 := by
    have hnat : (1093070623 : ℕ)^4131*4000000000000^3107 ≤ 1331537504477^3107*2500000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093070623 2500000000 1331537504477 4000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2084481233/5000000000 : ℝ)^4131 ≤ (31246215755673/100000000000000 : ℝ)^3107 := by
    have hnat : (2084481233 : ℕ)^4131*100000000000000^3107 ≤ 31246215755673^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084481233 5000000000 31246215755673 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4585636049/10000000000 : ℝ)^4131 ≤ (17732673310837/50000000000000 : ℝ)^3107 := by
    have hnat : (4585636049 : ℕ)^4131*50000000000000^3107 ≤ 17732673310837^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4585636049 10000000000 17732673310837 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1093070623/2500000000 : ℝ), (2084481233/5000000000 : ℝ), (4585636049/10000000000 : ℝ)] ![(1331537504477/4000000000000 : ℝ), (31246215755673/100000000000000 : ℝ), (17732673310837/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1093070623/2500000000 : ℝ)|^4131 ≤ (1331537504477/4000000000000 : ℝ)^3107
        have hw : |(1093070623/2500000000 : ℝ)|=(1093070623/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2084481233/5000000000 : ℝ)|^4131 ≤ (31246215755673/100000000000000 : ℝ)^3107
        have hw : |(2084481233/5000000000 : ℝ)|=(2084481233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4585636049/10000000000 : ℝ)|^4131 ≤ (17732673310837/50000000000000 : ℝ)^3107
        have hw : |(4585636049/10000000000 : ℝ)|=(4585636049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s3_4 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-109880701/500000000 : ℝ)*x 0 + (5225572873/10000000000 : ℝ)*x 1 + (1087261631/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (109880701/500000000 : ℝ)^4131 ≤ (6668725498349/50000000000000 : ℝ)^3107 := by
    have hnat : (109880701 : ℕ)^4131*50000000000000^3107 ≤ 6668725498349^3107*500000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109880701 500000000 6668725498349 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5225572873/10000000000 : ℝ)^4131 ≤ (21096331710233/50000000000000 : ℝ)^3107 := by
    have hnat : (5225572873 : ℕ)^4131*50000000000000^3107 ≤ 21096331710233^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225572873 10000000000 21096331710233 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1087261631/2000000000 : ℝ)^4131 ≤ (22234942784341/50000000000000 : ℝ)^3107 := by
    have hnat : (1087261631 : ℕ)^4131*50000000000000^3107 ≤ 22234942784341^3107*2000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087261631 2000000000 22234942784341 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-109880701/500000000 : ℝ), (5225572873/10000000000 : ℝ), (1087261631/2000000000 : ℝ)] ![(6668725498349/50000000000000 : ℝ), (21096331710233/50000000000000 : ℝ), (22234942784341/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-109880701/500000000 : ℝ)|^4131 ≤ (6668725498349/50000000000000 : ℝ)^3107
        have hw : |(-109880701/500000000 : ℝ)|=(109880701/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5225572873/10000000000 : ℝ)|^4131 ≤ (21096331710233/50000000000000 : ℝ)^3107
        have hw : |(5225572873/10000000000 : ℝ)|=(5225572873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1087261631/2000000000 : ℝ)|^4131 ≤ (22234942784341/50000000000000 : ℝ)^3107
        have hw : |(1087261631/2000000000 : ℝ)|=(1087261631/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s3_5 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1325519613/2500000000 : ℝ)*x 0 + (-261848229/1250000000 : ℝ)*x 1 + (679538447/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325519613/2500000000 : ℝ)^4131 ≤ (43015954111077/100000000000000 : ℝ)^3107 := by
    have hnat : (1325519613 : ℕ)^4131*100000000000000^3107 ≤ 43015954111077^3107*2500000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325519613 2500000000 43015954111077 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (261848229/1250000000 : ℝ)^4131 ≤ (6257083294899/50000000000000 : ℝ)^3107 := by
    have hnat : (261848229 : ℕ)^4131*50000000000000^3107 ≤ 6257083294899^3107*1250000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261848229 1250000000 6257083294899 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (679538447/1250000000 : ℝ)^4131 ≤ (44469879271381/100000000000000 : ℝ)^3107 := by
    have hnat : (679538447 : ℕ)^4131*100000000000000^3107 ≤ 44469879271381^3107*1250000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679538447 1250000000 44469879271381 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325519613/2500000000 : ℝ), (-261848229/1250000000 : ℝ), (679538447/1250000000 : ℝ)] ![(43015954111077/100000000000000 : ℝ), (6257083294899/50000000000000 : ℝ), (44469879271381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325519613/2500000000 : ℝ)|^4131 ≤ (43015954111077/100000000000000 : ℝ)^3107
        have hw : |(1325519613/2500000000 : ℝ)|=(1325519613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-261848229/1250000000 : ℝ)|^4131 ≤ (6257083294899/50000000000000 : ℝ)^3107
        have hw : |(-261848229/1250000000 : ℝ)|=(261848229/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(679538447/1250000000 : ℝ)|^4131 ≤ (44469879271381/100000000000000 : ℝ)^3107
        have hw : |(679538447/1250000000 : ℝ)|=(679538447/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s3_6 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5302078231/10000000000 : ℝ)*x 0 + (1087261593/2000000000 : ℝ)*x 1 + (-1047392801/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302078231/10000000000 : ℝ)^4131 ≤ (672124245737/1562500000000 : ℝ)^3107 := by
    have hnat : (5302078231 : ℕ)^4131*1562500000000^3107 ≤ 672124245737^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302078231 10000000000 672124245737 1562500000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1087261593/2000000000 : ℝ)^4131 ≤ (4446988350221/10000000000000 : ℝ)^3107 := by
    have hnat : (1087261593 : ℕ)^4131*10000000000000^3107 ≤ 4446988350221^3107*2000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087261593 2000000000 4446988350221 10000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1047392801/5000000000 : ℝ)^4131 ≤ (12514164762943/100000000000000 : ℝ)^3107 := by
    have hnat : (1047392801 : ℕ)^4131*100000000000000^3107 ≤ 12514164762943^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047392801 5000000000 12514164762943 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302078231/10000000000 : ℝ), (1087261593/2000000000 : ℝ), (-1047392801/5000000000 : ℝ)] ![(672124245737/1562500000000 : ℝ), (4446988350221/10000000000000 : ℝ), (12514164762943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302078231/10000000000 : ℝ)|^4131 ≤ (672124245737/1562500000000 : ℝ)^3107
        have hw : |(5302078231/10000000000 : ℝ)|=(5302078231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1087261593/2000000000 : ℝ)|^4131 ≤ (4446988350221/10000000000000 : ℝ)^3107
        have hw : |(1087261593/2000000000 : ℝ)|=(1087261593/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1047392801/5000000000 : ℝ)|^4131 ≤ (12514164762943/100000000000000 : ℝ)^3107
        have hw : |(-1047392801/5000000000 : ℝ)|=(1047392801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s3_7 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4372325541/10000000000 : ℝ)*x 0 + (2291966251/5000000000 : ℝ)*x 1 + (521334549/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4372325541/10000000000 : ℝ)^4131 ≤ (33288873387527/100000000000000 : ℝ)^3107 := by
    have hnat : (4372325541 : ℕ)^4131*100000000000000^3107 ≤ 33288873387527^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4372325541 10000000000 33288873387527 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2291966251/5000000000 : ℝ)^4131 ≤ (35447830171511/100000000000000 : ℝ)^3107 := by
    have hnat : (2291966251 : ℕ)^4131*100000000000000^3107 ≤ 35447830171511^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2291966251 5000000000 35447830171511 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521334549/1250000000 : ℝ)^4131 ≤ (31263296424389/100000000000000 : ℝ)^3107 := by
    have hnat : (521334549 : ℕ)^4131*100000000000000^3107 ≤ 31263296424389^3107*1250000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521334549 1250000000 31263296424389 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4372325541/10000000000 : ℝ), (2291966251/5000000000 : ℝ), (521334549/1250000000 : ℝ)] ![(33288873387527/100000000000000 : ℝ), (35447830171511/100000000000000 : ℝ), (31263296424389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4372325541/10000000000 : ℝ)|^4131 ≤ (33288873387527/100000000000000 : ℝ)^3107
        have hw : |(4372325541/10000000000 : ℝ)|=(4372325541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2291966251/5000000000 : ℝ)|^4131 ≤ (35447830171511/100000000000000 : ℝ)^3107
        have hw : |(2291966251/5000000000 : ℝ)|=(2291966251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(521334549/1250000000 : ℝ)|^4131 ≤ (31263296424389/100000000000000 : ℝ)^3107
        have hw : |(521334549/1250000000 : ℝ)|=(521334549/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1069_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74025701/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16731/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8727/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5203/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14901/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16731/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8727/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16731/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8727/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16731/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8727/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16731/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8727/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16731/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8727/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16731/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8727/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8727/100000 : ℝ) ^ (8261/2048 : ℝ) ≤ (5342889046874769/100000000000000000000 : ℝ) := by
    have hpowers : (8727/100000 : ℝ)^8261 ≤ (5342889046874769/100000000000000000000 : ℝ)^2048 := by
      have hnat : (8727 : ℕ)^8261*100000000000000000000^2048 ≤ 5342889046874769^2048*100000^8261 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8727 100000 5342889046874769 100000000000000000000 8261 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8727/100000 : ℝ)) (X := (5342889046874769/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (16731/100000 : ℝ) ^ (8261/2048 : ℝ) ≤ (7377801353339231/10000000000000000000 : ℝ) := by
    have hpowers : (16731/100000 : ℝ)^8261 ≤ (7377801353339231/10000000000000000000 : ℝ)^2048 := by
      have hnat : (16731 : ℕ)^8261*10000000000000000000^2048 ≤ 7377801353339231^2048*100000^8261 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16731 100000 7377801353339231 10000000000000000000 8261 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16731/100000 : ℝ)) (X := (7377801353339231/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005342889046874769/50000000000000000000 : ℝ) ≤ (2000052980496797/2000000000000000 : ℝ) ^ (8261/2048 : ℝ) := by
    have hpowers : (50005342889046874769/50000000000000000000 : ℝ)^2048 ≤ (2000052980496797/2000000000000000 : ℝ)^8261 := by
      have hnat : (50005342889046874769 : ℕ)^2048*2000000000000000^8261 ≤ 2000052980496797^8261*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005342889046874769 50000000000000000000 2000052980496797 2000000000000000 2048 8261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000052980496797/2000000000000000 : ℝ)) (X := (50005342889046874769/50000000000000000000 : ℝ)) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100079120902580267079/100000000000000000000 : ℝ) ≤ (10001960917796801/10000000000000000 : ℝ) ^ (8261/2048 : ℝ) := by
    have hpowers : (100079120902580267079/100000000000000000000 : ℝ)^2048 ≤ (10001960917796801/10000000000000000 : ℝ)^8261 := by
      have hnat : (100079120902580267079 : ℕ)^2048*10000000000000000^8261 ≤ 10001960917796801^8261*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100079120902580267079 100000000000000000000 10001960917796801 10000000000000000 2048 8261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001960917796801/10000000000000000 : ℝ)) (X := (100079120902580267079/100000000000000000000 : ℝ)) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (5007377801353339231/5000000000000000000 : ℝ) ≤ (10003656933109617/10000000000000000 : ℝ) ^ (8261/2048 : ℝ) := by
    have hpowers : (5007377801353339231/5000000000000000000 : ℝ)^2048 ≤ (10003656933109617/10000000000000000 : ℝ)^8261 := by
      have hnat : (5007377801353339231 : ℕ)^2048*10000000000000000^8261 ≤ 10003656933109617^8261*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5007377801353339231 5000000000000000000 10003656933109617 10000000000000000 2048 8261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003656933109617/10000000000000000 : ℝ)) (X := (5007377801353339231/5000000000000000000 : ℝ)) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5342889046874769/100000000000000000000 : ℝ) ≤ ((6667709835684327123/6670000000000000000 : ℝ)+2*(106000957051/50025000000000 : ℝ)*(8727/100000 : ℝ))^(8261/2048 : ℝ) := by
    rw [show (6667709835684327123/6670000000000000000 : ℝ)+2*(106000957051/50025000000000 : ℝ)*(8727/100000 : ℝ)=(2000052980496797/2000000000000000 : ℝ) by norm_num, show 1+2*(5342889046874769/100000000000000000000 : ℝ)=(50005342889046874769/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7377801353339231/10000000000000000000 : ℝ)+(5342889046874769/100000000000000000000 : ℝ) ≤ ((6667709835684327123/6670000000000000000 : ℝ)+(106000957051/50025000000000 : ℝ)*((16731/100000 : ℝ)+(8727/100000 : ℝ)))^(8261/2048 : ℝ) := by
    rw [show (6667709835684327123/6670000000000000000 : ℝ)+(106000957051/50025000000000 : ℝ)*((16731/100000 : ℝ)+(8727/100000 : ℝ))=(10001960917796801/10000000000000000 : ℝ) by norm_num, show 1+(7377801353339231/10000000000000000000 : ℝ)+(5342889046874769/100000000000000000000 : ℝ)=(100079120902580267079/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7377801353339231/10000000000000000000 : ℝ) ≤ ((6667709835684327123/6670000000000000000 : ℝ)+2*(106000957051/50025000000000 : ℝ)*(16731/100000 : ℝ))^(8261/2048 : ℝ) := by
    rw [show (6667709835684327123/6670000000000000000 : ℝ)+2*(106000957051/50025000000000 : ℝ)*(16731/100000 : ℝ)=(10003656933109617/10000000000000000 : ℝ) by norm_num, show 1+2*(7377801353339231/10000000000000000000 : ℝ)=(5007377801353339231/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6667709835684327123/6670000000000000000 : ℝ)*(X 1 0+X 2 0)+(106000957051/50025000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8261/2048 : ℝ)) (lo := (8727/100000 : ℝ)) (hi := (16731/100000 : ℝ)) (c := (6667709835684327123/6670000000000000000 : ℝ)) (alpha := (106000957051/50025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6667709835684327123/6670000000000000000 : ℝ)*(X 0 1+X 2 1)+(106000957051/50025000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8261/2048 : ℝ)) (lo := (8727/100000 : ℝ)) (hi := (16731/100000 : ℝ)) (c := (6667709835684327123/6670000000000000000 : ℝ)) (alpha := (106000957051/50025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6667709835684327123/6670000000000000000 : ℝ)*(X 0 2+X 1 2)+(106000957051/50025000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8261/2048 : ℝ)) (lo := (8727/100000 : ℝ)) (hi := (16731/100000 : ℝ)) (c := (6667709835684327123/6670000000000000000 : ℝ)) (alpha := (106000957051/50025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2197591633/10000000000 : ℝ)*X 0 0+(2718591053/5000000000 : ℝ)*X 0 1+(65308803/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338903383/2500000000 : ℝ)*X 1 0+(-576597231/2500000000 : ℝ)*X 1 1+(5224704343/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338903381/2500000000 : ℝ)*X 2 0+(5224704721/10000000000 : ℝ)*X 2 1+(-2306388439/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1093070623/2500000000 : ℝ)*X 0 0+(2084481233/5000000000 : ℝ)*X 0 1+(4585636049/10000000000 : ℝ)*X 0 2+(1093070623/2500000000 : ℝ)*X 1 0+(2084481233/5000000000 : ℝ)*X 1 1+(4585636049/10000000000 : ℝ)*X 1 2+(1093070623/2500000000 : ℝ)*X 2 0+(2084481233/5000000000 : ℝ)*X 2 1+(4585636049/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-109880701/500000000 : ℝ)*X 0 0+(5225572873/10000000000 : ℝ)*X 0 1+(1087261631/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1325519613/2500000000 : ℝ)*X 1 0+(-261848229/1250000000 : ℝ)*X 1 1+(679538447/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5302078231/10000000000 : ℝ)*X 2 0+(1087261593/2000000000 : ℝ)*X 2 1+(-1047392801/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4372325541/10000000000 : ℝ)*X 0 0+(2291966251/5000000000 : ℝ)*X 0 1+(521334549/1250000000 : ℝ)*X 0 2+(4372325541/10000000000 : ℝ)*X 1 0+(2291966251/5000000000 : ℝ)*X 1 1+(521334549/1250000000 : ℝ)*X 1 2+(4372325541/10000000000 : ℝ)*X 2 0+(2291966251/5000000000 : ℝ)*X 2 1+(521334549/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (226028845800769047076770003/41687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (389556427/25000000000000 : ℝ)*(base19) + (292028469/25000000000000 : ℝ)*(base23) + (205163673/100000000000000 : ℝ)*(lower2) + (18107707/100000000000000 : ℝ)*(upper3) + (195610889/100000000000000 : ℝ)*(upper5) + (888302675058813/25000000000000 : ℝ)*(major0) + (888302675058813/25000000000000 : ℝ)*(major1) + (888302675058813/25000000000000 : ℝ)*(major2) + (4706400119737593/100000000000000 : ℝ)*(sp0) + (4706435161375261/100000000000000 : ℝ)*(sp1) + (4706435551487093/100000000000000 : ℝ)*(sp2) + (479994550754561/20000000000000 : ℝ)*(sp3) + (2287491461/6250000000000 : ℝ)*(sp4) + (11746364013/100000000000000 : ℝ)*(sp7) + (2399984500136819/100000000000000 : ℝ)*(f.failure) + (4706436719600969/100000000000000 : ℝ)*(f.sum) + (1061653239051/833750000000000000000000000 : ℝ)*base66 + (760022143270984999/166750000000000000000000000000000 : ℝ)*base67 + (259462592072734999/166750000000000000000000000000000 : ℝ)*base69 + (58118002755734999/166750000000000000000000000000000 : ℝ)*base71 + (1926103819579/833750000000000000000000000 : ℝ)*base73 + (2038629577162484999/166750000000000000000000000000000 : ℝ)*base75 + (1385345638265734999/166750000000000000000000000000000 : ℝ)*base77 + (1267783910891265001/166750000000000000000000000000000 : ℝ)*base80 + (7480176091027/1667500000000000000000000000 : ℝ)*base82 + (22385119/5000000000000000000000 : ℝ)*base89 + (22385119/5000000000000000000000 : ℝ)*base91 + (22385119/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (206272793234514992676484089/83375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11212487/2500000000000 : ℝ)*(base19) + (313181423/100000000000000 : ℝ)*(base23) + (5328939/25000000000000 : ℝ)*(upper2) + (64079571/50000000000000 : ℝ)*(upper5) + (895638680182119/25000000000000 : ℝ)*(major0) + (895638680182119/25000000000000 : ℝ)*(major1) + (895638680182119/25000000000000 : ℝ)*(major2) + (1230834731/20000000000000 : ℝ)*(sp0) + (2842723559/100000000000000 : ℝ)*(sp1) + (1262126191/25000000000000 : ℝ)*(sp2) + (4745298547559629/100000000000000 : ℝ)*(sp4) + (949060282102049/20000000000000 : ℝ)*(sp5) + (4745299340047097/100000000000000 : ℝ)*(sp6) + (2419804657255779/100000000000000 : ℝ)*(sp7) + (2419804657255779/100000000000000 : ℝ)*(f.failure) + (1186326175433321/25000000000000 : ℝ)*(f.sum) + (2136300139657/833750000000000000000000000 : ℝ)*base65 + (1032634298963236363/166750000000000000000000000000000 : ℝ)*base68 + (968340612165263637/166750000000000000000000000000000 : ℝ)*base69 + (63833801126736363/166750000000000000000000000000000 : ℝ)*base72 + (2629174646901/1667500000000000000000000000 : ℝ)*base74 + (948570538401763637/166750000000000000000000000000000 : ℝ)*base75 + (1116767435322013637/166750000000000000000000000000000 : ℝ)*base77 + (714395962628263637/166750000000000000000000000000000 : ℝ)*base79 + (105143702369/1667500000000000000000000000 : ℝ)*base81 + (23223921/5000000000000000000000 : ℝ)*base90 + (23223921/5000000000000000000000 : ℝ)*base92 + (23223921/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1069_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74025701/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16731/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8727/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5203/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14901/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1069_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1069_s4_0 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2201243849/10000000000 : ℝ)*x 0 + (2702821573/5000000000 : ℝ)*x 1 + (2626928417/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2201243849/10000000000 : ℝ)^4131 ≤ (13366749111477/100000000000000 : ℝ)^3107 := by
    have hnat : (2201243849 : ℕ)^4131*100000000000000^3107 ≤ 13366749111477^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2201243849 10000000000 13366749111477 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2702821573/5000000000 : ℝ)^4131 ≤ (22068339102121/50000000000000 : ℝ)^3107 := by
    have hnat : (2702821573 : ℕ)^4131*50000000000000^3107 ≤ 22068339102121^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702821573 5000000000 22068339102121 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2626928417/5000000000 : ℝ)^4131 ≤ (42496572677219/100000000000000 : ℝ)^3107 := by
    have hnat : (2626928417 : ℕ)^4131*100000000000000^3107 ≤ 42496572677219^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626928417 5000000000 42496572677219 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2201243849/10000000000 : ℝ), (2702821573/5000000000 : ℝ), (2626928417/5000000000 : ℝ)] ![(13366749111477/100000000000000 : ℝ), (22068339102121/50000000000000 : ℝ), (42496572677219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2201243849/10000000000 : ℝ)|^4131 ≤ (13366749111477/100000000000000 : ℝ)^3107
        have hw : |(-2201243849/10000000000 : ℝ)|=(2201243849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2702821573/5000000000 : ℝ)|^4131 ≤ (22068339102121/50000000000000 : ℝ)^3107
        have hw : |(2702821573/5000000000 : ℝ)|=(2702821573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2626928417/5000000000 : ℝ)|^4131 ≤ (42496572677219/100000000000000 : ℝ)^3107
        have hw : |(2626928417/5000000000 : ℝ)|=(2626928417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s4_1 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347797137/10000000000 : ℝ)*x 0 + (-569610929/2500000000 : ℝ)*x 1 + (656732099/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347797137/10000000000 : ℝ)^4131 ≤ (43509817200349/100000000000000 : ℝ)^3107 := by
    have hnat : (5347797137 : ℕ)^4131*100000000000000^3107 ≤ 43509817200349^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347797137 10000000000 43509817200349 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (569610929/2500000000 : ℝ)^4131 ≤ (2798722111809/20000000000000 : ℝ)^3107 := by
    have hnat : (569610929 : ℕ)^4131*20000000000000^3107 ≤ 2798722111809^3107*2500000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      569610929 2500000000 2798722111809 20000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (656732099/1250000000 : ℝ)^4131 ≤ (42496572225531/100000000000000 : ℝ)^3107 := by
    have hnat : (656732099 : ℕ)^4131*100000000000000^3107 ≤ 42496572225531^3107*1250000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656732099 1250000000 42496572225531 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347797137/10000000000 : ℝ), (-569610929/2500000000 : ℝ), (656732099/1250000000 : ℝ)] ![(43509817200349/100000000000000 : ℝ), (2798722111809/20000000000000 : ℝ), (42496572225531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347797137/10000000000 : ℝ)|^4131 ≤ (43509817200349/100000000000000 : ℝ)^3107
        have hw : |(5347797137/10000000000 : ℝ)|=(5347797137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-569610929/2500000000 : ℝ)|^4131 ≤ (2798722111809/20000000000000 : ℝ)^3107
        have hw : |(-569610929/2500000000 : ℝ)|=(569610929/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(656732099/1250000000 : ℝ)|^4131 ≤ (42496572225531/100000000000000 : ℝ)^3107
        have hw : |(656732099/1250000000 : ℝ)|=(656732099/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s4_2 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347797241/10000000000 : ℝ)*x 0 + (5253856747/10000000000 : ℝ)*x 1 + (-2278443637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347797241/10000000000 : ℝ)^4131 ≤ (5438727290671/12500000000000 : ℝ)^3107 := by
    have hnat : (5347797241 : ℕ)^4131*12500000000000^3107 ≤ 5438727290671^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347797241 10000000000 5438727290671 12500000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5253856747/10000000000 : ℝ)^4131 ≤ (42496571741579/100000000000000 : ℝ)^3107 := by
    have hnat : (5253856747 : ℕ)^4131*100000000000000^3107 ≤ 42496571741579^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253856747 10000000000 42496571741579 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2278443637/10000000000 : ℝ)^4131 ≤ (13993609913937/100000000000000 : ℝ)^3107 := by
    have hnat : (2278443637 : ℕ)^4131*100000000000000^3107 ≤ 13993609913937^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2278443637 10000000000 13993609913937 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347797241/10000000000 : ℝ), (5253856747/10000000000 : ℝ), (-2278443637/10000000000 : ℝ)] ![(5438727290671/12500000000000 : ℝ), (42496571741579/100000000000000 : ℝ), (13993609913937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347797241/10000000000 : ℝ)|^4131 ≤ (5438727290671/12500000000000 : ℝ)^3107
        have hw : |(5347797241/10000000000 : ℝ)|=(5347797241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5253856747/10000000000 : ℝ)|^4131 ≤ (42496571741579/100000000000000 : ℝ)^3107
        have hw : |(5253856747/10000000000 : ℝ)|=(5253856747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2278443637/10000000000 : ℝ)|^4131 ≤ (13993609913937/100000000000000 : ℝ)^3107
        have hw : |(-2278443637/10000000000 : ℝ)|=(2278443637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s4_3 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (874890573/2000000000 : ℝ)*x 0 + (845637223/2000000000 : ℝ)*x 1 + (4525843391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (874890573/2000000000 : ℝ)^4131 ≤ (33310409583983/100000000000000 : ℝ)^3107 := by
    have hnat : (874890573 : ℕ)^4131*100000000000000^3107 ≤ 33310409583983^3107*2000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874890573 2000000000 33310409583983 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (845637223/2000000000 : ℝ)^4131 ≤ (15918882447993/50000000000000 : ℝ)^3107 := by
    have hnat : (845637223 : ℕ)^4131*50000000000000^3107 ≤ 15918882447993^3107*2000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845637223 2000000000 15918882447993 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4525843391/10000000000 : ℝ)^4131 ≤ (17425912754509/50000000000000 : ℝ)^3107 := by
    have hnat : (4525843391 : ℕ)^4131*50000000000000^3107 ≤ 17425912754509^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4525843391 10000000000 17425912754509 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(874890573/2000000000 : ℝ), (845637223/2000000000 : ℝ), (4525843391/10000000000 : ℝ)] ![(33310409583983/100000000000000 : ℝ), (15918882447993/50000000000000 : ℝ), (17425912754509/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(874890573/2000000000 : ℝ)|^4131 ≤ (33310409583983/100000000000000 : ℝ)^3107
        have hw : |(874890573/2000000000 : ℝ)|=(874890573/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(845637223/2000000000 : ℝ)|^4131 ≤ (15918882447993/50000000000000 : ℝ)^3107
        have hw : |(845637223/2000000000 : ℝ)|=(845637223/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4525843391/10000000000 : ℝ)|^4131 ≤ (17425912754509/50000000000000 : ℝ)^3107
        have hw : |(4525843391/10000000000 : ℝ)|=(4525843391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s4_4 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2201251999/10000000000 : ℝ)*x 0 + (656787631/1250000000 : ℝ)*x 1 + (337824813/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2201251999/10000000000 : ℝ)^4131 ≤ (13366814912017/100000000000000 : ℝ)^3107 := by
    have hnat : (2201251999 : ℕ)^4131*100000000000000^3107 ≤ 13366814912017^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2201251999 10000000000 13366814912017 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (656787631/1250000000 : ℝ)^4131 ≤ (42501350036527/100000000000000 : ℝ)^3107 := by
    have hnat : (656787631 : ℕ)^4131*100000000000000^3107 ≤ 42501350036527^3107*1250000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656787631 1250000000 42501350036527 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337824813/625000000 : ℝ)^4131 ≤ (8826367007273/20000000000000 : ℝ)^3107 := by
    have hnat : (337824813 : ℕ)^4131*20000000000000^3107 ≤ 8826367007273^3107*625000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337824813 625000000 8826367007273 20000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2201251999/10000000000 : ℝ), (656787631/1250000000 : ℝ), (337824813/625000000 : ℝ)] ![(13366814912017/100000000000000 : ℝ), (42501350036527/100000000000000 : ℝ), (8826367007273/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2201251999/10000000000 : ℝ)|^4131 ≤ (13366814912017/100000000000000 : ℝ)^3107
        have hw : |(-2201251999/10000000000 : ℝ)|=(2201251999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(656787631/1250000000 : ℝ)|^4131 ≤ (42501350036527/100000000000000 : ℝ)^3107
        have hw : |(656787631/1250000000 : ℝ)|=(656787631/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337824813/625000000 : ℝ)|^4131 ≤ (8826367007273/20000000000000 : ℝ)^3107
        have hw : |(337824813/625000000 : ℝ)|=(337824813/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s4_5 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (663694787/1250000000 : ℝ)*x 0 + (-2127103171/10000000000 : ℝ)*x 1 + (2702598457/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663694787/1250000000 : ℝ)^4131 ≤ (43096657321491/100000000000000 : ℝ)^3107 := by
    have hnat : (663694787 : ℕ)^4131*100000000000000^3107 ≤ 43096657321491^3107*1250000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663694787 1250000000 43096657321491 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2127103171/10000000000 : ℝ)^4131 ≤ (255430172929/2000000000000 : ℝ)^3107 := by
    have hnat : (2127103171 : ℕ)^4131*2000000000000^3107 ≤ 255430172929^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127103171 10000000000 255430172929 2000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2702598457/5000000000 : ℝ)^4131 ≤ (22065917007969/50000000000000 : ℝ)^3107 := by
    have hnat : (2702598457 : ℕ)^4131*50000000000000^3107 ≤ 22065917007969^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702598457 5000000000 22065917007969 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663694787/1250000000 : ℝ), (-2127103171/10000000000 : ℝ), (2702598457/5000000000 : ℝ)] ![(43096657321491/100000000000000 : ℝ), (255430172929/2000000000000 : ℝ), (22065917007969/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663694787/1250000000 : ℝ)|^4131 ≤ (43096657321491/100000000000000 : ℝ)^3107
        have hw : |(663694787/1250000000 : ℝ)|=(663694787/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2127103171/10000000000 : ℝ)|^4131 ≤ (255430172929/2000000000000 : ℝ)^3107
        have hw : |(-2127103171/10000000000 : ℝ)|=(2127103171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2702598457/5000000000 : ℝ)|^4131 ≤ (22065917007969/50000000000000 : ℝ)^3107
        have hw : |(2702598457/5000000000 : ℝ)|=(2702598457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s4_6 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1327389531/2500000000 : ℝ)*x 0 + (5405196923/10000000000 : ℝ)*x 1 + (-66471981/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327389531/2500000000 : ℝ)^4131 ≤ (43096655465279/100000000000000 : ℝ)^3107 := by
    have hnat : (1327389531 : ℕ)^4131*100000000000000^3107 ≤ 43096655465279^3107*2500000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327389531 2500000000 43096655465279 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5405196923/10000000000 : ℝ)^4131 ≤ (22065917056819/50000000000000 : ℝ)^3107 := by
    have hnat : (5405196923 : ℕ)^4131*50000000000000^3107 ≤ 22065917056819^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405196923 10000000000 22065917056819 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (66471981/312500000 : ℝ)^4131 ≤ (12771510410699/100000000000000 : ℝ)^3107 := by
    have hnat : (66471981 : ℕ)^4131*100000000000000^3107 ≤ 12771510410699^3107*312500000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66471981 312500000 12771510410699 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327389531/2500000000 : ℝ), (5405196923/10000000000 : ℝ), (-66471981/312500000 : ℝ)] ![(43096655465279/100000000000000 : ℝ), (22065917056819/50000000000000 : ℝ), (12771510410699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327389531/2500000000 : ℝ)|^4131 ≤ (43096655465279/100000000000000 : ℝ)^3107
        have hw : |(1327389531/2500000000 : ℝ)|=(1327389531/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5405196923/10000000000 : ℝ)|^4131 ≤ (22065917056819/50000000000000 : ℝ)^3107
        have hw : |(5405196923/10000000000 : ℝ)|=(5405196923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-66471981/312500000 : ℝ)|^4131 ≤ (12771510410699/100000000000000 : ℝ)^3107
        have hw : |(-66471981/312500000 : ℝ)|=(66471981/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s4_7 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (174978739/400000000 : ℝ)*x 0 + (4524972167/10000000000 : ℝ)*x 1 + (4229061249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174978739/400000000 : ℝ)^4131 ≤ (33310567626279/100000000000000 : ℝ)^3107 := by
    have hnat : (174978739 : ℕ)^4131*100000000000000^3107 ≤ 33310567626279^3107*400000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174978739 400000000 33310567626279 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4524972167/10000000000 : ℝ)^4131 ≤ (17421452845397/50000000000000 : ℝ)^3107 := by
    have hnat : (4524972167 : ℕ)^4131*50000000000000^3107 ≤ 17421452845397^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4524972167 10000000000 17421452845397 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4229061249/10000000000 : ℝ)^4131 ≤ (31846526664727/100000000000000 : ℝ)^3107 := by
    have hnat : (4229061249 : ℕ)^4131*100000000000000^3107 ≤ 31846526664727^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229061249 10000000000 31846526664727 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(174978739/400000000 : ℝ), (4524972167/10000000000 : ℝ), (4229061249/10000000000 : ℝ)] ![(33310567626279/100000000000000 : ℝ), (17421452845397/50000000000000 : ℝ), (31846526664727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(174978739/400000000 : ℝ)|^4131 ≤ (33310567626279/100000000000000 : ℝ)^3107
        have hw : |(174978739/400000000 : ℝ)|=(174978739/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4524972167/10000000000 : ℝ)|^4131 ≤ (17421452845397/50000000000000 : ℝ)^3107
        have hw : |(4524972167/10000000000 : ℝ)|=(4524972167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4229061249/10000000000 : ℝ)|^4131 ≤ (31846526664727/100000000000000 : ℝ)^3107
        have hw : |(4229061249/10000000000 : ℝ)|=(4229061249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1069_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74025701/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14901/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5203/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11029/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7121/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14901/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5203/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14901/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5203/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14901/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5203/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14901/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5203/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14901/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5203/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14901/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5203/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5203/50000 : ℝ) ^ (8261/2048 : ℝ) ≤ (2172982315576287/20000000000000000000 : ℝ) := by
    have hpowers : (5203/50000 : ℝ)^8261 ≤ (2172982315576287/20000000000000000000 : ℝ)^2048 := by
      have hnat : (5203 : ℕ)^8261*20000000000000000000^2048 ≤ 2172982315576287^2048*50000^8261 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5203 50000 2172982315576287 20000000000000000000 8261 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5203/50000 : ℝ)) (X := (2172982315576287/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14901/100000 : ℝ) ^ (8261/2048 : ℝ) ≤ (462387540978519/1000000000000000000 : ℝ) := by
    have hpowers : (14901/100000 : ℝ)^8261 ≤ (462387540978519/1000000000000000000 : ℝ)^2048 := by
      have hnat : (14901 : ℕ)^8261*1000000000000000000^2048 ≤ 462387540978519^2048*100000^8261 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14901 100000 462387540978519 1000000000000000000 8261 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14901/100000 : ℝ)) (X := (462387540978519/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002172982315576287/10000000000000000000 : ℝ) ≤ (2500134666026527/2500000000000000 : ℝ) ^ (8261/2048 : ℝ) := by
    have hpowers : (10002172982315576287/10000000000000000000 : ℝ)^2048 ≤ (2500134666026527/2500000000000000 : ℝ)^8261 := by
      have hnat : (10002172982315576287 : ℕ)^2048*2500000000000000^8261 ≤ 2500134666026527^8261*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002172982315576287 10000000000000000000 2500134666026527 2500000000000000 2048 8261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500134666026527/2500000000000000 : ℝ)) (X := (10002172982315576287/10000000000000000000 : ℝ)) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20011420733135146667/20000000000000000000 : ℝ) ≤ (10001415363791159/10000000000000000 : ℝ) ^ (8261/2048 : ℝ) := by
    have hpowers : (20011420733135146667/20000000000000000000 : ℝ)^2048 ≤ (10001415363791159/10000000000000000 : ℝ)^8261 := by
      have hnat : (20011420733135146667 : ℕ)^2048*10000000000000000^8261 ≤ 10001415363791159^8261*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20011420733135146667 20000000000000000000 10001415363791159 10000000000000000 2048 8261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001415363791159/10000000000000000 : ℝ)) (X := (20011420733135146667/20000000000000000000 : ℝ)) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (500462387540978519/500000000000000000 : ℝ) ≤ (1000229206347621/1000000000000000 : ℝ) ^ (8261/2048 : ℝ) := by
    have hpowers : (500462387540978519/500000000000000000 : ℝ)^2048 ≤ (1000229206347621/1000000000000000 : ℝ)^8261 := by
      have hnat : (500462387540978519 : ℕ)^2048*1000000000000000^8261 ≤ 1000229206347621^8261*500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500462387540978519 500000000000000000 1000229206347621 1000000000000000 2048 8261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000229206347621/1000000000000000 : ℝ)) (X := (500462387540978519/500000000000000000 : ℝ)) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2172982315576287/20000000000000000000 : ℝ) ≤ ((702096490957994907/702343750000000000 : ℝ)+2*(876699685051/449500000000000 : ℝ)*(5203/50000 : ℝ))^(8261/2048 : ℝ) := by
    rw [show (702096490957994907/702343750000000000 : ℝ)+2*(876699685051/449500000000000 : ℝ)*(5203/50000 : ℝ)=(2500134666026527/2500000000000000 : ℝ) by norm_num, show 1+2*(2172982315576287/20000000000000000000 : ℝ)=(10002172982315576287/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(462387540978519/1000000000000000000 : ℝ)+(2172982315576287/20000000000000000000 : ℝ) ≤ ((702096490957994907/702343750000000000 : ℝ)+(876699685051/449500000000000 : ℝ)*((14901/100000 : ℝ)+(5203/50000 : ℝ)))^(8261/2048 : ℝ) := by
    rw [show (702096490957994907/702343750000000000 : ℝ)+(876699685051/449500000000000 : ℝ)*((14901/100000 : ℝ)+(5203/50000 : ℝ))=(10001415363791159/10000000000000000 : ℝ) by norm_num, show 1+(462387540978519/1000000000000000000 : ℝ)+(2172982315576287/20000000000000000000 : ℝ)=(20011420733135146667/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(462387540978519/1000000000000000000 : ℝ) ≤ ((702096490957994907/702343750000000000 : ℝ)+2*(876699685051/449500000000000 : ℝ)*(14901/100000 : ℝ))^(8261/2048 : ℝ) := by
    rw [show (702096490957994907/702343750000000000 : ℝ)+2*(876699685051/449500000000000 : ℝ)*(14901/100000 : ℝ)=(1000229206347621/1000000000000000 : ℝ) by norm_num, show 1+2*(462387540978519/1000000000000000000 : ℝ)=(500462387540978519/500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (702096490957994907/702343750000000000 : ℝ)*(X 1 0+X 2 0)+(876699685051/449500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8261/2048 : ℝ)) (lo := (5203/50000 : ℝ)) (hi := (14901/100000 : ℝ)) (c := (702096490957994907/702343750000000000 : ℝ)) (alpha := (876699685051/449500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (702096490957994907/702343750000000000 : ℝ)*(X 0 1+X 2 1)+(876699685051/449500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8261/2048 : ℝ)) (lo := (5203/50000 : ℝ)) (hi := (14901/100000 : ℝ)) (c := (702096490957994907/702343750000000000 : ℝ)) (alpha := (876699685051/449500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (702096490957994907/702343750000000000 : ℝ)*(X 0 2+X 1 2)+(876699685051/449500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8261/2048 : ℝ)) (lo := (5203/50000 : ℝ)) (hi := (14901/100000 : ℝ)) (c := (702096490957994907/702343750000000000 : ℝ)) (alpha := (876699685051/449500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2201243849/10000000000 : ℝ)*X 0 0+(2702821573/5000000000 : ℝ)*X 0 1+(2626928417/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347797137/10000000000 : ℝ)*X 1 0+(-569610929/2500000000 : ℝ)*X 1 1+(656732099/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347797241/10000000000 : ℝ)*X 2 0+(5253856747/10000000000 : ℝ)*X 2 1+(-2278443637/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((874890573/2000000000 : ℝ)*X 0 0+(845637223/2000000000 : ℝ)*X 0 1+(4525843391/10000000000 : ℝ)*X 0 2+(874890573/2000000000 : ℝ)*X 1 0+(845637223/2000000000 : ℝ)*X 1 1+(4525843391/10000000000 : ℝ)*X 1 2+(874890573/2000000000 : ℝ)*X 2 0+(845637223/2000000000 : ℝ)*X 2 1+(4525843391/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2201251999/10000000000 : ℝ)*X 0 0+(656787631/1250000000 : ℝ)*X 0 1+(337824813/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((663694787/1250000000 : ℝ)*X 1 0+(-2127103171/10000000000 : ℝ)*X 1 1+(2702598457/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1327389531/2500000000 : ℝ)*X 2 0+(5405196923/10000000000 : ℝ)*X 2 1+(-66471981/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((174978739/400000000 : ℝ)*X 0 0+(4524972167/10000000000 : ℝ)*X 0 1+(4229061249/10000000000 : ℝ)*X 0 2+(174978739/400000000 : ℝ)*X 1 0+(4524972167/10000000000 : ℝ)*X 1 1+(4229061249/10000000000 : ℝ)*X 1 2+(174978739/400000000 : ℝ)*X 2 0+(4524972167/10000000000 : ℝ)*X 2 1+(4229061249/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (46033294897750424433095259/17558593750000000000000000000000 : ℝ) := by norm_num
    linear_combination (56419771/25000000000000 : ℝ)*(base19) + (71685047/50000000000000 : ℝ)*(base23) + (133125029/100000000000000 : ℝ)*(lower2) + (1114391/4000000000000 : ℝ)*(upper3) + (10295217/50000000000000 : ℝ)*(lower4) + (2486946213452371/50000000000000 : ℝ)*(major0) + (2486946213452371/50000000000000 : ℝ)*(major1) + (2486946213452371/50000000000000 : ℝ)*(major2) + (823526255916977/12500000000000 : ℝ)*(sp0) + (6588213229889489/100000000000000 : ℝ)*(sp1) + (3294106656099239/50000000000000 : ℝ)*(sp2) + (1679784428569121/50000000000000 : ℝ)*(sp3) + (852058189/25000000000000 : ℝ)*(sp4) + (2453712797/100000000000000 : ℝ)*(sp7) + (3359571310851039/100000000000000 : ℝ)*(f.failure) + (1647053363892143/25000000000000 : ℝ)*(f.sum) + (29965485251267/22475000000000000000000000000 : ℝ)*base65 + (16997666466307359/4389648437500000000000000000000 : ℝ)*base67 + (70840834219286997/35117187500000000000000000000000 : ℝ)*base69 + (514049699714433369/70234375000000000000000000000000 : ℝ)*base71 + (4224988955533/22475000000000000000000000000 : ℝ)*base74 + (52374795769150503/35117187500000000000000000000000 : ℝ)*base76 + (100896766482431753/35117187500000000000000000000000 : ℝ)*base78 + (134436679693036997/35117187500000000000000000000000 : ℝ)*base79 + (20343607099067/22475000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (31446661/5000000000000000000000 : ℝ)*base90 + (31446661/5000000000000000000000 : ℝ)*base92 + (31446661/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (103815537865893053300504811/70234375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (699723769/100000000000000 : ℝ)*(base19) + (217589249/50000000000000 : ℝ)*(base23) + (55411847/100000000000000 : ℝ)*(lower3) + (20276683/100000000000000 : ℝ)*(lower4) + (1250809658942059/25000000000000 : ℝ)*(major0) + (1250809658942059/25000000000000 : ℝ)*(major1) + (1250809658942059/25000000000000 : ℝ)*(major2) + (317342837/25000000000000 : ℝ)*(sp0) + (4411747957/20000000000000 : ℝ)*(sp1) + (4916087667/50000000000000 : ℝ)*(sp2) + (165677075170223/2500000000000 : ℝ)*(sp4) + (3313530758858357/50000000000000 : ℝ)*(sp5) + (1656768502206609/25000000000000 : ℝ)*(sp6) + (844848236521299/25000000000000 : ℝ)*(sp7) + (844848236521299/25000000000000 : ℝ)*(f.failure) + (1656771069045067/25000000000000 : ℝ)*(f.sum) + (2263216306059/5618750000000000000000000000 : ℝ)*base65 + (352089223303066099/35117187500000000000000000000000 : ℝ)*base68 + (581601278838378599/35117187500000000000000000000000 : ℝ)*base70 + (309326569872616573/70234375000000000000000000000000 : ℝ)*base72 + (57795304100257/11237500000000000000000000000 : ℝ)*base74 + (287901726685097349/35117187500000000000000000000000 : ℝ)*base76 + (102892213201176681/8779296875000000000000000000000 : ℝ)*base78 + (28183862660158653/4389648437500000000000000000000 : ℝ)*base80 + (42191479723307/11237500000000000000000000000 : ℝ)*base82 + (9905599/1250000000000000000000 : ℝ)*base89 + (9905599/1250000000000000000000 : ℝ)*base91 + (9905599/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1069_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74025701/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14901/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5203/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11029/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7121/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1069_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1069_s5_0 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2202063317/10000000000 : ℝ)*x 0 + (5396905107/10000000000 : ℝ)*x 1 + (2631028793/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2202063317/10000000000 : ℝ)^4131 ≤ (13373365640497/100000000000000 : ℝ)^3107 := by
    have hnat : (2202063317 : ℕ)^4131*100000000000000^3107 ≤ 13373365640497^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2202063317 10000000000 13373365640497 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396905107/10000000000 : ℝ)^4131 ≤ (8808368824229/20000000000000 : ℝ)^3107 := by
    have hnat : (5396905107 : ℕ)^4131*20000000000000^3107 ≤ 8808368824229^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396905107 10000000000 8808368824229 20000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631028793/5000000000 : ℝ)^4131 ≤ (8516958043633/20000000000000 : ℝ)^3107 := by
    have hnat : (2631028793 : ℕ)^4131*20000000000000^3107 ≤ 8516958043633^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631028793 5000000000 8516958043633 20000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2202063317/10000000000 : ℝ), (5396905107/10000000000 : ℝ), (2631028793/5000000000 : ℝ)] ![(13373365640497/100000000000000 : ℝ), (8808368824229/20000000000000 : ℝ), (8516958043633/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2202063317/10000000000 : ℝ)|^4131 ≤ (13373365640497/100000000000000 : ℝ)^3107
        have hw : |(-2202063317/10000000000 : ℝ)|=(2202063317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396905107/10000000000 : ℝ)|^4131 ≤ (8808368824229/20000000000000 : ℝ)^3107
        have hw : |(5396905107/10000000000 : ℝ)|=(5396905107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631028793/5000000000 : ℝ)|^4131 ≤ (8516958043633/20000000000000 : ℝ)^3107
        have hw : |(2631028793/5000000000 : ℝ)|=(2631028793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s5_1 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672810597/5000000000 : ℝ)*x 0 + (-1135259237/5000000000 : ℝ)*x 1 + (1315514361/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672810597/5000000000 : ℝ)^4131 ≤ (5435785068671/12500000000000 : ℝ)^3107 := by
    have hnat : (2672810597 : ℕ)^4131*12500000000000^3107 ≤ 5435785068671^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672810597 5000000000 5435785068671 12500000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1135259237/5000000000 : ℝ)^4131 ≤ (696446537331/5000000000000 : ℝ)^3107 := by
    have hnat : (1135259237 : ℕ)^4131*5000000000000^3107 ≤ 696446537331^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1135259237 5000000000 696446537331 5000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315514361/2500000000 : ℝ)^4131 ≤ (42584788690243/100000000000000 : ℝ)^3107 := by
    have hnat : (1315514361 : ℕ)^4131*100000000000000^3107 ≤ 42584788690243^3107*2500000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315514361 2500000000 42584788690243 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672810597/5000000000 : ℝ), (-1135259237/5000000000 : ℝ), (1315514361/2500000000 : ℝ)] ![(5435785068671/12500000000000 : ℝ), (696446537331/5000000000000 : ℝ), (42584788690243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672810597/5000000000 : ℝ)|^4131 ≤ (5435785068671/12500000000000 : ℝ)^3107
        have hw : |(2672810597/5000000000 : ℝ)|=(2672810597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1135259237/5000000000 : ℝ)|^4131 ≤ (696446537331/5000000000000 : ℝ)^3107
        have hw : |(-1135259237/5000000000 : ℝ)|=(1135259237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1315514361/2500000000 : ℝ)|^4131 ≤ (42584788690243/100000000000000 : ℝ)^3107
        have hw : |(1315514361/2500000000 : ℝ)|=(1315514361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s5_2 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672810487/5000000000 : ℝ)*x 0 + (1315514411/2500000000 : ℝ)*x 1 + (-2270518503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672810487/5000000000 : ℝ)^4131 ≤ (43486278169841/100000000000000 : ℝ)^3107 := by
    have hnat : (2672810487 : ℕ)^4131*100000000000000^3107 ≤ 43486278169841^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672810487 5000000000 43486278169841 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315514411/2500000000 : ℝ)^4131 ≤ (21292395421123/50000000000000 : ℝ)^3107 := by
    have hnat : (1315514411 : ℕ)^4131*50000000000000^3107 ≤ 21292395421123^3107*2500000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315514411 2500000000 21292395421123 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2270518503/10000000000 : ℝ)^4131 ≤ (348223274579/2500000000000 : ℝ)^3107 := by
    have hnat : (2270518503 : ℕ)^4131*2500000000000^3107 ≤ 348223274579^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2270518503 10000000000 348223274579 2500000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672810487/5000000000 : ℝ), (1315514411/2500000000 : ℝ), (-2270518503/10000000000 : ℝ)] ![(43486278169841/100000000000000 : ℝ), (21292395421123/50000000000000 : ℝ), (348223274579/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672810487/5000000000 : ℝ)|^4131 ≤ (43486278169841/100000000000000 : ℝ)^3107
        have hw : |(2672810487/5000000000 : ℝ)|=(2672810487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1315514411/2500000000 : ℝ)|^4131 ≤ (21292395421123/50000000000000 : ℝ)^3107
        have hw : |(1315514411/2500000000 : ℝ)|=(1315514411/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2270518503/10000000000 : ℝ)|^4131 ≤ (348223274579/2500000000000 : ℝ)^3107
        have hw : |(-2270518503/10000000000 : ℝ)|=(2270518503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s5_3 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4374929453/10000000000 : ℝ)*x 0 + (4244731819/10000000000 : ℝ)*x 1 + (140911647/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4374929453/10000000000 : ℝ)^4131 ≤ (4164404355989/12500000000000 : ℝ)^3107 := by
    have hnat : (4374929453 : ℕ)^4131*12500000000000^3107 ≤ 4164404355989^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4374929453 10000000000 4164404355989 12500000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4244731819/10000000000 : ℝ)^4131 ≤ (1000110005709/3125000000000 : ℝ)^3107 := by
    have hnat : (4244731819 : ℕ)^4131*3125000000000^3107 ≤ 1000110005709^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4244731819 10000000000 1000110005709 3125000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (140911647/312500000 : ℝ)^4131 ≤ (34681244948259/100000000000000 : ℝ)^3107 := by
    have hnat : (140911647 : ℕ)^4131*100000000000000^3107 ≤ 34681244948259^3107*312500000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140911647 312500000 34681244948259 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4374929453/10000000000 : ℝ), (4244731819/10000000000 : ℝ), (140911647/312500000 : ℝ)] ![(4164404355989/12500000000000 : ℝ), (1000110005709/3125000000000 : ℝ), (34681244948259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4374929453/10000000000 : ℝ)|^4131 ≤ (4164404355989/12500000000000 : ℝ)^3107
        have hw : |(4374929453/10000000000 : ℝ)|=(4374929453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4244731819/10000000000 : ℝ)|^4131 ≤ (1000110005709/3125000000000 : ℝ)^3107
        have hw : |(4244731819/10000000000 : ℝ)|=(4244731819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(140911647/312500000 : ℝ)|^4131 ≤ (34681244948259/100000000000000 : ℝ)^3107
        have hw : |(140911647/312500000 : ℝ)|=(140911647/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s5_4 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-68814661/312500000 : ℝ)*x 0 + (2631204147/5000000000 : ℝ)*x 1 + (5396552961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (68814661/312500000 : ℝ)^4131 ≤ (534936510249/4000000000000 : ℝ)^3107 := by
    have hnat : (68814661 : ℕ)^4131*4000000000000^3107 ≤ 534936510249^3107*312500000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68814661 312500000 534936510249 4000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631204147/5000000000 : ℝ)^4131 ≤ (21294281941391/50000000000000 : ℝ)^3107 := by
    have hnat : (2631204147 : ℕ)^4131*50000000000000^3107 ≤ 21294281941391^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631204147 5000000000 21294281941391 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396552961/10000000000 : ℝ)^4131 ≤ (4403802333487/10000000000000 : ℝ)^3107 := by
    have hnat : (5396552961 : ℕ)^4131*10000000000000^3107 ≤ 4403802333487^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396552961 10000000000 4403802333487 10000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-68814661/312500000 : ℝ), (2631204147/5000000000 : ℝ), (5396552961/10000000000 : ℝ)] ![(534936510249/4000000000000 : ℝ), (21294281941391/50000000000000 : ℝ), (4403802333487/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-68814661/312500000 : ℝ)|^4131 ≤ (534936510249/4000000000000 : ℝ)^3107
        have hw : |(-68814661/312500000 : ℝ)|=(68814661/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631204147/5000000000 : ℝ)|^4131 ≤ (21294281941391/50000000000000 : ℝ)^3107
        have hw : |(2631204147/5000000000 : ℝ)|=(2631204147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5396552961/10000000000 : ℝ)|^4131 ≤ (4403802333487/10000000000000 : ℝ)^3107
        have hw : |(5396552961/10000000000 : ℝ)|=(5396552961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s5_5 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5311647957/10000000000 : ℝ)*x 0 + (-2136023169/10000000000 : ℝ)*x 1 + (4216057/7812500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311647957/10000000000 : ℝ)^4131 ≤ (84217207539/195312500000 : ℝ)^3107 := by
    have hnat : (5311647957 : ℕ)^4131*195312500000^3107 ≤ 84217207539^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311647957 10000000000 84217207539 195312500000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2136023169/10000000000 : ℝ)^4131 ≤ (20548426227/160000000000 : ℝ)^3107 := by
    have hnat : (2136023169 : ℕ)^4131*160000000000^3107 ≤ 20548426227^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136023169 10000000000 20548426227 160000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4216057/7812500 : ℝ)^4131 ≤ (2201901166201/5000000000000 : ℝ)^3107 := by
    have hnat : (4216057 : ℕ)^4131*5000000000000^3107 ≤ 2201901166201^3107*7812500^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4216057 7812500 2201901166201 5000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311647957/10000000000 : ℝ), (-2136023169/10000000000 : ℝ), (4216057/7812500 : ℝ)] ![(84217207539/195312500000 : ℝ), (20548426227/160000000000 : ℝ), (2201901166201/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311647957/10000000000 : ℝ)|^4131 ≤ (84217207539/195312500000 : ℝ)^3107
        have hw : |(5311647957/10000000000 : ℝ)|=(5311647957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2136023169/10000000000 : ℝ)|^4131 ≤ (20548426227/160000000000 : ℝ)^3107
        have hw : |(-2136023169/10000000000 : ℝ)|=(2136023169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4216057/7812500 : ℝ)|^4131 ≤ (2201901166201/5000000000000 : ℝ)^3107
        have hw : |(4216057/7812500 : ℝ)|=(4216057/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s5_6 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5311647967/10000000000 : ℝ)*x 0 + (2698276477/5000000000 : ℝ)*x 1 + (-534005791/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311647967/10000000000 : ℝ)^4131 ≤ (43119210367901/100000000000000 : ℝ)^3107 := by
    have hnat : (5311647967 : ℕ)^4131*100000000000000^3107 ≤ 43119210367901^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311647967 10000000000 43119210367901 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2698276477/5000000000 : ℝ)^4131 ≤ (44038023258921/100000000000000 : ℝ)^3107 := by
    have hnat : (2698276477 : ℕ)^4131*100000000000000^3107 ≤ 44038023258921^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698276477 5000000000 44038023258921 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (534005791/2500000000 : ℝ)^4131 ≤ (401336448497/3125000000000 : ℝ)^3107 := by
    have hnat : (534005791 : ℕ)^4131*3125000000000^3107 ≤ 401336448497^3107*2500000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534005791 2500000000 401336448497 3125000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311647967/10000000000 : ℝ), (2698276477/5000000000 : ℝ), (-534005791/2500000000 : ℝ)] ![(43119210367901/100000000000000 : ℝ), (44038023258921/100000000000000 : ℝ), (401336448497/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311647967/10000000000 : ℝ)|^4131 ≤ (43119210367901/100000000000000 : ℝ)^3107
        have hw : |(5311647967/10000000000 : ℝ)|=(5311647967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2698276477/5000000000 : ℝ)|^4131 ≤ (44038023258921/100000000000000 : ℝ)^3107
        have hw : |(2698276477/5000000000 : ℝ)|=(2698276477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-534005791/2500000000 : ℝ)|^4131 ≤ (401336448497/3125000000000 : ℝ)^3107
        have hw : |(-534005791/2500000000 : ℝ)|=(534005791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s5_7 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2187470381/5000000000 : ℝ)*x 0 + (2254242101/5000000000 : ℝ)*x 1 + (849084543/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2187470381/5000000000 : ℝ)^4131 ≤ (16657674674571/50000000000000 : ℝ)^3107 := by
    have hnat : (2187470381 : ℕ)^4131*50000000000000^3107 ≤ 16657674674571^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187470381 5000000000 16657674674571 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2254242101/5000000000 : ℝ)^4131 ≤ (346742044073/1000000000000 : ℝ)^3107 := by
    have hnat : (2254242101 : ℕ)^4131*1000000000000^3107 ≤ 346742044073^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254242101 5000000000 346742044073 1000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (849084543/2000000000 : ℝ)^4131 ≤ (32010446234911/100000000000000 : ℝ)^3107 := by
    have hnat : (849084543 : ℕ)^4131*100000000000000^3107 ≤ 32010446234911^3107*2000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849084543 2000000000 32010446234911 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2187470381/5000000000 : ℝ), (2254242101/5000000000 : ℝ), (849084543/2000000000 : ℝ)] ![(16657674674571/50000000000000 : ℝ), (346742044073/1000000000000 : ℝ), (32010446234911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2187470381/5000000000 : ℝ)|^4131 ≤ (16657674674571/50000000000000 : ℝ)^3107
        have hw : |(2187470381/5000000000 : ℝ)|=(2187470381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2254242101/5000000000 : ℝ)|^4131 ≤ (346742044073/1000000000000 : ℝ)^3107
        have hw : |(2254242101/5000000000 : ℝ)|=(2254242101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(849084543/2000000000 : ℝ)|^4131 ≤ (32010446234911/100000000000000 : ℝ)^3107
        have hw : |(849084543/2000000000 : ℝ)|=(849084543/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1069_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74025701/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7121/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11029/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11203/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14059/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7121/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11029/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7121/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11029/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7121/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11029/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7121/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11029/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7121/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11029/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7121/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11029/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11029/100000 : ℝ) ^ (8261/2048 : ℝ) ≤ (13736821119107381/100000000000000000000 : ℝ) := by
    have hpowers : (11029/100000 : ℝ)^8261 ≤ (13736821119107381/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11029 : ℕ)^8261*100000000000000000000^2048 ≤ 13736821119107381^2048*100000^8261 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11029 100000 13736821119107381 100000000000000000000 8261 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11029/100000 : ℝ)) (X := (13736821119107381/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7121/50000 : ℝ) ^ (8261/2048 : ℝ) ≤ (38527119662647121/100000000000000000000 : ℝ) := by
    have hpowers : (7121/50000 : ℝ)^8261 ≤ (38527119662647121/100000000000000000000 : ℝ)^2048 := by
      have hnat : (7121 : ℕ)^8261*100000000000000000000^2048 ≤ 38527119662647121^2048*50000^8261 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7121 50000 38527119662647121 100000000000000000000 8261 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7121/50000 : ℝ)) (X := (38527119662647121/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013736821119107381/50000000000000000000 : ℝ) ≤ (2500170258465153/2500000000000000 : ℝ) ^ (8261/2048 : ℝ) := by
    have hpowers : (50013736821119107381/50000000000000000000 : ℝ)^2048 ≤ (2500170258465153/2500000000000000 : ℝ)^8261 := by
      have hnat : (50013736821119107381 : ℕ)^2048*2500000000000000^8261 ≤ 2500170258465153^8261*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013736821119107381 50000000000000000000 2500170258465153 2500000000000000 2048 8261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500170258465153/2500000000000000 : ℝ)) (X := (50013736821119107381/50000000000000000000 : ℝ)) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50026131970390877251/50000000000000000000 : ℝ) ≤ (2000259086117089/2000000000000000 : ℝ) ^ (8261/2048 : ℝ) := by
    have hpowers : (50026131970390877251/50000000000000000000 : ℝ)^2048 ≤ (2000259086117089/2000000000000000 : ℝ)^8261 := by
      have hnat : (50026131970390877251 : ℕ)^2048*2000000000000000^8261 ≤ 2000259086117089^8261*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026131970390877251 50000000000000000000 2000259086117089 2000000000000000 2048 8261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000259086117089/2000000000000000 : ℝ)) (X := (50026131970390877251/50000000000000000000 : ℝ)) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50038527119662647121/50000000000000000000 : ℝ) ≤ (5000954913655139/5000000000000000 : ℝ) ^ (8261/2048 : ℝ) := by
    have hpowers : (50038527119662647121/50000000000000000000 : ℝ)^2048 ≤ (5000954913655139/5000000000000000 : ℝ)^8261 := by
      have hnat : (50038527119662647121 : ℕ)^2048*5000000000000000^8261 ≤ 5000954913655139^8261*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50038527119662647121 50000000000000000000 5000954913655139 5000000000000000 2048 8261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000954913655139/5000000000000000 : ℝ)) (X := (50038527119662647121/50000000000000000000 : ℝ)) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13736821119107381/100000000000000000000 : ℝ) ≤ ((16059317899418890021/16065000000000000000 : ℝ)+2*(614396724833/321300000000000 : ℝ)*(11029/100000 : ℝ))^(8261/2048 : ℝ) := by
    rw [show (16059317899418890021/16065000000000000000 : ℝ)+2*(614396724833/321300000000000 : ℝ)*(11029/100000 : ℝ)=(2500170258465153/2500000000000000 : ℝ) by norm_num, show 1+2*(13736821119107381/100000000000000000000 : ℝ)=(50013736821119107381/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(38527119662647121/100000000000000000000 : ℝ)+(13736821119107381/100000000000000000000 : ℝ) ≤ ((16059317899418890021/16065000000000000000 : ℝ)+(614396724833/321300000000000 : ℝ)*((7121/50000 : ℝ)+(11029/100000 : ℝ)))^(8261/2048 : ℝ) := by
    rw [show (16059317899418890021/16065000000000000000 : ℝ)+(614396724833/321300000000000 : ℝ)*((7121/50000 : ℝ)+(11029/100000 : ℝ))=(2000259086117089/2000000000000000 : ℝ) by norm_num, show 1+(38527119662647121/100000000000000000000 : ℝ)+(13736821119107381/100000000000000000000 : ℝ)=(50026131970390877251/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(38527119662647121/100000000000000000000 : ℝ) ≤ ((16059317899418890021/16065000000000000000 : ℝ)+2*(614396724833/321300000000000 : ℝ)*(7121/50000 : ℝ))^(8261/2048 : ℝ) := by
    rw [show (16059317899418890021/16065000000000000000 : ℝ)+2*(614396724833/321300000000000 : ℝ)*(7121/50000 : ℝ)=(5000954913655139/5000000000000000 : ℝ) by norm_num, show 1+2*(38527119662647121/100000000000000000000 : ℝ)=(50038527119662647121/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16059317899418890021/16065000000000000000 : ℝ)*(X 1 0+X 2 0)+(614396724833/321300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8261/2048 : ℝ)) (lo := (11029/100000 : ℝ)) (hi := (7121/50000 : ℝ)) (c := (16059317899418890021/16065000000000000000 : ℝ)) (alpha := (614396724833/321300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16059317899418890021/16065000000000000000 : ℝ)*(X 0 1+X 2 1)+(614396724833/321300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8261/2048 : ℝ)) (lo := (11029/100000 : ℝ)) (hi := (7121/50000 : ℝ)) (c := (16059317899418890021/16065000000000000000 : ℝ)) (alpha := (614396724833/321300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16059317899418890021/16065000000000000000 : ℝ)*(X 0 2+X 1 2)+(614396724833/321300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8261/2048 : ℝ)) (lo := (11029/100000 : ℝ)) (hi := (7121/50000 : ℝ)) (c := (16059317899418890021/16065000000000000000 : ℝ)) (alpha := (614396724833/321300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2202063317/10000000000 : ℝ)*X 0 0+(5396905107/10000000000 : ℝ)*X 0 1+(2631028793/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672810597/5000000000 : ℝ)*X 1 0+(-1135259237/5000000000 : ℝ)*X 1 1+(1315514361/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672810487/5000000000 : ℝ)*X 2 0+(1315514411/2500000000 : ℝ)*X 2 1+(-2270518503/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4374929453/10000000000 : ℝ)*X 0 0+(4244731819/10000000000 : ℝ)*X 0 1+(140911647/312500000 : ℝ)*X 0 2+(4374929453/10000000000 : ℝ)*X 1 0+(4244731819/10000000000 : ℝ)*X 1 1+(140911647/312500000 : ℝ)*X 1 2+(4374929453/10000000000 : ℝ)*X 2 0+(4244731819/10000000000 : ℝ)*X 2 1+(140911647/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-68814661/312500000 : ℝ)*X 0 0+(2631204147/5000000000 : ℝ)*X 0 1+(5396552961/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311647957/10000000000 : ℝ)*X 1 0+(-2136023169/10000000000 : ℝ)*X 1 1+(4216057/7812500 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311647967/10000000000 : ℝ)*X 2 0+(2698276477/5000000000 : ℝ)*X 2 1+(-534005791/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2187470381/5000000000 : ℝ)*X 0 0+(2254242101/5000000000 : ℝ)*X 0 1+(849084543/2000000000 : ℝ)*X 0 2+(2187470381/5000000000 : ℝ)*X 1 0+(2254242101/5000000000 : ℝ)*X 1 1+(849084543/2000000000 : ℝ)*X 1 2+(2187470381/5000000000 : ℝ)*X 2 0+(2254242101/5000000000 : ℝ)*X 2 1+(849084543/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (69394339368289291283/7000000000000000000000000 : ℝ) := by norm_num
    linear_combination (988017787/50000000000000 : ℝ)*(base19) + (190851461/12500000000000 : ℝ)*(base23) + (4989141/5000000000000 : ℝ)*(lower2) + (209349693/100000000000000 : ℝ)*(upper3) + (2279421/10000000000000 : ℝ)*(lower4) + (34992245977293/625000000000 : ℝ)*(major0) + (34992245977293/625000000000 : ℝ)*(major1) + (34992245977293/625000000000 : ℝ)*(major2) + (7415840057296697/100000000000000 : ℝ)*(sp0) + (7415884296904323/100000000000000 : ℝ)*(sp1) + (7415884746128209/100000000000000 : ℝ)*(sp2) + (3781596090161289/100000000000000 : ℝ)*(sp3) + (46215643201/100000000000000 : ℝ)*(sp4) + (36019183329/100000000000000 : ℝ)*(sp7) + (1890816054672309/50000000000000 : ℝ)*(f.failure) + (3707943136469949/50000000000000 : ℝ)*(f.sum) + (77055338687/31500000000000000000000000 : ℝ)*base66 + (407557610863247/196875000000000000000000000000 : ℝ)*base68 + (140235119413247/196875000000000000000000000000 : ℝ)*base70 + (349355014733407/49218750000000000000000000000 : ℝ)*base71 + (44916427153/63000000000000000000000000 : ℝ)*base74 + (1010699729407439/98437500000000000000000000000 : ℝ)*base75 + (1249839908520907/49218750000000000000000000000 : ℝ)*base77 + (332275112353609/24609375000000000000000000000 : ℝ)*base80 + (78021116431/15750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (986391/2500000000000000000000 : ℝ)*base90 + (986391/2500000000000000000000 : ℝ)*base92 + (986391/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16607785269821008261718393/6375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (492654387/100000000000000 : ℝ)*(base19) + (552347041/100000000000000 : ℝ)*(base23) + (3694731/6250000000000 : ℝ)*(upper3) + (735709/4000000000000 : ℝ)*(lower4) + (48692457/100000000000000 : ℝ)*(upper5) + (2814007652198393/50000000000000 : ℝ)*(major0) + (2814007652198393/50000000000000 : ℝ)*(major1) + (2814007652198393/50000000000000 : ℝ)*(major2) + (3102885591/25000000000000 : ℝ)*(sp1) + (7068155453/50000000000000 : ℝ)*(sp2) + (7454637743252309/100000000000000 : ℝ)*(sp4) + (3727312419527779/50000000000000 : ℝ)*(sp5) + (7454623054594363/100000000000000 : ℝ)*(sp6) + (95034819467579/2500000000000 : ℝ)*(sp7) + (95034819467579/2500000000000 : ℝ)*(f.failure) + (7454637743252309/100000000000000 : ℝ)*(f.sum) + (6420698679847/1147500000000000000000000000 : ℝ)*base65 + (1176521130054444821/114750000000000000000000000000000 : ℝ)*base68 + (1253734934303694821/114750000000000000000000000000000 : ℝ)*base70 + (1381824529200444821/114750000000000000000000000000000 : ℝ)*base72 + (191468007083/71718750000000000000000000 : ℝ)*base74 + (211292963878055179/114750000000000000000000000000000 : ℝ)*base75 + (609122987565305179/114750000000000000000000000000000 : ℝ)*base77 + (3515242362624444821/114750000000000000000000000000000 : ℝ)*base80 + (863404867429/573750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (252121/125000000000000000000 : ℝ)*base90 + (252121/125000000000000000000 : ℝ)*base92 + (252121/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1069_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74025701/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7121/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11029/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11203/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14059/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1069_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1069_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74025701/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16731/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8727/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11203/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14059/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1069_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1069_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1069_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74025701/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16731/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8727/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11203/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14059/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1069_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
