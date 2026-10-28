-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1096_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:58:52.014772+00:00
-- url     : https://prove2.me/submissions/b85bd49e-3b47-4de3-9931-e84532c2d9d1

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
theorem support_rectangle_w1096_s6_0 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2189039839/10000000000 : ℝ)*x 0 + (134857631/250000000 : ℝ)*x 1 + (1316135683/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2189039839/10000000000 : ℝ)^8289 ≤ (13297078428249/100000000000000 : ℝ)^6241 := by
    have hnat : (2189039839 : ℕ)^8289*100000000000000^6241 ≤ 13297078428249^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189039839 10000000000 13297078428249 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (134857631/250000000 : ℝ)^8289 ≤ (5506548769327/12500000000000 : ℝ)^6241 := by
    have hnat : (134857631 : ℕ)^8289*12500000000000^6241 ≤ 5506548769327^6241*250000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134857631 250000000 5506548769327 12500000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316135683/2500000000 : ℝ)^8289 ≤ (10662632848637/25000000000000 : ℝ)^6241 := by
    have hnat : (1316135683 : ℕ)^8289*25000000000000^6241 ≤ 10662632848637^6241*2500000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316135683 2500000000 10662632848637 25000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2189039839/10000000000 : ℝ), (134857631/250000000 : ℝ), (1316135683/2500000000 : ℝ)] ![(13297078428249/100000000000000 : ℝ), (5506548769327/12500000000000 : ℝ), (10662632848637/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2189039839/10000000000 : ℝ)|^8289 ≤ (13297078428249/100000000000000 : ℝ)^6241
        have hw : |(-2189039839/10000000000 : ℝ)|=(2189039839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(134857631/250000000 : ℝ)|^8289 ≤ (5506548769327/12500000000000 : ℝ)^6241
        have hw : |(134857631/250000000 : ℝ)|=(134857631/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316135683/2500000000 : ℝ)|^8289 ≤ (10662632848637/25000000000000 : ℝ)^6241
        have hw : |(1316135683/2500000000 : ℝ)|=(1316135683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s6_1 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1069004167/2000000000 : ℝ)*x 0 + (-1127438041/5000000000 : ℝ)*x 1 + (5264542661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069004167/2000000000 : ℝ)^8289 ≤ (5439829914271/12500000000000 : ℝ)^6241 := by
    have hnat : (1069004167 : ℕ)^8289*12500000000000^6241 ≤ 5439829914271^6241*2000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069004167 2000000000 5439829914271 12500000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1127438041/5000000000 : ℝ)^8289 ≤ (1383083004069/10000000000000 : ℝ)^6241 := by
    have hnat : (1127438041 : ℕ)^8289*10000000000000^6241 ≤ 1383083004069^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127438041 5000000000 1383083004069 10000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264542661/10000000000 : ℝ)^8289 ≤ (42650530630589/100000000000000 : ℝ)^6241 := by
    have hnat : (5264542661 : ℕ)^8289*100000000000000^6241 ≤ 42650530630589^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264542661 10000000000 42650530630589 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069004167/2000000000 : ℝ), (-1127438041/5000000000 : ℝ), (5264542661/10000000000 : ℝ)] ![(5439829914271/12500000000000 : ℝ), (1383083004069/10000000000000 : ℝ), (42650530630589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069004167/2000000000 : ℝ)|^8289 ≤ (5439829914271/12500000000000 : ℝ)^6241
        have hw : |(1069004167/2000000000 : ℝ)|=(1069004167/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1127438041/5000000000 : ℝ)|^8289 ≤ (1383083004069/10000000000000 : ℝ)^6241
        have hw : |(-1127438041/5000000000 : ℝ)|=(1127438041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264542661/10000000000 : ℝ)|^8289 ≤ (42650530630589/100000000000000 : ℝ)^6241
        have hw : |(5264542661/10000000000 : ℝ)|=(5264542661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s6_2 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668127609/1250000000 : ℝ)*x 0 + (658067833/1250000000 : ℝ)*x 1 + (-563719007/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668127609/1250000000 : ℝ)^8289 ≤ (1740745588571/4000000000000 : ℝ)^6241 := by
    have hnat : (668127609 : ℕ)^8289*4000000000000^6241 ≤ 1740745588571^6241*1250000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668127609 1250000000 1740745588571 4000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658067833/1250000000 : ℝ)^8289 ≤ (42650530662869/100000000000000 : ℝ)^6241 := by
    have hnat : (658067833 : ℕ)^8289*100000000000000^6241 ≤ 42650530662869^6241*1250000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658067833 1250000000 42650530662869 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (563719007/2500000000 : ℝ)^8289 ≤ (13830829600777/100000000000000 : ℝ)^6241 := by
    have hnat : (563719007 : ℕ)^8289*100000000000000^6241 ≤ 13830829600777^6241*2500000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563719007 2500000000 13830829600777 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668127609/1250000000 : ℝ), (658067833/1250000000 : ℝ), (-563719007/2500000000 : ℝ)] ![(1740745588571/4000000000000 : ℝ), (42650530662869/100000000000000 : ℝ), (13830829600777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668127609/1250000000 : ℝ)|^8289 ≤ (1740745588571/4000000000000 : ℝ)^6241
        have hw : |(668127609/1250000000 : ℝ)|=(668127609/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658067833/1250000000 : ℝ)|^8289 ≤ (42650530662869/100000000000000 : ℝ)^6241
        have hw : |(658067833/1250000000 : ℝ)|=(658067833/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-563719007/2500000000 : ℝ)|^8289 ≤ (13830829600777/100000000000000 : ℝ)^6241
        have hw : |(-563719007/2500000000 : ℝ)|=(563719007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s6_3 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2185585907/5000000000 : ℝ)*x 0 + (169805531/400000000 : ℝ)*x 1 + (4500970463/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2185585907/5000000000 : ℝ)^8289 ≤ (16658241821329/50000000000000 : ℝ)^6241 := by
    have hnat : (2185585907 : ℕ)^8289*50000000000000^6241 ≤ 16658241821329^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185585907 5000000000 16658241821329 50000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169805531/400000000 : ℝ)^8289 ≤ (16023360649729/50000000000000 : ℝ)^6241 := by
    have hnat : (169805531 : ℕ)^8289*50000000000000^6241 ≤ 16023360649729^6241*400000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169805531 400000000 16023360649729 50000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4500970463/10000000000 : ℝ)^8289 ≤ (17318397524793/50000000000000 : ℝ)^6241 := by
    have hnat : (4500970463 : ℕ)^8289*50000000000000^6241 ≤ 17318397524793^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4500970463 10000000000 17318397524793 50000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2185585907/5000000000 : ℝ), (169805531/400000000 : ℝ), (4500970463/10000000000 : ℝ)] ![(16658241821329/50000000000000 : ℝ), (16023360649729/50000000000000 : ℝ), (17318397524793/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2185585907/5000000000 : ℝ)|^8289 ≤ (16658241821329/50000000000000 : ℝ)^6241
        have hw : |(2185585907/5000000000 : ℝ)|=(2185585907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169805531/400000000 : ℝ)|^8289 ≤ (16023360649729/50000000000000 : ℝ)^6241
        have hw : |(169805531/400000000 : ℝ)|=(169805531/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4500970463/10000000000 : ℝ)|^8289 ≤ (17318397524793/50000000000000 : ℝ)^6241
        have hw : |(4500970463/10000000000 : ℝ)|=(4500970463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s6_4 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-13681531/62500000 : ℝ)*x 0 + (2632435171/5000000000 : ℝ)*x 1 + (2696988211/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13681531/62500000 : ℝ)^8289 ≤ (13297119743031/100000000000000 : ℝ)^6241 := by
    have hnat : (13681531 : ℕ)^8289*100000000000000^6241 ≤ 13297119743031^6241*62500000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13681531 62500000 13297119743031 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632435171/5000000000 : ℝ)^8289 ≤ (5331757063737/12500000000000 : ℝ)^6241 := by
    have hnat : (2632435171 : ℕ)^8289*12500000000000^6241 ≤ 5331757063737^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632435171 5000000000 5331757063737 12500000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696988211/5000000000 : ℝ)^8289 ≤ (44048823729117/100000000000000 : ℝ)^6241 := by
    have hnat : (2696988211 : ℕ)^8289*100000000000000^6241 ≤ 44048823729117^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696988211 5000000000 44048823729117 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-13681531/62500000 : ℝ), (2632435171/5000000000 : ℝ), (2696988211/5000000000 : ℝ)] ![(13297119743031/100000000000000 : ℝ), (5331757063737/12500000000000 : ℝ), (44048823729117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-13681531/62500000 : ℝ)|^8289 ≤ (13297119743031/100000000000000 : ℝ)^6241
        have hw : |(-13681531/62500000 : ℝ)|=(13681531/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632435171/5000000000 : ℝ)|^8289 ≤ (5331757063737/12500000000000 : ℝ)^6241
        have hw : |(2632435171/5000000000 : ℝ)|=(2632435171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696988211/5000000000 : ℝ)|^8289 ≤ (44048823729117/100000000000000 : ℝ)^6241
        have hw : |(2696988211/5000000000 : ℝ)|=(2696988211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s6_5 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312259277/10000000000 : ℝ)*x 0 + (-425088461/2000000000 : ℝ)*x 1 + (5393976409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312259277/10000000000 : ℝ)^8289 ≤ (43164722801889/100000000000000 : ℝ)^6241 := by
    have hnat : (5312259277 : ℕ)^8289*100000000000000^6241 ≤ 43164722801889^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312259277 10000000000 43164722801889 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (425088461/2000000000 : ℝ)^8289 ≤ (12786453602213/100000000000000 : ℝ)^6241 := by
    have hnat : (425088461 : ℕ)^8289*100000000000000^6241 ≤ 12786453602213^6241*2000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425088461 2000000000 12786453602213 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393976409/10000000000 : ℝ)^8289 ≤ (22024411794059/50000000000000 : ℝ)^6241 := by
    have hnat : (5393976409 : ℕ)^8289*50000000000000^6241 ≤ 22024411794059^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393976409 10000000000 22024411794059 50000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312259277/10000000000 : ℝ), (-425088461/2000000000 : ℝ), (5393976409/10000000000 : ℝ)] ![(43164722801889/100000000000000 : ℝ), (12786453602213/100000000000000 : ℝ), (22024411794059/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312259277/10000000000 : ℝ)|^8289 ≤ (43164722801889/100000000000000 : ℝ)^6241
        have hw : |(5312259277/10000000000 : ℝ)|=(5312259277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-425088461/2000000000 : ℝ)|^8289 ≤ (12786453602213/100000000000000 : ℝ)^6241
        have hw : |(-425088461/2000000000 : ℝ)|=(425088461/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393976409/10000000000 : ℝ)|^8289 ≤ (22024411794059/50000000000000 : ℝ)^6241
        have hw : |(5393976409/10000000000 : ℝ)|=(5393976409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s6_6 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664032409/1250000000 : ℝ)*x 0 + (2696988201/5000000000 : ℝ)*x 1 + (-2125442321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664032409/1250000000 : ℝ)^8289 ≤ (4316472274793/10000000000000 : ℝ)^6241 := by
    have hnat : (664032409 : ℕ)^8289*10000000000000^6241 ≤ 4316472274793^6241*1250000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664032409 1250000000 4316472274793 10000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696988201/5000000000 : ℝ)^8289 ≤ (11012205878049/25000000000000 : ℝ)^6241 := by
    have hnat : (2696988201 : ℕ)^8289*25000000000000^6241 ≤ 11012205878049^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696988201 5000000000 11012205878049 25000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2125442321/10000000000 : ℝ)^8289 ≤ (12786453730053/100000000000000 : ℝ)^6241 := by
    have hnat : (2125442321 : ℕ)^8289*100000000000000^6241 ≤ 12786453730053^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125442321 10000000000 12786453730053 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664032409/1250000000 : ℝ), (2696988201/5000000000 : ℝ), (-2125442321/10000000000 : ℝ)] ![(4316472274793/10000000000000 : ℝ), (11012205878049/25000000000000 : ℝ), (12786453730053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664032409/1250000000 : ℝ)|^8289 ≤ (4316472274793/10000000000000 : ℝ)^6241
        have hw : |(664032409/1250000000 : ℝ)|=(664032409/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696988201/5000000000 : ℝ)|^8289 ≤ (11012205878049/25000000000000 : ℝ)^6241
        have hw : |(2696988201/5000000000 : ℝ)|=(2696988201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2125442321/10000000000 : ℝ)|^8289 ≤ (12786453730053/100000000000000 : ℝ)^6241
        have hw : |(-2125442321/10000000000 : ℝ)|=(2125442321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s6_7 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2185590893/5000000000 : ℝ)*x 0 + (2250162217/5000000000 : ℝ)*x 1 + (4245786729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2185590893/5000000000 : ℝ)^8289 ≤ (8329146147313/25000000000000 : ℝ)^6241 := by
    have hnat : (2185590893 : ℕ)^8289*25000000000000^6241 ≤ 8329146147313^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185590893 5000000000 8329146147313 25000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2250162217/5000000000 : ℝ)^8289 ≤ (34630192353927/100000000000000 : ℝ)^6241 := by
    have hnat : (2250162217 : ℕ)^8289*100000000000000^6241 ≤ 34630192353927^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250162217 5000000000 34630192353927 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4245786729/10000000000 : ℝ)^8289 ≤ (16026611521069/50000000000000 : ℝ)^6241 := by
    have hnat : (4245786729 : ℕ)^8289*50000000000000^6241 ≤ 16026611521069^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4245786729 10000000000 16026611521069 50000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2185590893/5000000000 : ℝ), (2250162217/5000000000 : ℝ), (4245786729/10000000000 : ℝ)] ![(8329146147313/25000000000000 : ℝ), (34630192353927/100000000000000 : ℝ), (16026611521069/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2185590893/5000000000 : ℝ)|^8289 ≤ (8329146147313/25000000000000 : ℝ)^6241
        have hw : |(2185590893/5000000000 : ℝ)|=(2185590893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2250162217/5000000000 : ℝ)|^8289 ≤ (34630192353927/100000000000000 : ℝ)^6241
        have hw : |(2250162217/5000000000 : ℝ)|=(2250162217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4245786729/10000000000 : ℝ)|^8289 ≤ (16026611521069/50000000000000 : ℝ)^6241
        have hw : |(4245786729/10000000000 : ℝ)|=(4245786729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1096_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37144247/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1407/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5623/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11283/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14031/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1407/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5623/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1407/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5623/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1407/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5623/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1407/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5623/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1407/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5623/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1407/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5623/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5623/50000 : ℝ) ^ (259/64 : ℝ) ≤ (72190135335651/500000000000000000 : ℝ) := by
    have hpowers : (5623/50000 : ℝ)^259 ≤ (72190135335651/500000000000000000 : ℝ)^64 := by
      have hnat : (5623 : ℕ)^259*500000000000000000^64 ≤ 72190135335651^64*50000^259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5623 50000 72190135335651 500000000000000000 259 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5623/50000 : ℝ)) (X := (72190135335651/500000000000000000 : ℝ)) (by norm_num) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have hpowhi : (1407/10000 : ℝ) ^ (259/64 : ℝ) ≤ (35748076245909549/100000000000000000000 : ℝ) := by
    have hpowers : (1407/10000 : ℝ)^259 ≤ (35748076245909549/100000000000000000000 : ℝ)^64 := by
      have hnat : (1407 : ℕ)^259*100000000000000000000^64 ≤ 35748076245909549^64*10000^259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1407 10000 35748076245909549 100000000000000000000 259 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1407/10000 : ℝ)) (X := (35748076245909549/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (250072190135335651/250000000000000000 : ℝ) ≤ (2500178365502651/2500000000000000 : ℝ) ^ (259/64 : ℝ) := by
    have hpowers : (250072190135335651/250000000000000000 : ℝ)^64 ≤ (2500178365502651/2500000000000000 : ℝ)^259 := by
      have hnat : (250072190135335651 : ℕ)^64*2500000000000000^259 ≤ 2500178365502651^259*250000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        250072190135335651 250000000000000000 2500178365502651 2500000000000000 64 259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500178365502651/2500000000000000 : ℝ)) (X := (250072190135335651/250000000000000000 : ℝ)) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050186103313039749/100000000000000000000 : ℝ) ≤ (10001239885707043/10000000000000000 : ℝ) ^ (259/64 : ℝ) := by
    have hpowers : (100050186103313039749/100000000000000000000 : ℝ)^64 ≤ (10001239885707043/10000000000000000 : ℝ)^259 := by
      have hnat : (100050186103313039749 : ℕ)^64*10000000000000000^259 ≤ 10001239885707043^259*100000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050186103313039749 100000000000000000000 10001239885707043 10000000000000000 64 259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001239885707043/10000000000000000 : ℝ)) (X := (100050186103313039749/100000000000000000000 : ℝ)) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035748076245909549/50000000000000000000 : ℝ) ≤ (5000883154701741/5000000000000000 : ℝ) ^ (259/64 : ℝ) := by
    have hpowers : (50035748076245909549/50000000000000000000 : ℝ)^64 ≤ (5000883154701741/5000000000000000 : ℝ)^259 := by
      have hnat : (50035748076245909549 : ℕ)^64*5000000000000000^259 ≤ 5000883154701741^259*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035748076245909549 50000000000000000000 5000883154701741 5000000000000000 64 259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000883154701741/5000000000000000 : ℝ)) (X := (50035748076245909549/50000000000000000000 : ℝ)) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(72190135335651/500000000000000000 : ℝ) ≤ ((7057543623734409927/7060000000000000000 : ℝ)+2*(526423696439/282400000000000 : ℝ)*(5623/50000 : ℝ))^(259/64 : ℝ) := by
    rw [show (7057543623734409927/7060000000000000000 : ℝ)+2*(526423696439/282400000000000 : ℝ)*(5623/50000 : ℝ)=(2500178365502651/2500000000000000 : ℝ) by norm_num, show 1+2*(72190135335651/500000000000000000 : ℝ)=(250072190135335651/250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35748076245909549/100000000000000000000 : ℝ)+(72190135335651/500000000000000000 : ℝ) ≤ ((7057543623734409927/7060000000000000000 : ℝ)+(526423696439/282400000000000 : ℝ)*((1407/10000 : ℝ)+(5623/50000 : ℝ)))^(259/64 : ℝ) := by
    rw [show (7057543623734409927/7060000000000000000 : ℝ)+(526423696439/282400000000000 : ℝ)*((1407/10000 : ℝ)+(5623/50000 : ℝ))=(10001239885707043/10000000000000000 : ℝ) by norm_num, show 1+(35748076245909549/100000000000000000000 : ℝ)+(72190135335651/500000000000000000 : ℝ)=(100050186103313039749/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35748076245909549/100000000000000000000 : ℝ) ≤ ((7057543623734409927/7060000000000000000 : ℝ)+2*(526423696439/282400000000000 : ℝ)*(1407/10000 : ℝ))^(259/64 : ℝ) := by
    rw [show (7057543623734409927/7060000000000000000 : ℝ)+2*(526423696439/282400000000000 : ℝ)*(1407/10000 : ℝ)=(5000883154701741/5000000000000000 : ℝ) by norm_num, show 1+2*(35748076245909549/100000000000000000000 : ℝ)=(50035748076245909549/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7057543623734409927/7060000000000000000 : ℝ)*(X 1 0+X 2 0)+(526423696439/282400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (259/64 : ℝ)) (lo := (5623/50000 : ℝ)) (hi := (1407/10000 : ℝ)) (c := (7057543623734409927/7060000000000000000 : ℝ)) (alpha := (526423696439/282400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7057543623734409927/7060000000000000000 : ℝ)*(X 0 1+X 2 1)+(526423696439/282400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (259/64 : ℝ)) (lo := (5623/50000 : ℝ)) (hi := (1407/10000 : ℝ)) (c := (7057543623734409927/7060000000000000000 : ℝ)) (alpha := (526423696439/282400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7057543623734409927/7060000000000000000 : ℝ)*(X 0 2+X 1 2)+(526423696439/282400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (259/64 : ℝ)) (lo := (5623/50000 : ℝ)) (hi := (1407/10000 : ℝ)) (c := (7057543623734409927/7060000000000000000 : ℝ)) (alpha := (526423696439/282400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2189039839/10000000000 : ℝ)*X 0 0+(134857631/250000000 : ℝ)*X 0 1+(1316135683/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069004167/2000000000 : ℝ)*X 1 0+(-1127438041/5000000000 : ℝ)*X 1 1+(5264542661/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668127609/1250000000 : ℝ)*X 2 0+(658067833/1250000000 : ℝ)*X 2 1+(-563719007/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2185585907/5000000000 : ℝ)*X 0 0+(169805531/400000000 : ℝ)*X 0 1+(4500970463/10000000000 : ℝ)*X 0 2+(2185585907/5000000000 : ℝ)*X 1 0+(169805531/400000000 : ℝ)*X 1 1+(4500970463/10000000000 : ℝ)*X 1 2+(2185585907/5000000000 : ℝ)*X 2 0+(169805531/400000000 : ℝ)*X 2 1+(4500970463/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-13681531/62500000 : ℝ)*X 0 0+(2632435171/5000000000 : ℝ)*X 0 1+(2696988211/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312259277/10000000000 : ℝ)*X 1 0+(-425088461/2000000000 : ℝ)*X 1 1+(5393976409/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664032409/1250000000 : ℝ)*X 2 0+(2696988201/5000000000 : ℝ)*X 2 1+(-2125442321/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2185590893/5000000000 : ℝ)*X 0 0+(2250162217/5000000000 : ℝ)*X 0 1+(4245786729/10000000000 : ℝ)*X 0 2+(2185590893/5000000000 : ℝ)*X 1 0+(2250162217/5000000000 : ℝ)*X 1 1+(4245786729/10000000000 : ℝ)*X 1 2+(2185590893/5000000000 : ℝ)*X 2 0+(2250162217/5000000000 : ℝ)*X 2 1+(4245786729/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1766067951386419859235194229/353000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (152534699/12500000000000 : ℝ)*(base19) + (1156194247/100000000000000 : ℝ)*(base23) + (15691631/25000000000000 : ℝ)*(lower2) + (61423007/50000000000000 : ℝ)*(upper3) + (6502423/5000000000000 : ℝ)*(upper5) + (5807645679729791/100000000000000 : ℝ)*(major0) + (5807645679729791/100000000000000 : ℝ)*(major1) + (5807645679729791/100000000000000 : ℝ)*(major2) + (192660356189667/2500000000000 : ℝ)*(sp0) + (7706443953992159/100000000000000 : ℝ)*(sp1) + (481652751129719/6250000000000 : ℝ)*(sp2) + (1954414359532061/50000000000000 : ℝ)*(sp3) + (30926683071/100000000000000 : ℝ)*(sp4) + (8649679093/50000000000000 : ℝ)*(sp7) + (977211504605577/25000000000000 : ℝ)*(f.failure) + (7706445174269751/100000000000000 : ℝ)*(f.sum) + (127420440479369/14120000000000000000000000000 : ℝ)*base65 + (3400533610691739743/706000000000000000000000000000000 : ℝ)*base68 + (7366860152832260257/706000000000000000000000000000000 : ℝ)*base69 + (9948005707130260257/706000000000000000000000000000000 : ℝ)*base71 + (25080030181929/14120000000000000000000000000 : ℝ)*base73 + (8123085811329739743/706000000000000000000000000000000 : ℝ)*base76 + (7921583280692260257/706000000000000000000000000000000 : ℝ)*base77 + (6651692652464260257/706000000000000000000000000000000 : ℝ)*base79 + (80329066486089/14120000000000000000000000000 : ℝ)*base81 + (4084481/625000000000000000000 : ℝ)*base90 + (4084481/625000000000000000000 : ℝ)*base92 + (4084481/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (562690523826392242203950331/353000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (510231001/100000000000000 : ℝ)*(base19) + (257312363/50000000000000 : ℝ)*(base23) + (674521/6250000000000 : ℝ)*(upper2) + (39629/100000000000 : ℝ)*(upper3) + (3136891/5000000000000 : ℝ)*(upper5) + (5837129849079483/100000000000000 : ℝ)*(major0) + (5837129849079483/100000000000000 : ℝ)*(major1) + (5837129849079483/100000000000000 : ℝ)*(major2) + (7158695687/50000000000000 : ℝ)*(sp1) + (3229429739/25000000000000 : ℝ)*(sp2) + (1936392313794563/25000000000000 : ℝ)*(sp4) + (1936388606888969/25000000000000 : ℝ)*(sp5) + (7745555822834569/100000000000000 : ℝ)*(sp6) + (982172597461641/25000000000000 : ℝ)*(sp7) + (982172597461641/25000000000000 : ℝ)*(f.failure) + (1936392313794563/25000000000000 : ℝ)*(f.sum) + (63861365121043/14120000000000000000000000000 : ℝ)*base66 + (1040117315893152741/706000000000000000000000000000000 : ℝ)*base67 + (7304966078653152741/706000000000000000000000000000000 : ℝ)*base69 + (3241936963977152741/706000000000000000000000000000000 : ℝ)*base71 + (85936863202323/14120000000000000000000000000 : ℝ)*base74 + (11092965903929152741/706000000000000000000000000000000 : ℝ)*base75 + (879460136629152741/706000000000000000000000000000000 : ℝ)*base77 + (19056406115265152741/706000000000000000000000000000000 : ℝ)*base79 + (104360269413643/14120000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2420673/625000000000000000000 : ℝ)*base90 + (2420673/625000000000000000000 : ℝ)*base92 + (2420673/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1096_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37144247/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1407/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5623/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11283/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14031/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1096_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1096_s7_0 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1094537823/5000000000 : ℝ)*x 0 + (539390237/1000000000 : ℝ)*x 1 + (5264921977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1094537823/5000000000 : ℝ)^8289 ≤ (6648683654839/50000000000000 : ℝ)^6241 := by
    have hnat : (1094537823 : ℕ)^8289*50000000000000^6241 ≤ 6648683654839^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094537823 5000000000 6648683654839 50000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539390237/1000000000 : ℝ)^8289 ≤ (688250321191/1562500000000 : ℝ)^6241 := by
    have hnat : (539390237 : ℕ)^8289*1562500000000^6241 ≤ 688250321191^6241*1000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539390237 1000000000 688250321191 1562500000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264921977/10000000000 : ℝ)^8289 ≤ (21327306057033/50000000000000 : ℝ)^6241 := by
    have hnat : (5264921977 : ℕ)^8289*50000000000000^6241 ≤ 21327306057033^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264921977 10000000000 21327306057033 50000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1094537823/5000000000 : ℝ), (539390237/1000000000 : ℝ), (5264921977/10000000000 : ℝ)] ![(6648683654839/50000000000000 : ℝ), (688250321191/1562500000000 : ℝ), (21327306057033/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1094537823/5000000000 : ℝ)|^8289 ≤ (6648683654839/50000000000000 : ℝ)^6241
        have hw : |(-1094537823/5000000000 : ℝ)|=(1094537823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539390237/1000000000 : ℝ)|^8289 ≤ (688250321191/1562500000000 : ℝ)^6241
        have hw : |(539390237/1000000000 : ℝ)|=(539390237/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264921977/10000000000 : ℝ)|^8289 ≤ (21327306057033/50000000000000 : ℝ)^6241
        have hw : |(5264921977/10000000000 : ℝ)|=(5264921977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s7_1 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344919613/10000000000 : ℝ)*x 0 + (-2254509309/10000000000 : ℝ)*x 1 + (1052984413/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344919613/10000000000 : ℝ)^8289 ≤ (43517544734373/100000000000000 : ℝ)^6241 := by
    have hnat : (5344919613 : ℕ)^8289*100000000000000^6241 ≤ 43517544734373^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344919613 10000000000 43517544734373 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2254509309/10000000000 : ℝ)^8289 ≤ (3456960546817/25000000000000 : ℝ)^6241 := by
    have hnat : (2254509309 : ℕ)^8289*25000000000000^6241 ≤ 3456960546817^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254509309 10000000000 3456960546817 25000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052984413/2000000000 : ℝ)^8289 ≤ (42654613060967/100000000000000 : ℝ)^6241 := by
    have hnat : (1052984413 : ℕ)^8289*100000000000000^6241 ≤ 42654613060967^6241*2000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052984413 2000000000 42654613060967 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344919613/10000000000 : ℝ), (-2254509309/10000000000 : ℝ), (1052984413/2000000000 : ℝ)] ![(43517544734373/100000000000000 : ℝ), (3456960546817/25000000000000 : ℝ), (42654613060967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344919613/10000000000 : ℝ)|^8289 ≤ (43517544734373/100000000000000 : ℝ)^6241
        have hw : |(5344919613/10000000000 : ℝ)|=(5344919613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2254509309/10000000000 : ℝ)|^8289 ≤ (3456960546817/25000000000000 : ℝ)^6241
        have hw : |(-2254509309/10000000000 : ℝ)|=(2254509309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052984413/2000000000 : ℝ)|^8289 ≤ (42654613060967/100000000000000 : ℝ)^6241
        have hw : |(1052984413/2000000000 : ℝ)|=(1052984413/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s7_2 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672459917/5000000000 : ℝ)*x 0 + (1316230479/2500000000 : ℝ)*x 1 + (-2254509213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672459917/5000000000 : ℝ)^8289 ≤ (5439693390523/12500000000000 : ℝ)^6241 := by
    have hnat : (2672459917 : ℕ)^8289*12500000000000^6241 ≤ 5439693390523^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672459917 5000000000 5439693390523 12500000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316230479/2500000000 : ℝ)^8289 ≤ (42654611457691/100000000000000 : ℝ)^6241 := by
    have hnat : (1316230479 : ℕ)^8289*100000000000000^6241 ≤ 42654611457691^6241*2500000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316230479 2500000000 42654611457691 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2254509213/10000000000 : ℝ)^8289 ≤ (13827841405241/100000000000000 : ℝ)^6241 := by
    have hnat : (2254509213 : ℕ)^8289*100000000000000^6241 ≤ 13827841405241^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254509213 10000000000 13827841405241 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672459917/5000000000 : ℝ), (1316230479/2500000000 : ℝ), (-2254509213/10000000000 : ℝ)] ![(5439693390523/12500000000000 : ℝ), (42654611457691/100000000000000 : ℝ), (13827841405241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672459917/5000000000 : ℝ)|^8289 ≤ (5439693390523/12500000000000 : ℝ)^6241
        have hw : |(2672459917/5000000000 : ℝ)|=(2672459917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316230479/2500000000 : ℝ)|^8289 ≤ (42654611457691/100000000000000 : ℝ)^6241
        have hw : |(1316230479/2500000000 : ℝ)|=(1316230479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2254509213/10000000000 : ℝ)|^8289 ≤ (13827841405241/100000000000000 : ℝ)^6241
        have hw : |(-2254509213/10000000000 : ℝ)|=(2254509213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s7_3 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4371191789/10000000000 : ℝ)*x 0 + (84918139/200000000 : ℝ)*x 1 + (4500196579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4371191789/10000000000 : ℝ)^8289 ≤ (6663337169947/20000000000000 : ℝ)^6241 := by
    have hnat : (4371191789 : ℕ)^8289*20000000000000^6241 ≤ 6663337169947^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4371191789 10000000000 6663337169947 20000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84918139/200000000 : ℝ)^8289 ≤ (32054428477261/100000000000000 : ℝ)^6241 := by
    have hnat : (84918139 : ℕ)^8289*100000000000000^6241 ≤ 32054428477261^6241*200000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84918139 200000000 32054428477261 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4500196579/10000000000 : ℝ)^8289 ≤ (34628885657423/100000000000000 : ℝ)^6241 := by
    have hnat : (4500196579 : ℕ)^8289*100000000000000^6241 ≤ 34628885657423^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4500196579 10000000000 34628885657423 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4371191789/10000000000 : ℝ), (84918139/200000000 : ℝ), (4500196579/10000000000 : ℝ)] ![(6663337169947/20000000000000 : ℝ), (32054428477261/100000000000000 : ℝ), (34628885657423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4371191789/10000000000 : ℝ)|^8289 ≤ (6663337169947/20000000000000 : ℝ)^6241
        have hw : |(4371191789/10000000000 : ℝ)|=(4371191789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(84918139/200000000 : ℝ)|^8289 ≤ (32054428477261/100000000000000 : ℝ)^6241
        have hw : |(84918139/200000000 : ℝ)|=(84918139/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4500196579/10000000000 : ℝ)|^8289 ≤ (34628885657423/100000000000000 : ℝ)^6241
        have hw : |(4500196579/10000000000 : ℝ)|=(4500196579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s7_4 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1094540373/5000000000 : ℝ)*x 0 + (5265245773/10000000000 : ℝ)*x 1 + (674197167/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1094540373/5000000000 : ℝ)^8289 ≤ (13297408455259/100000000000000 : ℝ)^6241 := by
    have hnat : (1094540373 : ℕ)^8289*100000000000000^6241 ≤ 13297408455259^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094540373 5000000000 13297408455259 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265245773/10000000000 : ℝ)^8289 ≤ (21329048136173/50000000000000 : ℝ)^6241 := by
    have hnat : (5265245773 : ℕ)^8289*50000000000000^6241 ≤ 21329048136173^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265245773 10000000000 21329048136173 50000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674197167/1250000000 : ℝ)^8289 ≤ (44044495258741/100000000000000 : ℝ)^6241 := by
    have hnat : (674197167 : ℕ)^8289*100000000000000^6241 ≤ 44044495258741^6241*1250000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674197167 1250000000 44044495258741 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1094540373/5000000000 : ℝ), (5265245773/10000000000 : ℝ), (674197167/1250000000 : ℝ)] ![(13297408455259/100000000000000 : ℝ), (21329048136173/50000000000000 : ℝ), (44044495258741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1094540373/5000000000 : ℝ)|^8289 ≤ (13297408455259/100000000000000 : ℝ)^6241
        have hw : |(-1094540373/5000000000 : ℝ)|=(1094540373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265245773/10000000000 : ℝ)|^8289 ≤ (21329048136173/50000000000000 : ℝ)^6241
        have hw : |(5265245773/10000000000 : ℝ)|=(5265245773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674197167/1250000000 : ℝ)|^8289 ≤ (44044495258741/100000000000000 : ℝ)^6241
        have hw : |(674197167/1250000000 : ℝ)|=(674197167/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s7_5 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656177761/5000000000 : ℝ)*x 0 + (-1062927007/5000000000 : ℝ)*x 1 + (2696788667/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656177761/5000000000 : ℝ)^8289 ≤ (10791440367691/25000000000000 : ℝ)^6241 := by
    have hnat : (2656177761 : ℕ)^8289*25000000000000^6241 ≤ 10791440367691^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656177761 5000000000 10791440367691 25000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1062927007/5000000000 : ℝ)^8289 ≤ (12789743276547/100000000000000 : ℝ)^6241 := by
    have hnat : (1062927007 : ℕ)^8289*100000000000000^6241 ≤ 12789743276547^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062927007 5000000000 12789743276547 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696788667/5000000000 : ℝ)^8289 ≤ (880889904741/2000000000000 : ℝ)^6241 := by
    have hnat : (2696788667 : ℕ)^8289*2000000000000^6241 ≤ 880889904741^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696788667 5000000000 880889904741 2000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656177761/5000000000 : ℝ), (-1062927007/5000000000 : ℝ), (2696788667/5000000000 : ℝ)] ![(10791440367691/25000000000000 : ℝ), (12789743276547/100000000000000 : ℝ), (880889904741/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656177761/5000000000 : ℝ)|^8289 ≤ (10791440367691/25000000000000 : ℝ)^6241
        have hw : |(2656177761/5000000000 : ℝ)|=(2656177761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1062927007/5000000000 : ℝ)|^8289 ≤ (12789743276547/100000000000000 : ℝ)^6241
        have hw : |(-1062927007/5000000000 : ℝ)|=(1062927007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696788667/5000000000 : ℝ)|^8289 ≤ (880889904741/2000000000000 : ℝ)^6241
        have hw : |(2696788667/5000000000 : ℝ)|=(2696788667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s7_6 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312355523/10000000000 : ℝ)*x 0 + (5393577333/10000000000 : ℝ)*x 1 + (-1062927007/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312355523/10000000000 : ℝ)^8289 ≤ (10791440370389/25000000000000 : ℝ)^6241 := by
    have hnat : (5312355523 : ℕ)^8289*25000000000000^6241 ≤ 10791440370389^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312355523 10000000000 10791440370389 25000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393577333/10000000000 : ℝ)^8289 ≤ (11011123806551/25000000000000 : ℝ)^6241 := by
    have hnat : (5393577333 : ℕ)^8289*25000000000000^6241 ≤ 11011123806551^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393577333 10000000000 11011123806551 25000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1062927007/5000000000 : ℝ)^8289 ≤ (12789743276547/100000000000000 : ℝ)^6241 := by
    have hnat : (1062927007 : ℕ)^8289*100000000000000^6241 ≤ 12789743276547^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062927007 5000000000 12789743276547 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312355523/10000000000 : ℝ), (5393577333/10000000000 : ℝ), (-1062927007/5000000000 : ℝ)] ![(10791440370389/25000000000000 : ℝ), (11011123806551/25000000000000 : ℝ), (12789743276547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312355523/10000000000 : ℝ)|^8289 ≤ (10791440370389/25000000000000 : ℝ)^6241
        have hw : |(5312355523/10000000000 : ℝ)|=(5312355523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393577333/10000000000 : ℝ)|^8289 ≤ (11011123806551/25000000000000 : ℝ)^6241
        have hw : |(5393577333/10000000000 : ℝ)|=(5393577333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1062927007/5000000000 : ℝ)|^8289 ≤ (12789743276547/100000000000000 : ℝ)^6241
        have hw : |(-1062927007/5000000000 : ℝ)|=(1062927007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s7_7 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (874240317/2000000000 : ℝ)*x 0 + (4499558343/10000000000 : ℝ)*x 1 + (1061636891/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (874240317/2000000000 : ℝ)^8289 ≤ (8329196253707/25000000000000 : ℝ)^6241 := by
    have hnat : (874240317 : ℕ)^8289*25000000000000^6241 ≤ 8329196253707^6241*2000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874240317 2000000000 8329196253707 25000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4499558343/10000000000 : ℝ)^8289 ≤ (8655590743957/25000000000000 : ℝ)^6241 := by
    have hnat : (4499558343 : ℕ)^8289*25000000000000^6241 ≤ 8655590743957^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4499558343 10000000000 8655590743957 25000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1061636891/2500000000 : ℝ)^8289 ≤ (16030425995807/50000000000000 : ℝ)^6241 := by
    have hnat : (1061636891 : ℕ)^8289*50000000000000^6241 ≤ 16030425995807^6241*2500000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061636891 2500000000 16030425995807 50000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(874240317/2000000000 : ℝ), (4499558343/10000000000 : ℝ), (1061636891/2500000000 : ℝ)] ![(8329196253707/25000000000000 : ℝ), (8655590743957/25000000000000 : ℝ), (16030425995807/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(874240317/2000000000 : ℝ)|^8289 ≤ (8329196253707/25000000000000 : ℝ)^6241
        have hw : |(874240317/2000000000 : ℝ)|=(874240317/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4499558343/10000000000 : ℝ)|^8289 ≤ (8655590743957/25000000000000 : ℝ)^6241
        have hw : |(4499558343/10000000000 : ℝ)|=(4499558343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1061636891/2500000000 : ℝ)|^8289 ≤ (16030425995807/50000000000000 : ℝ)^6241
        have hw : |(1061636891/2500000000 : ℝ)|=(1061636891/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1096_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37144247/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14031/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11283/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11291/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14023/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14031/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11283/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14031/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11283/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14031/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11283/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14031/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11283/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14031/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11283/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14031/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11283/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11283/100000 : ℝ) ^ (259/64 : ℝ) ≤ (2926245445807953/20000000000000000000 : ℝ) := by
    have hpowers : (11283/100000 : ℝ)^259 ≤ (2926245445807953/20000000000000000000 : ℝ)^64 := by
      have hnat : (11283 : ℕ)^259*20000000000000000000^64 ≤ 2926245445807953^64*100000^259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11283 100000 2926245445807953 20000000000000000000 259 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11283/100000 : ℝ)) (X := (2926245445807953/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have hpowhi : (14031/100000 : ℝ) ^ (259/64 : ℝ) ≤ (35348767652501511/100000000000000000000 : ℝ) := by
    have hpowers : (14031/100000 : ℝ)^259 ≤ (35348767652501511/100000000000000000000 : ℝ)^64 := by
      have hnat : (14031 : ℕ)^259*100000000000000000000^64 ≤ 35348767652501511^64*100000^259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14031 100000 35348767652501511 100000000000000000000 259 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14031/100000 : ℝ)) (X := (35348767652501511/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002926245445807953/10000000000000000000 : ℝ) ≤ (5000361504018767/5000000000000000 : ℝ) ^ (259/64 : ℝ) := by
    have hpowers : (10002926245445807953/10000000000000000000 : ℝ)^64 ≤ (5000361504018767/5000000000000000 : ℝ)^259 := by
      have hnat : (10002926245445807953 : ℕ)^64*5000000000000000^259 ≤ 5000361504018767^259*10000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002926245445807953 10000000000000000000 5000361504018767 5000000000000000 64 259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000361504018767/5000000000000000 : ℝ)) (X := (10002926245445807953/10000000000000000000 : ℝ)) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012494998720385319/25000000000000000000 : ℝ) ≤ (2000246958919953/2000000000000000 : ℝ) ^ (259/64 : ℝ) := by
    have hpowers : (25012494998720385319/25000000000000000000 : ℝ)^64 ≤ (2000246958919953/2000000000000000 : ℝ)^259 := by
      have hnat : (25012494998720385319 : ℕ)^64*2000000000000000^259 ≤ 2000246958919953^259*25000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012494998720385319 25000000000000000000 2000246958919953 2000000000000000 64 259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000246958919953/2000000000000000 : ℝ)) (X := (25012494998720385319/25000000000000000000 : ℝ)) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035348767652501511/50000000000000000000 : ℝ) ≤ (2500436645290499/2500000000000000 : ℝ) ^ (259/64 : ℝ) := by
    have hpowers : (50035348767652501511/50000000000000000000 : ℝ)^64 ≤ (2500436645290499/2500000000000000 : ℝ)^259 := by
      have hnat : (50035348767652501511 : ℕ)^64*2500000000000000^259 ≤ 2500436645290499^259*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035348767652501511 50000000000000000000 2500436645290499 2500000000000000 64 259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500436645290499/2500000000000000 : ℝ)) (X := (50035348767652501511/50000000000000000000 : ℝ)) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2926245445807953/20000000000000000000 : ℝ) ≤ ((4578406308420639781/4580000000000000000 : ℝ)+2*(511786562231/274800000000000 : ℝ)*(11283/100000 : ℝ))^(259/64 : ℝ) := by
    rw [show (4578406308420639781/4580000000000000000 : ℝ)+2*(511786562231/274800000000000 : ℝ)*(11283/100000 : ℝ)=(5000361504018767/5000000000000000 : ℝ) by norm_num, show 1+2*(2926245445807953/20000000000000000000 : ℝ)=(10002926245445807953/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35348767652501511/100000000000000000000 : ℝ)+(2926245445807953/20000000000000000000 : ℝ) ≤ ((4578406308420639781/4580000000000000000 : ℝ)+(511786562231/274800000000000 : ℝ)*((14031/100000 : ℝ)+(11283/100000 : ℝ)))^(259/64 : ℝ) := by
    rw [show (4578406308420639781/4580000000000000000 : ℝ)+(511786562231/274800000000000 : ℝ)*((14031/100000 : ℝ)+(11283/100000 : ℝ))=(2000246958919953/2000000000000000 : ℝ) by norm_num, show 1+(35348767652501511/100000000000000000000 : ℝ)+(2926245445807953/20000000000000000000 : ℝ)=(25012494998720385319/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35348767652501511/100000000000000000000 : ℝ) ≤ ((4578406308420639781/4580000000000000000 : ℝ)+2*(511786562231/274800000000000 : ℝ)*(14031/100000 : ℝ))^(259/64 : ℝ) := by
    rw [show (4578406308420639781/4580000000000000000 : ℝ)+2*(511786562231/274800000000000 : ℝ)*(14031/100000 : ℝ)=(2500436645290499/2500000000000000 : ℝ) by norm_num, show 1+2*(35348767652501511/100000000000000000000 : ℝ)=(50035348767652501511/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4578406308420639781/4580000000000000000 : ℝ)*(X 1 0+X 2 0)+(511786562231/274800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (259/64 : ℝ)) (lo := (11283/100000 : ℝ)) (hi := (14031/100000 : ℝ)) (c := (4578406308420639781/4580000000000000000 : ℝ)) (alpha := (511786562231/274800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4578406308420639781/4580000000000000000 : ℝ)*(X 0 1+X 2 1)+(511786562231/274800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (259/64 : ℝ)) (lo := (11283/100000 : ℝ)) (hi := (14031/100000 : ℝ)) (c := (4578406308420639781/4580000000000000000 : ℝ)) (alpha := (511786562231/274800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4578406308420639781/4580000000000000000 : ℝ)*(X 0 2+X 1 2)+(511786562231/274800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (259/64 : ℝ)) (lo := (11283/100000 : ℝ)) (hi := (14031/100000 : ℝ)) (c := (4578406308420639781/4580000000000000000 : ℝ)) (alpha := (511786562231/274800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1094537823/5000000000 : ℝ)*X 0 0+(539390237/1000000000 : ℝ)*X 0 1+(5264921977/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344919613/10000000000 : ℝ)*X 1 0+(-2254509309/10000000000 : ℝ)*X 1 1+(1052984413/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672459917/5000000000 : ℝ)*X 2 0+(1316230479/2500000000 : ℝ)*X 2 1+(-2254509213/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4371191789/10000000000 : ℝ)*X 0 0+(84918139/200000000 : ℝ)*X 0 1+(4500196579/10000000000 : ℝ)*X 0 2+(4371191789/10000000000 : ℝ)*X 1 0+(84918139/200000000 : ℝ)*X 1 1+(4500196579/10000000000 : ℝ)*X 1 2+(4371191789/10000000000 : ℝ)*X 2 0+(84918139/200000000 : ℝ)*X 2 1+(4500196579/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1094540373/5000000000 : ℝ)*X 0 0+(5265245773/10000000000 : ℝ)*X 0 1+(674197167/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656177761/5000000000 : ℝ)*X 1 0+(-1062927007/5000000000 : ℝ)*X 1 1+(2696788667/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312355523/10000000000 : ℝ)*X 2 0+(5393577333/10000000000 : ℝ)*X 2 1+(-1062927007/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((874240317/2000000000 : ℝ)*X 0 0+(4499558343/10000000000 : ℝ)*X 0 1+(1061636891/2500000000 : ℝ)*X 0 2+(874240317/2000000000 : ℝ)*X 1 0+(4499558343/10000000000 : ℝ)*X 1 1+(1061636891/2500000000 : ℝ)*X 1 2+(874240317/2000000000 : ℝ)*X 2 0+(4499558343/10000000000 : ℝ)*X 2 1+(1061636891/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (337680463229912860553758611/57250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (644116737/50000000000000 : ℝ)*(base19) + (1335273241/100000000000000 : ℝ)*(base23) + (73101649/50000000000000 : ℝ)*(lower2) + (92275689/100000000000000 : ℝ)*(upper3) + (25477647/25000000000000 : ℝ)*(upper5) + (1460720002775523/25000000000000 : ℝ)*(major0) + (1460720002775523/25000000000000 : ℝ)*(major1) + (1460720002775523/25000000000000 : ℝ)*(major2) + (193828843393511/2500000000000 : ℝ)*(sp0) + (7753197990969423/100000000000000 : ℝ)*(sp1) + (969149742991207/12500000000000 : ℝ)*(sp2) + (1966270302405421/50000000000000 : ℝ)*(sp3) + (45543462457/100000000000000 : ℝ)*(sp4) + (4985394703/25000000000000 : ℝ)*(sp7) + (786512109277931/20000000000000 : ℝ)*(f.failure) + (7753199279202897/100000000000000 : ℝ)*(f.sum) + (8555068312851/1145000000000000000000000000 : ℝ)*base65 + (816897141133930463/114500000000000000000000000000000 : ℝ)*base67 + (996149130639430463/114500000000000000000000000000000 : ℝ)*base69 + (277622845023930463/114500000000000000000000000000000 : ℝ)*base71 + (2886127000233/572500000000000000000000000 : ℝ)*base73 + (2659526039574069537/114500000000000000000000000000000 : ℝ)*base76 + (1150204009351430463/114500000000000000000000000000000 : ℝ)*base77 + (615778822973569537/114500000000000000000000000000000 : ℝ)*base80 + (5628807199361/1145000000000000000000000000 : ℝ)*base81 + (712957/500000000000000000000 : ℝ)*base89 + (712957/500000000000000000000 : ℝ)*base91 + (712957/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (360005668582825785053675109/57250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (46150731/4000000000000 : ℝ)*(base19) + (1259189413/100000000000000 : ℝ)*(base23) + (12485051/10000000000000 : ℝ)*(upper3) + (47264103/100000000000000 : ℝ)*(lower4) + (127139553/100000000000000 : ℝ)*(upper5) + (2936178683029437/50000000000000 : ℝ)*(major0) + (2936178683029437/50000000000000 : ℝ)*(major1) + (2936178683029437/50000000000000 : ℝ)*(major2) + (1967785033/6250000000000 : ℝ)*(sp1) + (1060274369/3125000000000 : ℝ)*(sp2) + (7792314191132529/100000000000000 : ℝ)*(sp4) + (3896140776401863/50000000000000 : ℝ)*(sp5) + (7792279003163307/100000000000000 : ℝ)*(sp6) + (3952400331374919/100000000000000 : ℝ)*(sp7) + (3952400331374919/100000000000000 : ℝ)*(f.failure) + (7792314191132529/100000000000000 : ℝ)*(f.sum) + (4388329108159/2290000000000000000000000000 : ℝ)*base65 + (2350391538342683297/229000000000000000000000000000000 : ℝ)*base67 + (3960018586288683297/229000000000000000000000000000000 : ℝ)*base69 + (2559535379549683297/229000000000000000000000000000000 : ℝ)*base71 + (5688298171359/2290000000000000000000000000 : ℝ)*base73 + (3773879586548683297/229000000000000000000000000000000 : ℝ)*base75 + (1200460457963316703/229000000000000000000000000000000 : ℝ)*base78 + (6973914719124683297/229000000000000000000000000000000 : ℝ)*base79 + (6246774181589/2290000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (9059007/2500000000000000000000 : ℝ)*base90 + (9059007/2500000000000000000000 : ℝ)*base92 + (9059007/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1096_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37144247/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14031/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11283/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11291/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14023/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1096_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1096_s8_0 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2189081787/10000000000 : ℝ)*x 0 + (269690963/500000000 : ℝ)*x 1 + (1053000229/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2189081787/10000000000 : ℝ)^8289 ≤ (6648708426901/50000000000000 : ℝ)^6241 := by
    have hnat : (2189081787 : ℕ)^8289*50000000000000^6241 ≤ 6648708426901^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189081787 10000000000 6648708426901 50000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269690963/500000000 : ℝ)^8289 ≤ (11011779785993/25000000000000 : ℝ)^6241 := by
    have hnat : (269690963 : ℕ)^8289*25000000000000^6241 ≤ 11011779785993^6241*500000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269690963 500000000 11011779785993 25000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053000229/2000000000 : ℝ)^8289 ≤ (42655463982959/100000000000000 : ℝ)^6241 := by
    have hnat : (1053000229 : ℕ)^8289*100000000000000^6241 ≤ 42655463982959^6241*2000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053000229 2000000000 42655463982959 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2189081787/10000000000 : ℝ), (269690963/500000000 : ℝ), (1053000229/2000000000 : ℝ)] ![(6648708426901/50000000000000 : ℝ), (11011779785993/25000000000000 : ℝ), (42655463982959/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2189081787/10000000000 : ℝ)|^8289 ≤ (6648708426901/50000000000000 : ℝ)^6241
        have hw : |(-2189081787/10000000000 : ℝ)|=(2189081787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269690963/500000000 : ℝ)|^8289 ≤ (11011779785993/25000000000000 : ℝ)^6241
        have hw : |(269690963/500000000 : ℝ)|=(269690963/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053000229/2000000000 : ℝ)|^8289 ≤ (42655463982959/100000000000000 : ℝ)^6241
        have hw : |(1053000229/2000000000 : ℝ)|=(1053000229/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s8_1 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344899171/10000000000 : ℝ)*x 0 + (-2254431909/10000000000 : ℝ)*x 1 + (1316250301/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344899171/10000000000 : ℝ)^8289 ≤ (21758661841231/50000000000000 : ℝ)^6241 := by
    have hnat : (5344899171 : ℕ)^8289*50000000000000^6241 ≤ 21758661841231^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344899171 10000000000 21758661841231 50000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2254431909/10000000000 : ℝ)^8289 ≤ (6913605840903/50000000000000 : ℝ)^6241 := by
    have hnat : (2254431909 : ℕ)^8289*50000000000000^6241 ≤ 6913605840903^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254431909 10000000000 6913605840903 50000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316250301/2500000000 : ℝ)^8289 ≤ (5331933077227/12500000000000 : ℝ)^6241 := by
    have hnat : (1316250301 : ℕ)^8289*12500000000000^6241 ≤ 5331933077227^6241*2500000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316250301 2500000000 5331933077227 12500000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344899171/10000000000 : ℝ), (-2254431909/10000000000 : ℝ), (1316250301/2500000000 : ℝ)] ![(21758661841231/50000000000000 : ℝ), (6913605840903/50000000000000 : ℝ), (5331933077227/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344899171/10000000000 : ℝ)|^8289 ≤ (21758661841231/50000000000000 : ℝ)^6241
        have hw : |(5344899171/10000000000 : ℝ)|=(5344899171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2254431909/10000000000 : ℝ)|^8289 ≤ (6913605840903/50000000000000 : ℝ)^6241
        have hw : |(-2254431909/10000000000 : ℝ)|=(2254431909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316250301/2500000000 : ℝ)|^8289 ≤ (5331933077227/12500000000000 : ℝ)^6241
        have hw : |(1316250301/2500000000 : ℝ)|=(1316250301/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s8_2 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336224803/2500000000 : ℝ)*x 0 + (1053000239/2000000000 : ℝ)*x 1 + (-2254431867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336224803/2500000000 : ℝ)^8289 ≤ (2175866206291/5000000000000 : ℝ)^6241 := by
    have hnat : (1336224803 : ℕ)^8289*5000000000000^6241 ≤ 2175866206291^6241*2500000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336224803 2500000000 2175866206291 5000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053000239/2000000000 : ℝ)^8289 ≤ (42655464520973/100000000000000 : ℝ)^6241 := by
    have hnat : (1053000239 : ℕ)^8289*100000000000000^6241 ≤ 42655464520973^6241*2000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053000239 2000000000 42655464520973 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2254431867/10000000000 : ℝ)^8289 ≤ (6913605669837/50000000000000 : ℝ)^6241 := by
    have hnat : (2254431867 : ℕ)^8289*50000000000000^6241 ≤ 6913605669837^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254431867 10000000000 6913605669837 50000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336224803/2500000000 : ℝ), (1053000239/2000000000 : ℝ), (-2254431867/10000000000 : ℝ)] ![(2175866206291/5000000000000 : ℝ), (42655464520973/100000000000000 : ℝ), (6913605669837/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336224803/2500000000 : ℝ)|^8289 ≤ (2175866206291/5000000000000 : ℝ)^6241
        have hw : |(1336224803/2500000000 : ℝ)|=(1336224803/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053000239/2000000000 : ℝ)|^8289 ≤ (42655464520973/100000000000000 : ℝ)^6241
        have hw : |(1053000239/2000000000 : ℝ)|=(1053000239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2254431867/10000000000 : ℝ)|^8289 ≤ (6913605669837/50000000000000 : ℝ)^6241
        have hw : |(-2254431867/10000000000 : ℝ)|=(2254431867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s8_3 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (21855979/50000000 : ℝ)*x 0 + (4246066331/10000000000 : ℝ)*x 1 + (1125009059/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21855979/50000000 : ℝ)^8289 ≤ (6663345290631/20000000000000 : ℝ)^6241 := by
    have hnat : (21855979 : ℕ)^8289*20000000000000^6241 ≤ 6663345290631^6241*50000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21855979 50000000 6663345290631 20000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4246066331/10000000000 : ℝ)^8289 ≤ (1602801329009/5000000000000 : ℝ)^6241 := by
    have hnat : (4246066331 : ℕ)^8289*5000000000000^6241 ≤ 1602801329009^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4246066331 10000000000 1602801329009 5000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1125009059/2500000000 : ℝ)^8289 ≤ (34627246946101/100000000000000 : ℝ)^6241 := by
    have hnat : (1125009059 : ℕ)^8289*100000000000000^6241 ≤ 34627246946101^6241*2500000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125009059 2500000000 34627246946101 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21855979/50000000 : ℝ), (4246066331/10000000000 : ℝ), (1125009059/2500000000 : ℝ)] ![(6663345290631/20000000000000 : ℝ), (1602801329009/5000000000000 : ℝ), (34627246946101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21855979/50000000 : ℝ)|^8289 ≤ (6663345290631/20000000000000 : ℝ)^6241
        have hw : |(21855979/50000000 : ℝ)|=(21855979/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4246066331/10000000000 : ℝ)|^8289 ≤ (1602801329009/5000000000000 : ℝ)^6241
        have hw : |(4246066331/10000000000 : ℝ)|=(4246066331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1125009059/2500000000 : ℝ)|^8289 ≤ (34627246946101/100000000000000 : ℝ)^6241
        have hw : |(1125009059/2500000000 : ℝ)|=(1125009059/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s8_4 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1094543519/5000000000 : ℝ)*x 0 + (1316331059/2500000000 : ℝ)*x 1 + (5393494809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1094543519/5000000000 : ℝ)^8289 ≤ (6648729608827/50000000000000 : ℝ)^6241 := by
    have hnat : (1094543519 : ℕ)^8289*50000000000000^6241 ≤ 6648729608827^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094543519 5000000000 6648729608827 50000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316331059/2500000000 : ℝ)^8289 ≤ (4265894057227/10000000000000 : ℝ)^6241 := by
    have hnat : (1316331059 : ℕ)^8289*10000000000000^6241 ≤ 4265894057227^6241*2500000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316331059 2500000000 4265894057227 10000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393494809/10000000000 : ℝ)^8289 ≤ (220218000937/500000000000 : ℝ)^6241 := by
    have hnat : (5393494809 : ℕ)^8289*500000000000^6241 ≤ 220218000937^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393494809 10000000000 220218000937 500000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1094543519/5000000000 : ℝ), (1316331059/2500000000 : ℝ), (5393494809/10000000000 : ℝ)] ![(6648729608827/50000000000000 : ℝ), (4265894057227/10000000000000 : ℝ), (220218000937/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1094543519/5000000000 : ℝ)|^8289 ≤ (6648729608827/50000000000000 : ℝ)^6241
        have hw : |(-1094543519/5000000000 : ℝ)|=(1094543519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316331059/2500000000 : ℝ)|^8289 ≤ (4265894057227/10000000000000 : ℝ)^6241
        have hw : |(1316331059/2500000000 : ℝ)|=(1316331059/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393494809/10000000000 : ℝ)|^8289 ≤ (220218000937/500000000000 : ℝ)^6241
        have hw : |(5393494809/10000000000 : ℝ)|=(5393494809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s8_5 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312376029/10000000000 : ℝ)*x 0 + (-2125937997/10000000000 : ℝ)*x 1 + (1078699011/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312376029/10000000000 : ℝ)^8289 ≤ (43165982781579/100000000000000 : ℝ)^6241 := by
    have hnat : (5312376029 : ℕ)^8289*100000000000000^6241 ≤ 43165982781579^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312376029 10000000000 43165982781579 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2125937997/10000000000 : ℝ)^8289 ≤ (12790414350753/100000000000000 : ℝ)^6241 := by
    have hnat : (2125937997 : ℕ)^8289*100000000000000^6241 ≤ 12790414350753^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125937997 10000000000 12790414350753 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078699011/2000000000 : ℝ)^8289 ≤ (2202180142773/5000000000000 : ℝ)^6241 := by
    have hnat : (1078699011 : ℕ)^8289*5000000000000^6241 ≤ 2202180142773^6241*2000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078699011 2000000000 2202180142773 5000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312376029/10000000000 : ℝ), (-2125937997/10000000000 : ℝ), (1078699011/2000000000 : ℝ)] ![(43165982781579/100000000000000 : ℝ), (12790414350753/100000000000000 : ℝ), (2202180142773/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312376029/10000000000 : ℝ)|^8289 ≤ (43165982781579/100000000000000 : ℝ)^6241
        have hw : |(5312376029/10000000000 : ℝ)|=(5312376029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2125937997/10000000000 : ℝ)|^8289 ≤ (12790414350753/100000000000000 : ℝ)^6241
        have hw : |(-2125937997/10000000000 : ℝ)|=(2125937997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078699011/2000000000 : ℝ)|^8289 ≤ (2202180142773/5000000000000 : ℝ)^6241
        have hw : |(1078699011/2000000000 : ℝ)|=(1078699011/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s8_6 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312375937/10000000000 : ℝ)*x 0 + (5393495261/10000000000 : ℝ)*x 1 + (-2125937841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312375937/10000000000 : ℝ)^8289 ≤ (21582990894359/50000000000000 : ℝ)^6241 := by
    have hnat : (5312375937 : ℕ)^8289*50000000000000^6241 ≤ 21582990894359^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312375937 10000000000 21582990894359 50000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393495261/10000000000 : ℝ)^8289 ≤ (44043605089689/100000000000000 : ℝ)^6241 := by
    have hnat : (5393495261 : ℕ)^8289*100000000000000^6241 ≤ 44043605089689^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393495261 10000000000 44043605089689 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2125937841/10000000000 : ℝ)^8289 ≤ (12790413104211/100000000000000 : ℝ)^6241 := by
    have hnat : (2125937841 : ℕ)^8289*100000000000000^6241 ≤ 12790413104211^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125937841 10000000000 12790413104211 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312375937/10000000000 : ℝ), (5393495261/10000000000 : ℝ), (-2125937841/10000000000 : ℝ)] ![(21582990894359/50000000000000 : ℝ), (44043605089689/100000000000000 : ℝ), (12790413104211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312375937/10000000000 : ℝ)|^8289 ≤ (21582990894359/50000000000000 : ℝ)^6241
        have hw : |(5312375937/10000000000 : ℝ)|=(5312375937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393495261/10000000000 : ℝ)|^8289 ≤ (44043605089689/100000000000000 : ℝ)^6241
        have hw : |(5393495261/10000000000 : ℝ)|=(5393495261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2125937841/10000000000 : ℝ)|^8289 ≤ (12790413104211/100000000000000 : ℝ)^6241
        have hw : |(-2125937841/10000000000 : ℝ)|=(2125937841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s8_7 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2185602969/5000000000 : ℝ)*x 0 + (4499399321/10000000000 : ℝ)*x 1 + (4246705239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2185602969/5000000000 : ℝ)^8289 ≤ (33316829080353/100000000000000 : ℝ)^6241 := by
    have hnat : (2185602969 : ℕ)^8289*100000000000000^6241 ≤ 33316829080353^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185602969 5000000000 33316829080353 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4499399321/10000000000 : ℝ)^8289 ≤ (17310368920369/50000000000000 : ℝ)^6241 := by
    have hnat : (4499399321 : ℕ)^8289*50000000000000^6241 ≤ 17310368920369^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4499399321 10000000000 17310368920369 50000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4246705239/10000000000 : ℝ)^8289 ≤ (128249732267/400000000000 : ℝ)^6241 := by
    have hnat : (4246705239 : ℕ)^8289*400000000000^6241 ≤ 128249732267^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4246705239 10000000000 128249732267 400000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2185602969/5000000000 : ℝ), (4499399321/10000000000 : ℝ), (4246705239/10000000000 : ℝ)] ![(33316829080353/100000000000000 : ℝ), (17310368920369/50000000000000 : ℝ), (128249732267/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2185602969/5000000000 : ℝ)|^8289 ≤ (33316829080353/100000000000000 : ℝ)^6241
        have hw : |(2185602969/5000000000 : ℝ)|=(2185602969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4499399321/10000000000 : ℝ)|^8289 ≤ (17310368920369/50000000000000 : ℝ)^6241
        have hw : |(4499399321/10000000000 : ℝ)|=(4499399321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4246705239/10000000000 : ℝ)|^8289 ≤ (128249732267/400000000000 : ℝ)^6241
        have hw : |(4246705239/10000000000 : ℝ)|=(4246705239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1096_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37144247/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14023/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11291/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11293/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14021/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14023/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11291/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14023/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11291/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14023/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11291/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14023/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11291/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14023/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11291/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14023/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11291/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11291/100000 : ℝ) ^ (259/64 : ℝ) ≤ (2934650974267697/20000000000000000000 : ℝ) := by
    have hpowers : (11291/100000 : ℝ)^259 ≤ (2934650974267697/20000000000000000000 : ℝ)^64 := by
      have hnat : (11291 : ℕ)^259*20000000000000000000^64 ≤ 2934650974267697^64*100000^259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11291 100000 2934650974267697 20000000000000000000 259 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11291/100000 : ℝ)) (X := (2934650974267697/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have hpowhi : (14023/100000 : ℝ) ^ (259/64 : ℝ) ≤ (17633637525730071/50000000000000000000 : ℝ) := by
    have hpowers : (14023/100000 : ℝ)^259 ≤ (17633637525730071/50000000000000000000 : ℝ)^64 := by
      have hnat : (14023 : ℕ)^259*50000000000000000000^64 ≤ 17633637525730071^64*100000^259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14023 100000 17633637525730071 50000000000000000000 259 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14023/100000 : ℝ)) (X := (17633637525730071/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002934650974267697/10000000000000000000 : ℝ) ≤ (10000725084621171/10000000000000000 : ℝ) ^ (259/64 : ℝ) := by
    have hpowers : (10002934650974267697/10000000000000000000 : ℝ)^64 ≤ (10000725084621171/10000000000000000 : ℝ)^259 := by
      have hnat : (10002934650974267697 : ℕ)^64*10000000000000000^259 ≤ 10000725084621171^259*10000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002934650974267697 10000000000000000000 10000725084621171 10000000000000000 64 259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000725084621171/10000000000000000 : ℝ)) (X := (10002934650974267697/10000000000000000000 : ℝ)) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049940529922798627/100000000000000000000 : ℝ) ≤ (2500308454942633/2500000000000000 : ℝ) ^ (259/64 : ℝ) := by
    have hpowers : (100049940529922798627/100000000000000000000 : ℝ)^64 ≤ (2500308454942633/2500000000000000 : ℝ)^259 := by
      have hnat : (100049940529922798627 : ℕ)^64*2500000000000000^259 ≤ 2500308454942633^259*100000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049940529922798627 100000000000000000000 2500308454942633 2500000000000000 64 259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500308454942633/2500000000000000 : ℝ)) (X := (100049940529922798627/100000000000000000000 : ℝ)) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017633637525730071/25000000000000000000 : ℝ) ≤ (10001742554919893/10000000000000000 : ℝ) ^ (259/64 : ℝ) := by
    have hpowers : (25017633637525730071/25000000000000000000 : ℝ)^64 ≤ (10001742554919893/10000000000000000 : ℝ)^259 := by
      have hnat : (25017633637525730071 : ℕ)^64*10000000000000000^259 ≤ 10001742554919893^259*25000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017633637525730071 25000000000000000000 10001742554919893 10000000000000000 64 259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001742554919893/10000000000000000 : ℝ)) (X := (25017633637525730071/25000000000000000000 : ℝ)) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2934650974267697/20000000000000000000 : ℝ) ≤ ((2731049267404216907/2732000000000000000 : ℝ)+2*(508735149361/273200000000000 : ℝ)*(11291/100000 : ℝ))^(259/64 : ℝ) := by
    rw [show (2731049267404216907/2732000000000000000 : ℝ)+2*(508735149361/273200000000000 : ℝ)*(11291/100000 : ℝ)=(10000725084621171/10000000000000000 : ℝ) by norm_num, show 1+2*(2934650974267697/20000000000000000000 : ℝ)=(10002934650974267697/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17633637525730071/50000000000000000000 : ℝ)+(2934650974267697/20000000000000000000 : ℝ) ≤ ((2731049267404216907/2732000000000000000 : ℝ)+(508735149361/273200000000000 : ℝ)*((14023/100000 : ℝ)+(11291/100000 : ℝ)))^(259/64 : ℝ) := by
    rw [show (2731049267404216907/2732000000000000000 : ℝ)+(508735149361/273200000000000 : ℝ)*((14023/100000 : ℝ)+(11291/100000 : ℝ))=(2500308454942633/2500000000000000 : ℝ) by norm_num, show 1+(17633637525730071/50000000000000000000 : ℝ)+(2934650974267697/20000000000000000000 : ℝ)=(100049940529922798627/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17633637525730071/50000000000000000000 : ℝ) ≤ ((2731049267404216907/2732000000000000000 : ℝ)+2*(508735149361/273200000000000 : ℝ)*(14023/100000 : ℝ))^(259/64 : ℝ) := by
    rw [show (2731049267404216907/2732000000000000000 : ℝ)+2*(508735149361/273200000000000 : ℝ)*(14023/100000 : ℝ)=(10001742554919893/10000000000000000 : ℝ) by norm_num, show 1+2*(17633637525730071/50000000000000000000 : ℝ)=(25017633637525730071/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2731049267404216907/2732000000000000000 : ℝ)*(X 1 0+X 2 0)+(508735149361/273200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (259/64 : ℝ)) (lo := (11291/100000 : ℝ)) (hi := (14023/100000 : ℝ)) (c := (2731049267404216907/2732000000000000000 : ℝ)) (alpha := (508735149361/273200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2731049267404216907/2732000000000000000 : ℝ)*(X 0 1+X 2 1)+(508735149361/273200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (259/64 : ℝ)) (lo := (11291/100000 : ℝ)) (hi := (14023/100000 : ℝ)) (c := (2731049267404216907/2732000000000000000 : ℝ)) (alpha := (508735149361/273200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2731049267404216907/2732000000000000000 : ℝ)*(X 0 2+X 1 2)+(508735149361/273200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (259/64 : ℝ)) (lo := (11291/100000 : ℝ)) (hi := (14023/100000 : ℝ)) (c := (2731049267404216907/2732000000000000000 : ℝ)) (alpha := (508735149361/273200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2189081787/10000000000 : ℝ)*X 0 0+(269690963/500000000 : ℝ)*X 0 1+(1053000229/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344899171/10000000000 : ℝ)*X 1 0+(-2254431909/10000000000 : ℝ)*X 1 1+(1316250301/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336224803/2500000000 : ℝ)*X 2 0+(1053000239/2000000000 : ℝ)*X 2 1+(-2254431867/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((21855979/50000000 : ℝ)*X 0 0+(4246066331/10000000000 : ℝ)*X 0 1+(1125009059/2500000000 : ℝ)*X 0 2+(21855979/50000000 : ℝ)*X 1 0+(4246066331/10000000000 : ℝ)*X 1 1+(1125009059/2500000000 : ℝ)*X 1 2+(21855979/50000000 : ℝ)*X 2 0+(4246066331/10000000000 : ℝ)*X 2 1+(1125009059/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1094543519/5000000000 : ℝ)*X 0 0+(1316331059/2500000000 : ℝ)*X 0 1+(5393494809/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312376029/10000000000 : ℝ)*X 1 0+(-2125937997/10000000000 : ℝ)*X 1 1+(1078699011/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312375937/10000000000 : ℝ)*X 2 0+(5393495261/10000000000 : ℝ)*X 2 1+(-2125937841/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2185602969/5000000000 : ℝ)*X 0 0+(4499399321/10000000000 : ℝ)*X 0 1+(4246705239/10000000000 : ℝ)*X 0 2+(2185602969/5000000000 : ℝ)*X 1 0+(4499399321/10000000000 : ℝ)*X 1 1+(4246705239/10000000000 : ℝ)*X 1 2+(2185602969/5000000000 : ℝ)*X 2 0+(4499399321/10000000000 : ℝ)*X 2 1+(4246705239/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (236613142401615651466540419/68300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (151742283/25000000000000 : ℝ)*(base19) + (327458119/50000000000000 : ℝ)*(base23) + (6200751/100000000000000 : ℝ)*(lower2) + (26301717/100000000000000 : ℝ)*(upper3) + (95890187/100000000000000 : ℝ)*(upper5) + (5850210707988661/100000000000000 : ℝ)*(major0) + (5850210707988661/100000000000000 : ℝ)*(major1) + (5850210707988661/100000000000000 : ℝ)*(major2) + (3881451465716711/50000000000000 : ℝ)*(sp0) + (7762926208860901/100000000000000 : ℝ)*(sp1) + (1940731540228449/25000000000000 : ℝ)*(sp2) + (984371233756171/25000000000000 : ℝ)*(sp3) + (23884396611/100000000000000 : ℝ)*(sp4) + (4774822609/50000000000000 : ℝ)*(sp7) + (3937494484669901/100000000000000 : ℝ)*(f.failure) + (7762926815830033/100000000000000 : ℝ)*(f.sum) + (92837571292699/13660000000000000000000000000 : ℝ)*base66 + (3142666440683101527/273200000000000000000000000000000 : ℝ)*base67 + (228736081198701527/273200000000000000000000000000000 : ℝ)*base69 + (7365256170630701527/273200000000000000000000000000000 : ℝ)*base71 + (99285132559559/13660000000000000000000000000 : ℝ)*base74 + (3401526710340701527/273200000000000000000000000000000 : ℝ)*base75 + (1674195366581501527/273200000000000000000000000000000 : ℝ)*base77 + (2077123987169698473/273200000000000000000000000000000 : ℝ)*base80 + (107405838926419/13660000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (8790453/2500000000000000000000 : ℝ)*base90 + (8790453/2500000000000000000000 : ℝ)*base92 + (8790453/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (28822201329465076084621779/13660000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1102271609/100000000000000 : ℝ)*(base19) + (318420343/25000000000000 : ℝ)*(base23) + (95988499/25000000000000 : ℝ)*(lower1) + (22170501/25000000000000 : ℝ)*(upper2) + (78934653/25000000000000 : ℝ)*(upper3) + (10308563/12500000000000 : ℝ)*(upper5) + (1175940193152501/20000000000000 : ℝ)*(major0) + (1175940193152501/20000000000000 : ℝ)*(major1) + (1175940193152501/20000000000000 : ℝ)*(major2) + (2850121821/12500000000000 : ℝ)*(sp2) + (312082356290961/4000000000000 : ℝ)*(sp4) + (487628612812651/6250000000000 : ℝ)*(sp5) + (1560406966523617/20000000000000 : ℝ)*(sp6) + (1978671476959307/50000000000000 : ℝ)*(sp7) + (1978671476959307/50000000000000 : ℝ)*(f.failure) + (312082356290961/4000000000000 : ℝ)*(f.sum) + (2324036207037/2732000000000000000000000000 : ℝ)*base65 + (18365254960015593/54640000000000000000000000000000 : ℝ)*base68 + (2175844698936704407/54640000000000000000000000000000 : ℝ)*base69 + (146386092530704407/54640000000000000000000000000000 : ℝ)*base71 + (3892973647517/2732000000000000000000000000 : ℝ)*base73 + (603249948907504407/54640000000000000000000000000000 : ℝ)*base75 + (815465186694624407/54640000000000000000000000000000 : ℝ)*base77 + (154885396821184407/54640000000000000000000000000000 : ℝ)*base79 + (37699983442601/2732000000000000000000000000 : ℝ)*base81 + (4343171/1250000000000000000000 : ℝ)*base90 + (4343171/1250000000000000000000 : ℝ)*base92 + (4343171/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1096_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37144247/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14023/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11291/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11293/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14021/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1096_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1096_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37144247/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1407/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5623/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11293/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14021/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1096_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1096_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1096_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37144247/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1407/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5623/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11293/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14021/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1096_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
