-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1448_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:58:51.55498+00:00
-- url     : https://prove2.me/submissions/c87239b2-68c0-4417-9031-15f0965fa2ff

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
theorem support_rectangle_w1448_s0_0 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1748106179/10000000000 : ℝ)*x 0 + (2976189869/5000000000 : ℝ)*x 1 + (4835563299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1748106179/10000000000 : ℝ)^551 ≤ (10312607018639/100000000000000 : ℝ)^423 := by
    have hnat : (1748106179 : ℕ)^551*100000000000000^423 ≤ 10312607018639^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1748106179 10000000000 10312607018639 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2976189869/5000000000 : ℝ)^551 ≤ (50875876882891/100000000000000 : ℝ)^423 := by
    have hnat : (2976189869 : ℕ)^551*100000000000000^423 ≤ 50875876882891^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2976189869 5000000000 50875876882891 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4835563299/10000000000 : ℝ)^551 ≤ (38811516076199/100000000000000 : ℝ)^423 := by
    have hnat : (4835563299 : ℕ)^551*100000000000000^423 ≤ 38811516076199^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4835563299 10000000000 38811516076199 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1748106179/10000000000 : ℝ), (2976189869/5000000000 : ℝ), (4835563299/10000000000 : ℝ)] ![(10312607018639/100000000000000 : ℝ), (50875876882891/100000000000000 : ℝ), (38811516076199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1748106179/10000000000 : ℝ)|^551 ≤ (10312607018639/100000000000000 : ℝ)^423
        have hw : |(-1748106179/10000000000 : ℝ)|=(1748106179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2976189869/5000000000 : ℝ)|^551 ≤ (50875876882891/100000000000000 : ℝ)^423
        have hw : |(2976189869/5000000000 : ℝ)|=(2976189869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4835563299/10000000000 : ℝ)|^551 ≤ (38811516076199/100000000000000 : ℝ)^423
        have hw : |(4835563299/10000000000 : ℝ)|=(4835563299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s0_1 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5489988657/10000000000 : ℝ)*x 0 + (-2378166499/10000000000 : ℝ)*x 1 + (151111349/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5489988657/10000000000 : ℝ)^551 ≤ (11447368216791/25000000000000 : ℝ)^423 := by
    have hnat : (5489988657 : ℕ)^551*25000000000000^423 ≤ 11447368216791^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5489988657 10000000000 11447368216791 25000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2378166499/10000000000 : ℝ)^551 ≤ (15399012410403/100000000000000 : ℝ)^423 := by
    have hnat : (2378166499 : ℕ)^551*100000000000000^423 ≤ 15399012410403^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2378166499 10000000000 15399012410403 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (151111349/312500000 : ℝ)^551 ≤ (38811514706591/100000000000000 : ℝ)^423 := by
    have hnat : (151111349 : ℕ)^551*100000000000000^423 ≤ 38811514706591^423*312500000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      151111349 312500000 38811514706591 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5489988657/10000000000 : ℝ), (-2378166499/10000000000 : ℝ), (151111349/312500000 : ℝ)] ![(11447368216791/25000000000000 : ℝ), (15399012410403/100000000000000 : ℝ), (38811514706591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5489988657/10000000000 : ℝ)|^551 ≤ (11447368216791/25000000000000 : ℝ)^423
        have hw : |(5489988657/10000000000 : ℝ)|=(5489988657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2378166499/10000000000 : ℝ)|^551 ≤ (15399012410403/100000000000000 : ℝ)^423
        have hw : |(-2378166499/10000000000 : ℝ)|=(2378166499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(151111349/312500000 : ℝ)|^551 ≤ (38811514706591/100000000000000 : ℝ)^423
        have hw : |(151111349/312500000 : ℝ)|=(151111349/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s0_2 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1372497133/2500000000 : ℝ)*x 0 + (604445391/1250000000 : ℝ)*x 1 + (-237816671/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1372497133/2500000000 : ℝ)^551 ≤ (9157894301823/20000000000000 : ℝ)^423 := by
    have hnat : (1372497133 : ℕ)^551*20000000000000^423 ≤ 9157894301823^423*2500000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372497133 2500000000 9157894301823 20000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (604445391/1250000000 : ℝ)^551 ≤ (38811514288391/100000000000000 : ℝ)^423 := by
    have hnat : (604445391 : ℕ)^551*100000000000000^423 ≤ 38811514288391^423*1250000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      604445391 1250000000 38811514288391 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (237816671/1000000000 : ℝ)^551 ≤ (15399014190093/100000000000000 : ℝ)^423 := by
    have hnat : (237816671 : ℕ)^551*100000000000000^423 ≤ 15399014190093^423*1000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      237816671 1000000000 15399014190093 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1372497133/2500000000 : ℝ), (604445391/1250000000 : ℝ), (-237816671/1000000000 : ℝ)] ![(9157894301823/20000000000000 : ℝ), (38811514288391/100000000000000 : ℝ), (15399014190093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1372497133/2500000000 : ℝ)|^551 ≤ (9157894301823/20000000000000 : ℝ)^423
        have hw : |(1372497133/2500000000 : ℝ)|=(1372497133/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(604445391/1250000000 : ℝ)|^551 ≤ (38811514288391/100000000000000 : ℝ)^423
        have hw : |(604445391/1250000000 : ℝ)|=(604445391/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-237816671/1000000000 : ℝ)|^551 ≤ (15399014190093/100000000000000 : ℝ)^423
        have hw : |(-237816671/1000000000 : ℝ)|=(237816671/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s0_3 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (832657639/2000000000 : ℝ)*x 0 + (3102936029/10000000000 : ℝ)*x 1 + (5535813073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (832657639/2000000000 : ℝ)^551 ≤ (31935797989781/100000000000000 : ℝ)^423 := by
    have hnat : (832657639 : ℕ)^551*100000000000000^423 ≤ 31935797989781^423*2000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      832657639 2000000000 31935797989781 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3102936029/10000000000 : ℝ)^551 ≤ (4355249439029/20000000000000 : ℝ)^423 := by
    have hnat : (3102936029 : ℕ)^551*20000000000000^423 ≤ 4355249439029^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3102936029 10000000000 4355249439029 20000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5535813073/10000000000 : ℝ)^551 ≤ (23143977403089/50000000000000 : ℝ)^423 := by
    have hnat : (5535813073 : ℕ)^551*50000000000000^423 ≤ 23143977403089^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5535813073 10000000000 23143977403089 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(832657639/2000000000 : ℝ), (3102936029/10000000000 : ℝ), (5535813073/10000000000 : ℝ)] ![(31935797989781/100000000000000 : ℝ), (4355249439029/20000000000000 : ℝ), (23143977403089/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(832657639/2000000000 : ℝ)|^551 ≤ (31935797989781/100000000000000 : ℝ)^423
        have hw : |(832657639/2000000000 : ℝ)|=(832657639/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3102936029/10000000000 : ℝ)|^551 ≤ (4355249439029/20000000000000 : ℝ)^423
        have hw : |(3102936029/10000000000 : ℝ)|=(3102936029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5535813073/10000000000 : ℝ)|^551 ≤ (23143977403089/50000000000000 : ℝ)^423
        have hw : |(5535813073/10000000000 : ℝ)|=(5535813073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s0_4 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1752033469/10000000000 : ℝ)*x 0 + (2432047641/5000000000 : ℝ)*x 1 + (740353611/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1752033469/10000000000 : ℝ)^551 ≤ (10342796272751/100000000000000 : ℝ)^423 := by
    have hnat : (1752033469 : ℕ)^551*100000000000000^423 ≤ 10342796272751^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1752033469 10000000000 10342796272751 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2432047641/5000000000 : ℝ)^551 ≤ (19555042200603/50000000000000 : ℝ)^423 := by
    have hnat : (2432047641 : ℕ)^551*50000000000000^423 ≤ 19555042200603^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2432047641 5000000000 19555042200603 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (740353611/1250000000 : ℝ)^551 ≤ (25273559652447/50000000000000 : ℝ)^423 := by
    have hnat : (740353611 : ℕ)^551*50000000000000^423 ≤ 25273559652447^423*1250000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      740353611 1250000000 25273559652447 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1752033469/10000000000 : ℝ), (2432047641/5000000000 : ℝ), (740353611/1250000000 : ℝ)] ![(10342796272751/100000000000000 : ℝ), (19555042200603/50000000000000 : ℝ), (25273559652447/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1752033469/10000000000 : ℝ)|^551 ≤ (10342796272751/100000000000000 : ℝ)^423
        have hw : |(-1752033469/10000000000 : ℝ)|=(1752033469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2432047641/5000000000 : ℝ)|^551 ≤ (19555042200603/50000000000000 : ℝ)^423
        have hw : |(2432047641/5000000000 : ℝ)|=(2432047641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(740353611/1250000000 : ℝ)|^551 ≤ (25273559652447/50000000000000 : ℝ)^423
        have hw : |(740353611/1250000000 : ℝ)|=(740353611/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s0_5 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (16203383/31250000 : ℝ)*x 0 + (-129090097/1000000000 : ℝ)*x 1 + (5922828957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16203383/31250000 : ℝ)^551 ≤ (8501011510027/20000000000000 : ℝ)^423 := by
    have hnat : (16203383 : ℕ)^551*20000000000000^423 ≤ 8501011510027^423*31250000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16203383 31250000 8501011510027 20000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129090097/1000000000 : ℝ)^551 ≤ (3473911184089/50000000000000 : ℝ)^423 := by
    have hnat : (129090097 : ℕ)^551*50000000000000^423 ≤ 3473911184089^423*1000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129090097 1000000000 3473911184089 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5922828957/10000000000 : ℝ)^551 ≤ (50547120071951/100000000000000 : ℝ)^423 := by
    have hnat : (5922828957 : ℕ)^551*100000000000000^423 ≤ 50547120071951^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5922828957 10000000000 50547120071951 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16203383/31250000 : ℝ), (-129090097/1000000000 : ℝ), (5922828957/10000000000 : ℝ)] ![(8501011510027/20000000000000 : ℝ), (3473911184089/50000000000000 : ℝ), (50547120071951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16203383/31250000 : ℝ)|^551 ≤ (8501011510027/20000000000000 : ℝ)^423
        have hw : |(16203383/31250000 : ℝ)|=(16203383/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-129090097/1000000000 : ℝ)|^551 ≤ (3473911184089/50000000000000 : ℝ)^423
        have hw : |(-129090097/1000000000 : ℝ)|=(129090097/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5922828957/10000000000 : ℝ)|^551 ≤ (50547120071951/100000000000000 : ℝ)^423
        have hw : |(5922828957/10000000000 : ℝ)|=(5922828957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s0_6 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (518508259/1000000000 : ℝ)*x 0 + (2961414401/5000000000 : ℝ)*x 1 + (-1290901169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (518508259/1000000000 : ℝ)^551 ≤ (531313223381/1250000000000 : ℝ)^423 := by
    have hnat : (518508259 : ℕ)^551*1250000000000^423 ≤ 531313223381^423*1000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518508259 1000000000 531313223381 1250000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2961414401/5000000000 : ℝ)^551 ≤ (12636779587213/25000000000000 : ℝ)^423 := by
    have hnat : (2961414401 : ℕ)^551*25000000000000^423 ≤ 12636779587213^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2961414401 5000000000 12636779587213 25000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1290901169/10000000000 : ℝ)^551 ≤ (277912950533/4000000000000 : ℝ)^423 := by
    have hnat : (1290901169 : ℕ)^551*4000000000000^423 ≤ 277912950533^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1290901169 10000000000 277912950533 4000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(518508259/1000000000 : ℝ), (2961414401/5000000000 : ℝ), (-1290901169/10000000000 : ℝ)] ![(531313223381/1250000000000 : ℝ), (12636779587213/25000000000000 : ℝ), (277912950533/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(518508259/1000000000 : ℝ)|^551 ≤ (531313223381/1250000000000 : ℝ)^423
        have hw : |(518508259/1000000000 : ℝ)|=(518508259/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2961414401/5000000000 : ℝ)|^551 ≤ (12636779587213/25000000000000 : ℝ)^423
        have hw : |(2961414401/5000000000 : ℝ)|=(2961414401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1290901169/10000000000 : ℝ)|^551 ≤ (277912950533/4000000000000 : ℝ)^423
        have hw : |(-1290901169/10000000000 : ℝ)|=(1290901169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s0_7 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2085921263/5000000000 : ℝ)*x 0 + (547365849/1000000000 : ℝ)*x 1 + (791827487/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2085921263/5000000000 : ℝ)^551 ≤ (32021299445043/100000000000000 : ℝ)^423 := by
    have hnat : (2085921263 : ℕ)^551*100000000000000^423 ≤ 32021299445043^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085921263 5000000000 32021299445043 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (547365849/1000000000 : ℝ)^551 ≤ (570151692907/1250000000000 : ℝ)^423 := by
    have hnat : (547365849 : ℕ)^551*1250000000000^423 ≤ 570151692907^423*1000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547365849 1000000000 570151692907 1250000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (791827487/2500000000 : ℝ)^551 ≤ (4473313023579/20000000000000 : ℝ)^423 := by
    have hnat : (791827487 : ℕ)^551*20000000000000^423 ≤ 4473313023579^423*2500000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      791827487 2500000000 4473313023579 20000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2085921263/5000000000 : ℝ), (547365849/1000000000 : ℝ), (791827487/2500000000 : ℝ)] ![(32021299445043/100000000000000 : ℝ), (570151692907/1250000000000 : ℝ), (4473313023579/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2085921263/5000000000 : ℝ)|^551 ≤ (32021299445043/100000000000000 : ℝ)^423
        have hw : |(2085921263/5000000000 : ℝ)|=(2085921263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(547365849/1000000000 : ℝ)|^551 ≤ (570151692907/1250000000000 : ℝ)^423
        have hw : |(547365849/1000000000 : ℝ)|=(547365849/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(791827487/2500000000 : ℝ)|^551 ≤ (4473313023579/20000000000000 : ℝ)^423
        have hw : |(791827487/2500000000 : ℝ)|=(791827487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1448_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79460081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2181/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1633/6250 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4407/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4407 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4407*1^1024 ≤ 0^1024*1^4407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4407 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4407 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4407/1024 : ℝ) ≤ (969061269697282311/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4407 ≤ (969061269697282311/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4407*50000000000000000000^1024 ≤ 969061269697282311^1024*5^4407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 969061269697282311 50000000000000000000 4407 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (969061269697282311/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4407 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4407/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4407 := by
      have hnat : (1 : ℕ)^1024*1^4407 ≤ 1^4407*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4407 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50969061269697282311/50000000000000000000 : ℝ) ≤ (10044702525026117/10000000000000000 : ℝ) ^ (4407/1024 : ℝ) := by
    have hpowers : (50969061269697282311/50000000000000000000 : ℝ)^1024 ≤ (10044702525026117/10000000000000000 : ℝ)^4407 := by
      have hnat : (50969061269697282311 : ℕ)^1024*10000000000000000^4407 ≤ 10044702525026117^4407*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50969061269697282311 50000000000000000000 10044702525026117 10000000000000000 1024 4407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10044702525026117/10000000000000000 : ℝ)) (X := (50969061269697282311/50000000000000000000 : ℝ)) (by norm_num) 4407 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25969061269697282311/25000000000000000000 : ℝ) ≤ (5044702525026117/5000000000000000 : ℝ) ^ (4407/1024 : ℝ) := by
    have hpowers : (25969061269697282311/25000000000000000000 : ℝ)^1024 ≤ (5044702525026117/5000000000000000 : ℝ)^4407 := by
      have hnat : (25969061269697282311 : ℕ)^1024*5000000000000000^4407 ≤ 5044702525026117^4407*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25969061269697282311 25000000000000000000 5044702525026117 5000000000000000 1024 4407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5044702525026117/5000000000000000 : ℝ)) (X := (25969061269697282311/25000000000000000000 : ℝ)) (by norm_num) 4407 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(44702525026117/4000000000000000 : ℝ)*(0 : ℝ))^(4407/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(44702525026117/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(969061269697282311/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(44702525026117/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4407/1024 : ℝ) := by
    rw [show (1 : ℝ)+(44702525026117/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10044702525026117/10000000000000000 : ℝ) by norm_num, show 1+(969061269697282311/50000000000000000000 : ℝ)+(0 : ℝ)=(50969061269697282311/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(969061269697282311/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(44702525026117/4000000000000000 : ℝ)*(2/5 : ℝ))^(4407/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(44702525026117/4000000000000000 : ℝ)*(2/5 : ℝ)=(5044702525026117/5000000000000000 : ℝ) by norm_num, show 1+2*(969061269697282311/50000000000000000000 : ℝ)=(25969061269697282311/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(44702525026117/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4407/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (44702525026117/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(44702525026117/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4407/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (44702525026117/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(44702525026117/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4407/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (44702525026117/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1748106179/10000000000 : ℝ)*X 0 0+(2976189869/5000000000 : ℝ)*X 0 1+(4835563299/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5489988657/10000000000 : ℝ)*X 1 0+(-2378166499/10000000000 : ℝ)*X 1 1+(151111349/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1372497133/2500000000 : ℝ)*X 2 0+(604445391/1250000000 : ℝ)*X 2 1+(-237816671/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((832657639/2000000000 : ℝ)*X 0 0+(3102936029/10000000000 : ℝ)*X 0 1+(5535813073/10000000000 : ℝ)*X 0 2+(832657639/2000000000 : ℝ)*X 1 0+(3102936029/10000000000 : ℝ)*X 1 1+(5535813073/10000000000 : ℝ)*X 1 2+(832657639/2000000000 : ℝ)*X 2 0+(3102936029/10000000000 : ℝ)*X 2 1+(5535813073/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1752033469/10000000000 : ℝ)*X 0 0+(2432047641/5000000000 : ℝ)*X 0 1+(740353611/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((16203383/31250000 : ℝ)*X 1 0+(-129090097/1000000000 : ℝ)*X 1 1+(5922828957/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((518508259/1000000000 : ℝ)*X 2 0+(2961414401/5000000000 : ℝ)*X 2 1+(-1290901169/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2085921263/5000000000 : ℝ)*X 0 0+(547365849/1000000000 : ℝ)*X 0 1+(791827487/2500000000 : ℝ)*X 0 2+(2085921263/5000000000 : ℝ)*X 1 0+(547365849/1000000000 : ℝ)*X 1 1+(791827487/2500000000 : ℝ)*X 1 2+(2085921263/5000000000 : ℝ)*X 2 0+(547365849/1000000000 : ℝ)*X 2 1+(791827487/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (905683912023652599132483/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (71275293/50000000000000 : ℝ)*(base1) + (1021902233/100000000000000 : ℝ)*(base19) + (1001514961/100000000000000 : ℝ)*(base23) + (3421547/2500000000000 : ℝ)*(upper3) + (18443791/25000000000000 : ℝ)*(upper5) + (653223559081933/100000000000000 : ℝ)*(major0) + (653223559081933/100000000000000 : ℝ)*(major1) + (653223559081933/100000000000000 : ℝ)*(major2) + (44770271807891/5000000000000 : ℝ)*(sp0) + (89540712502797/10000000000000 : ℝ)*(sp1) + (895407145415243/100000000000000 : ℝ)*(sp2) + (51379651229413/12500000000000 : ℝ)*(sp3) + (356665371/12500000000000 : ℝ)*(sp4) + (733950223/50000000000000 : ℝ)*(sp7) + (82207764057267/20000000000000 : ℝ)*(f.failure) + (895408146930203/100000000000000 : ℝ)*(f.sum) + (799530052955839/200000000000000000000000000000 : ℝ)*base66 + (141223628955839/400000000000000000000000000000 : ℝ)*base68 + (4135587862244161/400000000000000000000000000000 : ℝ)*base69 + (1445737701444161/400000000000000000000000000000 : ℝ)*base71 + (1467022097355839/200000000000000000000000000000 : ℝ)*base74 + (506123383844161/400000000000000000000000000000 : ℝ)*base75 + (290365092955839/400000000000000000000000000000 : ℝ)*base78 + (2657492416155839/400000000000000000000000000000 : ℝ)*base80 + (262592273844161/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base87 + (5541373/1000000000000000000000 : ℝ)*base90 + (5541373/1000000000000000000000 : ℝ)*base92 + (5541373/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (114042334224124755994599/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (520932603/25000000000000 : ℝ)*(base19) + (525444821/25000000000000 : ℝ)*(base23) + (45299917/25000000000000 : ℝ)*(base32) + (312370861/100000000000000 : ℝ)*(upper3) + (195233657/100000000000000 : ℝ)*(upper5) + (172263710977949/25000000000000 : ℝ)*(major0) + (172263710977949/25000000000000 : ℝ)*(major1) + (172263710977949/25000000000000 : ℝ)*(major2) + (5000790871/100000000000000 : ℝ)*(sp1) + (1303697833/25000000000000 : ℝ)*(sp2) + (472261921435257/50000000000000 : ℝ)*(sp4) + (944516758349231/100000000000000 : ℝ)*(sp5) + (472258263149949/50000000000000 : ℝ)*(sp6) + (108396339910129/25000000000000 : ℝ)*(sp7) + (54198192605023/12500000000000 : ℝ)*(f.failure) + (472261921435257/50000000000000 : ℝ)*(f.sum) + (7046681405967/50000000000000000000000000000 : ℝ)*base66 + (72608742705967/100000000000000000000000000000 : ℝ)*base68 + (368365323905967/100000000000000000000000000000 : ℝ)*base70 + (307843666205967/100000000000000000000000000000 : ℝ)*base72 + (154086029044033/50000000000000000000000000000 : ℝ)*base73 + (408476620205967/100000000000000000000000000000 : ℝ)*base76 + (90335549905967/100000000000000000000000000000 : ℝ)*base78 + (583904117105967/100000000000000000000000000000 : ℝ)*base80 + (3984898205967/50000000000000000000000000000 : ℝ)*base82 + (3586863/625000000000000000000 : ℝ)*base89 + (3586863/625000000000000000000 : ℝ)*base91 + (3586863/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1448_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79460081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2181/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1633/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1448_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1448_s1_0 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1917773127/10000000000 : ℝ)*x 0 + (5597715079/10000000000 : ℝ)*x 1 + (5081425353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1917773127/10000000000 : ℝ)^551 ≤ (2908783109503/25000000000000 : ℝ)^423 := by
    have hnat : (1917773127 : ℕ)^551*25000000000000^423 ≤ 2908783109503^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1917773127 10000000000 2908783109503 25000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5597715079/10000000000 : ℝ)^551 ≤ (46963313934253/100000000000000 : ℝ)^423 := by
    have hnat : (5597715079 : ℕ)^551*100000000000000^423 ≤ 46963313934253^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5597715079 10000000000 46963313934253 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5081425353/10000000000 : ℝ)^551 ≤ (10350388403611/25000000000000 : ℝ)^423 := by
    have hnat : (5081425353 : ℕ)^551*25000000000000^423 ≤ 10350388403611^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5081425353 10000000000 10350388403611 25000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1917773127/10000000000 : ℝ), (5597715079/10000000000 : ℝ), (5081425353/10000000000 : ℝ)] ![(2908783109503/25000000000000 : ℝ), (46963313934253/100000000000000 : ℝ), (10350388403611/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1917773127/10000000000 : ℝ)|^551 ≤ (2908783109503/25000000000000 : ℝ)^423
        have hw : |(-1917773127/10000000000 : ℝ)|=(1917773127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5597715079/10000000000 : ℝ)|^551 ≤ (46963313934253/100000000000000 : ℝ)^423
        have hw : |(5597715079/10000000000 : ℝ)|=(5597715079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5081425353/10000000000 : ℝ)|^551 ≤ (10350388403611/25000000000000 : ℝ)^423
        have hw : |(5081425353/10000000000 : ℝ)|=(5081425353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s1_1 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5394914983/10000000000 : ℝ)*x 0 + (-1095479127/5000000000 : ℝ)*x 1 + (317589177/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5394914983/10000000000 : ℝ)^551 ≤ (44759272590821/100000000000000 : ℝ)^423 := by
    have hnat : (5394914983 : ℕ)^551*100000000000000^423 ≤ 44759272590821^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394914983 10000000000 44759272590821 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1095479127/5000000000 : ℝ)^551 ≤ (6919579044133/50000000000000 : ℝ)^423 := by
    have hnat : (1095479127 : ℕ)^551*50000000000000^423 ≤ 6919579044133^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095479127 5000000000 6919579044133 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (317589177/625000000 : ℝ)^551 ≤ (20700784655611/50000000000000 : ℝ)^423 := by
    have hnat : (317589177 : ℕ)^551*50000000000000^423 ≤ 20700784655611^423*625000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317589177 625000000 20700784655611 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5394914983/10000000000 : ℝ), (-1095479127/5000000000 : ℝ), (317589177/625000000 : ℝ)] ![(44759272590821/100000000000000 : ℝ), (6919579044133/50000000000000 : ℝ), (20700784655611/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5394914983/10000000000 : ℝ)|^551 ≤ (44759272590821/100000000000000 : ℝ)^423
        have hw : |(5394914983/10000000000 : ℝ)|=(5394914983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1095479127/5000000000 : ℝ)|^551 ≤ (6919579044133/50000000000000 : ℝ)^423
        have hw : |(-1095479127/5000000000 : ℝ)|=(1095479127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(317589177/625000000 : ℝ)|^551 ≤ (20700784655611/50000000000000 : ℝ)^423
        have hw : |(317589177/625000000 : ℝ)|=(317589177/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s1_2 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5394915959/10000000000 : ℝ)*x 0 + (2540712711/5000000000 : ℝ)*x 1 + (-219095879/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5394915959/10000000000 : ℝ)^551 ≤ (44759283138563/100000000000000 : ℝ)^423 := by
    have hnat : (5394915959 : ℕ)^551*100000000000000^423 ≤ 44759283138563^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394915959 10000000000 44759283138563 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2540712711/5000000000 : ℝ)^551 ≤ (10350388586687/25000000000000 : ℝ)^423 := by
    have hnat : (2540712711 : ℕ)^551*25000000000000^423 ≤ 10350388586687^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2540712711 5000000000 10350388586687 25000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (219095879/1000000000 : ℝ)^551 ≤ (6919581249199/50000000000000 : ℝ)^423 := by
    have hnat : (219095879 : ℕ)^551*50000000000000^423 ≤ 6919581249199^423*1000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219095879 1000000000 6919581249199 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5394915959/10000000000 : ℝ), (2540712711/5000000000 : ℝ), (-219095879/1000000000 : ℝ)] ![(44759283138563/100000000000000 : ℝ), (10350388586687/25000000000000 : ℝ), (6919581249199/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5394915959/10000000000 : ℝ)|^551 ≤ (44759283138563/100000000000000 : ℝ)^423
        have hw : |(5394915959/10000000000 : ℝ)|=(5394915959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2540712711/5000000000 : ℝ)|^551 ≤ (10350388586687/25000000000000 : ℝ)^423
        have hw : |(2540712711/5000000000 : ℝ)|=(2540712711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-219095879/1000000000 : ℝ)|^551 ≤ (6919581249199/50000000000000 : ℝ)^423
        have hw : |(-219095879/1000000000 : ℝ)|=(219095879/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s1_3 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (34185423/80000000 : ℝ)*x 0 + (467950343/1250000000 : ℝ)*x 1 + (194731507/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34185423/80000000 : ℝ)^551 ≤ (33038174323953/100000000000000 : ℝ)^423 := by
    have hnat : (34185423 : ℕ)^551*100000000000000^423 ≤ 33038174323953^423*80000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34185423 80000000 33038174323953 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (467950343/1250000000 : ℝ)^551 ≤ (3475978236661/12500000000000 : ℝ)^423 := by
    have hnat : (467950343 : ℕ)^551*12500000000000^423 ≤ 3475978236661^423*1250000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467950343 1250000000 3475978236661 12500000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (194731507/400000000 : ℝ)^551 ≤ (9788499942089/25000000000000 : ℝ)^423 := by
    have hnat : (194731507 : ℕ)^551*25000000000000^423 ≤ 9788499942089^423*400000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      194731507 400000000 9788499942089 25000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(34185423/80000000 : ℝ), (467950343/1250000000 : ℝ), (194731507/400000000 : ℝ)] ![(33038174323953/100000000000000 : ℝ), (3475978236661/12500000000000 : ℝ), (9788499942089/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(34185423/80000000 : ℝ)|^551 ≤ (33038174323953/100000000000000 : ℝ)^423
        have hw : |(34185423/80000000 : ℝ)|=(34185423/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(467950343/1250000000 : ℝ)|^551 ≤ (3475978236661/12500000000000 : ℝ)^423
        have hw : |(467950343/1250000000 : ℝ)|=(467950343/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(194731507/400000000 : ℝ)|^551 ≤ (9788499942089/25000000000000 : ℝ)^423
        have hw : |(194731507/400000000 : ℝ)|=(194731507/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s1_4 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1918146143/10000000000 : ℝ)*x 0 + (5087389771/10000000000 : ℝ)*x 1 + (5591651001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1918146143/10000000000 : ℝ)^551 ≤ (5819040212541/50000000000000 : ℝ)^423 := by
    have hnat : (1918146143 : ℕ)^551*50000000000000^423 ≤ 5819040212541^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1918146143 10000000000 5819040212541 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5087389771/10000000000 : ℝ)^551 ≤ (259155411419/625000000000 : ℝ)^423 := by
    have hnat : (5087389771 : ℕ)^551*625000000000^423 ≤ 259155411419^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5087389771 10000000000 259155411419 625000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5591651001/10000000000 : ℝ)^551 ≤ (23448526866627/50000000000000 : ℝ)^423 := by
    have hnat : (5591651001 : ℕ)^551*50000000000000^423 ≤ 23448526866627^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5591651001 10000000000 23448526866627 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1918146143/10000000000 : ℝ), (5087389771/10000000000 : ℝ), (5591651001/10000000000 : ℝ)] ![(5819040212541/50000000000000 : ℝ), (259155411419/625000000000 : ℝ), (23448526866627/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1918146143/10000000000 : ℝ)|^551 ≤ (5819040212541/50000000000000 : ℝ)^423
        have hw : |(-1918146143/10000000000 : ℝ)|=(1918146143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5087389771/10000000000 : ℝ)|^551 ≤ (259155411419/625000000000 : ℝ)^423
        have hw : |(5087389771/10000000000 : ℝ)|=(5087389771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5591651001/10000000000 : ℝ)|^551 ≤ (23448526866627/50000000000000 : ℝ)^423
        have hw : |(5591651001/10000000000 : ℝ)|=(5591651001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s1_5 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5259835343/10000000000 : ℝ)*x 0 + (-1680733343/10000000000 : ℝ)*x 1 + (5591651031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5259835343/10000000000 : ℝ)^551 ≤ (10826253648621/25000000000000 : ℝ)^423 := by
    have hnat : (5259835343 : ℕ)^551*25000000000000^423 ≤ 10826253648621^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259835343 10000000000 10826253648621 25000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1680733343/10000000000 : ℝ)^551 ≤ (9797931330119/100000000000000 : ℝ)^423 := by
    have hnat : (1680733343 : ℕ)^551*100000000000000^423 ≤ 9797931330119^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1680733343 10000000000 9797931330119 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5591651031/10000000000 : ℝ)^551 ≤ (46897054061/100000000000 : ℝ)^423 := by
    have hnat : (5591651031 : ℕ)^551*100000000000^423 ≤ 46897054061^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5591651031 10000000000 46897054061 100000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5259835343/10000000000 : ℝ), (-1680733343/10000000000 : ℝ), (5591651031/10000000000 : ℝ)] ![(10826253648621/25000000000000 : ℝ), (9797931330119/100000000000000 : ℝ), (46897054061/100000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5259835343/10000000000 : ℝ)|^551 ≤ (10826253648621/25000000000000 : ℝ)^423
        have hw : |(5259835343/10000000000 : ℝ)|=(5259835343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1680733343/10000000000 : ℝ)|^551 ≤ (9797931330119/100000000000000 : ℝ)^423
        have hw : |(-1680733343/10000000000 : ℝ)|=(1680733343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5591651031/10000000000 : ℝ)|^551 ≤ (46897054061/100000000000 : ℝ)^423
        have hw : |(5591651031/10000000000 : ℝ)|=(5591651031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s1_6 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5259835251/10000000000 : ℝ)*x 0 + (5591650991/10000000000 : ℝ)*x 1 + (-1680733531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5259835251/10000000000 : ℝ)^551 ≤ (43305013607829/100000000000000 : ℝ)^423 := by
    have hnat : (5259835251 : ℕ)^551*100000000000000^423 ≤ 43305013607829^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259835251 10000000000 43305013607829 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5591650991/10000000000 : ℝ)^551 ≤ (9379410724801/20000000000000 : ℝ)^423 := by
    have hnat : (5591650991 : ℕ)^551*20000000000000^423 ≤ 9379410724801^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5591650991 10000000000 9379410724801 20000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1680733531/10000000000 : ℝ)^551 ≤ (9797932757713/100000000000000 : ℝ)^423 := by
    have hnat : (1680733531 : ℕ)^551*100000000000000^423 ≤ 9797932757713^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1680733531 10000000000 9797932757713 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5259835251/10000000000 : ℝ), (5591650991/10000000000 : ℝ), (-1680733531/10000000000 : ℝ)] ![(43305013607829/100000000000000 : ℝ), (9379410724801/20000000000000 : ℝ), (9797932757713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5259835251/10000000000 : ℝ)|^551 ≤ (43305013607829/100000000000000 : ℝ)^423
        have hw : |(5259835251/10000000000 : ℝ)|=(5259835251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5591650991/10000000000 : ℝ)|^551 ≤ (9379410724801/20000000000000 : ℝ)^423
        have hw : |(5591650991/10000000000 : ℝ)|=(5591650991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1680733531/10000000000 : ℝ)|^551 ≤ (9797932757713/100000000000000 : ℝ)^423
        have hw : |(-1680733531/10000000000 : ℝ)|=(1680733531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s1_7 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2136995473/5000000000 : ℝ)*x 0 + (4855295527/10000000000 : ℝ)*x 1 + (150272431/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2136995473/5000000000 : ℝ)^551 ≤ (3304636306757/10000000000000 : ℝ)^423 := by
    have hnat : (2136995473 : ℕ)^551*10000000000000^423 ≤ 3304636306757^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136995473 5000000000 3304636306757 10000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4855295527/10000000000 : ℝ)^551 ≤ (1560717764659/4000000000000 : ℝ)^423 := by
    have hnat : (4855295527 : ℕ)^551*4000000000000^423 ≤ 1560717764659^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4855295527 10000000000 1560717764659 4000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (150272431/400000000 : ℝ)^551 ≤ (27935692803073/100000000000000 : ℝ)^423 := by
    have hnat : (150272431 : ℕ)^551*100000000000000^423 ≤ 27935692803073^423*400000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      150272431 400000000 27935692803073 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2136995473/5000000000 : ℝ), (4855295527/10000000000 : ℝ), (150272431/400000000 : ℝ)] ![(3304636306757/10000000000000 : ℝ), (1560717764659/4000000000000 : ℝ), (27935692803073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2136995473/5000000000 : ℝ)|^551 ≤ (3304636306757/10000000000000 : ℝ)^423
        have hw : |(2136995473/5000000000 : ℝ)|=(2136995473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4855295527/10000000000 : ℝ)|^551 ≤ (1560717764659/4000000000000 : ℝ)^423
        have hw : |(4855295527/10000000000 : ℝ)|=(4855295527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(150272431/400000000 : ℝ)|^551 ≤ (27935692803073/100000000000000 : ℝ)^423
        have hw : |(150272431/400000000 : ℝ)|=(150272431/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1448_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79460081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1633/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2181/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (3903/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9361/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1633/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2181/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1633/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2181/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1633/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2181/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1633/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2181/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1633/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2181/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1633/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2181/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2181/100000 : ℝ) ^ (4407/1024 : ℝ) ≤ (3540170846609/50000000000000000000 : ℝ) := by
    have hpowers : (2181/100000 : ℝ)^4407 ≤ (3540170846609/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2181 : ℕ)^4407*50000000000000000000^1024 ≤ 3540170846609^1024*100000^4407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2181 100000 3540170846609 50000000000000000000 4407 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2181/100000 : ℝ)) (X := (3540170846609/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4407 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1633/6250 : ℝ) ^ (4407/1024 : ℝ) ≤ (310022659290750427/100000000000000000000 : ℝ) := by
    have hpowers : (1633/6250 : ℝ)^4407 ≤ (310022659290750427/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1633 : ℕ)^4407*100000000000000000000^1024 ≤ 310022659290750427^1024*6250^4407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1633 6250 310022659290750427 100000000000000000000 4407 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1633/6250 : ℝ)) (X := (310022659290750427/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4407 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000003540170846609/25000000000000000000 : ℝ) ≤ (10000000329034241/10000000000000000 : ℝ) ^ (4407/1024 : ℝ) := by
    have hpowers : (25000003540170846609/25000000000000000000 : ℝ)^1024 ≤ (10000000329034241/10000000000000000 : ℝ)^4407 := by
      have hnat : (25000003540170846609 : ℕ)^1024*10000000000000000^4407 ≤ 10000000329034241^4407*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000003540170846609 25000000000000000000 10000000329034241 10000000000000000 1024 4407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000329034241/10000000000000000 : ℝ)) (X := (25000003540170846609/25000000000000000000 : ℝ)) (by norm_num) 4407 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20062005947926488729/20000000000000000000 : ℝ) ≤ (10007195220442813/10000000000000000 : ℝ) ^ (4407/1024 : ℝ) := by
    have hpowers : (20062005947926488729/20000000000000000000 : ℝ)^1024 ≤ (10007195220442813/10000000000000000 : ℝ)^4407 := by
      have hnat : (20062005947926488729 : ℕ)^1024*10000000000000000^4407 ≤ 10007195220442813^4407*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20062005947926488729 20000000000000000000 10007195220442813 10000000000000000 1024 4407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007195220442813/10000000000000000 : ℝ)) (X := (20062005947926488729/20000000000000000000 : ℝ)) (by norm_num) 4407 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50310022659290750427/50000000000000000000 : ℝ) ≤ (2002878022370277/2000000000000000 : ℝ) ^ (4407/1024 : ℝ) := by
    have hpowers : (50310022659290750427/50000000000000000000 : ℝ)^1024 ≤ (2002878022370277/2000000000000000 : ℝ)^4407 := by
      have hnat : (50310022659290750427 : ℕ)^1024*2000000000000000^4407 ≤ 2002878022370277^4407*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50310022659290750427 50000000000000000000 2002878022370277 2000000000000000 1024 4407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2002878022370277/2000000000000000 : ℝ)) (X := (50310022659290750427/50000000000000000000 : ℝ)) (by norm_num) 4407 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3540170846609/50000000000000000000 : ℝ) ≤ ((34205517680436968309/34210000000000000000 : ℝ)+2*(256960407449/85525000000000 : ℝ)*(2181/100000 : ℝ))^(4407/1024 : ℝ) := by
    rw [show (34205517680436968309/34210000000000000000 : ℝ)+2*(256960407449/85525000000000 : ℝ)*(2181/100000 : ℝ)=(10000000329034241/10000000000000000 : ℝ) by norm_num, show 1+2*(3540170846609/50000000000000000000 : ℝ)=(25000003540170846609/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(310022659290750427/100000000000000000000 : ℝ)+(3540170846609/50000000000000000000 : ℝ) ≤ ((34205517680436968309/34210000000000000000 : ℝ)+(256960407449/85525000000000 : ℝ)*((1633/6250 : ℝ)+(2181/100000 : ℝ)))^(4407/1024 : ℝ) := by
    rw [show (34205517680436968309/34210000000000000000 : ℝ)+(256960407449/85525000000000 : ℝ)*((1633/6250 : ℝ)+(2181/100000 : ℝ))=(10007195220442813/10000000000000000 : ℝ) by norm_num, show 1+(310022659290750427/100000000000000000000 : ℝ)+(3540170846609/50000000000000000000 : ℝ)=(20062005947926488729/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(310022659290750427/100000000000000000000 : ℝ) ≤ ((34205517680436968309/34210000000000000000 : ℝ)+2*(256960407449/85525000000000 : ℝ)*(1633/6250 : ℝ))^(4407/1024 : ℝ) := by
    rw [show (34205517680436968309/34210000000000000000 : ℝ)+2*(256960407449/85525000000000 : ℝ)*(1633/6250 : ℝ)=(2002878022370277/2000000000000000 : ℝ) by norm_num, show 1+2*(310022659290750427/100000000000000000000 : ℝ)=(50310022659290750427/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34205517680436968309/34210000000000000000 : ℝ)*(X 1 0+X 2 0)+(256960407449/85525000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4407/1024 : ℝ)) (lo := (2181/100000 : ℝ)) (hi := (1633/6250 : ℝ)) (c := (34205517680436968309/34210000000000000000 : ℝ)) (alpha := (256960407449/85525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34205517680436968309/34210000000000000000 : ℝ)*(X 0 1+X 2 1)+(256960407449/85525000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4407/1024 : ℝ)) (lo := (2181/100000 : ℝ)) (hi := (1633/6250 : ℝ)) (c := (34205517680436968309/34210000000000000000 : ℝ)) (alpha := (256960407449/85525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34205517680436968309/34210000000000000000 : ℝ)*(X 0 2+X 1 2)+(256960407449/85525000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4407/1024 : ℝ)) (lo := (2181/100000 : ℝ)) (hi := (1633/6250 : ℝ)) (c := (34205517680436968309/34210000000000000000 : ℝ)) (alpha := (256960407449/85525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1917773127/10000000000 : ℝ)*X 0 0+(5597715079/10000000000 : ℝ)*X 0 1+(5081425353/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5394914983/10000000000 : ℝ)*X 1 0+(-1095479127/5000000000 : ℝ)*X 1 1+(317589177/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5394915959/10000000000 : ℝ)*X 2 0+(2540712711/5000000000 : ℝ)*X 2 1+(-219095879/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((34185423/80000000 : ℝ)*X 0 0+(467950343/1250000000 : ℝ)*X 0 1+(194731507/400000000 : ℝ)*X 0 2+(34185423/80000000 : ℝ)*X 1 0+(467950343/1250000000 : ℝ)*X 1 1+(194731507/400000000 : ℝ)*X 1 2+(34185423/80000000 : ℝ)*X 2 0+(467950343/1250000000 : ℝ)*X 2 1+(194731507/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1918146143/10000000000 : ℝ)*X 0 0+(5087389771/10000000000 : ℝ)*X 0 1+(5591651001/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5259835343/10000000000 : ℝ)*X 1 0+(-1680733343/10000000000 : ℝ)*X 1 1+(5591651031/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5259835251/10000000000 : ℝ)*X 2 0+(5591650991/10000000000 : ℝ)*X 2 1+(-1680733531/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2136995473/5000000000 : ℝ)*X 0 0+(4855295527/10000000000 : ℝ)*X 0 1+(150272431/400000000 : ℝ)*X 0 2+(2136995473/5000000000 : ℝ)*X 1 0+(4855295527/10000000000 : ℝ)*X 1 1+(150272431/400000000 : ℝ)*X 1 2+(2136995473/5000000000 : ℝ)*X 2 0+(4855295527/10000000000 : ℝ)*X 2 1+(150272431/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (201220221647713386353176881/38875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4230371/800000000000 : ℝ)*(base19) + (917229787/100000000000000 : ℝ)*(base23) + (6099381/25000000000000 : ℝ)*(upper2) + (26329467/25000000000000 : ℝ)*(upper3) + (353257415380111/25000000000000 : ℝ)*(major0) + (353257415380111/25000000000000 : ℝ)*(major1) + (353257415380111/25000000000000 : ℝ)*(major2) + (968453069922347/50000000000000 : ℝ)*(sp0) + (242114282383623/12500000000000 : ℝ)*(sp1) + (121057098944937/6250000000000 : ℝ)*(sp2) + (444570319366331/50000000000000 : ℝ)*(sp3) + (1729604133/20000000000000 : ℝ)*(sp4) + (14375829/5000000000000 : ℝ)*(sp6) + (744781353/20000000000000 : ℝ)*(sp7) + (444572181319713/50000000000000 : ℝ)*(f.failure) + (1936914787865359/100000000000000 : ℝ)*(f.sum) + (3158750769199/1555000000000000000000000000 : ℝ)*base65 + (325108041899499791/77750000000000000000000000000000 : ℝ)*base68 + (304494429156499791/77750000000000000000000000000000 : ℝ)*base70 + (32104600216499791/77750000000000000000000000000000 : ℝ)*base72 + (4568590098001/1555000000000000000000000000 : ℝ)*base74 + (689086051344249791/77750000000000000000000000000000 : ℝ)*base76 + (51974983915499791/77750000000000000000000000000000 : ℝ)*base78 + (219849070497749791/77750000000000000000000000000000 : ℝ)*base80 + (920838937491/1555000000000000000000000000 : ℝ)*base82 + (18123247/2500000000000000000000 : ℝ)*base90 + (18123247/2500000000000000000000 : ℝ)*base92 + (18123247/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (33126591661477727511459/4276250000000000000000000000 : ℝ) := by norm_num
    linear_combination (57264957/100000000000000 : ℝ)*(base1) + (1676969857/100000000000000 : ℝ)*(base19) + (326089003/20000000000000 : ℝ)*(base23) + (193342479/100000000000000 : ℝ)*(upper3) + (6298903/4000000000000 : ℝ)*(upper5) + (361680474899289/25000000000000 : ℝ)*(major0) + (361680474899289/25000000000000 : ℝ)*(major1) + (361680474899289/25000000000000 : ℝ)*(major2) + (10188718721/100000000000000 : ℝ)*(sp1) + (1945533713/20000000000000 : ℝ)*(sp2) + (495774625830817/25000000000000 : ℝ)*(sp4) + (991543290184867/50000000000000 : ℝ)*(sp5) + (495771771986183/25000000000000 : ℝ)*(sp6) + (910345037649529/100000000000000 : ℝ)*(sp7) + (910345094914487/100000000000000 : ℝ)*(f.failure) + (247887305757289/12500000000000 : ℝ)*(f.sum) + (4911848316813/8552500000000000000000000000 : ℝ)*base65 + (6802200937256282301/855250000000000000000000000000000 : ℝ)*base67 + (5216552186438282301/855250000000000000000000000000000 : ℝ)*base69 + (1508880399565717699/855250000000000000000000000000000 : ℝ)*base72 + (57453701878041/17105000000000000000000000000 : ℝ)*base73 + (542381756241217699/855250000000000000000000000000000 : ℝ)*base76 + (2619226725341217699/855250000000000000000000000000000 : ℝ)*base78 + (2788686119982782301/855250000000000000000000000000000 : ℝ)*base79 + (31899053456211/17105000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (25093447/5000000000000000000000 : ℝ)*base89 + (25093447/5000000000000000000000 : ℝ)*base91 + (25093447/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1448_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79460081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1633/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2181/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3903/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9361/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1448_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1448_s2_0 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1949515147/10000000000 : ℝ)*x 0 + (5454013377/10000000000 : ℝ)*x 1 + (1301168489/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1949515147/10000000000 : ℝ)^551 ≤ (2377322316027/20000000000000 : ℝ)^423 := by
    have hnat : (1949515147 : ℕ)^551*20000000000000^423 ≤ 2377322316027^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1949515147 10000000000 2377322316027 20000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5454013377/10000000000 : ℝ)^551 ≤ (45399011422969/100000000000000 : ℝ)^423 := by
    have hnat : (5454013377 : ℕ)^551*100000000000000^423 ≤ 45399011422969^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5454013377 10000000000 45399011422969 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1301168489/2500000000 : ℝ)^551 ≤ (8542875395121/20000000000000 : ℝ)^423 := by
    have hnat : (1301168489 : ℕ)^551*20000000000000^423 ≤ 8542875395121^423*2500000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1301168489 2500000000 8542875395121 20000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1949515147/10000000000 : ℝ), (5454013377/10000000000 : ℝ), (1301168489/2500000000 : ℝ)] ![(2377322316027/20000000000000 : ℝ), (45399011422969/100000000000000 : ℝ), (8542875395121/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1949515147/10000000000 : ℝ)|^551 ≤ (2377322316027/20000000000000 : ℝ)^423
        have hw : |(-1949515147/10000000000 : ℝ)|=(1949515147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5454013377/10000000000 : ℝ)|^551 ≤ (45399011422969/100000000000000 : ℝ)^423
        have hw : |(5454013377/10000000000 : ℝ)|=(5454013377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1301168489/2500000000 : ℝ)|^551 ≤ (8542875395121/20000000000000 : ℝ)^423
        have hw : |(1301168489/2500000000 : ℝ)|=(1301168489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s2_1 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5358951789/10000000000 : ℝ)*x 0 + (-1038847341/5000000000 : ℝ)*x 1 + (650584197/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5358951789/10000000000 : ℝ)^551 ≤ (44371006935551/100000000000000 : ℝ)^423 := by
    have hnat : (5358951789 : ℕ)^551*100000000000000^423 ≤ 44371006935551^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5358951789 10000000000 44371006935551 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1038847341/5000000000 : ℝ)^551 ≤ (12914620132509/100000000000000 : ℝ)^423 := by
    have hnat : (1038847341 : ℕ)^551*100000000000000^423 ≤ 12914620132509^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038847341 5000000000 12914620132509 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (650584197/1250000000 : ℝ)^551 ≤ (42714372913273/100000000000000 : ℝ)^423 := by
    have hnat : (650584197 : ℕ)^551*100000000000000^423 ≤ 42714372913273^423*1250000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      650584197 1250000000 42714372913273 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5358951789/10000000000 : ℝ), (-1038847341/5000000000 : ℝ), (650584197/1250000000 : ℝ)] ![(44371006935551/100000000000000 : ℝ), (12914620132509/100000000000000 : ℝ), (42714372913273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5358951789/10000000000 : ℝ)|^551 ≤ (44371006935551/100000000000000 : ℝ)^423
        have hw : |(5358951789/10000000000 : ℝ)|=(5358951789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1038847341/5000000000 : ℝ)|^551 ≤ (12914620132509/100000000000000 : ℝ)^423
        have hw : |(-1038847341/5000000000 : ℝ)|=(1038847341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(650584197/1250000000 : ℝ)|^551 ≤ (42714372913273/100000000000000 : ℝ)^423
        have hw : |(650584197/1250000000 : ℝ)|=(650584197/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s2_2 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5358951127/10000000000 : ℝ)*x 0 + (5204674189/10000000000 : ℝ)*x 1 + (-1038847377/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5358951127/10000000000 : ℝ)^551 ≤ (11092749948927/25000000000000 : ℝ)^423 := by
    have hnat : (5358951127 : ℕ)^551*25000000000000^423 ≤ 11092749948927^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5358951127 10000000000 11092749948927 25000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5204674189/10000000000 : ℝ)^551 ≤ (5339297433307/12500000000000 : ℝ)^423 := by
    have hnat : (5204674189 : ℕ)^551*12500000000000^423 ≤ 5339297433307^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5204674189 10000000000 5339297433307 12500000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1038847377/5000000000 : ℝ)^551 ≤ (516584828619/4000000000000 : ℝ)^423 := by
    have hnat : (1038847377 : ℕ)^551*4000000000000^423 ≤ 516584828619^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038847377 5000000000 516584828619 4000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5358951127/10000000000 : ℝ), (5204674189/10000000000 : ℝ), (-1038847377/5000000000 : ℝ)] ![(11092749948927/25000000000000 : ℝ), (5339297433307/12500000000000 : ℝ), (516584828619/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5358951127/10000000000 : ℝ)|^551 ≤ (11092749948927/25000000000000 : ℝ)^423
        have hw : |(5358951127/10000000000 : ℝ)|=(5358951127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5204674189/10000000000 : ℝ)|^551 ≤ (5339297433307/12500000000000 : ℝ)^423
        have hw : |(5204674189/10000000000 : ℝ)|=(5204674189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1038847377/5000000000 : ℝ)|^551 ≤ (516584828619/4000000000000 : ℝ)^423
        have hw : |(-1038847377/5000000000 : ℝ)|=(1038847377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s2_3 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2147814379/5000000000 : ℝ)*x 0 + (4031691389/10000000000 : ℝ)*x 1 + (571856847/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2147814379/5000000000 : ℝ)^551 ≤ (665289172221/2000000000000 : ℝ)^423 := by
    have hnat : (2147814379 : ℕ)^551*2000000000000^423 ≤ 665289172221^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147814379 5000000000 665289172221 2000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4031691389/10000000000 : ℝ)^551 ≤ (30627217718937/100000000000000 : ℝ)^423 := by
    have hnat : (4031691389 : ℕ)^551*100000000000000^423 ≤ 30627217718937^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4031691389 10000000000 30627217718937 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (571856847/1250000000 : ℝ)^551 ≤ (9027080913081/25000000000000 : ℝ)^423 := by
    have hnat : (571856847 : ℕ)^551*25000000000000^423 ≤ 9027080913081^423*1250000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      571856847 1250000000 9027080913081 25000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2147814379/5000000000 : ℝ), (4031691389/10000000000 : ℝ), (571856847/1250000000 : ℝ)] ![(665289172221/2000000000000 : ℝ), (30627217718937/100000000000000 : ℝ), (9027080913081/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2147814379/5000000000 : ℝ)|^551 ≤ (665289172221/2000000000000 : ℝ)^423
        have hw : |(2147814379/5000000000 : ℝ)|=(2147814379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4031691389/10000000000 : ℝ)|^551 ≤ (30627217718937/100000000000000 : ℝ)^423
        have hw : |(4031691389/10000000000 : ℝ)|=(4031691389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(571856847/1250000000 : ℝ)|^551 ≤ (9027080913081/25000000000000 : ℝ)^423
        have hw : |(571856847/1250000000 : ℝ)|=(571856847/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s2_4 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1949556861/10000000000 : ℝ)*x 0 + (5206074513/10000000000 : ℝ)*x 1 + (2726300923/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1949556861/10000000000 : ℝ)^551 ≤ (2377388576713/20000000000000 : ℝ)^423 := by
    have hnat : (1949556861 : ℕ)^551*20000000000000^423 ≤ 2377388576713^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1949556861 10000000000 2377388576713 20000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5206074513/10000000000 : ℝ)^551 ≤ (10682337506171/25000000000000 : ℝ)^423 := by
    have hnat : (5206074513 : ℕ)^551*25000000000000^423 ≤ 10682337506171^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5206074513 10000000000 10682337506171 25000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2726300923/5000000000 : ℝ)^551 ≤ (45383707074627/100000000000000 : ℝ)^423 := by
    have hnat : (2726300923 : ℕ)^551*100000000000000^423 ≤ 45383707074627^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2726300923 5000000000 45383707074627 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1949556861/10000000000 : ℝ), (5206074513/10000000000 : ℝ), (2726300923/5000000000 : ℝ)] ![(2377388576713/20000000000000 : ℝ), (10682337506171/25000000000000 : ℝ), (45383707074627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1949556861/10000000000 : ℝ)|^551 ≤ (2377388576713/20000000000000 : ℝ)^423
        have hw : |(-1949556861/10000000000 : ℝ)|=(1949556861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5206074513/10000000000 : ℝ)|^551 ≤ (10682337506171/25000000000000 : ℝ)^423
        have hw : |(5206074513/10000000000 : ℝ)|=(5206074513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2726300923/5000000000 : ℝ)|^551 ≤ (45383707074627/100000000000000 : ℝ)^423
        have hw : |(2726300923/5000000000 : ℝ)|=(2726300923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s2_5 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2647000449/5000000000 : ℝ)*x 0 + (-1829764899/10000000000 : ℝ)*x 1 + (5452603163/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647000449/5000000000 : ℝ)^551 ≤ (43671782829787/100000000000000 : ℝ)^423 := by
    have hnat : (2647000449 : ℕ)^551*100000000000000^423 ≤ 43671782829787^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647000449 5000000000 43671782829787 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1829764899/10000000000 : ℝ)^551 ≤ (10944495795871/100000000000000 : ℝ)^423 := by
    have hnat : (1829764899 : ℕ)^551*100000000000000^423 ≤ 10944495795871^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1829764899 10000000000 10944495795871 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5452603163/10000000000 : ℝ)^551 ≤ (11345930338369/25000000000000 : ℝ)^423 := by
    have hnat : (5452603163 : ℕ)^551*25000000000000^423 ≤ 11345930338369^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5452603163 10000000000 11345930338369 25000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647000449/5000000000 : ℝ), (-1829764899/10000000000 : ℝ), (5452603163/10000000000 : ℝ)] ![(43671782829787/100000000000000 : ℝ), (10944495795871/100000000000000 : ℝ), (11345930338369/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647000449/5000000000 : ℝ)|^551 ≤ (43671782829787/100000000000000 : ℝ)^423
        have hw : |(2647000449/5000000000 : ℝ)|=(2647000449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1829764899/10000000000 : ℝ)|^551 ≤ (10944495795871/100000000000000 : ℝ)^423
        have hw : |(-1829764899/10000000000 : ℝ)|=(1829764899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5452603163/10000000000 : ℝ)|^551 ≤ (11345930338369/25000000000000 : ℝ)^423
        have hw : |(5452603163/10000000000 : ℝ)|=(5452603163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s2_6 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5293999953/10000000000 : ℝ)*x 0 + (1363150697/2500000000 : ℝ)*x 1 + (-73190669/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293999953/10000000000 : ℝ)^551 ≤ (21835886337627/50000000000000 : ℝ)^423 := by
    have hnat : (5293999953 : ℕ)^551*50000000000000^423 ≤ 21835886337627^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293999953 10000000000 21835886337627 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1363150697/2500000000 : ℝ)^551 ≤ (9076743457549/20000000000000 : ℝ)^423 := by
    have hnat : (1363150697 : ℕ)^551*20000000000000^423 ≤ 9076743457549^423*2500000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1363150697 2500000000 9076743457549 20000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (73190669/400000000 : ℝ)^551 ≤ (2188902004569/20000000000000 : ℝ)^423 := by
    have hnat : (73190669 : ℕ)^551*20000000000000^423 ≤ 2188902004569^423*400000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73190669 400000000 2188902004569 20000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293999953/10000000000 : ℝ), (1363150697/2500000000 : ℝ), (-73190669/400000000 : ℝ)] ![(21835886337627/50000000000000 : ℝ), (9076743457549/20000000000000 : ℝ), (2188902004569/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293999953/10000000000 : ℝ)|^551 ≤ (21835886337627/50000000000000 : ℝ)^423
        have hw : |(5293999953/10000000000 : ℝ)|=(5293999953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1363150697/2500000000 : ℝ)|^551 ≤ (9076743457549/20000000000000 : ℝ)^423
        have hw : |(1363150697/2500000000 : ℝ)|=(1363150697/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-73190669/400000000 : ℝ)|^551 ≤ (2188902004569/20000000000000 : ℝ)^423
        have hw : |(-73190669/400000000 : ℝ)|=(73190669/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s2_7 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2147860231/5000000000 : ℝ)*x 0 + (914361161/2000000000 : ℝ)*x 1 + (4034765073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2147860231/5000000000 : ℝ)^551 ≤ (8316345909631/25000000000000 : ℝ)^423 := by
    have hnat : (2147860231 : ℕ)^551*25000000000000^423 ≤ 8316345909631^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147860231 5000000000 8316345909631 25000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (914361161/2000000000 : ℝ)^551 ≤ (18038489958991/50000000000000 : ℝ)^423 := by
    have hnat : (914361161 : ℕ)^551*50000000000000^423 ≤ 18038489958991^423*2000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      914361161 2000000000 18038489958991 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4034765073/10000000000 : ℝ)^551 ≤ (239512784603/781250000000 : ℝ)^423 := by
    have hnat : (4034765073 : ℕ)^551*781250000000^423 ≤ 239512784603^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4034765073 10000000000 239512784603 781250000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2147860231/5000000000 : ℝ), (914361161/2000000000 : ℝ), (4034765073/10000000000 : ℝ)] ![(8316345909631/25000000000000 : ℝ), (18038489958991/50000000000000 : ℝ), (239512784603/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2147860231/5000000000 : ℝ)|^551 ≤ (8316345909631/25000000000000 : ℝ)^423
        have hw : |(2147860231/5000000000 : ℝ)|=(2147860231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(914361161/2000000000 : ℝ)|^551 ≤ (18038489958991/50000000000000 : ℝ)^423
        have hw : |(914361161/2000000000 : ℝ)|=(914361161/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4034765073/10000000000 : ℝ)|^551 ≤ (239512784603/781250000000 : ℝ)^423
        have hw : |(4034765073/10000000000 : ℝ)|=(4034765073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1448_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79460081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9361/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3903/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10467/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15743/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9361/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3903/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9361/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3903/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9361/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3903/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9361/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3903/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9361/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3903/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9361/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3903/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3903/50000 : ℝ) ^ (4407/1024 : ℝ) ≤ (855662753393403/50000000000000000000 : ℝ) := by
    have hpowers : (3903/50000 : ℝ)^4407 ≤ (855662753393403/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3903 : ℕ)^4407*50000000000000000000^1024 ≤ 855662753393403^1024*50000^4407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3903 50000 855662753393403 50000000000000000000 4407 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3903/50000 : ℝ)) (X := (855662753393403/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4407 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9361/50000 : ℝ) ^ (4407/1024 : ℝ) ≤ (36930431741923781/50000000000000000000 : ℝ) := by
    have hpowers : (9361/50000 : ℝ)^4407 ≤ (36930431741923781/50000000000000000000 : ℝ)^1024 := by
      have hnat : (9361 : ℕ)^4407*50000000000000000000^1024 ≤ 36930431741923781^1024*50000^4407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9361 50000 36930431741923781 50000000000000000000 4407 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9361/50000 : ℝ)) (X := (36930431741923781/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4407 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000855662753393403/25000000000000000000 : ℝ) ≤ (10000079526857201/10000000000000000 : ℝ) ^ (4407/1024 : ℝ) := by
    have hpowers : (25000855662753393403/25000000000000000000 : ℝ)^1024 ≤ (10000079526857201/10000000000000000 : ℝ)^4407 := by
      have hnat : (25000855662753393403 : ℕ)^1024*10000000000000000^4407 ≤ 10000079526857201^4407*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000855662753393403 25000000000000000000 10000079526857201 10000000000000000 1024 4407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000079526857201/10000000000000000 : ℝ)) (X := (25000855662753393403/25000000000000000000 : ℝ)) (by norm_num) 4407 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (781840407726489331/781250000000000000 : ℝ) ≤ (10001755468227709/10000000000000000 : ℝ) ^ (4407/1024 : ℝ) := by
    have hpowers : (781840407726489331/781250000000000000 : ℝ)^1024 ≤ (10001755468227709/10000000000000000 : ℝ)^4407 := by
      have hnat : (781840407726489331 : ℕ)^1024*10000000000000000^4407 ≤ 10001755468227709^4407*781250000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781840407726489331 781250000000000000 10001755468227709 10000000000000000 1024 4407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001755468227709/10000000000000000 : ℝ)) (X := (781840407726489331/781250000000000000 : ℝ)) (by norm_num) 4407 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25036930431741923781/25000000000000000000 : ℝ) ≤ (10003431409598217/10000000000000000 : ℝ) ^ (4407/1024 : ℝ) := by
    have hpowers : (25036930431741923781/25000000000000000000 : ℝ)^1024 ≤ (10003431409598217/10000000000000000 : ℝ)^4407 := by
      have hnat : (25036930431741923781 : ℕ)^1024*10000000000000000^4407 ≤ 10003431409598217^4407*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25036930431741923781 25000000000000000000 10003431409598217 10000000000000000 1024 4407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003431409598217/10000000000000000 : ℝ)) (X := (25036930431741923781/25000000000000000000 : ℝ)) (by norm_num) 4407 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(855662753393403/50000000000000000000 : ℝ) ≤ ((5456735165924841761/5458000000000000000 : ℝ)+2*(418985342627/272900000000000 : ℝ)*(3903/50000 : ℝ))^(4407/1024 : ℝ) := by
    rw [show (5456735165924841761/5458000000000000000 : ℝ)+2*(418985342627/272900000000000 : ℝ)*(3903/50000 : ℝ)=(10000079526857201/10000000000000000 : ℝ) by norm_num, show 1+2*(855662753393403/50000000000000000000 : ℝ)=(25000855662753393403/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36930431741923781/50000000000000000000 : ℝ)+(855662753393403/50000000000000000000 : ℝ) ≤ ((5456735165924841761/5458000000000000000 : ℝ)+(418985342627/272900000000000 : ℝ)*((9361/50000 : ℝ)+(3903/50000 : ℝ)))^(4407/1024 : ℝ) := by
    rw [show (5456735165924841761/5458000000000000000 : ℝ)+(418985342627/272900000000000 : ℝ)*((9361/50000 : ℝ)+(3903/50000 : ℝ))=(10001755468227709/10000000000000000 : ℝ) by norm_num, show 1+(36930431741923781/50000000000000000000 : ℝ)+(855662753393403/50000000000000000000 : ℝ)=(781840407726489331/781250000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36930431741923781/50000000000000000000 : ℝ) ≤ ((5456735165924841761/5458000000000000000 : ℝ)+2*(418985342627/272900000000000 : ℝ)*(9361/50000 : ℝ))^(4407/1024 : ℝ) := by
    rw [show (5456735165924841761/5458000000000000000 : ℝ)+2*(418985342627/272900000000000 : ℝ)*(9361/50000 : ℝ)=(10003431409598217/10000000000000000 : ℝ) by norm_num, show 1+2*(36930431741923781/50000000000000000000 : ℝ)=(25036930431741923781/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5456735165924841761/5458000000000000000 : ℝ)*(X 1 0+X 2 0)+(418985342627/272900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4407/1024 : ℝ)) (lo := (3903/50000 : ℝ)) (hi := (9361/50000 : ℝ)) (c := (5456735165924841761/5458000000000000000 : ℝ)) (alpha := (418985342627/272900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5456735165924841761/5458000000000000000 : ℝ)*(X 0 1+X 2 1)+(418985342627/272900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4407/1024 : ℝ)) (lo := (3903/50000 : ℝ)) (hi := (9361/50000 : ℝ)) (c := (5456735165924841761/5458000000000000000 : ℝ)) (alpha := (418985342627/272900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5456735165924841761/5458000000000000000 : ℝ)*(X 0 2+X 1 2)+(418985342627/272900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4407/1024 : ℝ)) (lo := (3903/50000 : ℝ)) (hi := (9361/50000 : ℝ)) (c := (5456735165924841761/5458000000000000000 : ℝ)) (alpha := (418985342627/272900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1949515147/10000000000 : ℝ)*X 0 0+(5454013377/10000000000 : ℝ)*X 0 1+(1301168489/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5358951789/10000000000 : ℝ)*X 1 0+(-1038847341/5000000000 : ℝ)*X 1 1+(650584197/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5358951127/10000000000 : ℝ)*X 2 0+(5204674189/10000000000 : ℝ)*X 2 1+(-1038847377/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2147814379/5000000000 : ℝ)*X 0 0+(4031691389/10000000000 : ℝ)*X 0 1+(571856847/1250000000 : ℝ)*X 0 2+(2147814379/5000000000 : ℝ)*X 1 0+(4031691389/10000000000 : ℝ)*X 1 1+(571856847/1250000000 : ℝ)*X 1 2+(2147814379/5000000000 : ℝ)*X 2 0+(4031691389/10000000000 : ℝ)*X 2 1+(571856847/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1949556861/10000000000 : ℝ)*X 0 0+(5206074513/10000000000 : ℝ)*X 0 1+(2726300923/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647000449/5000000000 : ℝ)*X 1 0+(-1829764899/10000000000 : ℝ)*X 1 1+(5452603163/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293999953/10000000000 : ℝ)*X 2 0+(1363150697/2500000000 : ℝ)*X 2 1+(-73190669/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2147860231/5000000000 : ℝ)*X 0 0+(914361161/2000000000 : ℝ)*X 0 1+(4034765073/10000000000 : ℝ)*X 0 2+(2147860231/5000000000 : ℝ)*X 1 0+(914361161/2000000000 : ℝ)*X 1 1+(4034765073/10000000000 : ℝ)*X 1 2+(2147860231/5000000000 : ℝ)*X 2 0+(914361161/2000000000 : ℝ)*X 2 1+(4034765073/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (262780142624580296151947469/68225000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (75663977/100000000000000 : ℝ)*(base21) + (7849249/12500000000000 : ℝ)*(upper2) + (19969951/12500000000000 : ℝ)*(lower4) + (33616487/25000000000000 : ℝ)*(upper5) + (1462917985499143/50000000000000 : ℝ)*(major0) + (1462917985499143/50000000000000 : ℝ)*(major1) + (1462917985499143/50000000000000 : ℝ)*(major2) + (4010598954017697/100000000000000 : ℝ)*(sp0) + (2005296403499909/50000000000000 : ℝ)*(sp1) + (1002648484299067/25000000000000 : ℝ)*(sp2) + (1841071383077017/100000000000000 : ℝ)*(sp3) + (6147017879/100000000000000 : ℝ)*(sp5) + (1235289363/25000000000000 : ℝ)*(sp6) + (1476512873/100000000000000 : ℝ)*(sp7) + (184107285958989/10000000000000 : ℝ)*(f.failure) + (4010598954017697/100000000000000 : ℝ)*(f.sum) + (72911993762363/13645000000000000000000000000 : ℝ)*base66 + (3087543372166969177/272900000000000000000000000000000 : ℝ)*base68 + (3800691094369177/272900000000000000000000000000000 : ℝ)*base70 + (2824364427456930823/272900000000000000000000000000000 : ℝ)*base71 + (46292393461923/13645000000000000000000000000 : ℝ)*base74 + (411884738832069177/272900000000000000000000000000000 : ℝ)*base76 + (2205336501242269177/272900000000000000000000000000000 : ℝ)*base78 + (1580090181268069177/272900000000000000000000000000000 : ℝ)*base80 + (14863570479217/13645000000000000000000000000 : ℝ)*base81 + (1381891/500000000000000000000 : ℝ)*base90 + (1381891/500000000000000000000 : ℝ)*base92 + (1381891/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2427524240434236241652536587/272900000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (29826049/20000000000000 : ℝ)*(base19) + (68530989/100000000000000 : ℝ)*(upper2) + (152289263/100000000000000 : ℝ)*(upper3) + (354334739/100000000000000 : ℝ)*(lower4) + (2959198041026963/100000000000000 : ℝ)*(major0) + (2959198041026963/100000000000000 : ℝ)*(major1) + (2959198041026963/100000000000000 : ℝ)*(major2) + (10331721/10000000000000 : ℝ)*(sp0) + (2280417391/12500000000000 : ℝ)*(sp1) + (1581336103/25000000000000 : ℝ)*(sp3) + (4056329847542777/100000000000000 : ℝ)*(sp4) + (2028155779195307/50000000000000 : ℝ)*(sp5) + (4056329950859987/100000000000000 : ℝ)*(sp6) + (931029754669951/50000000000000 : ℝ)*(sp7) + (1862065834684313/100000000000000 : ℝ)*(f.failure) + (4056329950859987/100000000000000 : ℝ)*(f.sum) + (2701761031029/3411250000000000000000000000 : ℝ)*base65 + (3257787362578778157/545800000000000000000000000000000 : ℝ)*base68 + (3318285750882578157/545800000000000000000000000000000 : ℝ)*base70 + (5560018829641778157/545800000000000000000000000000000 : ℝ)*base72 + (51426053538119/13645000000000000000000000000 : ℝ)*base74 + (4446260432508978157/545800000000000000000000000000000 : ℝ)*base76 + (3490077376654378157/545800000000000000000000000000000 : ℝ)*base78 + (901341155791778157/545800000000000000000000000000000 : ℝ)*base80 + (168823646883/6822500000000000000000000000 : ℝ)*base81 + (29590647/5000000000000000000000 : ℝ)*base90 + (29590647/5000000000000000000000 : ℝ)*base92 + (29590647/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1448_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79460081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9361/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3903/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10467/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15743/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1448_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1448_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79460081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10467/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15743/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1448_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1448_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1448_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79460081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10467/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15743/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1448_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
