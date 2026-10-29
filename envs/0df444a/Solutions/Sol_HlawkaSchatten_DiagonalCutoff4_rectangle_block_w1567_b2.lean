-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1567_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:26:33.143867+00:00
-- url     : https://prove2.me/submissions/c1a39e43-e386-4b8b-9988-5beb902e8d42

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
theorem support_rectangle_w1567_s6_0 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-111857633/625000000 : ℝ)*x 0 + (5426165981/10000000000 : ℝ)*x 1 + (41759709/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (111857633/625000000 : ℝ)^4631 ≤ (10981384475063/100000000000000 : ℝ)^3607 := by
    have hnat : (111857633 : ℕ)^4631*100000000000000^3607 ≤ 10981384475063^3607*625000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111857633 625000000 10981384475063 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5426165981/10000000000 : ℝ)^4631 ≤ (22808024557209/50000000000000 : ℝ)^3607 := by
    have hnat : (5426165981 : ℕ)^4631*50000000000000^3607 ≤ 22808024557209^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426165981 10000000000 22808024557209 50000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41759709/80000000 : ℝ)^4631 ≤ (43402566398089/100000000000000 : ℝ)^3607 := by
    have hnat : (41759709 : ℕ)^4631*100000000000000^3607 ≤ 43402566398089^3607*80000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41759709 80000000 43402566398089 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-111857633/625000000 : ℝ), (5426165981/10000000000 : ℝ), (41759709/80000000 : ℝ)] ![(10981384475063/100000000000000 : ℝ), (22808024557209/50000000000000 : ℝ), (43402566398089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-111857633/625000000 : ℝ)|^4631 ≤ (10981384475063/100000000000000 : ℝ)^3607
        have hw : |(-111857633/625000000 : ℝ)|=(111857633/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5426165981/10000000000 : ℝ)|^4631 ≤ (22808024557209/50000000000000 : ℝ)^3607
        have hw : |(5426165981/10000000000 : ℝ)|=(5426165981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(41759709/80000000 : ℝ)|^4631 ≤ (43402566398089/100000000000000 : ℝ)^3607
        have hw : |(41759709/80000000 : ℝ)|=(41759709/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_s6_1 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674186631/5000000000 : ℝ)*x 0 + (-947608827/5000000000 : ℝ)*x 1 + (5219963821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674186631/5000000000 : ℝ)^4631 ≤ (11194531373449/25000000000000 : ℝ)^3607 := by
    have hnat : (2674186631 : ℕ)^4631*25000000000000^3607 ≤ 11194531373449^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674186631 5000000000 11194531373449 25000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (947608827/5000000000 : ℝ)^4631 ≤ (47277224029/400000000000 : ℝ)^3607 := by
    have hnat : (947608827 : ℕ)^4631*400000000000^3607 ≤ 47277224029^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      947608827 5000000000 47277224029 400000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219963821/10000000000 : ℝ)^4631 ≤ (4340256849043/10000000000000 : ℝ)^3607 := by
    have hnat : (5219963821 : ℕ)^4631*10000000000000^3607 ≤ 4340256849043^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219963821 10000000000 4340256849043 10000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674186631/5000000000 : ℝ), (-947608827/5000000000 : ℝ), (5219963821/10000000000 : ℝ)] ![(11194531373449/25000000000000 : ℝ), (47277224029/400000000000 : ℝ), (4340256849043/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674186631/5000000000 : ℝ)|^4631 ≤ (11194531373449/25000000000000 : ℝ)^3607
        have hw : |(2674186631/5000000000 : ℝ)|=(2674186631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-947608827/5000000000 : ℝ)|^4631 ≤ (47277224029/400000000000 : ℝ)^3607
        have hw : |(-947608827/5000000000 : ℝ)|=(947608827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219963821/10000000000 : ℝ)|^4631 ≤ (4340256849043/10000000000000 : ℝ)^3607
        have hw : |(5219963821/10000000000 : ℝ)|=(5219963821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_s6_2 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674186663/5000000000 : ℝ)*x 0 + (5219963753/10000000000 : ℝ)*x 1 + (-947608829/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674186663/5000000000 : ℝ)^4631 ≤ (2238906309087/5000000000000 : ℝ)^3607 := by
    have hnat : (2674186663 : ℕ)^4631*5000000000000^3607 ≤ 2238906309087^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674186663 5000000000 2238906309087 5000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219963753/10000000000 : ℝ)^4631 ≤ (10850641941129/25000000000000 : ℝ)^3607 := by
    have hnat : (5219963753 : ℕ)^4631*25000000000000^3607 ≤ 10850641941129^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219963753 10000000000 10850641941129 25000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (947608829/5000000000 : ℝ)^4631 ≤ (11819306039277/100000000000000 : ℝ)^3607 := by
    have hnat : (947608829 : ℕ)^4631*100000000000000^3607 ≤ 11819306039277^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      947608829 5000000000 11819306039277 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674186663/5000000000 : ℝ), (5219963753/10000000000 : ℝ), (-947608829/5000000000 : ℝ)] ![(2238906309087/5000000000000 : ℝ), (10850641941129/25000000000000 : ℝ), (11819306039277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674186663/5000000000 : ℝ)|^4631 ≤ (2238906309087/5000000000000 : ℝ)^3607
        have hw : |(2674186663/5000000000 : ℝ)|=(2674186663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219963753/10000000000 : ℝ)|^4631 ≤ (10850641941129/25000000000000 : ℝ)^3607
        have hw : |(5219963753/10000000000 : ℝ)|=(5219963753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-947608829/5000000000 : ℝ)|^4631 ≤ (11819306039277/100000000000000 : ℝ)^3607
        have hw : |(-947608829/5000000000 : ℝ)|=(947608829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_s6_3 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2122414491/5000000000 : ℝ)*x 0 + (2003795639/5000000000 : ℝ)*x 1 + (2246674471/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2122414491/5000000000 : ℝ)^4631 ≤ (33282238206223/100000000000000 : ℝ)^3607 := by
    have hnat : (2122414491 : ℕ)^4631*100000000000000^3607 ≤ 33282238206223^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122414491 5000000000 33282238206223 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2003795639/5000000000 : ℝ)^4631 ≤ (3091327605087/10000000000000 : ℝ)^3607 := by
    have hnat : (2003795639 : ℕ)^4631*10000000000000^3607 ≤ 3091327605087^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2003795639 5000000000 3091327605087 10000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2246674471/5000000000 : ℝ)^4631 ≤ (35804485724421/100000000000000 : ℝ)^3607 := by
    have hnat : (2246674471 : ℕ)^4631*100000000000000^3607 ≤ 35804485724421^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246674471 5000000000 35804485724421 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2122414491/5000000000 : ℝ), (2003795639/5000000000 : ℝ), (2246674471/5000000000 : ℝ)] ![(33282238206223/100000000000000 : ℝ), (3091327605087/10000000000000 : ℝ), (35804485724421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2122414491/5000000000 : ℝ)|^4631 ≤ (33282238206223/100000000000000 : ℝ)^3607
        have hw : |(2122414491/5000000000 : ℝ)|=(2122414491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2003795639/5000000000 : ℝ)|^4631 ≤ (3091327605087/10000000000000 : ℝ)^3607
        have hw : |(2003795639/5000000000 : ℝ)|=(2003795639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2246674471/5000000000 : ℝ)|^4631 ≤ (35804485724421/100000000000000 : ℝ)^3607
        have hw : |(2246674471/5000000000 : ℝ)|=(2246674471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_s6_4 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1789748937/10000000000 : ℝ)*x 0 + (1044207429/2000000000 : ℝ)*x 1 + (217003383/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1789748937/10000000000 : ℝ)^4631 ≤ (10981595669107/100000000000000 : ℝ)^3607 := by
    have hnat : (1789748937 : ℕ)^4631*100000000000000^3607 ≤ 10981595669107^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1789748937 10000000000 10981595669107 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1044207429/2000000000 : ℝ)^4631 ≤ (43414026787883/100000000000000 : ℝ)^3607 := by
    have hnat : (1044207429 : ℕ)^4631*100000000000000^3607 ≤ 43414026787883^3607*2000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044207429 2000000000 43414026787883 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (217003383/400000000 : ℝ)^4631 ≤ (45604377532561/100000000000000 : ℝ)^3607 := by
    have hnat : (217003383 : ℕ)^4631*100000000000000^3607 ≤ 45604377532561^3607*400000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217003383 400000000 45604377532561 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1789748937/10000000000 : ℝ), (1044207429/2000000000 : ℝ), (217003383/400000000 : ℝ)] ![(10981595669107/100000000000000 : ℝ), (43414026787883/100000000000000 : ℝ), (45604377532561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1789748937/10000000000 : ℝ)|^4631 ≤ (10981595669107/100000000000000 : ℝ)^3607
        have hw : |(-1789748937/10000000000 : ℝ)|=(1789748937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1044207429/2000000000 : ℝ)|^4631 ≤ (43414026787883/100000000000000 : ℝ)^3607
        have hw : |(1044207429/2000000000 : ℝ)|=(1044207429/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(217003383/400000000 : ℝ)|^4631 ≤ (45604377532561/100000000000000 : ℝ)^3607
        have hw : |(217003383/400000000 : ℝ)|=(217003383/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_s6_5 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2122446211/5000000000 : ℝ)*x 0 + (561352563/1250000000 : ℝ)*x 1 + (501267283/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2122446211/5000000000 : ℝ)^4631 ≤ (16641438414983/50000000000000 : ℝ)^3607 := by
    have hnat : (2122446211 : ℕ)^4631*50000000000000^3607 ≤ 16641438414983^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122446211 5000000000 16641438414983 50000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (561352563/1250000000 : ℝ)^4631 ≤ (17889310330533/50000000000000 : ℝ)^3607 := by
    have hnat : (561352563 : ℕ)^4631*50000000000000^3607 ≤ 17889310330533^3607*1250000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561352563 1250000000 17889310330533 50000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (501267283/1250000000 : ℝ)^4631 ≤ (15469251245739/50000000000000 : ℝ)^3607 := by
    have hnat : (501267283 : ℕ)^4631*50000000000000^3607 ≤ 15469251245739^3607*1250000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501267283 1250000000 15469251245739 50000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2122446211/5000000000 : ℝ), (561352563/1250000000 : ℝ), (501267283/1250000000 : ℝ)] ![(16641438414983/50000000000000 : ℝ), (17889310330533/50000000000000 : ℝ), (15469251245739/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2122446211/5000000000 : ℝ)|^4631 ≤ (16641438414983/50000000000000 : ℝ)^3607
        have hw : |(2122446211/5000000000 : ℝ)|=(2122446211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(561352563/1250000000 : ℝ)|^4631 ≤ (17889310330533/50000000000000 : ℝ)^3607
        have hw : |(561352563/1250000000 : ℝ)|=(561352563/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(501267283/1250000000 : ℝ)|^4631 ≤ (15469251245739/50000000000000 : ℝ)^3607
        have hw : |(501267283/1250000000 : ℝ)|=(501267283/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1567_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41946731/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11111/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1389/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3097/20000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (11111/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11111/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11111/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11111/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11111/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11111/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11111/100000 : ℝ) ^ (4629/1024 : ℝ) ≤ (971291625623909/20000000000000000000 : ℝ) := by
    have hpowers : (11111/100000 : ℝ)^4629 ≤ (971291625623909/20000000000000000000 : ℝ)^1024 := by
      have hnat : (11111 : ℕ)^4629*20000000000000000000^1024 ≤ 971291625623909^1024*100000^4629 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11111 100000 971291625623909 20000000000000000000 4629 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11111/100000 : ℝ)) (X := (971291625623909/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4629 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3097/20000 : ℝ) ^ (4629/1024 : ℝ) ≤ (21776460637976013/100000000000000000000 : ℝ) := by
    have hpowers : (3097/20000 : ℝ)^4629 ≤ (21776460637976013/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3097 : ℕ)^4629*100000000000000000000^1024 ≤ 21776460637976013^1024*20000^4629 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3097 20000 21776460637976013 100000000000000000000 4629 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3097/20000 : ℝ)) (X := (21776460637976013/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4629 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000971291625623909/10000000000000000000 : ℝ) ≤ (80001718842099/80000000000000 : ℝ) ^ (4629/1024 : ℝ) := by
    have hpowers : (10000971291625623909/10000000000000000000 : ℝ)^1024 ≤ (80001718842099/80000000000000 : ℝ)^4629 := by
      have hnat : (10000971291625623909 : ℕ)^1024*80000000000000^4629 ≤ 80001718842099^4629*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000971291625623909 10000000000000000000 80001718842099 80000000000000 1024 4629 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80001718842099/80000000000000 : ℝ)) (X := (10000971291625623909/10000000000000000000 : ℝ)) (by norm_num) 4629 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50013316459383047779/50000000000000000000 : ℝ) ≤ (10000589096585923/10000000000000000 : ℝ) ^ (4629/1024 : ℝ) := by
    have hpowers : (50013316459383047779/50000000000000000000 : ℝ)^1024 ≤ (10000589096585923/10000000000000000 : ℝ)^4629 := by
      have hnat : (50013316459383047779 : ℕ)^1024*10000000000000000^4629 ≤ 10000589096585923^4629*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013316459383047779 50000000000000000000 10000589096585923 10000000000000000 1024 4629 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000589096585923/10000000000000000 : ℝ)) (X := (50013316459383047779/50000000000000000000 : ℝ)) (by norm_num) 4629 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50021776460637976013/50000000000000000000 : ℝ) ≤ (10000963337909471/10000000000000000 : ℝ) ^ (4629/1024 : ℝ) := by
    have hpowers : (50021776460637976013/50000000000000000000 : ℝ)^1024 ≤ (10000963337909471/10000000000000000 : ℝ)^4629 := by
      have hnat : (50021776460637976013 : ℕ)^1024*10000000000000000^4629 ≤ 10000963337909471^4629*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021776460637976013 50000000000000000000 10000963337909471 10000000000000000 1024 4629 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000963337909471/10000000000000000 : ℝ)) (X := (50021776460637976013/50000000000000000000 : ℝ)) (by norm_num) 4629 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(971291625623909/20000000000000000000 : ℝ) ≤ ((21866311693112872297/21870000000000000000 : ℝ)+2*(93560330887/109350000000000 : ℝ)*(11111/100000 : ℝ))^(4629/1024 : ℝ) := by
    rw [show (21866311693112872297/21870000000000000000 : ℝ)+2*(93560330887/109350000000000 : ℝ)*(11111/100000 : ℝ)=(80001718842099/80000000000000 : ℝ) by norm_num, show 1+2*(971291625623909/20000000000000000000 : ℝ)=(10000971291625623909/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(21776460637976013/100000000000000000000 : ℝ)+(971291625623909/20000000000000000000 : ℝ) ≤ ((21866311693112872297/21870000000000000000 : ℝ)+(93560330887/109350000000000 : ℝ)*((3097/20000 : ℝ)+(11111/100000 : ℝ)))^(4629/1024 : ℝ) := by
    rw [show (21866311693112872297/21870000000000000000 : ℝ)+(93560330887/109350000000000 : ℝ)*((3097/20000 : ℝ)+(11111/100000 : ℝ))=(10000589096585923/10000000000000000 : ℝ) by norm_num, show 1+(21776460637976013/100000000000000000000 : ℝ)+(971291625623909/20000000000000000000 : ℝ)=(50013316459383047779/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(21776460637976013/100000000000000000000 : ℝ) ≤ ((21866311693112872297/21870000000000000000 : ℝ)+2*(93560330887/109350000000000 : ℝ)*(3097/20000 : ℝ))^(4629/1024 : ℝ) := by
    rw [show (21866311693112872297/21870000000000000000 : ℝ)+2*(93560330887/109350000000000 : ℝ)*(3097/20000 : ℝ)=(10000963337909471/10000000000000000 : ℝ) by norm_num, show 1+2*(21776460637976013/100000000000000000000 : ℝ)=(50021776460637976013/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (21866311693112872297/21870000000000000000 : ℝ)*(X 1 0+X 2 0)+(93560330887/109350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4629/1024 : ℝ)) (lo := (11111/100000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (21866311693112872297/21870000000000000000 : ℝ)) (alpha := (93560330887/109350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (21866311693112872297/21870000000000000000 : ℝ)*(X 0 1+X 2 1)+(93560330887/109350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4629/1024 : ℝ)) (lo := (11111/100000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (21866311693112872297/21870000000000000000 : ℝ)) (alpha := (93560330887/109350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (21866311693112872297/21870000000000000000 : ℝ)*(X 0 2+X 1 2)+(93560330887/109350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4629/1024 : ℝ)) (lo := (11111/100000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (21866311693112872297/21870000000000000000 : ℝ)) (alpha := (93560330887/109350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-111857633/625000000 : ℝ)*X 0 0+(5426165981/10000000000 : ℝ)*X 0 1+(41759709/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674186631/5000000000 : ℝ)*X 1 0+(-947608827/5000000000 : ℝ)*X 1 1+(5219963821/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674186663/5000000000 : ℝ)*X 2 0+(5219963753/10000000000 : ℝ)*X 2 1+(-947608829/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2122414491/5000000000 : ℝ)*X 0 0+(2003795639/5000000000 : ℝ)*X 0 1+(2246674471/5000000000 : ℝ)*X 0 2+(2122414491/5000000000 : ℝ)*X 1 0+(2003795639/5000000000 : ℝ)*X 1 1+(2246674471/5000000000 : ℝ)*X 1 2+(2122414491/5000000000 : ℝ)*X 2 0+(2003795639/5000000000 : ℝ)*X 2 1+(2246674471/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1789748937/10000000000 : ℝ)*X 0 0+(1044207429/2000000000 : ℝ)*X 0 1+(217003383/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2122446211/5000000000 : ℝ)*X 0 0+(561352563/1250000000 : ℝ)*X 0 1+(501267283/1250000000 : ℝ)*X 0 2+(2122446211/5000000000 : ℝ)*X 1 0+(561352563/1250000000 : ℝ)*X 1 1+(501267283/1250000000 : ℝ)*X 1 2+(2122446211/5000000000 : ℝ)*X 2 0+(561352563/1250000000 : ℝ)*X 2 1+(501267283/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s6_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (33380886506643461680593949/9112500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (151560793/25000000000000 : ℝ)*(base19) + (648765121/100000000000000 : ℝ)*(base23) + (274067/400000000000 : ℝ)*(upper3) + (8295337/100000000000000 : ℝ)*(upper4) + (62306781/100000000000000 : ℝ)*(upper5) + (86353541305783/2500000000000 : ℝ)*(major0) + (86353541305783/2500000000000 : ℝ)*(major1) + (86353541305783/2500000000000 : ℝ)*(major2) + (121240501521149/2500000000000 : ℝ)*(sp0) + (2424817437935879/50000000000000 : ℝ)*(sp1) + (4849634833349809/100000000000000 : ℝ)*(sp2) + (2058643539446863/100000000000000 : ℝ)*(sp3) + (1542126897/10000000000000 : ℝ)*(sp4) + (4160794259/100000000000000 : ℝ)*(sp5) + (2058647700241123/100000000000000 : ℝ)*(f.failure) + (484963548211493/10000000000000 : ℝ)*(f.sum) + (2830767730771/1093500000000000000000000000 : ℝ)*base66 + (18852373967745161/6075000000000000000000000000000 : ℝ)*base68 + (20988003269354839/6075000000000000000000000000000 : ℝ)*base69 + (50040565144754839/6075000000000000000000000000000 : ℝ)*base71 + (10617244507/218700000000000000000000000 : ℝ)*base73 + (31222518481245161/6075000000000000000000000000000 : ℝ)*base76 + (24193504806404839/6075000000000000000000000000000 : ℝ)*base77 + (72817579247729839/6075000000000000000000000000000 : ℝ)*base79 + (755459618521/136687500000000000000000000 : ℝ)*base81 + (21618913/2500000000000000000000 : ℝ)*base89 + (21618913/2500000000000000000000 : ℝ)*base91 + (21618913/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1567_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41946731/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11111/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1389/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1567_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1567_box_0 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-792716157/5000000000 : ℝ)*x 0 + (5396914237/10000000000 : ℝ)*x 1 + (21081693/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (792716157/5000000000 : ℝ)^4631 ≤ (4699435544857/50000000000000 : ℝ)^3607 := by
    have hnat : (792716157 : ℕ)^4631*50000000000000^3607 ≤ 4699435544857^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      792716157 5000000000 4699435544857 50000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396914237/10000000000 : ℝ)^4631 ≤ (22650284455611/50000000000000 : ℝ)^3607 := by
    have hnat : (5396914237 : ℕ)^4631*50000000000000^3607 ≤ 22650284455611^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396914237 10000000000 22650284455611 50000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21081693/39062500 : ℝ)^4631 ≤ (22650279988659/50000000000000 : ℝ)^3607 := by
    have hnat : (21081693 : ℕ)^4631*50000000000000^3607 ≤ 22650279988659^3607*39062500^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21081693 39062500 22650279988659 50000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-792716157/5000000000 : ℝ), (5396914237/10000000000 : ℝ), (21081693/39062500 : ℝ)] ![(4699435544857/50000000000000 : ℝ), (22650284455611/50000000000000 : ℝ), (22650279988659/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-792716157/5000000000 : ℝ)|^4631 ≤ (4699435544857/50000000000000 : ℝ)^3607
        have hw : |(-792716157/5000000000 : ℝ)|=(792716157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396914237/10000000000 : ℝ)|^4631 ≤ (22650284455611/50000000000000 : ℝ)^3607
        have hw : |(5396914237/10000000000 : ℝ)|=(5396914237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(21081693/39062500 : ℝ)|^4631 ≤ (22650279988659/50000000000000 : ℝ)^3607
        have hw : |(21081693/39062500 : ℝ)|=(21081693/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_box_1 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5271142471/10000000000 : ℝ)*x 0 + (-1760251097/10000000000 : ℝ)*x 1 + (2698456933/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5271142471/10000000000 : ℝ)^4631 ≤ (5493708760967/12500000000000 : ℝ)^3607 := by
    have hnat : (5271142471 : ℕ)^4631*12500000000000^3607 ≤ 5493708760967^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271142471 10000000000 5493708760967 12500000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1760251097/10000000000 : ℝ)^4631 ≤ (10749764974913/100000000000000 : ℝ)^3607 := by
    have hnat : (1760251097 : ℕ)^4631*100000000000000^3607 ≤ 10749764974913^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1760251097 10000000000 10749764974913 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698456933/5000000000 : ℝ)^4631 ≤ (22650282456529/50000000000000 : ℝ)^3607 := by
    have hnat : (2698456933 : ℕ)^4631*50000000000000^3607 ≤ 22650282456529^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698456933 5000000000 22650282456529 50000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5271142471/10000000000 : ℝ), (-1760251097/10000000000 : ℝ), (2698456933/5000000000 : ℝ)] ![(5493708760967/12500000000000 : ℝ), (10749764974913/100000000000000 : ℝ), (22650282456529/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5271142471/10000000000 : ℝ)|^4631 ≤ (5493708760967/12500000000000 : ℝ)^3607
        have hw : |(5271142471/10000000000 : ℝ)|=(5271142471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1760251097/10000000000 : ℝ)|^4631 ≤ (10749764974913/100000000000000 : ℝ)^3607
        have hw : |(-1760251097/10000000000 : ℝ)|=(1760251097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698456933/5000000000 : ℝ)|^4631 ≤ (22650282456529/50000000000000 : ℝ)^3607
        have hw : |(2698456933/5000000000 : ℝ)|=(2698456933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_box_2 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5271142957/10000000000 : ℝ)*x 0 + (5396913829/10000000000 : ℝ)*x 1 + (-352050097/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5271142957/10000000000 : ℝ)^4631 ≤ (43949675290281/100000000000000 : ℝ)^3607 := by
    have hnat : (5271142957 : ℕ)^4631*100000000000000^3607 ≤ 43949675290281^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271142957 10000000000 43949675290281 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396913829/10000000000 : ℝ)^4631 ≤ (45300564514319/100000000000000 : ℝ)^3607 := by
    have hnat : (5396913829 : ℕ)^4631*100000000000000^3607 ≤ 45300564514319^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396913829 10000000000 45300564514319 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (352050097/2000000000 : ℝ)^4631 ≤ (429990407057/4000000000000 : ℝ)^3607 := by
    have hnat : (352050097 : ℕ)^4631*4000000000000^3607 ≤ 429990407057^3607*2000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      352050097 2000000000 429990407057 4000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5271142957/10000000000 : ℝ), (5396913829/10000000000 : ℝ), (-352050097/2000000000 : ℝ)] ![(43949675290281/100000000000000 : ℝ), (45300564514319/100000000000000 : ℝ), (429990407057/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5271142957/10000000000 : ℝ)|^4631 ≤ (43949675290281/100000000000000 : ℝ)^3607
        have hw : |(5271142957/10000000000 : ℝ)|=(5271142957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396913829/10000000000 : ℝ)|^4631 ≤ (45300564514319/100000000000000 : ℝ)^3607
        have hw : |(5396913829/10000000000 : ℝ)|=(5396913829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-352050097/2000000000 : ℝ)|^4631 ≤ (429990407057/4000000000000 : ℝ)^3607
        have hw : |(-352050097/2000000000 : ℝ)|=(352050097/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_box_3 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4445627697/10000000000 : ℝ)*x 0 + (4151080569/10000000000 : ℝ)*x 1 + (830216317/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4445627697/10000000000 : ℝ)^4631 ≤ (1412680497439/4000000000000 : ℝ)^3607 := by
    have hnat : (4445627697 : ℕ)^4631*4000000000000^3607 ≤ 1412680497439^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4445627697 10000000000 1412680497439 4000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4151080569/10000000000 : ℝ)^4631 ≤ (32341488696937/100000000000000 : ℝ)^3607 := by
    have hnat : (4151080569 : ℕ)^4631*100000000000000^3607 ≤ 32341488696937^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4151080569 10000000000 32341488696937 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (830216317/2000000000 : ℝ)^4631 ≤ (404268735749/1250000000000 : ℝ)^3607 := by
    have hnat : (830216317 : ℕ)^4631*1250000000000^3607 ≤ 404268735749^3607*2000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      830216317 2000000000 404268735749 1250000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4445627697/10000000000 : ℝ), (4151080569/10000000000 : ℝ), (830216317/2000000000 : ℝ)] ![(1412680497439/4000000000000 : ℝ), (32341488696937/100000000000000 : ℝ), (404268735749/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4445627697/10000000000 : ℝ)|^4631 ≤ (1412680497439/4000000000000 : ℝ)^3607
        have hw : |(4445627697/10000000000 : ℝ)|=(4445627697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4151080569/10000000000 : ℝ)|^4631 ≤ (32341488696937/100000000000000 : ℝ)^3607
        have hw : |(4151080569/10000000000 : ℝ)|=(4151080569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(830216317/2000000000 : ℝ)|^4631 ≤ (404268735749/1250000000000 : ℝ)^3607
        have hw : |(830216317/2000000000 : ℝ)|=(830216317/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_box_4 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-49985069/250000000 : ℝ)*x 0 + (2622500799/5000000000 : ℝ)*x 1 + (1311250543/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (49985069/250000000 : ℝ)^4631 ≤ (2531985216967/20000000000000 : ℝ)^3607 := by
    have hnat : (49985069 : ℕ)^4631*20000000000000^3607 ≤ 2531985216967^3607*250000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49985069 250000000 2531985216967 20000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622500799/5000000000 : ℝ)^4631 ≤ (8734006776471/20000000000000 : ℝ)^3607 := by
    have hnat : (2622500799 : ℕ)^4631*20000000000000^3607 ≤ 8734006776471^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622500799 5000000000 8734006776471 20000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311250543/2500000000 : ℝ)^4631 ≤ (21835020009129/50000000000000 : ℝ)^3607 := by
    have hnat : (1311250543 : ℕ)^4631*50000000000000^3607 ≤ 21835020009129^3607*2500000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311250543 2500000000 21835020009129 50000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-49985069/250000000 : ℝ), (2622500799/5000000000 : ℝ), (1311250543/2500000000 : ℝ)] ![(2531985216967/20000000000000 : ℝ), (8734006776471/20000000000000 : ℝ), (21835020009129/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-49985069/250000000 : ℝ)|^4631 ≤ (2531985216967/20000000000000 : ℝ)^3607
        have hw : |(-49985069/250000000 : ℝ)|=(49985069/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622500799/5000000000 : ℝ)|^4631 ≤ (8734006776471/20000000000000 : ℝ)^3607
        have hw : |(2622500799/5000000000 : ℝ)|=(2622500799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311250543/2500000000 : ℝ)|^4631 ≤ (21835020009129/50000000000000 : ℝ)^3607
        have hw : |(1311250543/2500000000 : ℝ)|=(1311250543/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_box_5 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2688233937/5000000000 : ℝ)*x 0 + (-91184053/500000000 : ℝ)*x 1 + (2622500937/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688233937/5000000000 : ℝ)^4631 ≤ (45080342692921/100000000000000 : ℝ)^3607 := by
    have hnat : (2688233937 : ℕ)^4631*100000000000000^3607 ≤ 45080342692921^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688233937 5000000000 45080342692921 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (91184053/500000000 : ℝ)^4631 ≤ (449984818491/4000000000000 : ℝ)^3607 := by
    have hnat : (91184053 : ℕ)^4631*4000000000000^3607 ≤ 449984818491^3607*500000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91184053 500000000 449984818491 4000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622500937/5000000000 : ℝ)^4631 ≤ (545875460409/1250000000000 : ℝ)^3607 := by
    have hnat : (2622500937 : ℕ)^4631*1250000000000^3607 ≤ 545875460409^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622500937 5000000000 545875460409 1250000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688233937/5000000000 : ℝ), (-91184053/500000000 : ℝ), (2622500937/5000000000 : ℝ)] ![(45080342692921/100000000000000 : ℝ), (449984818491/4000000000000 : ℝ), (545875460409/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688233937/5000000000 : ℝ)|^4631 ≤ (45080342692921/100000000000000 : ℝ)^3607
        have hw : |(2688233937/5000000000 : ℝ)|=(2688233937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-91184053/500000000 : ℝ)|^4631 ≤ (449984818491/4000000000000 : ℝ)^3607
        have hw : |(-91184053/500000000 : ℝ)|=(91184053/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622500937/5000000000 : ℝ)|^4631 ≤ (545875460409/1250000000000 : ℝ)^3607
        have hw : |(2622500937/5000000000 : ℝ)|=(2622500937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_box_6 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1075293579/2000000000 : ℝ)*x 0 + (5245002283/10000000000 : ℝ)*x 1 + (-1823680479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075293579/2000000000 : ℝ)^4631 ≤ (45080342918989/100000000000000 : ℝ)^3607 := by
    have hnat : (1075293579 : ℕ)^4631*100000000000000^3607 ≤ 45080342918989^3607*2000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075293579 2000000000 45080342918989 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245002283/10000000000 : ℝ)^4631 ≤ (43670041204817/100000000000000 : ℝ)^3607 := by
    have hnat : (5245002283 : ℕ)^4631*100000000000000^3607 ≤ 43670041204817^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245002283 10000000000 43670041204817 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1823680479/10000000000 : ℝ)^4631 ≤ (2249923172167/20000000000000 : ℝ)^3607 := by
    have hnat : (1823680479 : ℕ)^4631*20000000000000^3607 ≤ 2249923172167^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1823680479 10000000000 2249923172167 20000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075293579/2000000000 : ℝ), (5245002283/10000000000 : ℝ), (-1823680479/10000000000 : ℝ)] ![(45080342918989/100000000000000 : ℝ), (43670041204817/100000000000000 : ℝ), (2249923172167/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075293579/2000000000 : ℝ)|^4631 ≤ (45080342918989/100000000000000 : ℝ)^3607
        have hw : |(1075293579/2000000000 : ℝ)|=(1075293579/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245002283/10000000000 : ℝ)|^4631 ≤ (43670041204817/100000000000000 : ℝ)^3607
        have hw : |(5245002283/10000000000 : ℝ)|=(5245002283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1823680479/10000000000 : ℝ)|^4631 ≤ (2249923172167/20000000000000 : ℝ)^3607
        have hw : |(-1823680479/10000000000 : ℝ)|=(1823680479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_box_7 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4041354181/10000000000 : ℝ)*x 0 + (4353090371/10000000000 : ℝ)*x 1 + (2176544897/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4041354181/10000000000 : ℝ)^4631 ≤ (31248047208857/100000000000000 : ℝ)^3607 := by
    have hnat : (4041354181 : ℕ)^4631*100000000000000^3607 ≤ 31248047208857^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4041354181 10000000000 31248047208857 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4353090371/10000000000 : ℝ)^4631 ≤ (1375039172687/4000000000000 : ℝ)^3607 := by
    have hnat : (4353090371 : ℕ)^4631*4000000000000^3607 ≤ 1375039172687^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4353090371 10000000000 1375039172687 4000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2176544897/5000000000 : ℝ)^4631 ≤ (17187986733547/50000000000000 : ℝ)^3607 := by
    have hnat : (2176544897 : ℕ)^4631*50000000000000^3607 ≤ 17187986733547^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176544897 5000000000 17187986733547 50000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4041354181/10000000000 : ℝ), (4353090371/10000000000 : ℝ), (2176544897/5000000000 : ℝ)] ![(31248047208857/100000000000000 : ℝ), (1375039172687/4000000000000 : ℝ), (17187986733547/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4041354181/10000000000 : ℝ)|^4631 ≤ (31248047208857/100000000000000 : ℝ)^3607
        have hw : |(4041354181/10000000000 : ℝ)|=(4041354181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4353090371/10000000000 : ℝ)|^4631 ≤ (1375039172687/4000000000000 : ℝ)^3607
        have hw : |(4353090371/10000000000 : ℝ)|=(4353090371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2176544897/5000000000 : ℝ)|^4631 ≤ (17187986733547/50000000000000 : ℝ)^3607
        have hw : |(2176544897/5000000000 : ℝ)|=(2176544897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_box_8 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-477916717/2500000000 : ℝ)*x 0 + (2569002073/5000000000 : ℝ)*x 1 + (5417194197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (477916717/2500000000 : ℝ)^4631 ≤ (11951174271731/100000000000000 : ℝ)^3607 := by
    have hnat : (477916717 : ℕ)^4631*100000000000000^3607 ≤ 11951174271731^3607*2500000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      477916717 2500000000 11951174271731 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2569002073/5000000000 : ℝ)^4631 ≤ (21264794399579/50000000000000 : ℝ)^3607 := by
    have hnat : (2569002073 : ℕ)^4631*50000000000000^3607 ≤ 21264794399579^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2569002073 5000000000 21264794399579 50000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5417194197/10000000000 : ℝ)^4631 ≤ (11379809230191/25000000000000 : ℝ)^3607 := by
    have hnat : (5417194197 : ℕ)^4631*25000000000000^3607 ≤ 11379809230191^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417194197 10000000000 11379809230191 25000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-477916717/2500000000 : ℝ), (2569002073/5000000000 : ℝ), (5417194197/10000000000 : ℝ)] ![(11951174271731/100000000000000 : ℝ), (21264794399579/50000000000000 : ℝ), (11379809230191/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-477916717/2500000000 : ℝ)|^4631 ≤ (11951174271731/100000000000000 : ℝ)^3607
        have hw : |(-477916717/2500000000 : ℝ)|=(477916717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2569002073/5000000000 : ℝ)|^4631 ≤ (21264794399579/50000000000000 : ℝ)^3607
        have hw : |(2569002073/5000000000 : ℝ)|=(2569002073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5417194197/10000000000 : ℝ)|^4631 ≤ (11379809230191/25000000000000 : ℝ)^3607
        have hw : |(5417194197/10000000000 : ℝ)|=(5417194197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_box_9 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628538959/5000000000 : ℝ)*x 0 + (-1751550169/10000000000 : ℝ)*x 1 + (2708597221/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628538959/5000000000 : ℝ)^4631 ≤ (10949792148091/25000000000000 : ℝ)^3607 := by
    have hnat : (2628538959 : ℕ)^4631*25000000000000^3607 ≤ 10949792148091^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628538959 5000000000 10949792148091 25000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1751550169/10000000000 : ℝ)^4631 ≤ (10681591823097/100000000000000 : ℝ)^3607 := by
    have hnat : (1751550169 : ℕ)^4631*100000000000000^3607 ≤ 10681591823097^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1751550169 10000000000 10681591823097 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2708597221/5000000000 : ℝ)^4631 ≤ (364153916511/800000000000 : ℝ)^3607 := by
    have hnat : (2708597221 : ℕ)^4631*800000000000^3607 ≤ 364153916511^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708597221 5000000000 364153916511 800000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628538959/5000000000 : ℝ), (-1751550169/10000000000 : ℝ), (2708597221/5000000000 : ℝ)] ![(10949792148091/25000000000000 : ℝ), (10681591823097/100000000000000 : ℝ), (364153916511/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628538959/5000000000 : ℝ)|^4631 ≤ (10949792148091/25000000000000 : ℝ)^3607
        have hw : |(2628538959/5000000000 : ℝ)|=(2628538959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1751550169/10000000000 : ℝ)|^4631 ≤ (10681591823097/100000000000000 : ℝ)^3607
        have hw : |(-1751550169/10000000000 : ℝ)|=(1751550169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2708597221/5000000000 : ℝ)|^4631 ≤ (364153916511/800000000000 : ℝ)^3607
        have hw : |(2708597221/5000000000 : ℝ)|=(2708597221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_box_10 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (82141841/156250000 : ℝ)*x 0 + (5417194523/10000000000 : ℝ)*x 1 + (-1751550187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82141841/156250000 : ℝ)^4631 ≤ (43799167586873/100000000000000 : ℝ)^3607 := by
    have hnat : (82141841 : ℕ)^4631*100000000000000^3607 ≤ 43799167586873^3607*156250000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82141841 156250000 43799167586873 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5417194523/10000000000 : ℝ)^4631 ≤ (45519240437719/100000000000000 : ℝ)^3607 := by
    have hnat : (5417194523 : ℕ)^4631*100000000000000^3607 ≤ 45519240437719^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417194523 10000000000 45519240437719 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1751550187/10000000000 : ℝ)^4631 ≤ (1068159196403/10000000000000 : ℝ)^3607 := by
    have hnat : (1751550187 : ℕ)^4631*10000000000000^3607 ≤ 1068159196403^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1751550187 10000000000 1068159196403 10000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(82141841/156250000 : ℝ), (5417194523/10000000000 : ℝ), (-1751550187/10000000000 : ℝ)] ![(43799167586873/100000000000000 : ℝ), (45519240437719/100000000000000 : ℝ), (1068159196403/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(82141841/156250000 : ℝ)|^4631 ≤ (43799167586873/100000000000000 : ℝ)^3607
        have hw : |(82141841/156250000 : ℝ)|=(82141841/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5417194523/10000000000 : ℝ)|^4631 ≤ (45519240437719/100000000000000 : ℝ)^3607
        have hw : |(5417194523/10000000000 : ℝ)|=(5417194523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1751550187/10000000000 : ℝ)|^4631 ≤ (1068159196403/10000000000000 : ℝ)^3607
        have hw : |(-1751550187/10000000000 : ℝ)|=(1751550187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_box_11 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4498453541/10000000000 : ℝ)*x 0 + (4124078851/10000000000 : ℝ)*x 1 + (4124078783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4498453541/10000000000 : ℝ)^4631 ≤ (35856716631919/100000000000000 : ℝ)^3607 := by
    have hnat : (4498453541 : ℕ)^4631*100000000000000^3607 ≤ 35856716631919^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498453541 10000000000 35856716631919 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4124078851/10000000000 : ℝ)^4631 ≤ (400895525241/1250000000000 : ℝ)^3607 := by
    have hnat : (4124078851 : ℕ)^4631*1250000000000^3607 ≤ 400895525241^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4124078851 10000000000 400895525241 1250000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4124078783/10000000000 : ℝ)^4631 ≤ (1603582067017/5000000000000 : ℝ)^3607 := by
    have hnat : (4124078783 : ℕ)^4631*5000000000000^3607 ≤ 1603582067017^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4124078783 10000000000 1603582067017 5000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4498453541/10000000000 : ℝ), (4124078851/10000000000 : ℝ), (4124078783/10000000000 : ℝ)] ![(35856716631919/100000000000000 : ℝ), (400895525241/1250000000000 : ℝ), (1603582067017/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4498453541/10000000000 : ℝ)|^4631 ≤ (35856716631919/100000000000000 : ℝ)^3607
        have hw : |(4498453541/10000000000 : ℝ)|=(4498453541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4124078851/10000000000 : ℝ)|^4631 ≤ (400895525241/1250000000000 : ℝ)^3607
        have hw : |(4124078851/10000000000 : ℝ)|=(4124078851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4124078783/10000000000 : ℝ)|^4631 ≤ (1603582067017/5000000000000 : ℝ)^3607
        have hw : |(4124078783/10000000000 : ℝ)|=(4124078783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_box_12 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-836421607/5000000000 : ℝ)*x 0 + (2750321191/5000000000 : ℝ)*x 1 + (5229952391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (836421607/5000000000 : ℝ)^4631 ≤ (5034659024093/50000000000000 : ℝ)^3607 := by
    have hnat : (836421607 : ℕ)^4631*50000000000000^3607 ≤ 5034659024093^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      836421607 5000000000 5034659024093 50000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2750321191/5000000000 : ℝ)^4631 ≤ (23210727188779/50000000000000 : ℝ)^3607 := by
    have hnat : (2750321191 : ℕ)^4631*50000000000000^3607 ≤ 23210727188779^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2750321191 5000000000 23210727188779 50000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5229952391/10000000000 : ℝ)^4631 ≤ (21754613779523/50000000000000 : ℝ)^3607 := by
    have hnat : (5229952391 : ℕ)^4631*50000000000000^3607 ≤ 21754613779523^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229952391 10000000000 21754613779523 50000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-836421607/5000000000 : ℝ), (2750321191/5000000000 : ℝ), (5229952391/10000000000 : ℝ)] ![(5034659024093/50000000000000 : ℝ), (23210727188779/50000000000000 : ℝ), (21754613779523/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-836421607/5000000000 : ℝ)|^4631 ≤ (5034659024093/50000000000000 : ℝ)^3607
        have hw : |(-836421607/5000000000 : ℝ)|=(836421607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2750321191/5000000000 : ℝ)|^4631 ≤ (23210727188779/50000000000000 : ℝ)^3607
        have hw : |(2750321191/5000000000 : ℝ)|=(2750321191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5229952391/10000000000 : ℝ)|^4631 ≤ (21754613779523/50000000000000 : ℝ)^3607
        have hw : |(5229952391/10000000000 : ℝ)|=(5229952391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_box_13 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5386903421/10000000000 : ℝ)*x 0 + (-365958909/2000000000 : ℝ)*x 1 + (2614976077/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5386903421/10000000000 : ℝ)^4631 ≤ (9038542704791/20000000000000 : ℝ)^3607 := by
    have hnat : (5386903421 : ℕ)^4631*20000000000000^3607 ≤ 9038542704791^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386903421 10000000000 9038542704791 20000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (365958909/2000000000 : ℝ)^4631 ≤ (11298061441561/100000000000000 : ℝ)^3607 := by
    have hnat : (365958909 : ℕ)^4631*100000000000000^3607 ≤ 11298061441561^3607*2000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      365958909 2000000000 11298061441561 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2614976077/5000000000 : ℝ)^4631 ≤ (43509225027647/100000000000000 : ℝ)^3607 := by
    have hnat : (2614976077 : ℕ)^4631*100000000000000^3607 ≤ 43509225027647^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614976077 5000000000 43509225027647 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5386903421/10000000000 : ℝ), (-365958909/2000000000 : ℝ), (2614976077/5000000000 : ℝ)] ![(9038542704791/20000000000000 : ℝ), (11298061441561/100000000000000 : ℝ), (43509225027647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5386903421/10000000000 : ℝ)|^4631 ≤ (9038542704791/20000000000000 : ℝ)^3607
        have hw : |(5386903421/10000000000 : ℝ)|=(5386903421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-365958909/2000000000 : ℝ)|^4631 ≤ (11298061441561/100000000000000 : ℝ)^3607
        have hw : |(-365958909/2000000000 : ℝ)|=(365958909/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2614976077/5000000000 : ℝ)|^4631 ≤ (43509225027647/100000000000000 : ℝ)^3607
        have hw : |(2614976077/5000000000 : ℝ)|=(2614976077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_box_14 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (215476129/400000000 : ℝ)*x 0 + (2614976157/5000000000 : ℝ)*x 1 + (-365958919/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215476129/400000000 : ℝ)^4631 ≤ (4519271141283/10000000000000 : ℝ)^3607 := by
    have hnat : (215476129 : ℕ)^4631*10000000000000^3607 ≤ 4519271141283^3607*400000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215476129 400000000 4519271141283 10000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2614976157/5000000000 : ℝ)^4631 ≤ (1359663335519/3125000000000 : ℝ)^3607 := by
    have hnat : (2614976157 : ℕ)^4631*3125000000000^3607 ≤ 1359663335519^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614976157 5000000000 1359663335519 3125000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (365958919/2000000000 : ℝ)^4631 ≤ (11298061837931/100000000000000 : ℝ)^3607 := by
    have hnat : (365958919 : ℕ)^4631*100000000000000^3607 ≤ 11298061837931^3607*2000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      365958919 2000000000 11298061837931 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215476129/400000000 : ℝ), (2614976157/5000000000 : ℝ), (-365958919/2000000000 : ℝ)] ![(4519271141283/10000000000000 : ℝ), (1359663335519/3125000000000 : ℝ), (11298061837931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215476129/400000000 : ℝ)|^4631 ≤ (4519271141283/10000000000000 : ℝ)^3607
        have hw : |(215476129/400000000 : ℝ)|=(215476129/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2614976157/5000000000 : ℝ)|^4631 ≤ (1359663335519/3125000000000 : ℝ)^3607
        have hw : |(2614976157/5000000000 : ℝ)|=(2614976157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-365958919/2000000000 : ℝ)|^4631 ≤ (11298061837931/100000000000000 : ℝ)^3607
        have hw : |(-365958919/2000000000 : ℝ)|=(365958919/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_box_15 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1000110111/2500000000 : ℝ)*x 0 + (2186539213/5000000000 : ℝ)*x 1 + (1093269427/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1000110111/2500000000 : ℝ)^4631 ≤ (6168495091859/20000000000000 : ℝ)^3607 := by
    have hnat : (1000110111 : ℕ)^4631*20000000000000^3607 ≤ 6168495091859^3607*2500000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000110111 2500000000 6168495091859 20000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2186539213/5000000000 : ℝ)^4631 ≤ (4322345738293/12500000000000 : ℝ)^3607 := by
    have hnat : (2186539213 : ℕ)^4631*12500000000000^3607 ≤ 4322345738293^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186539213 5000000000 4322345738293 12500000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1093269427/2500000000 : ℝ)^4631 ≤ (34578758617221/100000000000000 : ℝ)^3607 := by
    have hnat : (1093269427 : ℕ)^4631*100000000000000^3607 ≤ 34578758617221^3607*2500000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093269427 2500000000 34578758617221 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1000110111/2500000000 : ℝ), (2186539213/5000000000 : ℝ), (1093269427/2500000000 : ℝ)] ![(6168495091859/20000000000000 : ℝ), (4322345738293/12500000000000 : ℝ), (34578758617221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1000110111/2500000000 : ℝ)|^4631 ≤ (6168495091859/20000000000000 : ℝ)^3607
        have hw : |(1000110111/2500000000 : ℝ)|=(1000110111/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2186539213/5000000000 : ℝ)|^4631 ≤ (4322345738293/12500000000000 : ℝ)^3607
        have hw : |(2186539213/5000000000 : ℝ)|=(2186539213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1093269427/2500000000 : ℝ)|^4631 ≤ (34578758617221/100000000000000 : ℝ)^3607
        have hw : |(1093269427/2500000000 : ℝ)|=(1093269427/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1567_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41946731/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1389/12500 : ℝ)*pair X i i ≤ pair X i h) :
    -(63823/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(7361/12500 : ℝ) ∧ (8089/10000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (21587/25000 : ℝ) := by
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
  have lower0 : (1389/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1389/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1389/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1389/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1389/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1389/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1389/12500 : ℝ) ^ (4629/1024 : ℝ) ≤ (4858434290046281/100000000000000000000 : ℝ) := by
    have hpowers : (1389/12500 : ℝ)^4629 ≤ (4858434290046281/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1389 : ℕ)^4629*100000000000000000000^1024 ≤ 4858434290046281^1024*12500^4629 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1389 12500 4858434290046281 100000000000000000000 4629 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1389/12500 : ℝ)) (X := (4858434290046281/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4629 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3097/20000 : ℝ) ^ (4629/1024 : ℝ) ≤ (21776460637976013/100000000000000000000 : ℝ) := by
    have hpowers : (3097/20000 : ℝ)^4629 ≤ (21776460637976013/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3097 : ℕ)^4629*100000000000000000000^1024 ≤ 21776460637976013^1024*20000^4629 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3097 20000 21776460637976013 100000000000000000000 4629 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3097/20000 : ℝ)) (X := (21776460637976013/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4629 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004858434290046281/50000000000000000000 : ℝ) ≤ (10000214942686731/10000000000000000 : ℝ) ^ (4629/1024 : ℝ) := by
    have hpowers : (50004858434290046281/50000000000000000000 : ℝ)^1024 ≤ (10000214942686731/10000000000000000 : ℝ)^4629 := by
      have hnat : (50004858434290046281 : ℕ)^1024*10000000000000000^4629 ≤ 10000214942686731^4629*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004858434290046281 50000000000000000000 10000214942686731 10000000000000000 1024 4629 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000214942686731/10000000000000000 : ℝ)) (X := (50004858434290046281/50000000000000000000 : ℝ)) (by norm_num) 4629 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50013317447464011147/50000000000000000000 : ℝ) ≤ (10000589140292343/10000000000000000 : ℝ) ^ (4629/1024 : ℝ) := by
    have hpowers : (50013317447464011147/50000000000000000000 : ℝ)^1024 ≤ (10000589140292343/10000000000000000 : ℝ)^4629 := by
      have hnat : (50013317447464011147 : ℕ)^1024*10000000000000000^4629 ≤ 10000589140292343^4629*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013317447464011147 50000000000000000000 10000589140292343 10000000000000000 1024 4629 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000589140292343/10000000000000000 : ℝ)) (X := (50013317447464011147/50000000000000000000 : ℝ)) (by norm_num) 4629 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50021776460637976013/50000000000000000000 : ℝ) ≤ (2000192667579591/2000000000000000 : ℝ) ^ (4629/1024 : ℝ) := by
    have hpowers : (50021776460637976013/50000000000000000000 : ℝ)^1024 ≤ (2000192667579591/2000000000000000 : ℝ)^4629 := by
      have hnat : (50021776460637976013 : ℕ)^1024*2000000000000000^4629 ≤ 2000192667579591^4629*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021776460637976013 50000000000000000000 2000192667579591 2000000000000000 1024 4629 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000192667579591/2000000000000000 : ℝ)) (X := (50021776460637976013/50000000000000000000 : ℝ)) (by norm_num) 4629 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4858434290046281/100000000000000000000 : ℝ) ≤ ((1748904951071278143/1749200000000000000 : ℝ)+2*(93549401403/109325000000000 : ℝ)*(1389/12500 : ℝ))^(4629/1024 : ℝ) := by
    rw [show (1748904951071278143/1749200000000000000 : ℝ)+2*(93549401403/109325000000000 : ℝ)*(1389/12500 : ℝ)=(10000214942686731/10000000000000000 : ℝ) by norm_num, show 1+2*(4858434290046281/100000000000000000000 : ℝ)=(50004858434290046281/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(21776460637976013/100000000000000000000 : ℝ)+(4858434290046281/100000000000000000000 : ℝ) ≤ ((1748904951071278143/1749200000000000000 : ℝ)+(93549401403/109325000000000 : ℝ)*((3097/20000 : ℝ)+(1389/12500 : ℝ)))^(4629/1024 : ℝ) := by
    rw [show (1748904951071278143/1749200000000000000 : ℝ)+(93549401403/109325000000000 : ℝ)*((3097/20000 : ℝ)+(1389/12500 : ℝ))=(10000589140292343/10000000000000000 : ℝ) by norm_num, show 1+(21776460637976013/100000000000000000000 : ℝ)+(4858434290046281/100000000000000000000 : ℝ)=(50013317447464011147/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(21776460637976013/100000000000000000000 : ℝ) ≤ ((1748904951071278143/1749200000000000000 : ℝ)+2*(93549401403/109325000000000 : ℝ)*(3097/20000 : ℝ))^(4629/1024 : ℝ) := by
    rw [show (1748904951071278143/1749200000000000000 : ℝ)+2*(93549401403/109325000000000 : ℝ)*(3097/20000 : ℝ)=(2000192667579591/2000000000000000 : ℝ) by norm_num, show 1+2*(21776460637976013/100000000000000000000 : ℝ)=(50021776460637976013/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1748904951071278143/1749200000000000000 : ℝ)*(X 1 0+X 2 0)+(93549401403/109325000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4629/1024 : ℝ)) (lo := (1389/12500 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (1748904951071278143/1749200000000000000 : ℝ)) (alpha := (93549401403/109325000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1748904951071278143/1749200000000000000 : ℝ)*(X 0 1+X 2 1)+(93549401403/109325000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4629/1024 : ℝ)) (lo := (1389/12500 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (1748904951071278143/1749200000000000000 : ℝ)) (alpha := (93549401403/109325000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1748904951071278143/1749200000000000000 : ℝ)*(X 0 2+X 1 2)+(93549401403/109325000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4629/1024 : ℝ)) (lo := (1389/12500 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (1748904951071278143/1749200000000000000 : ℝ)) (alpha := (93549401403/109325000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-792716157/5000000000 : ℝ)*X 0 0+(5396914237/10000000000 : ℝ)*X 0 1+(21081693/39062500 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5271142471/10000000000 : ℝ)*X 1 0+(-1760251097/10000000000 : ℝ)*X 1 1+(2698456933/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5271142957/10000000000 : ℝ)*X 2 0+(5396913829/10000000000 : ℝ)*X 2 1+(-352050097/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4445627697/10000000000 : ℝ)*X 0 0+(4151080569/10000000000 : ℝ)*X 0 1+(830216317/2000000000 : ℝ)*X 0 2+(4445627697/10000000000 : ℝ)*X 1 0+(4151080569/10000000000 : ℝ)*X 1 1+(830216317/2000000000 : ℝ)*X 1 2+(4445627697/10000000000 : ℝ)*X 2 0+(4151080569/10000000000 : ℝ)*X 2 1+(830216317/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-49985069/250000000 : ℝ)*X 0 0+(2622500799/5000000000 : ℝ)*X 0 1+(1311250543/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2688233937/5000000000 : ℝ)*X 1 0+(-91184053/500000000 : ℝ)*X 1 1+(2622500937/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1075293579/2000000000 : ℝ)*X 2 0+(5245002283/10000000000 : ℝ)*X 2 1+(-1823680479/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4041354181/10000000000 : ℝ)*X 0 0+(4353090371/10000000000 : ℝ)*X 0 1+(2176544897/5000000000 : ℝ)*X 0 2+(4041354181/10000000000 : ℝ)*X 1 0+(4353090371/10000000000 : ℝ)*X 1 1+(2176544897/5000000000 : ℝ)*X 1 2+(4041354181/10000000000 : ℝ)*X 2 0+(4353090371/10000000000 : ℝ)*X 2 1+(2176544897/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-477916717/2500000000 : ℝ)*X 0 0+(2569002073/5000000000 : ℝ)*X 0 1+(5417194197/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2628538959/5000000000 : ℝ)*X 1 0+(-1751550169/10000000000 : ℝ)*X 1 1+(2708597221/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((82141841/156250000 : ℝ)*X 2 0+(5417194523/10000000000 : ℝ)*X 2 1+(-1751550187/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4498453541/10000000000 : ℝ)*X 0 0+(4124078851/10000000000 : ℝ)*X 0 1+(4124078783/10000000000 : ℝ)*X 0 2+(4498453541/10000000000 : ℝ)*X 1 0+(4124078851/10000000000 : ℝ)*X 1 1+(4124078783/10000000000 : ℝ)*X 1 2+(4498453541/10000000000 : ℝ)*X 2 0+(4124078851/10000000000 : ℝ)*X 2 1+(4124078783/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-836421607/5000000000 : ℝ)*X 0 0+(2750321191/5000000000 : ℝ)*X 0 1+(5229952391/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5386903421/10000000000 : ℝ)*X 1 0+(-365958909/2000000000 : ℝ)*X 1 1+(2614976077/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((215476129/400000000 : ℝ)*X 2 0+(2614976157/5000000000 : ℝ)*X 2 1+(-365958919/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1000110111/2500000000 : ℝ)*X 0 0+(2186539213/5000000000 : ℝ)*X 0 1+(1093269427/2500000000 : ℝ)*X 0 2+(1000110111/2500000000 : ℝ)*X 1 0+(2186539213/5000000000 : ℝ)*X 1 1+(1093269427/2500000000 : ℝ)*X 1 2+(1000110111/2500000000 : ℝ)*X 2 0+(2186539213/5000000000 : ℝ)*X 2 1+(1093269427/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-63823/100000 : ℝ) ≤ (-223271012834861355947313576231/349840000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24170033/100000000000000 : ℝ)*(lower0) + (76396321/50000000000000 : ℝ)*(lower2) + (2402219/5000000000000 : ℝ)*(lower3) + (18427622683219/800000000000 : ℝ)*(major0) + (18427622683219/800000000000 : ℝ)*(major1) + (18427622683219/800000000000 : ℝ)*(major2) + (3086776649/100000000000000 : ℝ)*(sp1) + (813833463794329/25000000000000 : ℝ)*(sp4) + (813833036419301/25000000000000 : ℝ)*(sp5) + (162761326009327/5000000000000 : ℝ)*(sp6) + (13728318044369/1000000000000 : ℝ)*(sp7) + (688638269/50000000000000 : ℝ)*(sp12) + (54356133657/50000000000000 : ℝ)*(sp14) + (2452997351/20000000000000 : ℝ)*(sp15) + (274568813884731/20000000000000 : ℝ)*(f.failure) + (1627667616226927/50000000000000 : ℝ)*(f.sum) + (955647436107/546625000000000000000000000 : ℝ)*base65 + (1228668486183277/1399360000000000000000000000000 : ℝ)*base67 + (2870150481441683/1399360000000000000000000000000 : ℝ)*base70 + (11658686184035117/1399360000000000000000000000000 : ℝ)*base71 + (9108021879001/4373000000000000000000000000 : ℝ)*base74 + (3614815938635117/1399360000000000000000000000000 : ℝ)*base75 + (5704805437899117/1399360000000000000000000000000 : ℝ)*base77 + (5040034045979757/1399360000000000000000000000000 : ℝ)*base79 + (22356070687/17492000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1264361/500000000000000000000 : ℝ)*base89 + (1264361/500000000000000000000 : ℝ)*base91 + (1264361/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (7361/12500 : ℝ) ≤ (51505772865557728311679552521327/87460000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (278239289/100000000000000 : ℝ)*(lower1) + (6080583/25000000000000 : ℝ)*(lower2) + (15653661/6250000000000 : ℝ)*(upper4) + (2383485098109079/100000000000000 : ℝ)*(major0) + (2383485098109079/100000000000000 : ℝ)*(major1) + (2383485098109079/100000000000000 : ℝ)*(major2) + (166339548152519/5000000000000 : ℝ)*(sp0) + (1663364448848877/50000000000000 : ℝ)*(sp1) + (3326795534826669/100000000000000 : ℝ)*(sp2) + (88783608182343/6250000000000 : ℝ)*(sp3) + (162295877/10000000000000 : ℝ)*(sp6) + (2543447077/50000000000000 : ℝ)*(sp7) + (3097367529/50000000000000 : ℝ)*(sp8) + (17065021921/25000000000000 : ℝ)*(sp9) + (710271408905821/50000000000000 : ℝ)*(f.failure) + (1663398578892719/50000000000000 : ℝ)*(f.sum) + (109903612980529/10932500000000000000000000000 : ℝ)*base65 + (1458919104104672297/174920000000000000000000000000000 : ℝ)*base67 + (125051970415712297/174920000000000000000000000000000 : ℝ)*base69 + (689690435972432297/174920000000000000000000000000000 : ℝ)*base71 + (14684447780517/5466250000000000000000000000 : ℝ)*base73 + (1929254545331792297/174920000000000000000000000000000 : ℝ)*base75 + (1249795236984392297/174920000000000000000000000000000 : ℝ)*base77 + (275905935438312297/174920000000000000000000000000000 : ℝ)*base79 + (167556389216583/21865000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (9678849/1250000000000000000000 : ℝ)*base90 + (9678849/1250000000000000000000 : ℝ)*base92 + (9678849/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (8089/10000 : ℝ) ≤ (1105447298554984279999287031053/1366562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1322027/10000000000000 : ℝ)*(lower1) + (573201/50000000000000 : ℝ)*(upper2) + (25097451/50000000000000 : ℝ)*(lower5) + (80322756819039/3125000000000 : ℝ)*(major0) + (80322756819039/3125000000000 : ℝ)*(major1) + (80322756819039/3125000000000 : ℝ)*(major2) + (2081095057/50000000000000 : ℝ)*(sp0) + (40913475443/100000000000000 : ℝ)*(sp1) + (64034529717/100000000000000 : ℝ)*(sp2) + (5431497077/20000000000000 : ℝ)*(sp3) + (1790893946723093/50000000000000 : ℝ)*(sp8) + (3581751142160857/100000000000000 : ℝ)*(sp9) + (3581728021106583/100000000000000 : ℝ)*(sp10) + (765936519433387/50000000000000 : ℝ)*(sp11) + (1531900196352159/100000000000000 : ℝ)*(f.failure) + (35817920556363/1000000000000 : ℝ)*(f.sum) + (56463773582499/21865000000000000000000000000 : ℝ)*base66 + (21073012116249673/5466250000000000000000000000000 : ℝ)*base68 + (3259058234354673/5466250000000000000000000000000 : ℝ)*base70 + (41512109133394077/5466250000000000000000000000000 : ℝ)*base71 + (30575375253999/21865000000000000000000000000 : ℝ)*base74 + (30398542771472173/5466250000000000000000000000000 : ℝ)*base76 + (41238943227286577/5466250000000000000000000000000 : ℝ)*base77 + (19829227757179673/5466250000000000000000000000000 : ℝ)*base80 + (65391289509589/21865000000000000000000000000 : ℝ)*base82 + (5157771/2500000000000000000000 : ℝ)*base90 + (5157771/2500000000000000000000 : ℝ)*base92 + (5157771/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-21587/25000 : ℝ) ≤ (-18879415114752698707729710799203/21865000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11737849/25000000000000 : ℝ)*(upper1) + (172494663/100000000000000 : ℝ)*(upper3) + (46842509/100000000000000 : ℝ)*(upper5) + (2610735597088771/100000000000000 : ℝ)*(major0) + (2610735597088771/100000000000000 : ℝ)*(major1) + (652683899272193/25000000000000 : ℝ)*(major2) + (6066184873/100000000000000 : ℝ)*(sp4) + (147661848581/100000000000000 : ℝ)*(sp5) + (9784731257/12500000000000 : ℝ)*(sp6) + (16332932423/100000000000000 : ℝ)*(sp7) + (1847132083106927/50000000000000 : ℝ)*(sp12) + (1847061285275073/50000000000000 : ℝ)*(sp13) + (369419195454867/10000000000000 : ℝ)*(sp14) + (388991604697971/25000000000000 : ℝ)*(sp15) + (1555982751724307/100000000000000 : ℝ)*(f.failure) + (3694270232398727/100000000000000 : ℝ)*(f.sum) + (11099708140763/21865000000000000000000000000 : ℝ)*base65 + (956485883004191747/174920000000000000000000000000000 : ℝ)*base68 + (634066550537490401/43730000000000000000000000000000 : ℝ)*base70 + (159956618202591747/174920000000000000000000000000000 : ℝ)*base72 + (87971334176597/21865000000000000000000000000 : ℝ)*base74 + (935969121413330401/43730000000000000000000000000000 : ℝ)*base76 + (1060891642753760253/174920000000000000000000000000000 : ℝ)*base77 + (597508654059040253/174920000000000000000000000000000 : ℝ)*base79 + (110822741950881/2733125000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (16890417/2500000000000000000000 : ℝ)*base89 + (16890417/2500000000000000000000 : ℝ)*base91 + (8109583/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1567_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41946731/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1389/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63823/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(7361/12500 : ℝ) else (8089/10000 : ℝ) ≤ X j i ∧ X j i ≤ (21587/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1567_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1567_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41946731/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11111/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63823/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(7361/12500 : ℝ) else (8089/10000 : ℝ) ≤ X j i ∧ X j i ≤ (21587/25000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1567_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1567_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41946731/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11111/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63823/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(7361/12500 : ℝ) else (8089/10000 : ℝ) ≤ X j i ∧ X j i ≤ (21587/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1567_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
