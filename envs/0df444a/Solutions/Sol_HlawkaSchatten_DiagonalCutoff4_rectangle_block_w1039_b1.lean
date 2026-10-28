-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1039_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:46:01.635108+00:00
-- url     : https://prove2.me/submissions/4916193c-8386-49da-b249-51e1e3b4295c

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
theorem support_rectangle_w1039_s3_0 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-138250721/625000000 : ℝ)*x 0 + (2720367209/5000000000 : ℝ)*x 1 + (1044276749/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (138250721/625000000 : ℝ)^1029 ≤ (3355335077923/25000000000000 : ℝ)^773 := by
    have hnat : (138250721 : ℕ)^1029*25000000000000^773 ≤ 3355335077923^773*625000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138250721 625000000 3355335077923 25000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2720367209/5000000000 : ℝ)^1029 ≤ (44474729825479/100000000000000 : ℝ)^773 := by
    have hnat : (2720367209 : ℕ)^1029*100000000000000^773 ≤ 44474729825479^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2720367209 5000000000 44474729825479 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1044276749/2000000000 : ℝ)^1029 ≤ (21051964921277/50000000000000 : ℝ)^773 := by
    have hnat : (1044276749 : ℕ)^1029*50000000000000^773 ≤ 21051964921277^773*2000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044276749 2000000000 21051964921277 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-138250721/625000000 : ℝ), (2720367209/5000000000 : ℝ), (1044276749/2000000000 : ℝ)] ![(3355335077923/25000000000000 : ℝ), (44474729825479/100000000000000 : ℝ), (21051964921277/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-138250721/625000000 : ℝ)|^1029 ≤ (3355335077923/25000000000000 : ℝ)^773
        have hw : |(-138250721/625000000 : ℝ)|=(138250721/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2720367209/5000000000 : ℝ)|^1029 ≤ (44474729825479/100000000000000 : ℝ)^773
        have hw : |(2720367209/5000000000 : ℝ)|=(2720367209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1044276749/2000000000 : ℝ)|^1029 ≤ (21051964921277/50000000000000 : ℝ)^773
        have hw : |(1044276749/2000000000 : ℝ)|=(1044276749/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s3_1 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2678195837/5000000000 : ℝ)*x 0 + (-290551701/1250000000 : ℝ)*x 1 + (5221384093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2678195837/5000000000 : ℝ)^1029 ≤ (43559312228169/100000000000000 : ℝ)^773 := by
    have hnat : (2678195837 : ℕ)^1029*100000000000000^773 ≤ 43559312228169^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2678195837 5000000000 43559312228169 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (290551701/1250000000 : ℝ)^1029 ≤ (14336754169451/100000000000000 : ℝ)^773 := by
    have hnat : (290551701 : ℕ)^1029*100000000000000^773 ≤ 14336754169451^773*1250000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      290551701 1250000000 14336754169451 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5221384093/10000000000 : ℝ)^1029 ≤ (42103933578083/100000000000000 : ℝ)^773 := by
    have hnat : (5221384093 : ℕ)^1029*100000000000000^773 ≤ 42103933578083^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5221384093 10000000000 42103933578083 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2678195837/5000000000 : ℝ), (-290551701/1250000000 : ℝ), (5221384093/10000000000 : ℝ)] ![(43559312228169/100000000000000 : ℝ), (14336754169451/100000000000000 : ℝ), (42103933578083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2678195837/5000000000 : ℝ)|^1029 ≤ (43559312228169/100000000000000 : ℝ)^773
        have hw : |(2678195837/5000000000 : ℝ)|=(2678195837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-290551701/1250000000 : ℝ)|^1029 ≤ (14336754169451/100000000000000 : ℝ)^773
        have hw : |(-290551701/1250000000 : ℝ)|=(290551701/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5221384093/10000000000 : ℝ)|^1029 ≤ (42103933578083/100000000000000 : ℝ)^773
        have hw : |(5221384093/10000000000 : ℝ)|=(5221384093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s3_2 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5356391793/10000000000 : ℝ)*x 0 + (652673049/1250000000 : ℝ)*x 1 + (-2324413061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356391793/10000000000 : ℝ)^1029 ≤ (43559313516393/100000000000000 : ℝ)^773 := by
    have hnat : (5356391793 : ℕ)^1029*100000000000000^773 ≤ 43559313516393^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356391793 10000000000 43559313516393 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (652673049/1250000000 : ℝ)^1029 ≤ (42103936787633/100000000000000 : ℝ)^773 := by
    have hnat : (652673049 : ℕ)^1029*100000000000000^773 ≤ 42103936787633^773*1250000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652673049 1250000000 42103936787633 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2324413061/10000000000 : ℝ)^1029 ≤ (1433674967827/10000000000000 : ℝ)^773 := by
    have hnat : (2324413061 : ℕ)^1029*10000000000000^773 ≤ 1433674967827^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2324413061 10000000000 1433674967827 10000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356391793/10000000000 : ℝ), (652673049/1250000000 : ℝ), (-2324413061/10000000000 : ℝ)] ![(43559313516393/100000000000000 : ℝ), (42103936787633/100000000000000 : ℝ), (1433674967827/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356391793/10000000000 : ℝ)|^1029 ≤ (43559313516393/100000000000000 : ℝ)^773
        have hw : |(5356391793/10000000000 : ℝ)|=(5356391793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(652673049/1250000000 : ℝ)|^1029 ≤ (42103936787633/100000000000000 : ℝ)^773
        have hw : |(652673049/1250000000 : ℝ)|=(652673049/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2324413061/10000000000 : ℝ)|^1029 ≤ (1433674967827/10000000000000 : ℝ)^773
        have hw : |(-2324413061/10000000000 : ℝ)|=(2324413061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s3_3 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4376366783/10000000000 : ℝ)*x 0 + (2083943299/5000000000 : ℝ)*x 1 + (1148869519/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4376366783/10000000000 : ℝ)^1029 ≤ (16642890293677/50000000000000 : ℝ)^773 := by
    have hnat : (4376366783 : ℕ)^1029*50000000000000^773 ≤ 16642890293677^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4376366783 10000000000 16642890293677 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2083943299/5000000000 : ℝ)^1029 ≤ (1949488642063/6250000000000 : ℝ)^773 := by
    have hnat : (2083943299 : ℕ)^1029*6250000000000^773 ≤ 1949488642063^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083943299 5000000000 1949488642063 6250000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1148869519/2500000000 : ℝ)^1029 ≤ (35522401123663/100000000000000 : ℝ)^773 := by
    have hnat : (1148869519 : ℕ)^1029*100000000000000^773 ≤ 35522401123663^773*2500000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1148869519 2500000000 35522401123663 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4376366783/10000000000 : ℝ), (2083943299/5000000000 : ℝ), (1148869519/2500000000 : ℝ)] ![(16642890293677/50000000000000 : ℝ), (1949488642063/6250000000000 : ℝ), (35522401123663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4376366783/10000000000 : ℝ)|^1029 ≤ (16642890293677/50000000000000 : ℝ)^773
        have hw : |(4376366783/10000000000 : ℝ)|=(4376366783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2083943299/5000000000 : ℝ)|^1029 ≤ (1949488642063/6250000000000 : ℝ)^773
        have hw : |(2083943299/5000000000 : ℝ)|=(2083943299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1148869519/2500000000 : ℝ)|^1029 ≤ (35522401123663/100000000000000 : ℝ)^773
        have hw : |(1148869519/2500000000 : ℝ)|=(1148869519/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s3_4 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-88481437/400000000 : ℝ)*x 0 + (5222300897/10000000000 : ℝ)*x 1 + (2719905763/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (88481437/400000000 : ℝ)^1029 ≤ (6710768649709/50000000000000 : ℝ)^773 := by
    have hnat : (88481437 : ℕ)^1029*50000000000000^773 ≤ 6710768649709^773*400000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88481437 400000000 6710768649709 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5222300897/10000000000 : ℝ)^1029 ≤ (21056887547427/50000000000000 : ℝ)^773 := by
    have hnat : (5222300897 : ℕ)^1029*50000000000000^773 ≤ 21056887547427^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5222300897 10000000000 21056887547427 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2719905763/5000000000 : ℝ)^1029 ≤ (4446468759107/10000000000000 : ℝ)^773 := by
    have hnat : (2719905763 : ℕ)^1029*10000000000000^773 ≤ 4446468759107^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719905763 5000000000 4446468759107 10000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-88481437/400000000 : ℝ), (5222300897/10000000000 : ℝ), (2719905763/5000000000 : ℝ)] ![(6710768649709/50000000000000 : ℝ), (21056887547427/50000000000000 : ℝ), (4446468759107/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-88481437/400000000 : ℝ)|^1029 ≤ (6710768649709/50000000000000 : ℝ)^773
        have hw : |(-88481437/400000000 : ℝ)|=(88481437/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5222300897/10000000000 : ℝ)|^1029 ≤ (21056887547427/50000000000000 : ℝ)^773
        have hw : |(5222300897/10000000000 : ℝ)|=(5222300897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2719905763/5000000000 : ℝ)|^1029 ≤ (4446468759107/10000000000000 : ℝ)^773
        have hw : |(2719905763/5000000000 : ℝ)|=(2719905763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s3_5 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (165664229/312500000 : ℝ)*x 0 + (-2105986887/10000000000 : ℝ)*x 1 + (16999409/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165664229/312500000 : ℝ)^1029 ≤ (42963458095929/100000000000000 : ℝ)^773 := by
    have hnat : (165664229 : ℕ)^1029*100000000000000^773 ≤ 42963458095929^773*312500000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165664229 312500000 42963458095929 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2105986887/10000000000 : ℝ)^1029 ≤ (6285930665447/50000000000000 : ℝ)^773 := by
    have hnat : (2105986887 : ℕ)^1029*50000000000000^773 ≤ 6285930665447^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105986887 10000000000 6285930665447 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16999409/31250000 : ℝ)^1029 ≤ (44464680561969/100000000000000 : ℝ)^773 := by
    have hnat : (16999409 : ℕ)^1029*100000000000000^773 ≤ 44464680561969^773*31250000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16999409 31250000 44464680561969 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165664229/312500000 : ℝ), (-2105986887/10000000000 : ℝ), (16999409/31250000 : ℝ)] ![(42963458095929/100000000000000 : ℝ), (6285930665447/50000000000000 : ℝ), (44464680561969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165664229/312500000 : ℝ)|^1029 ≤ (42963458095929/100000000000000 : ℝ)^773
        have hw : |(165664229/312500000 : ℝ)|=(165664229/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2105986887/10000000000 : ℝ)|^1029 ≤ (6285930665447/50000000000000 : ℝ)^773
        have hw : |(-2105986887/10000000000 : ℝ)|=(2105986887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(16999409/31250000 : ℝ)|^1029 ≤ (44464680561969/100000000000000 : ℝ)^773
        have hw : |(16999409/31250000 : ℝ)|=(16999409/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s3_6 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (662656867/1250000000 : ℝ)*x 0 + (2719905701/5000000000 : ℝ)*x 1 + (-131624169/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (662656867/1250000000 : ℝ)^1029 ≤ (42963453866883/100000000000000 : ℝ)^773 := by
    have hnat : (662656867 : ℕ)^1029*100000000000000^773 ≤ 42963453866883^773*1250000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662656867 1250000000 42963453866883 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2719905701/5000000000 : ℝ)^1029 ≤ (44464686241831/100000000000000 : ℝ)^773 := by
    have hnat : (2719905701 : ℕ)^1029*100000000000000^773 ≤ 44464686241831^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719905701 5000000000 44464686241831 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131624169/625000000 : ℝ)^1029 ≤ (196435310573/1562500000000 : ℝ)^773 := by
    have hnat : (131624169 : ℕ)^1029*1562500000000^773 ≤ 196435310573^773*625000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131624169 625000000 196435310573 1562500000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(662656867/1250000000 : ℝ), (2719905701/5000000000 : ℝ), (-131624169/625000000 : ℝ)] ![(42963453866883/100000000000000 : ℝ), (44464686241831/100000000000000 : ℝ), (196435310573/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(662656867/1250000000 : ℝ)|^1029 ≤ (42963453866883/100000000000000 : ℝ)^773
        have hw : |(662656867/1250000000 : ℝ)|=(662656867/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2719905701/5000000000 : ℝ)|^1029 ≤ (44464686241831/100000000000000 : ℝ)^773
        have hw : |(2719905701/5000000000 : ℝ)|=(2719905701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-131624169/625000000 : ℝ)|^1029 ≤ (196435310573/1562500000000 : ℝ)^773
        have hw : |(-131624169/625000000 : ℝ)|=(131624169/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s3_7 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4376413441/10000000000 : ℝ)*x 0 + (4593690371/10000000000 : ℝ)*x 1 + (1042421351/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4376413441/10000000000 : ℝ)^1029 ≤ (33286252985081/100000000000000 : ℝ)^773 := by
    have hnat : (4376413441 : ℕ)^1029*100000000000000^773 ≤ 33286252985081^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4376413441 10000000000 33286252985081 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4593690371/10000000000 : ℝ)^1029 ≤ (7100801431593/20000000000000 : ℝ)^773 := by
    have hnat : (4593690371 : ℕ)^1029*20000000000000^773 ≤ 7100801431593^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4593690371 10000000000 7100801431593 20000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1042421351/2500000000 : ℝ)^1029 ≤ (6241947968491/20000000000000 : ℝ)^773 := by
    have hnat : (1042421351 : ℕ)^1029*20000000000000^773 ≤ 6241947968491^773*2500000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042421351 2500000000 6241947968491 20000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4376413441/10000000000 : ℝ), (4593690371/10000000000 : ℝ), (1042421351/2500000000 : ℝ)] ![(33286252985081/100000000000000 : ℝ), (7100801431593/20000000000000 : ℝ), (6241947968491/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4376413441/10000000000 : ℝ)|^1029 ≤ (33286252985081/100000000000000 : ℝ)^773
        have hw : |(4376413441/10000000000 : ℝ)|=(4376413441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4593690371/10000000000 : ℝ)|^1029 ≤ (7100801431593/20000000000000 : ℝ)^773
        have hw : |(4593690371/10000000000 : ℝ)|=(4593690371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1042421351/2500000000 : ℝ)|^1029 ≤ (6241947968491/20000000000000 : ℝ)^773
        have hw : |(1042421351/2500000000 : ℝ)|=(1042421351/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1039_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147468077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1683/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8579/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2061/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7473/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1683/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8579/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1683/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8579/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1683/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8579/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1683/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8579/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1683/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8579/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1683/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8579/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8579/100000 : ℝ) ^ (8231/2048 : ℝ) ≤ (323084524723347/6250000000000000000 : ℝ) := by
    have hpowers : (8579/100000 : ℝ)^8231 ≤ (323084524723347/6250000000000000000 : ℝ)^2048 := by
      have hnat : (8579 : ℕ)^8231*6250000000000000000^2048 ≤ 323084524723347^2048*100000^8231 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8579 100000 323084524723347 6250000000000000000 8231 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8579/100000 : ℝ)) (X := (323084524723347/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1683/10000 : ℝ) ^ (8231/2048 : ℝ) ≤ (77553036700882499/100000000000000000000 : ℝ) := by
    have hpowers : (1683/10000 : ℝ)^8231 ≤ (77553036700882499/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1683 : ℕ)^8231*100000000000000000000^2048 ≤ 77553036700882499^2048*10000^8231 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1683 10000 77553036700882499 100000000000000000000 8231 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1683/10000 : ℝ)) (X := (77553036700882499/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125323084524723347/3125000000000000000 : ℝ) ≤ (2500064308240977/2500000000000000 : ℝ) ^ (8231/2048 : ℝ) := by
    have hpowers : (3125323084524723347/3125000000000000000 : ℝ)^2048 ≤ (2500064308240977/2500000000000000 : ℝ)^8231 := by
      have hnat : (3125323084524723347 : ℕ)^2048*2500000000000000^8231 ≤ 2500064308240977^8231*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125323084524723347 3125000000000000000 2500064308240977 2500000000000000 2048 8231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500064308240977/2500000000000000 : ℝ)) (X := (3125323084524723347/3125000000000000000 : ℝ)) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100082722389096456051/100000000000000000000 : ℝ) ≤ (2000411524337449/2000000000000000 : ℝ) ^ (8231/2048 : ℝ) := by
    have hpowers : (100082722389096456051/100000000000000000000 : ℝ)^2048 ≤ (2000411524337449/2000000000000000 : ℝ)^8231 := by
      have hnat : (100082722389096456051 : ℕ)^2048*2000000000000000^8231 ≤ 2000411524337449^8231*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100082722389096456051 100000000000000000000 2000411524337449 2000000000000000 2048 8231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000411524337449/2000000000000000 : ℝ)) (X := (100082722389096456051/100000000000000000000 : ℝ)) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50077553036700882499/50000000000000000000 : ℝ) ≤ (5001929005205291/5000000000000000 : ℝ) ^ (8231/2048 : ℝ) := by
    have hpowers : (50077553036700882499/50000000000000000000 : ℝ)^2048 ≤ (5001929005205291/5000000000000000 : ℝ)^8231 := by
      have hnat : (50077553036700882499 : ℕ)^2048*5000000000000000^8231 ≤ 5001929005205291^8231*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50077553036700882499 50000000000000000000 5001929005205291 5000000000000000 2048 8231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001929005205291/5000000000000000 : ℝ)) (X := (50077553036700882499/50000000000000000000 : ℝ)) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(323084524723347/6250000000000000000 : ℝ) ≤ ((41240615679735094331/41255000000000000000 : ℝ)+2*(1800388723337/825100000000000 : ℝ)*(8579/100000 : ℝ))^(8231/2048 : ℝ) := by
    rw [show (41240615679735094331/41255000000000000000 : ℝ)+2*(1800388723337/825100000000000 : ℝ)*(8579/100000 : ℝ)=(2500064308240977/2500000000000000 : ℝ) by norm_num, show 1+2*(323084524723347/6250000000000000000 : ℝ)=(3125323084524723347/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(77553036700882499/100000000000000000000 : ℝ)+(323084524723347/6250000000000000000 : ℝ) ≤ ((41240615679735094331/41255000000000000000 : ℝ)+(1800388723337/825100000000000 : ℝ)*((1683/10000 : ℝ)+(8579/100000 : ℝ)))^(8231/2048 : ℝ) := by
    rw [show (41240615679735094331/41255000000000000000 : ℝ)+(1800388723337/825100000000000 : ℝ)*((1683/10000 : ℝ)+(8579/100000 : ℝ))=(2000411524337449/2000000000000000 : ℝ) by norm_num, show 1+(77553036700882499/100000000000000000000 : ℝ)+(323084524723347/6250000000000000000 : ℝ)=(100082722389096456051/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(77553036700882499/100000000000000000000 : ℝ) ≤ ((41240615679735094331/41255000000000000000 : ℝ)+2*(1800388723337/825100000000000 : ℝ)*(1683/10000 : ℝ))^(8231/2048 : ℝ) := by
    rw [show (41240615679735094331/41255000000000000000 : ℝ)+2*(1800388723337/825100000000000 : ℝ)*(1683/10000 : ℝ)=(5001929005205291/5000000000000000 : ℝ) by norm_num, show 1+2*(77553036700882499/100000000000000000000 : ℝ)=(50077553036700882499/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (41240615679735094331/41255000000000000000 : ℝ)*(X 1 0+X 2 0)+(1800388723337/825100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8231/2048 : ℝ)) (lo := (8579/100000 : ℝ)) (hi := (1683/10000 : ℝ)) (c := (41240615679735094331/41255000000000000000 : ℝ)) (alpha := (1800388723337/825100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (41240615679735094331/41255000000000000000 : ℝ)*(X 0 1+X 2 1)+(1800388723337/825100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8231/2048 : ℝ)) (lo := (8579/100000 : ℝ)) (hi := (1683/10000 : ℝ)) (c := (41240615679735094331/41255000000000000000 : ℝ)) (alpha := (1800388723337/825100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (41240615679735094331/41255000000000000000 : ℝ)*(X 0 2+X 1 2)+(1800388723337/825100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8231/2048 : ℝ)) (lo := (8579/100000 : ℝ)) (hi := (1683/10000 : ℝ)) (c := (41240615679735094331/41255000000000000000 : ℝ)) (alpha := (1800388723337/825100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-138250721/625000000 : ℝ)*X 0 0+(2720367209/5000000000 : ℝ)*X 0 1+(1044276749/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2678195837/5000000000 : ℝ)*X 1 0+(-290551701/1250000000 : ℝ)*X 1 1+(5221384093/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5356391793/10000000000 : ℝ)*X 2 0+(652673049/1250000000 : ℝ)*X 2 1+(-2324413061/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4376366783/10000000000 : ℝ)*X 0 0+(2083943299/5000000000 : ℝ)*X 0 1+(1148869519/2500000000 : ℝ)*X 0 2+(4376366783/10000000000 : ℝ)*X 1 0+(2083943299/5000000000 : ℝ)*X 1 1+(1148869519/2500000000 : ℝ)*X 1 2+(4376366783/10000000000 : ℝ)*X 2 0+(2083943299/5000000000 : ℝ)*X 2 1+(1148869519/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-88481437/400000000 : ℝ)*X 0 0+(5222300897/10000000000 : ℝ)*X 0 1+(2719905763/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((165664229/312500000 : ℝ)*X 1 0+(-2105986887/10000000000 : ℝ)*X 1 1+(16999409/31250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((662656867/1250000000 : ℝ)*X 2 0+(2719905701/5000000000 : ℝ)*X 2 1+(-131624169/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4376413441/10000000000 : ℝ)*X 0 0+(4593690371/10000000000 : ℝ)*X 0 1+(1042421351/2500000000 : ℝ)*X 0 2+(4376413441/10000000000 : ℝ)*X 1 0+(4593690371/10000000000 : ℝ)*X 1 1+(1042421351/2500000000 : ℝ)*X 1 2+(4376413441/10000000000 : ℝ)*X 2 0+(4593690371/10000000000 : ℝ)*X 2 1+(1042421351/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5585150426879775283135364973/1031375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (315058557/20000000000000 : ℝ)*(base19) + (1274253541/100000000000000 : ℝ)*(base23) + (54772777/25000000000000 : ℝ)*(lower2) + (39005973/20000000000000 : ℝ)*(upper5) + (1724422864268139/50000000000000 : ℝ)*(major0) + (1724422864268139/50000000000000 : ℝ)*(major1) + (1724422864268139/50000000000000 : ℝ)*(major2) + (4558942245257407/100000000000000 : ℝ)*(sp0) + (2279491198274353/50000000000000 : ℝ)*(sp1) + (1139745837211377/25000000000000 : ℝ)*(sp2) + (2338694046511363/100000000000000 : ℝ)*(sp3) + (42377841643/100000000000000 : ℝ)*(sp4) + (651257559/100000000000000 : ℝ)*(sp5) + (126069539/1000000000000 : ℝ)*(sp7) + (2338706653465263/100000000000000 : ℝ)*(f.failure) + (91179692461981/2000000000000 : ℝ)*(f.sum) + (14816009921397/5156875000000000000000000000 : ℝ)*base65 + (6579308367970279991/2062750000000000000000000000000000 : ℝ)*base68 + (1860677177217220009/2062750000000000000000000000000000 : ℝ)*base69 + (4458441323208779991/2062750000000000000000000000000000 : ℝ)*base72 + (13066409183971/41255000000000000000000000000 : ℝ)*base73 + (18581846128368470009/2062750000000000000000000000000000 : ℝ)*base75 + (5085453973379220009/2062750000000000000000000000000000 : ℝ)*base77 + (14061964120782470009/2062750000000000000000000000000000 : ℝ)*base79 + (51555130426843/20627500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (79090749/10000000000000000000000 : ℝ)*base90 + (79090749/10000000000000000000000 : ℝ)*base92 + (79090749/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10361256675613352502190586499/1031375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1982309333/100000000000000 : ℝ)*(base19) + (841558269/50000000000000 : ℝ)*(base23) + (14364571/50000000000000 : ℝ)*(upper3) + (2303809/5000000000000 : ℝ)*(lower4) + (81390487/20000000000000 : ℝ)*(upper5) + (1738985445945357/50000000000000 : ℝ)*(major0) + (1738985445945357/50000000000000 : ℝ)*(major1) + (1738985445945357/50000000000000 : ℝ)*(major2) + (1058924873/4000000000000 : ℝ)*(sp1) + (22035810283/100000000000000 : ℝ)*(sp2) + (4597484647519201/100000000000000 : ℝ)*(sp4) + (4597456192088043/100000000000000 : ℝ)*(sp5) + (229873046429619/5000000000000 : ℝ)*(sp6) + (2358456801393507/100000000000000 : ℝ)*(sp7) + (2358456801393507/100000000000000 : ℝ)*(f.failure) + (4597484647519201/100000000000000 : ℝ)*(f.sum) + (6889606102899/5156875000000000000000000000 : ℝ)*base66 + (1569095797041578833/2062750000000000000000000000000000 : ℝ)*base68 + (23364316113418421167/2062750000000000000000000000000000 : ℝ)*base69 + (2543974853065828833/2062750000000000000000000000000000 : ℝ)*base72 + (20237500267919/20627500000000000000000000000 : ℝ)*base73 + (5976722176271171167/2062750000000000000000000000000000 : ℝ)*base75 + (13222310406135421167/2062750000000000000000000000000000 : ℝ)*base77 + (16878909980921171167/2062750000000000000000000000000000 : ℝ)*base79 + (11123275213857/41255000000000000000000000000 : ℝ)*base82 + (2423961/10000000000000000000000 : ℝ)*base90 + (2423961/10000000000000000000000 : ℝ)*base92 + (2423961/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1039_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147468077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1683/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8579/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2061/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7473/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1039_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1039_s4_0 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-553990089/2500000000 : ℝ)*x 0 + (1351836997/2500000000 : ℝ)*x 1 + (5252191673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (553990089/2500000000 : ℝ)^1029 ≤ (13453243936451/100000000000000 : ℝ)^773 := by
    have hnat : (553990089 : ℕ)^1029*100000000000000^773 ≤ 13453243936451^773*2500000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553990089 2500000000 13453243936451 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351836997/2500000000 : ℝ)^1029 ≤ (11027950653563/25000000000000 : ℝ)^773 := by
    have hnat : (1351836997 : ℕ)^1029*25000000000000^773 ≤ 11027950653563^773*2500000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351836997 2500000000 11027950653563 25000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5252191673/10000000000 : ℝ)^1029 ≤ (8486990686889/20000000000000 : ℝ)^773 := by
    have hnat : (5252191673 : ℕ)^1029*20000000000000^773 ≤ 8486990686889^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252191673 10000000000 8486990686889 20000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-553990089/2500000000 : ℝ), (1351836997/2500000000 : ℝ), (5252191673/10000000000 : ℝ)] ![(13453243936451/100000000000000 : ℝ), (11027950653563/25000000000000 : ℝ), (8486990686889/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-553990089/2500000000 : ℝ)|^1029 ≤ (13453243936451/100000000000000 : ℝ)^773
        have hw : |(-553990089/2500000000 : ℝ)|=(553990089/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351836997/2500000000 : ℝ)|^1029 ≤ (11027950653563/25000000000000 : ℝ)^773
        have hw : |(1351836997/2500000000 : ℝ)|=(1351836997/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5252191673/10000000000 : ℝ)|^1029 ≤ (8486990686889/20000000000000 : ℝ)^773
        have hw : |(5252191673/10000000000 : ℝ)|=(5252191673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s4_1 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2674073063/5000000000 : ℝ)*x 0 + (-2294903811/10000000000 : ℝ)*x 1 + (5252191703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674073063/5000000000 : ℝ)^1029 ≤ (43470073507237/100000000000000 : ℝ)^773 := by
    have hnat : (2674073063 : ℕ)^1029*100000000000000^773 ≤ 43470073507237^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674073063 5000000000 43470073507237 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2294903811/10000000000 : ℝ)^1029 ≤ (7047486360689/50000000000000 : ℝ)^773 := by
    have hnat : (2294903811 : ℕ)^1029*50000000000000^773 ≤ 7047486360689^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2294903811 10000000000 7047486360689 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5252191703/10000000000 : ℝ)^1029 ≤ (42434953757101/100000000000000 : ℝ)^773 := by
    have hnat : (5252191703 : ℕ)^1029*100000000000000^773 ≤ 42434953757101^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252191703 10000000000 42434953757101 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674073063/5000000000 : ℝ), (-2294903811/10000000000 : ℝ), (5252191703/10000000000 : ℝ)] ![(43470073507237/100000000000000 : ℝ), (7047486360689/50000000000000 : ℝ), (42434953757101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674073063/5000000000 : ℝ)|^1029 ≤ (43470073507237/100000000000000 : ℝ)^773
        have hw : |(2674073063/5000000000 : ℝ)|=(2674073063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2294903811/10000000000 : ℝ)|^1029 ≤ (7047486360689/50000000000000 : ℝ)^773
        have hw : |(-2294903811/10000000000 : ℝ)|=(2294903811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5252191703/10000000000 : ℝ)|^1029 ≤ (42434953757101/100000000000000 : ℝ)^773
        have hw : |(5252191703/10000000000 : ℝ)|=(5252191703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s4_2 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2674073093/5000000000 : ℝ)*x 0 + (41032747/78125000 : ℝ)*x 1 + (-458980769/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674073093/5000000000 : ℝ)^1029 ≤ (43470074156431/100000000000000 : ℝ)^773 := by
    have hnat : (2674073093 : ℕ)^1029*100000000000000^773 ≤ 43470074156431^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674073093 5000000000 43470074156431 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41032747/78125000 : ℝ)^1029 ≤ (21217476410699/50000000000000 : ℝ)^773 := by
    have hnat : (41032747 : ℕ)^1029*50000000000000^773 ≤ 21217476410699^773*78125000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41032747 78125000 21217476410699 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (458980769/2000000000 : ℝ)^1029 ≤ (14094972999359/100000000000000 : ℝ)^773 := by
    have hnat : (458980769 : ℕ)^1029*100000000000000^773 ≤ 14094972999359^773*2000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      458980769 2000000000 14094972999359 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674073093/5000000000 : ℝ), (41032747/78125000 : ℝ), (-458980769/2000000000 : ℝ)] ![(43470074156431/100000000000000 : ℝ), (21217476410699/50000000000000 : ℝ), (14094972999359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674073093/5000000000 : ℝ)|^1029 ≤ (43470074156431/100000000000000 : ℝ)^773
        have hw : |(2674073093/5000000000 : ℝ)|=(2674073093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(41032747/78125000 : ℝ)|^1029 ≤ (21217476410699/50000000000000 : ℝ)^773
        have hw : |(41032747/78125000 : ℝ)|=(41032747/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-458980769/2000000000 : ℝ)|^1029 ≤ (14094972999359/100000000000000 : ℝ)^773
        have hw : |(-458980769/2000000000 : ℝ)|=(458980769/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s4_3 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1094677989/2500000000 : ℝ)*x 0 + (846029113/2000000000 : ℝ)*x 1 + (2266300679/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1094677989/2500000000 : ℝ)^1029 ≤ (832738169969/2500000000000 : ℝ)^773 := by
    have hnat : (1094677989 : ℕ)^1029*2500000000000^773 ≤ 832738169969^773*2500000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094677989 2500000000 832738169969 2500000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (846029113/2000000000 : ℝ)^1029 ≤ (254508731283/800000000000 : ℝ)^773 := by
    have hnat : (846029113 : ℕ)^1029*800000000000^773 ≤ 254508731283^773*2000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846029113 2000000000 254508731283 800000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2266300679/5000000000 : ℝ)^1029 ≤ (6975376354167/20000000000000 : ℝ)^773 := by
    have hnat : (2266300679 : ℕ)^1029*20000000000000^773 ≤ 6975376354167^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2266300679 5000000000 6975376354167 20000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1094677989/2500000000 : ℝ), (846029113/2000000000 : ℝ), (2266300679/5000000000 : ℝ)] ![(832738169969/2500000000000 : ℝ), (254508731283/800000000000 : ℝ), (6975376354167/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1094677989/2500000000 : ℝ)|^1029 ≤ (832738169969/2500000000000 : ℝ)^773
        have hw : |(1094677989/2500000000 : ℝ)|=(1094677989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(846029113/2000000000 : ℝ)|^1029 ≤ (254508731283/800000000000 : ℝ)^773
        have hw : |(846029113/2000000000 : ℝ)|=(846029113/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2266300679/5000000000 : ℝ)|^1029 ≤ (6975376354167/20000000000000 : ℝ)^773
        have hw : |(2266300679/5000000000 : ℝ)|=(2266300679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s4_4 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2215969093/10000000000 : ℝ)*x 0 + (2626325621/5000000000 : ℝ)*x 1 + (5406886313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2215969093/10000000000 : ℝ)^1029 ≤ (2690662909203/20000000000000 : ℝ)^773 := by
    have hnat : (2215969093 : ℕ)^1029*20000000000000^773 ≤ 2690662909203^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2215969093 10000000000 2690662909203 20000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2626325621/5000000000 : ℝ)^1029 ≤ (663123379201/1562500000000 : ℝ)^773 := by
    have hnat : (2626325621 : ℕ)^1029*1562500000000^773 ≤ 663123379201^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626325621 5000000000 663123379201 1562500000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406886313/10000000000 : ℝ)^1029 ≤ (8821357833089/20000000000000 : ℝ)^773 := by
    have hnat : (5406886313 : ℕ)^1029*20000000000000^773 ≤ 8821357833089^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406886313 10000000000 8821357833089 20000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2215969093/10000000000 : ℝ), (2626325621/5000000000 : ℝ), (5406886313/10000000000 : ℝ)] ![(2690662909203/20000000000000 : ℝ), (663123379201/1562500000000 : ℝ), (8821357833089/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2215969093/10000000000 : ℝ)|^1029 ≤ (2690662909203/20000000000000 : ℝ)^773
        have hw : |(-2215969093/10000000000 : ℝ)|=(2215969093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2626325621/5000000000 : ℝ)|^1029 ≤ (663123379201/1562500000000 : ℝ)^773
        have hw : |(2626325621/5000000000 : ℝ)|=(2626325621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406886313/10000000000 : ℝ)|^1029 ≤ (8821357833089/20000000000000 : ℝ)^773
        have hw : |(5406886313/10000000000 : ℝ)|=(5406886313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s4_5 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5309151909/10000000000 : ℝ)*x 0 + (-535052323/2500000000 : ℝ)*x 1 + (5406886231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309151909/10000000000 : ℝ)^1029 ≤ (21524335224283/50000000000000 : ℝ)^773 := by
    have hnat : (5309151909 : ℕ)^1029*50000000000000^773 ≤ 21524335224283^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309151909 10000000000 21524335224283 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (535052323/2500000000 : ℝ)^1029 ≤ (3211135315177/25000000000000 : ℝ)^773 := by
    have hnat : (535052323 : ℕ)^1029*25000000000000^773 ≤ 3211135315177^773*2500000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535052323 2500000000 3211135315177 25000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406886231/10000000000 : ℝ)^1029 ≤ (22053394137499/50000000000000 : ℝ)^773 := by
    have hnat : (5406886231 : ℕ)^1029*50000000000000^773 ≤ 22053394137499^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406886231 10000000000 22053394137499 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309151909/10000000000 : ℝ), (-535052323/2500000000 : ℝ), (5406886231/10000000000 : ℝ)] ![(21524335224283/50000000000000 : ℝ), (3211135315177/25000000000000 : ℝ), (22053394137499/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309151909/10000000000 : ℝ)|^1029 ≤ (21524335224283/50000000000000 : ℝ)^773
        have hw : |(5309151909/10000000000 : ℝ)|=(5309151909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-535052323/2500000000 : ℝ)|^1029 ≤ (3211135315177/25000000000000 : ℝ)^773
        have hw : |(-535052323/2500000000 : ℝ)|=(535052323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406886231/10000000000 : ℝ)|^1029 ≤ (22053394137499/50000000000000 : ℝ)^773
        have hw : |(5406886231/10000000000 : ℝ)|=(5406886231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s4_6 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5309151877/10000000000 : ℝ)*x 0 + (5406886269/10000000000 : ℝ)*x 1 + (-535052321/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309151877/10000000000 : ℝ)^1029 ≤ (336317735181/781250000000 : ℝ)^773 := by
    have hnat : (5309151877 : ℕ)^1029*781250000000^773 ≤ 336317735181^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309151877 10000000000 336317735181 781250000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406886269/10000000000 : ℝ)^1029 ≤ (11026697171911/25000000000000 : ℝ)^773 := by
    have hnat : (5406886269 : ℕ)^1029*25000000000000^773 ≤ 11026697171911^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406886269 10000000000 11026697171911 25000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (535052321/2500000000 : ℝ)^1029 ≤ (3211135299199/25000000000000 : ℝ)^773 := by
    have hnat : (535052321 : ℕ)^1029*25000000000000^773 ≤ 3211135299199^773*2500000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535052321 2500000000 3211135299199 25000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309151877/10000000000 : ℝ), (5406886269/10000000000 : ℝ), (-535052321/2500000000 : ℝ)] ![(336317735181/781250000000 : ℝ), (11026697171911/25000000000000 : ℝ), (3211135299199/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309151877/10000000000 : ℝ)|^1029 ≤ (336317735181/781250000000 : ℝ)^773
        have hw : |(5309151877/10000000000 : ℝ)|=(5309151877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406886269/10000000000 : ℝ)|^1029 ≤ (11026697171911/25000000000000 : ℝ)^773
        have hw : |(5406886269/10000000000 : ℝ)|=(5406886269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-535052321/2500000000 : ℝ)|^1029 ≤ (3211135299199/25000000000000 : ℝ)^773
        have hw : |(-535052321/2500000000 : ℝ)|=(535052321/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s4_7 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (437872859/1000000000 : ℝ)*x 0 + (2265852381/5000000000 : ℝ)*x 1 + (33055047/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (437872859/1000000000 : ℝ)^1029 ≤ (8327423810631/25000000000000 : ℝ)^773 := by
    have hnat : (437872859 : ℕ)^1029*25000000000000^773 ≤ 8327423810631^773*1000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437872859 1000000000 8327423810631 25000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2265852381/5000000000 : ℝ)^1029 ≤ (17433849131761/50000000000000 : ℝ)^773 := by
    have hnat : (2265852381 : ℕ)^1029*50000000000000^773 ≤ 17433849131761^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2265852381 5000000000 17433849131761 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33055047/78125000 : ℝ)^1029 ≤ (795565161779/2500000000000 : ℝ)^773 := by
    have hnat : (33055047 : ℕ)^1029*2500000000000^773 ≤ 795565161779^773*78125000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33055047 78125000 795565161779 2500000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(437872859/1000000000 : ℝ), (2265852381/5000000000 : ℝ), (33055047/78125000 : ℝ)] ![(8327423810631/25000000000000 : ℝ), (17433849131761/50000000000000 : ℝ), (795565161779/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(437872859/1000000000 : ℝ)|^1029 ≤ (8327423810631/25000000000000 : ℝ)^773
        have hw : |(437872859/1000000000 : ℝ)|=(437872859/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2265852381/5000000000 : ℝ)|^1029 ≤ (17433849131761/50000000000000 : ℝ)^773
        have hw : |(2265852381/5000000000 : ℝ)|=(2265852381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(33055047/78125000 : ℝ)|^1029 ≤ (795565161779/2500000000000 : ℝ)^773
        have hw : |(33055047/78125000 : ℝ)|=(33055047/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1039_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147468077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7473/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2061/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (10963/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1781/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7473/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2061/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7473/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2061/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7473/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2061/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7473/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2061/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7473/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2061/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7473/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2061/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2061/20000 : ℝ) ^ (8231/2048 : ℝ) ≤ (10799346809306827/100000000000000000000 : ℝ) := by
    have hpowers : (2061/20000 : ℝ)^8231 ≤ (10799346809306827/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2061 : ℕ)^8231*100000000000000000000^2048 ≤ 10799346809306827^2048*20000^8231 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2061 20000 10799346809306827 100000000000000000000 8231 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2061/20000 : ℝ)) (X := (10799346809306827/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7473/50000 : ℝ) ^ (8231/2048 : ℝ) ≤ (48126072019040897/100000000000000000000 : ℝ) := by
    have hpowers : (7473/50000 : ℝ)^8231 ≤ (48126072019040897/100000000000000000000 : ℝ)^2048 := by
      have hnat : (7473 : ℕ)^8231*100000000000000000000^2048 ≤ 48126072019040897^2048*50000^8231 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7473 50000 48126072019040897 100000000000000000000 8231 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7473/50000 : ℝ)) (X := (48126072019040897/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010799346809306827/50000000000000000000 : ℝ) ≤ (10000537365284623/10000000000000000 : ℝ) ^ (8231/2048 : ℝ) := by
    have hpowers : (50010799346809306827/50000000000000000000 : ℝ)^2048 ≤ (10000537365284623/10000000000000000 : ℝ)^8231 := by
      have hnat : (50010799346809306827 : ℕ)^2048*10000000000000000^8231 ≤ 10000537365284623^8231*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010799346809306827 50000000000000000000 10000537365284623 10000000000000000 2048 8231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000537365284623/10000000000000000 : ℝ)) (X := (50010799346809306827/50000000000000000000 : ℝ)) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25014731354707086931/25000000000000000000 : ℝ) ≤ (10001465831105483/10000000000000000 : ℝ) ^ (8231/2048 : ℝ) := by
    have hpowers : (25014731354707086931/25000000000000000000 : ℝ)^2048 ≤ (10001465831105483/10000000000000000 : ℝ)^8231 := by
      have hnat : (25014731354707086931 : ℕ)^2048*10000000000000000^8231 ≤ 10001465831105483^8231*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014731354707086931 25000000000000000000 10001465831105483 10000000000000000 2048 8231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001465831105483/10000000000000000 : ℝ)) (X := (25014731354707086931/25000000000000000000 : ℝ)) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50048126072019040897/50000000000000000000 : ℝ) ≤ (10002394296926343/10000000000000000 : ℝ) ^ (8231/2048 : ℝ) := by
    have hpowers : (50048126072019040897/50000000000000000000 : ℝ)^2048 ≤ (10002394296926343/10000000000000000 : ℝ)^8231 := by
      have hnat : (50048126072019040897 : ℕ)^2048*10000000000000000^8231 ≤ 10002394296926343^8231*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50048126072019040897 50000000000000000000 10002394296926343 10000000000000000 2048 8231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002394296926343/10000000000000000 : ℝ)) (X := (50048126072019040897/50000000000000000000 : ℝ)) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10799346809306827/100000000000000000000 : ℝ) ≤ ((15464452743906003581/15470000000000000000 : ℝ)+2*(46423291043/23205000000000 : ℝ)*(2061/20000 : ℝ))^(8231/2048 : ℝ) := by
    rw [show (15464452743906003581/15470000000000000000 : ℝ)+2*(46423291043/23205000000000 : ℝ)*(2061/20000 : ℝ)=(10000537365284623/10000000000000000 : ℝ) by norm_num, show 1+2*(10799346809306827/100000000000000000000 : ℝ)=(50010799346809306827/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(48126072019040897/100000000000000000000 : ℝ)+(10799346809306827/100000000000000000000 : ℝ) ≤ ((15464452743906003581/15470000000000000000 : ℝ)+(46423291043/23205000000000 : ℝ)*((7473/50000 : ℝ)+(2061/20000 : ℝ)))^(8231/2048 : ℝ) := by
    rw [show (15464452743906003581/15470000000000000000 : ℝ)+(46423291043/23205000000000 : ℝ)*((7473/50000 : ℝ)+(2061/20000 : ℝ))=(10001465831105483/10000000000000000 : ℝ) by norm_num, show 1+(48126072019040897/100000000000000000000 : ℝ)+(10799346809306827/100000000000000000000 : ℝ)=(25014731354707086931/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(48126072019040897/100000000000000000000 : ℝ) ≤ ((15464452743906003581/15470000000000000000 : ℝ)+2*(46423291043/23205000000000 : ℝ)*(7473/50000 : ℝ))^(8231/2048 : ℝ) := by
    rw [show (15464452743906003581/15470000000000000000 : ℝ)+2*(46423291043/23205000000000 : ℝ)*(7473/50000 : ℝ)=(10002394296926343/10000000000000000 : ℝ) by norm_num, show 1+2*(48126072019040897/100000000000000000000 : ℝ)=(50048126072019040897/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15464452743906003581/15470000000000000000 : ℝ)*(X 1 0+X 2 0)+(46423291043/23205000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8231/2048 : ℝ)) (lo := (2061/20000 : ℝ)) (hi := (7473/50000 : ℝ)) (c := (15464452743906003581/15470000000000000000 : ℝ)) (alpha := (46423291043/23205000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15464452743906003581/15470000000000000000 : ℝ)*(X 0 1+X 2 1)+(46423291043/23205000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8231/2048 : ℝ)) (lo := (2061/20000 : ℝ)) (hi := (7473/50000 : ℝ)) (c := (15464452743906003581/15470000000000000000 : ℝ)) (alpha := (46423291043/23205000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15464452743906003581/15470000000000000000 : ℝ)*(X 0 2+X 1 2)+(46423291043/23205000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8231/2048 : ℝ)) (lo := (2061/20000 : ℝ)) (hi := (7473/50000 : ℝ)) (c := (15464452743906003581/15470000000000000000 : ℝ)) (alpha := (46423291043/23205000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-553990089/2500000000 : ℝ)*X 0 0+(1351836997/2500000000 : ℝ)*X 0 1+(5252191673/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674073063/5000000000 : ℝ)*X 1 0+(-2294903811/10000000000 : ℝ)*X 1 1+(5252191703/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674073093/5000000000 : ℝ)*X 2 0+(41032747/78125000 : ℝ)*X 2 1+(-458980769/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1094677989/2500000000 : ℝ)*X 0 0+(846029113/2000000000 : ℝ)*X 0 1+(2266300679/5000000000 : ℝ)*X 0 2+(1094677989/2500000000 : ℝ)*X 1 0+(846029113/2000000000 : ℝ)*X 1 1+(2266300679/5000000000 : ℝ)*X 1 2+(1094677989/2500000000 : ℝ)*X 2 0+(846029113/2000000000 : ℝ)*X 2 1+(2266300679/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2215969093/10000000000 : ℝ)*X 0 0+(2626325621/5000000000 : ℝ)*X 0 1+(5406886313/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5309151909/10000000000 : ℝ)*X 1 0+(-535052323/2500000000 : ℝ)*X 1 1+(5406886231/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5309151877/10000000000 : ℝ)*X 2 0+(5406886269/10000000000 : ℝ)*X 2 1+(-535052321/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((437872859/1000000000 : ℝ)*X 0 0+(2265852381/5000000000 : ℝ)*X 0 1+(33055047/78125000 : ℝ)*X 0 2+(437872859/1000000000 : ℝ)*X 1 0+(2265852381/5000000000 : ℝ)*X 1 1+(33055047/78125000 : ℝ)*X 1 2+(437872859/1000000000 : ℝ)*X 2 0+(2265852381/5000000000 : ℝ)*X 2 1+(33055047/78125000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (100989024234617212982059917/15470000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (348702413/25000000000000 : ℝ)*(base19) + (353495911/25000000000000 : ℝ)*(base23) + (28416531/100000000000000 : ℝ)*(lower2) + (187553703/100000000000000 : ℝ)*(upper3) + (14397809/12500000000000 : ℝ)*(upper5) + (97514809970619/2000000000000 : ℝ)*(major0) + (97514809970619/2000000000000 : ℝ)*(major1) + (97514809970619/2000000000000 : ℝ)*(major2) + (3222573246365681/50000000000000 : ℝ)*(sp0) + (6445177032493883/100000000000000 : ℝ)*(sp1) + (1611294253329973/25000000000000 : ℝ)*(sp2) + (1653142182431673/50000000000000 : ℝ)*(sp3) + (31934572173/100000000000000 : ℝ)*(sp4) + (17987293149/100000000000000 : ℝ)*(sp7) + (1653151176078247/50000000000000 : ℝ)*(f.failure) + (402823651706471/6250000000000 : ℝ)*(f.sum) + (350544089351/61880000000000000000000000 : ℝ)*base66 + (1158149304718433/1820000000000000000000000000000 : ℝ)*base68 + (11145304627141567/1820000000000000000000000000000 : ℝ)*base69 + (6924985038201567/1820000000000000000000000000000 : ℝ)*base71 + (829869103341/309400000000000000000000000 : ℝ)*base74 + (16999422845538433/1820000000000000000000000000000 : ℝ)*base76 + (2379919032078433/1820000000000000000000000000000 : ℝ)*base78 + (6447318553718433/1820000000000000000000000000000 : ℝ)*base80 + (172647524079/96687500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (13378981/5000000000000000000000 : ℝ)*base90 + (13378981/5000000000000000000000 : ℝ)*base92 + (13378981/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (615738672901753302833091357/193375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (84896409/10000000000000 : ℝ)*(base19) + (512405103/50000000000000 : ℝ)*(base23) + (128634423/100000000000000 : ℝ)*(upper2) + (287190707/100000000000000 : ℝ)*(upper5) + (1226205819600301/25000000000000 : ℝ)*(major0) + (1226205819600301/25000000000000 : ℝ)*(major1) + (1226205819600301/25000000000000 : ℝ)*(major2) + (2471360073/100000000000000 : ℝ)*(sp0) + (2424156699/10000000000000 : ℝ)*(sp1) + (320562127/1562500000000 : ℝ)*(sp2) + (6483620220004457/100000000000000 : ℝ)*(sp4) + (810449700104181/12500000000000 : ℝ)*(sp5) + (1296720230115639/20000000000000 : ℝ)*(sp6) + (665204751859781/20000000000000 : ℝ)*(sp7) + (665204751859781/20000000000000 : ℝ)*(f.failure) + (6483622691364529/100000000000000 : ℝ)*(f.sum) + (7070578556413/4641000000000000000000000000 : ℝ)*base66 + (56532721524001979/68250000000000000000000000000000 : ℝ)*base67 + (438867356797501979/68250000000000000000000000000000 : ℝ)*base69 + (369120183016498021/68250000000000000000000000000000 : ℝ)*base72 + (202779593789/290062500000000000000000000 : ℝ)*base73 + (2284035502891501979/68250000000000000000000000000000 : ℝ)*base75 + (417697426902751979/68250000000000000000000000000000 : ℝ)*base77 + (272935866902248021/68250000000000000000000000000000 : ℝ)*base80 + (2342383154113/1160250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base86 + (2288863/2000000000000000000000 : ℝ)*base90 + (2288863/2000000000000000000000 : ℝ)*base92 + (2288863/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1039_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147468077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7473/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2061/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10963/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1781/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1039_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1039_s5_0 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1108436361/5000000000 : ℝ)*x 0 + (5397786089/10000000000 : ℝ)*x 1 + (1052231047/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1108436361/5000000000 : ℝ)^1029 ≤ (3365154469153/25000000000000 : ℝ)^773 := by
    have hnat : (1108436361 : ℕ)^1029*25000000000000^773 ≤ 3365154469153^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1108436361 5000000000 3365154469153 25000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5397786089/10000000000 : ℝ)^1029 ≤ (11001999104169/25000000000000 : ℝ)^773 := by
    have hnat : (5397786089 : ℕ)^1029*25000000000000^773 ≤ 11001999104169^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397786089 10000000000 11001999104169 25000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052231047/2000000000 : ℝ)^1029 ≤ (664552901451/1562500000000 : ℝ)^773 := by
    have hnat : (1052231047 : ℕ)^1029*1562500000000^773 ≤ 664552901451^773*2000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052231047 2000000000 664552901451 1562500000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1108436361/5000000000 : ℝ), (5397786089/10000000000 : ℝ), (1052231047/2000000000 : ℝ)] ![(3365154469153/25000000000000 : ℝ), (11001999104169/25000000000000 : ℝ), (664552901451/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1108436361/5000000000 : ℝ)|^1029 ≤ (3365154469153/25000000000000 : ℝ)^773
        have hw : |(-1108436361/5000000000 : ℝ)|=(1108436361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5397786089/10000000000 : ℝ)|^1029 ≤ (11001999104169/25000000000000 : ℝ)^773
        have hw : |(5397786089/10000000000 : ℝ)|=(5397786089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052231047/2000000000 : ℝ)|^1029 ≤ (664552901451/1562500000000 : ℝ)^773
        have hw : |(1052231047/2000000000 : ℝ)|=(1052231047/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s5_1 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5345770689/10000000000 : ℝ)*x 0 + (-2286247153/10000000000 : ℝ)*x 1 + (657644403/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345770689/10000000000 : ℝ)^1029 ≤ (4344437342213/10000000000000 : ℝ)^773 := by
    have hnat : (5345770689 : ℕ)^1029*10000000000000^773 ≤ 4344437342213^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345770689 10000000000 4344437342213 10000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2286247153/10000000000 : ℝ)^1029 ≤ (560969639457/4000000000000 : ℝ)^773 := by
    have hnat : (2286247153 : ℕ)^1029*4000000000000^773 ≤ 560969639457^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2286247153 10000000000 560969639457 4000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (657644403/1250000000 : ℝ)^1029 ≤ (4253138557449/10000000000000 : ℝ)^773 := by
    have hnat : (657644403 : ℕ)^1029*10000000000000^773 ≤ 4253138557449^773*1250000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657644403 1250000000 4253138557449 10000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345770689/10000000000 : ℝ), (-2286247153/10000000000 : ℝ), (657644403/1250000000 : ℝ)] ![(4344437342213/10000000000000 : ℝ), (560969639457/4000000000000 : ℝ), (4253138557449/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345770689/10000000000 : ℝ)|^1029 ≤ (4344437342213/10000000000000 : ℝ)^773
        have hw : |(5345770689/10000000000 : ℝ)|=(5345770689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2286247153/10000000000 : ℝ)|^1029 ≤ (560969639457/4000000000000 : ℝ)^773
        have hw : |(-2286247153/10000000000 : ℝ)|=(2286247153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(657644403/1250000000 : ℝ)|^1029 ≤ (4253138557449/10000000000000 : ℝ)^773
        have hw : |(657644403/1250000000 : ℝ)|=(657644403/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s5_2 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5345770699/10000000000 : ℝ)*x 0 + (2630577609/5000000000 : ℝ)*x 1 + (-2286247149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345770699/10000000000 : ℝ)^1029 ≤ (43444373530313/100000000000000 : ℝ)^773 := by
    have hnat : (5345770699 : ℕ)^1029*100000000000000^773 ≤ 43444373530313^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345770699 10000000000 43444373530313 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2630577609/5000000000 : ℝ)^1029 ≤ (42531385509923/100000000000000 : ℝ)^773 := by
    have hnat : (2630577609 : ℕ)^1029*100000000000000^773 ≤ 42531385509923^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630577609 5000000000 42531385509923 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2286247149/10000000000 : ℝ)^1029 ≤ (7012120476881/50000000000000 : ℝ)^773 := by
    have hnat : (2286247149 : ℕ)^1029*50000000000000^773 ≤ 7012120476881^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2286247149 10000000000 7012120476881 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345770699/10000000000 : ℝ), (2630577609/5000000000 : ℝ), (-2286247149/10000000000 : ℝ)] ![(43444373530313/100000000000000 : ℝ), (42531385509923/100000000000000 : ℝ), (7012120476881/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345770699/10000000000 : ℝ)|^1029 ≤ (43444373530313/100000000000000 : ℝ)^773
        have hw : |(5345770699/10000000000 : ℝ)|=(5345770699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2630577609/5000000000 : ℝ)|^1029 ≤ (42531385509923/100000000000000 : ℝ)^773
        have hw : |(2630577609/5000000000 : ℝ)|=(2630577609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2286247149/10000000000 : ℝ)|^1029 ≤ (7012120476881/50000000000000 : ℝ)^773
        have hw : |(-2286247149/10000000000 : ℝ)|=(2286247149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s5_3 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4379239467/10000000000 : ℝ)*x 0 + (4248132403/10000000000 : ℝ)*x 1 + (4514475327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4379239467/10000000000 : ℝ)^1029 ≤ (416435859103/1250000000000 : ℝ)^773 := by
    have hnat : (4379239467 : ℕ)^1029*1250000000000^773 ≤ 416435859103^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4379239467 10000000000 416435859103 1250000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4248132403/10000000000 : ℝ)^1029 ≤ (1999611929203/6250000000000 : ℝ)^773 := by
    have hnat : (4248132403 : ℕ)^1029*6250000000000^773 ≤ 1999611929203^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4248132403 10000000000 1999611929203 6250000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4514475327/10000000000 : ℝ)^1029 ≤ (34691340390129/100000000000000 : ℝ)^773 := by
    have hnat : (4514475327 : ℕ)^1029*100000000000000^773 ≤ 34691340390129^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4514475327 10000000000 34691340390129 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4379239467/10000000000 : ℝ), (4248132403/10000000000 : ℝ), (4514475327/10000000000 : ℝ)] ![(416435859103/1250000000000 : ℝ), (1999611929203/6250000000000 : ℝ), (34691340390129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4379239467/10000000000 : ℝ)|^1029 ≤ (416435859103/1250000000000 : ℝ)^773
        have hw : |(4379239467/10000000000 : ℝ)|=(4379239467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4248132403/10000000000 : ℝ)|^1029 ≤ (1999611929203/6250000000000 : ℝ)^773
        have hw : |(4248132403/10000000000 : ℝ)|=(4248132403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4514475327/10000000000 : ℝ)|^1029 ≤ (34691340390129/100000000000000 : ℝ)^773
        have hw : |(4514475327/10000000000 : ℝ)|=(4514475327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s5_4 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2216878297/10000000000 : ℝ)*x 0 + (2630756029/5000000000 : ℝ)*x 1 + (5397428123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2216878297/10000000000 : ℝ)^1029 ≤ (13460662938063/100000000000000 : ℝ)^773 := by
    have hnat : (2216878297 : ℕ)^1029*100000000000000^773 ≤ 13460662938063^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2216878297 10000000000 13460662938063 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2630756029/5000000000 : ℝ)^1029 ≤ (42535225611433/100000000000000 : ℝ)^773 := by
    have hnat : (2630756029 : ℕ)^1029*100000000000000^773 ≤ 42535225611433^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630756029 5000000000 42535225611433 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5397428123/10000000000 : ℝ)^1029 ≤ (5500513929551/12500000000000 : ℝ)^773 := by
    have hnat : (5397428123 : ℕ)^1029*12500000000000^773 ≤ 5500513929551^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397428123 10000000000 5500513929551 12500000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2216878297/10000000000 : ℝ), (2630756029/5000000000 : ℝ), (5397428123/10000000000 : ℝ)] ![(13460662938063/100000000000000 : ℝ), (42535225611433/100000000000000 : ℝ), (5500513929551/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2216878297/10000000000 : ℝ)|^1029 ≤ (13460662938063/100000000000000 : ℝ)^773
        have hw : |(-2216878297/10000000000 : ℝ)|=(2216878297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2630756029/5000000000 : ℝ)|^1029 ≤ (42535225611433/100000000000000 : ℝ)^773
        have hw : |(2630756029/5000000000 : ℝ)|=(2630756029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5397428123/10000000000 : ℝ)|^1029 ≤ (5500513929551/12500000000000 : ℝ)^773
        have hw : |(5397428123/10000000000 : ℝ)|=(5397428123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s5_5 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2655715407/5000000000 : ℝ)*x 0 + (-2149975049/10000000000 : ℝ)*x 1 + (5397428003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655715407/5000000000 : ℝ)^1029 ≤ (2153663501047/5000000000000 : ℝ)^773 := by
    have hnat : (2655715407 : ℕ)^1029*5000000000000^773 ≤ 2153663501047^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655715407 5000000000 2153663501047 5000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2149975049/10000000000 : ℝ)^1029 ≤ (6461309913899/50000000000000 : ℝ)^773 := by
    have hnat : (2149975049 : ℕ)^1029*50000000000000^773 ≤ 6461309913899^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149975049 10000000000 6461309913899 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5397428003/10000000000 : ℝ)^1029 ≤ (44004110134071/100000000000000 : ℝ)^773 := by
    have hnat : (5397428003 : ℕ)^1029*100000000000000^773 ≤ 44004110134071^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397428003 10000000000 44004110134071 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655715407/5000000000 : ℝ), (-2149975049/10000000000 : ℝ), (5397428003/10000000000 : ℝ)] ![(2153663501047/5000000000000 : ℝ), (6461309913899/50000000000000 : ℝ), (44004110134071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655715407/5000000000 : ℝ)|^1029 ≤ (2153663501047/5000000000000 : ℝ)^773
        have hw : |(2655715407/5000000000 : ℝ)|=(2655715407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2149975049/10000000000 : ℝ)|^1029 ≤ (6461309913899/50000000000000 : ℝ)^773
        have hw : |(-2149975049/10000000000 : ℝ)|=(2149975049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5397428003/10000000000 : ℝ)|^1029 ≤ (44004110134071/100000000000000 : ℝ)^773
        have hw : |(5397428003/10000000000 : ℝ)|=(5397428003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s5_6 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5311431189/10000000000 : ℝ)*x 0 + (2698714009/5000000000 : ℝ)*x 1 + (-2149974523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311431189/10000000000 : ℝ)^1029 ≤ (21536637034577/50000000000000 : ℝ)^773 := by
    have hnat : (5311431189 : ℕ)^1029*50000000000000^773 ≤ 21536637034577^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311431189 10000000000 21536637034577 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2698714009/5000000000 : ℝ)^1029 ≤ (44004110296863/100000000000000 : ℝ)^773 := by
    have hnat : (2698714009 : ℕ)^1029*100000000000000^773 ≤ 44004110296863^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698714009 5000000000 44004110296863 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2149974523/10000000000 : ℝ)^1029 ≤ (12922615619187/100000000000000 : ℝ)^773 := by
    have hnat : (2149974523 : ℕ)^1029*100000000000000^773 ≤ 12922615619187^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149974523 10000000000 12922615619187 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311431189/10000000000 : ℝ), (2698714009/5000000000 : ℝ), (-2149974523/10000000000 : ℝ)] ![(21536637034577/50000000000000 : ℝ), (44004110296863/100000000000000 : ℝ), (12922615619187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311431189/10000000000 : ℝ)|^1029 ≤ (21536637034577/50000000000000 : ℝ)^773
        have hw : |(5311431189/10000000000 : ℝ)|=(5311431189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2698714009/5000000000 : ℝ)|^1029 ≤ (44004110296863/100000000000000 : ℝ)^773
        have hw : |(2698714009/5000000000 : ℝ)|=(2698714009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2149974523/10000000000 : ℝ)|^1029 ≤ (12922615619187/100000000000000 : ℝ)^773
        have hw : |(-2149974523/10000000000 : ℝ)|=(2149974523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s5_7 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4379250357/10000000000 : ℝ)*x 0 + (902756023/2000000000 : ℝ)*x 1 + (3319399/7812500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4379250357/10000000000 : ℝ)^1029 ≤ (16657489504957/50000000000000 : ℝ)^773 := by
    have hnat : (4379250357 : ℕ)^1029*50000000000000^773 ≤ 16657489504957^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4379250357 10000000000 16657489504957 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (902756023/2000000000 : ℝ)^1029 ≤ (34684228977771/100000000000000 : ℝ)^773 := by
    have hnat : (902756023 : ℕ)^1029*100000000000000^773 ≤ 34684228977771^773*2000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      902756023 2000000000 34684228977771 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3319399/7812500 : ℝ)^1029 ≤ (1600039599727/5000000000000 : ℝ)^773 := by
    have hnat : (3319399 : ℕ)^1029*5000000000000^773 ≤ 1600039599727^773*7812500^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3319399 7812500 1600039599727 5000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4379250357/10000000000 : ℝ), (902756023/2000000000 : ℝ), (3319399/7812500 : ℝ)] ![(16657489504957/50000000000000 : ℝ), (34684228977771/100000000000000 : ℝ), (1600039599727/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4379250357/10000000000 : ℝ)|^1029 ≤ (16657489504957/50000000000000 : ℝ)^773
        have hw : |(4379250357/10000000000 : ℝ)|=(4379250357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(902756023/2000000000 : ℝ)|^1029 ≤ (34684228977771/100000000000000 : ℝ)^773
        have hw : |(902756023/2000000000 : ℝ)|=(902756023/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3319399/7812500 : ℝ)|^1029 ≤ (1600039599727/5000000000000 : ℝ)^773
        have hw : |(3319399/7812500 : ℝ)|=(3319399/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1039_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147468077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1781/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10963/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5577/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (439/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1781/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10963/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1781/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10963/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1781/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10963/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1781/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10963/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1781/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10963/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1781/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10963/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10963/100000 : ℝ) ^ (8231/2048 : ℝ) ≤ (13849530858152467/100000000000000000000 : ℝ) := by
    have hpowers : (10963/100000 : ℝ)^8231 ≤ (13849530858152467/100000000000000000000 : ℝ)^2048 := by
      have hnat : (10963 : ℕ)^8231*100000000000000000000^2048 ≤ 13849530858152467^2048*100000^8231 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10963 100000 13849530858152467 100000000000000000000 8231 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10963/100000 : ℝ)) (X := (13849530858152467/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1781/12500 : ℝ) ^ (8231/2048 : ℝ) ≤ (9927516020515181/25000000000000000000 : ℝ) := by
    have hpowers : (1781/12500 : ℝ)^8231 ≤ (9927516020515181/25000000000000000000 : ℝ)^2048 := by
      have hnat : (1781 : ℕ)^8231*25000000000000000000^2048 ≤ 9927516020515181^2048*12500^8231 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1781 12500 9927516020515181 25000000000000000000 8231 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1781/12500 : ℝ)) (X := (9927516020515181/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013849530858152467/50000000000000000000 : ℝ) ≤ (5000344561885887/5000000000000000 : ℝ) ^ (8231/2048 : ℝ) := by
    have hpowers : (50013849530858152467/50000000000000000000 : ℝ)^2048 ≤ (5000344561885887/5000000000000000 : ℝ)^8231 := by
      have hnat : (50013849530858152467 : ℕ)^2048*5000000000000000^8231 ≤ 5000344561885887^8231*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013849530858152467 50000000000000000000 5000344561885887 5000000000000000 2048 8231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000344561885887/5000000000000000 : ℝ)) (X := (50013849530858152467/50000000000000000000 : ℝ)) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100053559594940213191/100000000000000000000 : ℝ) ≤ (10001332377493111/10000000000000000 : ℝ) ^ (8231/2048 : ℝ) := by
    have hpowers : (100053559594940213191/100000000000000000000 : ℝ)^2048 ≤ (10001332377493111/10000000000000000 : ℝ)^8231 := by
      have hnat : (100053559594940213191 : ℕ)^2048*10000000000000000^8231 ≤ 10001332377493111^8231*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100053559594940213191 100000000000000000000 10001332377493111 10000000000000000 2048 8231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001332377493111/10000000000000000 : ℝ)) (X := (100053559594940213191/100000000000000000000 : ℝ)) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12509927516020515181/12500000000000000000 : ℝ) ≤ (625123476950903/625000000000000 : ℝ) ^ (8231/2048 : ℝ) := by
    have hpowers : (12509927516020515181/12500000000000000000 : ℝ)^2048 ≤ (625123476950903/625000000000000 : ℝ)^8231 := by
      have hnat : (12509927516020515181 : ℕ)^2048*625000000000000^8231 ≤ 625123476950903^8231*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509927516020515181 12500000000000000000 625123476950903 625000000000000 2048 8231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625123476950903/625000000000000 : ℝ)) (X := (12509927516020515181/12500000000000000000 : ℝ)) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13849530858152467/100000000000000000000 : ℝ) ≤ ((1026192493453007579/1026562500000000000 : ℝ)+2*(643253721337/328500000000000 : ℝ)*(10963/100000 : ℝ))^(8231/2048 : ℝ) := by
    rw [show (1026192493453007579/1026562500000000000 : ℝ)+2*(643253721337/328500000000000 : ℝ)*(10963/100000 : ℝ)=(5000344561885887/5000000000000000 : ℝ) by norm_num, show 1+2*(13849530858152467/100000000000000000000 : ℝ)=(50013849530858152467/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9927516020515181/25000000000000000000 : ℝ)+(13849530858152467/100000000000000000000 : ℝ) ≤ ((1026192493453007579/1026562500000000000 : ℝ)+(643253721337/328500000000000 : ℝ)*((1781/12500 : ℝ)+(10963/100000 : ℝ)))^(8231/2048 : ℝ) := by
    rw [show (1026192493453007579/1026562500000000000 : ℝ)+(643253721337/328500000000000 : ℝ)*((1781/12500 : ℝ)+(10963/100000 : ℝ))=(10001332377493111/10000000000000000 : ℝ) by norm_num, show 1+(9927516020515181/25000000000000000000 : ℝ)+(13849530858152467/100000000000000000000 : ℝ)=(100053559594940213191/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9927516020515181/25000000000000000000 : ℝ) ≤ ((1026192493453007579/1026562500000000000 : ℝ)+2*(643253721337/328500000000000 : ℝ)*(1781/12500 : ℝ))^(8231/2048 : ℝ) := by
    rw [show (1026192493453007579/1026562500000000000 : ℝ)+2*(643253721337/328500000000000 : ℝ)*(1781/12500 : ℝ)=(625123476950903/625000000000000 : ℝ) by norm_num, show 1+2*(9927516020515181/25000000000000000000 : ℝ)=(12509927516020515181/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1026192493453007579/1026562500000000000 : ℝ)*(X 1 0+X 2 0)+(643253721337/328500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8231/2048 : ℝ)) (lo := (10963/100000 : ℝ)) (hi := (1781/12500 : ℝ)) (c := (1026192493453007579/1026562500000000000 : ℝ)) (alpha := (643253721337/328500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1026192493453007579/1026562500000000000 : ℝ)*(X 0 1+X 2 1)+(643253721337/328500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8231/2048 : ℝ)) (lo := (10963/100000 : ℝ)) (hi := (1781/12500 : ℝ)) (c := (1026192493453007579/1026562500000000000 : ℝ)) (alpha := (643253721337/328500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1026192493453007579/1026562500000000000 : ℝ)*(X 0 2+X 1 2)+(643253721337/328500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8231/2048 : ℝ)) (lo := (10963/100000 : ℝ)) (hi := (1781/12500 : ℝ)) (c := (1026192493453007579/1026562500000000000 : ℝ)) (alpha := (643253721337/328500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1108436361/5000000000 : ℝ)*X 0 0+(5397786089/10000000000 : ℝ)*X 0 1+(1052231047/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345770689/10000000000 : ℝ)*X 1 0+(-2286247153/10000000000 : ℝ)*X 1 1+(657644403/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345770699/10000000000 : ℝ)*X 2 0+(2630577609/5000000000 : ℝ)*X 2 1+(-2286247149/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4379239467/10000000000 : ℝ)*X 0 0+(4248132403/10000000000 : ℝ)*X 0 1+(4514475327/10000000000 : ℝ)*X 0 2+(4379239467/10000000000 : ℝ)*X 1 0+(4248132403/10000000000 : ℝ)*X 1 1+(4514475327/10000000000 : ℝ)*X 1 2+(4379239467/10000000000 : ℝ)*X 2 0+(4248132403/10000000000 : ℝ)*X 2 1+(4514475327/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2216878297/10000000000 : ℝ)*X 0 0+(2630756029/5000000000 : ℝ)*X 0 1+(5397428123/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655715407/5000000000 : ℝ)*X 1 0+(-2149975049/10000000000 : ℝ)*X 1 1+(5397428003/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311431189/10000000000 : ℝ)*X 2 0+(2698714009/5000000000 : ℝ)*X 2 1+(-2149974523/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4379250357/10000000000 : ℝ)*X 0 0+(902756023/2000000000 : ℝ)*X 0 1+(3319399/7812500 : ℝ)*X 0 2+(4379250357/10000000000 : ℝ)*X 1 0+(902756023/2000000000 : ℝ)*X 1 1+(3319399/7812500 : ℝ)*X 1 2+(4379250357/10000000000 : ℝ)*X 2 0+(902756023/2000000000 : ℝ)*X 2 1+(3319399/7812500 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1742042515121865491801/219000000000000000000000000 : ℝ) := by norm_num
    linear_combination (327918753/20000000000000 : ℝ)*(base19) + (1549782019/100000000000000 : ℝ)*(base23) + (442643/800000000000 : ℝ)*(lower2) + (193061183/100000000000000 : ℝ)*(upper3) + (31212771/25000000000000 : ℝ)*(upper5) + (221473588275679/4000000000000 : ℝ)*(major0) + (221473588275679/4000000000000 : ℝ)*(major1) + (221473588275679/4000000000000 : ℝ)*(major2) + (3659517330406763/50000000000000 : ℝ)*(sp0) + (914884409938219/12500000000000 : ℝ)*(sp1) + (3659537684658749/50000000000000 : ℝ)*(sp2) + (1877289593504439/50000000000000 : ℝ)*(sp3) + (42258285991/100000000000000 : ℝ)*(sp4) + (5760631121/25000000000000 : ℝ)*(sp7) + (1877301114766681/50000000000000 : ℝ)*(f.failure) + (7319076919099517/100000000000000 : ℝ)*(f.sum) + (126102368017/164250000000000000000000000 : ℝ)*base65 + (378093343045129/1026562500000000000000000000000 : ℝ)*base67 + (16005333442256617/2053125000000000000000000000000 : ℝ)*base70 + (3309439321963879/1026562500000000000000000000000 : ℝ)*base71 + (2585107630057/657000000000000000000000000 : ℝ)*base73 + (5948325188104871/1026562500000000000000000000000 : ℝ)*base76 + (30273196706813/128320312500000000000000000000 : ℝ)*base77 + (5346619975242371/1026562500000000000000000000000 : ℝ)*base80 + (659113981093/131400000000000000000000000 : ℝ)*base82 + (742437/5000000000000000000000 : ℝ)*base89 + (742437/5000000000000000000000 : ℝ)*base91 + (742437/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11902371992761950555481831/1069335937500000000000000000000 : ℝ) := by norm_num
    linear_combination (105932429/100000000000000 : ℝ)*(base23) + (36339639/20000000000000 : ℝ)*(lower2) + (2362453/2500000000000 : ℝ)*(upper4) + (63079723/100000000000000 : ℝ)*(upper5) + (5565915502544687/100000000000000 : ℝ)*(major0) + (5565915502544687/100000000000000 : ℝ)*(major1) + (5565915502544687/100000000000000 : ℝ)*(major2) + (6478921937/100000000000000 : ℝ)*(sp0) + (16469338587/100000000000000 : ℝ)*(sp2) + (4303773713/100000000000000 : ℝ)*(sp3) + (367875262727937/5000000000000 : ℝ)*(sp4) + (1839377933370169/25000000000000 : ℝ)*(sp5) + (367874757910483/5000000000000 : ℝ)*(sp6) + (1887157298407151/50000000000000 : ℝ)*(sp7) + (1887159450294007/50000000000000 : ℝ)*(f.failure) + (1839377933370169/25000000000000 : ℝ)*(f.sum) + (46708199894539/4106250000000000000000000000 : ℝ)*base66 + (408922548830533213/25664062500000000000000000000000 : ℝ)*base68 + (276191185141783213/25664062500000000000000000000000 : ℝ)*base70 + (2028133472990675801/51328125000000000000000000000000 : ℝ)*base72 + (9516723330053/8212500000000000000000000000 : ℝ)*base74 + (42511094669582051/51328125000000000000000000000000 : ℝ)*base76 + (16607203060404287/25664062500000000000000000000000 : ℝ)*base77 + (426274613534582051/51328125000000000000000000000000 : ℝ)*base80 + (89648332309381/16425000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (53085461/5000000000000000000000 : ℝ)*base90 + (53085461/5000000000000000000000 : ℝ)*base92 + (53085461/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1039_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147468077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1781/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10963/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5577/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (439/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1039_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1039_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147468077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1683/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8579/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5577/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (439/3125 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1039_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1039_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1039_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147468077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1683/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8579/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5577/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (439/3125 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1039_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
