-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1393_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:41:17.60099+00:00
-- url     : https://prove2.me/submissions/d82008ac-a00c-4d20-b36c-c19c10f398a1

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
theorem support_rectangle_w1393_s6_0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2000716597/10000000000 : ℝ)*x 0 + (541008327/1000000000 : ℝ)*x 1 + (5123083/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2000716597/10000000000 : ℝ)^4353 ≤ (3049090749071/25000000000000 : ℝ)^3329 := by
    have hnat : (2000716597 : ℕ)^4353*25000000000000^3329 ≤ 3049090749071^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2000716597 10000000000 3049090749071 25000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541008327/1000000000 : ℝ)^4353 ≤ (44785509223943/100000000000000 : ℝ)^3329 := by
    have hnat : (541008327 : ℕ)^4353*100000000000000^3329 ≤ 44785509223943^3329*1000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541008327 1000000000 44785509223943 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5123083/9765625 : ℝ)^4353 ≤ (10754531942987/25000000000000 : ℝ)^3329 := by
    have hnat : (5123083 : ℕ)^4353*25000000000000^3329 ≤ 10754531942987^3329*9765625^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5123083 9765625 10754531942987 25000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2000716597/10000000000 : ℝ), (541008327/1000000000 : ℝ), (5123083/9765625 : ℝ)] ![(3049090749071/25000000000000 : ℝ), (44785509223943/100000000000000 : ℝ), (10754531942987/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2000716597/10000000000 : ℝ)|^4353 ≤ (3049090749071/25000000000000 : ℝ)^3329
        have hw : |(-2000716597/10000000000 : ℝ)|=(2000716597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541008327/1000000000 : ℝ)|^4353 ≤ (44785509223943/100000000000000 : ℝ)^3329
        have hw : |(541008327/1000000000 : ℝ)|=(541008327/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5123083/9765625 : ℝ)|^4353 ≤ (10754531942987/25000000000000 : ℝ)^3329
        have hw : |(5123083/9765625 : ℝ)|=(5123083/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_s6_1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337015179/2500000000 : ℝ)*x 0 + (-13026629/62500000 : ℝ)*x 1 + (2623018533/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337015179/2500000000 : ℝ)^4353 ≤ (11028833016729/25000000000000 : ℝ)^3329 := by
    have hnat : (1337015179 : ℕ)^4353*25000000000000^3329 ≤ 11028833016729^3329*2500000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337015179 2500000000 11028833016729 25000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13026629/62500000 : ℝ)^4353 ≤ (1608317419/12500000000 : ℝ)^3329 := by
    have hnat : (13026629 : ℕ)^4353*12500000000^3329 ≤ 1608317419^3329*62500000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13026629 62500000 1608317419 12500000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623018533/5000000000 : ℝ)^4353 ≤ (43018128565411/100000000000000 : ℝ)^3329 := by
    have hnat : (2623018533 : ℕ)^4353*100000000000000^3329 ≤ 43018128565411^3329*5000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623018533 5000000000 43018128565411 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337015179/2500000000 : ℝ), (-13026629/62500000 : ℝ), (2623018533/5000000000 : ℝ)] ![(11028833016729/25000000000000 : ℝ), (1608317419/12500000000 : ℝ), (43018128565411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337015179/2500000000 : ℝ)|^4353 ≤ (11028833016729/25000000000000 : ℝ)^3329
        have hw : |(1337015179/2500000000 : ℝ)|=(1337015179/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-13026629/62500000 : ℝ)|^4353 ≤ (1608317419/12500000000 : ℝ)^3329
        have hw : |(-13026629/62500000 : ℝ)|=(13026629/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623018533/5000000000 : ℝ)|^4353 ≤ (43018128565411/100000000000000 : ℝ)^3329
        have hw : |(2623018533/5000000000 : ℝ)|=(2623018533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_s6_2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674030251/5000000000 : ℝ)*x 0 + (5246037157/10000000000 : ℝ)*x 1 + (-1042130403/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674030251/5000000000 : ℝ)^4353 ≤ (2757208109917/6250000000000 : ℝ)^3329 := by
    have hnat : (2674030251 : ℕ)^4353*6250000000000^3329 ≤ 2757208109917^3329*5000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674030251 5000000000 2757208109917 6250000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246037157/10000000000 : ℝ)^4353 ≤ (43018129541157/100000000000000 : ℝ)^3329 := by
    have hnat : (5246037157 : ℕ)^4353*100000000000000^3329 ≤ 43018129541157^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246037157 10000000000 43018129541157 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1042130403/5000000000 : ℝ)^4353 ≤ (12866540691963/100000000000000 : ℝ)^3329 := by
    have hnat : (1042130403 : ℕ)^4353*100000000000000^3329 ≤ 12866540691963^3329*5000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042130403 5000000000 12866540691963 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674030251/5000000000 : ℝ), (5246037157/10000000000 : ℝ), (-1042130403/5000000000 : ℝ)] ![(2757208109917/6250000000000 : ℝ), (43018129541157/100000000000000 : ℝ), (12866540691963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674030251/5000000000 : ℝ)|^4353 ≤ (2757208109917/6250000000000 : ℝ)^3329
        have hw : |(2674030251/5000000000 : ℝ)|=(2674030251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246037157/10000000000 : ℝ)|^4353 ≤ (43018129541157/100000000000000 : ℝ)^3329
        have hw : |(5246037157/10000000000 : ℝ)|=(5246037157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1042130403/5000000000 : ℝ)|^4353 ≤ (12866540691963/100000000000000 : ℝ)^3329
        have hw : |(-1042130403/5000000000 : ℝ)|=(1042130403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_s6_3 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (539182229/1250000000 : ℝ)*x 0 + (414159937/1000000000 : ℝ)*x 1 + (4491810949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539182229/1250000000 : ℝ)^4353 ≤ (16652059202289/50000000000000 : ℝ)^3329 := by
    have hnat : (539182229 : ℕ)^4353*50000000000000^3329 ≤ 16652059202289^3329*1250000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539182229 1250000000 16652059202289 50000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (414159937/1000000000 : ℝ)^4353 ≤ (31579775270551/100000000000000 : ℝ)^3329 := by
    have hnat : (414159937 : ℕ)^4353*100000000000000^3329 ≤ 31579775270551^3329*1000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414159937 1000000000 31579775270551 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4491810949/10000000000 : ℝ)^4353 ≤ (17558053156873/50000000000000 : ℝ)^3329 := by
    have hnat : (4491810949 : ℕ)^4353*50000000000000^3329 ≤ 17558053156873^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491810949 10000000000 17558053156873 50000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(539182229/1250000000 : ℝ), (414159937/1000000000 : ℝ), (4491810949/10000000000 : ℝ)] ![(16652059202289/50000000000000 : ℝ), (31579775270551/100000000000000 : ℝ), (17558053156873/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(539182229/1250000000 : ℝ)|^4353 ≤ (16652059202289/50000000000000 : ℝ)^3329
        have hw : |(539182229/1250000000 : ℝ)|=(539182229/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(414159937/1000000000 : ℝ)|^4353 ≤ (31579775270551/100000000000000 : ℝ)^3329
        have hw : |(414159937/1000000000 : ℝ)|=(414159937/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4491810949/10000000000 : ℝ)|^4353 ≤ (17558053156873/50000000000000 : ℝ)^3329
        have hw : |(4491810949/10000000000 : ℝ)|=(4491810949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_s6_4 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1000364197/5000000000 : ℝ)*x 0 + (655828341/1250000000 : ℝ)*x 1 + (1081898077/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1000364197/5000000000 : ℝ)^4353 ≤ (1524557128967/12500000000000 : ℝ)^3329 := by
    have hnat : (1000364197 : ℕ)^4353*12500000000000^3329 ≤ 1524557128967^3329*5000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000364197 5000000000 1524557128967 12500000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655828341/1250000000 : ℝ)^4353 ≤ (4302445131059/10000000000000 : ℝ)^3329 := by
    have hnat : (655828341 : ℕ)^4353*10000000000000^3329 ≤ 4302445131059^3329*1250000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655828341 1250000000 4302445131059 10000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081898077/2000000000 : ℝ)^4353 ≤ (44779091639651/100000000000000 : ℝ)^3329 := by
    have hnat : (1081898077 : ℕ)^4353*100000000000000^3329 ≤ 44779091639651^3329*2000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081898077 2000000000 44779091639651 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1000364197/5000000000 : ℝ), (655828341/1250000000 : ℝ), (1081898077/2000000000 : ℝ)] ![(1524557128967/12500000000000 : ℝ), (4302445131059/10000000000000 : ℝ), (44779091639651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1000364197/5000000000 : ℝ)|^4353 ≤ (1524557128967/12500000000000 : ℝ)^3329
        have hw : |(-1000364197/5000000000 : ℝ)|=(1000364197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655828341/1250000000 : ℝ)|^4353 ≤ (4302445131059/10000000000000 : ℝ)^3329
        have hw : |(655828341/1250000000 : ℝ)|=(655828341/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081898077/2000000000 : ℝ)|^4353 ≤ (44779091639651/100000000000000 : ℝ)^3329
        have hw : |(1081898077/2000000000 : ℝ)|=(1081898077/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_s6_5 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652784267/5000000000 : ℝ)*x 0 + (-960403571/5000000000 : ℝ)*x 1 + (5409490363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652784267/5000000000 : ℝ)^4353 ≤ (21828782196339/50000000000000 : ℝ)^3329 := by
    have hnat : (2652784267 : ℕ)^4353*50000000000000^3329 ≤ 21828782196339^3329*5000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652784267 5000000000 21828782196339 50000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (960403571/5000000000 : ℝ)^4353 ≤ (11563344195959/100000000000000 : ℝ)^3329 := by
    have hnat : (960403571 : ℕ)^4353*100000000000000^3329 ≤ 11563344195959^3329*5000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      960403571 5000000000 11563344195959 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409490363/10000000000 : ℝ)^4353 ≤ (559738642519/1250000000000 : ℝ)^3329 := by
    have hnat : (5409490363 : ℕ)^4353*1250000000000^3329 ≤ 559738642519^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409490363 10000000000 559738642519 1250000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652784267/5000000000 : ℝ), (-960403571/5000000000 : ℝ), (5409490363/10000000000 : ℝ)] ![(21828782196339/50000000000000 : ℝ), (11563344195959/100000000000000 : ℝ), (559738642519/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652784267/5000000000 : ℝ)|^4353 ≤ (21828782196339/50000000000000 : ℝ)^3329
        have hw : |(2652784267/5000000000 : ℝ)|=(2652784267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-960403571/5000000000 : ℝ)|^4353 ≤ (11563344195959/100000000000000 : ℝ)^3329
        have hw : |(-960403571/5000000000 : ℝ)|=(960403571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409490363/10000000000 : ℝ)|^4353 ≤ (559738642519/1250000000000 : ℝ)^3329
        have hw : |(5409490363/10000000000 : ℝ)|=(5409490363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_s6_6 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652784049/5000000000 : ℝ)*x 0 + (2704745227/5000000000 : ℝ)*x 1 + (-480201903/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652784049/5000000000 : ℝ)^4353 ≤ (2728597481339/6250000000000 : ℝ)^3329 := by
    have hnat : (2652784049 : ℕ)^4353*6250000000000^3329 ≤ 2728597481339^3329*5000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652784049 5000000000 2728597481339 6250000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704745227/5000000000 : ℝ)^4353 ≤ (44779092386517/100000000000000 : ℝ)^3329 := by
    have hnat : (2704745227 : ℕ)^4353*100000000000000^3329 ≤ 44779092386517^3329*5000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704745227 5000000000 44779092386517 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (480201903/2500000000 : ℝ)^4353 ≤ (11563347895709/100000000000000 : ℝ)^3329 := by
    have hnat : (480201903 : ℕ)^4353*100000000000000^3329 ≤ 11563347895709^3329*2500000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      480201903 2500000000 11563347895709 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652784049/5000000000 : ℝ), (2704745227/5000000000 : ℝ), (-480201903/2500000000 : ℝ)] ![(2728597481339/6250000000000 : ℝ), (44779092386517/100000000000000 : ℝ), (11563347895709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652784049/5000000000 : ℝ)|^4353 ≤ (2728597481339/6250000000000 : ℝ)^3329
        have hw : |(2652784049/5000000000 : ℝ)|=(2652784049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704745227/5000000000 : ℝ)|^4353 ≤ (44779092386517/100000000000000 : ℝ)^3329
        have hw : |(2704745227/5000000000 : ℝ)|=(2704745227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-480201903/2500000000 : ℝ)|^4353 ≤ (11563347895709/100000000000000 : ℝ)^3329
        have hw : |(-480201903/2500000000 : ℝ)|=(480201903/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_s6_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4313482663/10000000000 : ℝ)*x 0 + (4490551771/10000000000 : ℝ)*x 1 + (33142921/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4313482663/10000000000 : ℝ)^4353 ≤ (8326092274343/25000000000000 : ℝ)^3329 := by
    have hnat : (4313482663 : ℕ)^4353*25000000000000^3329 ≤ 8326092274343^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4313482663 10000000000 8326092274343 25000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4490551771/10000000000 : ℝ)^4353 ≤ (35103234843443/100000000000000 : ℝ)^3329 := by
    have hnat : (4490551771 : ℕ)^4353*100000000000000^3329 ≤ 35103234843443^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490551771 10000000000 35103234843443 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33142921/80000000 : ℝ)^4353 ≤ (7898099010373/25000000000000 : ℝ)^3329 := by
    have hnat : (33142921 : ℕ)^4353*25000000000000^3329 ≤ 7898099010373^3329*80000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33142921 80000000 7898099010373 25000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4313482663/10000000000 : ℝ), (4490551771/10000000000 : ℝ), (33142921/80000000 : ℝ)] ![(8326092274343/25000000000000 : ℝ), (35103234843443/100000000000000 : ℝ), (7898099010373/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4313482663/10000000000 : ℝ)|^4353 ≤ (8326092274343/25000000000000 : ℝ)^3329
        have hw : |(4313482663/10000000000 : ℝ)|=(4313482663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4490551771/10000000000 : ℝ)|^4353 ≤ (35103234843443/100000000000000 : ℝ)^3329
        have hw : |(4490551771/10000000000 : ℝ)|=(4490551771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(33142921/80000000 : ℝ)|^4353 ≤ (7898099010373/25000000000000 : ℝ)^3329
        have hw : |(33142921/80000000 : ℝ)|=(33142921/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1393_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156741667/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14743/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11259/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (352/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7369/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14743/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11259/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14743/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11259/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14743/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11259/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14743/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11259/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14743/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11259/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14743/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11259/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11259/100000 : ℝ) ^ (17/4 : ℝ) ≤ (9308382720901751/100000000000000000000 : ℝ) := by
    have hpowers : (11259/100000 : ℝ)^17 ≤ (9308382720901751/100000000000000000000 : ℝ)^4 := by
      have hnat : (11259 : ℕ)^17*100000000000000000000^4 ≤ 9308382720901751^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11259 100000 9308382720901751 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11259/100000 : ℝ)) (X := (9308382720901751/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have hpowhi : (14743/100000 : ℝ) ^ (17/4 : ℝ) ≤ (29274529817260467/100000000000000000000 : ℝ) := by
    have hpowers : (14743/100000 : ℝ)^17 ≤ (29274529817260467/100000000000000000000 : ℝ)^4 := by
      have hnat : (14743 : ℕ)^17*100000000000000000000^4 ≤ 29274529817260467^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14743 100000 29274529817260467 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14743/100000 : ℝ)) (X := (29274529817260467/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009308382720901751/50000000000000000000 : ℝ) ≤ (5000219005181329/5000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (50009308382720901751/50000000000000000000 : ℝ)^4 ≤ (5000219005181329/5000000000000000 : ℝ)^17 := by
      have hnat : (50009308382720901751 : ℕ)^4*5000000000000000^17 ≤ 5000219005181329^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009308382720901751 50000000000000000000 5000219005181329 5000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000219005181329/5000000000000000 : ℝ)) (X := (50009308382720901751/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have hcorner10 : (50019291456269081109/50000000000000000000 : ℝ) ≤ (2500226924835097/2500000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (50019291456269081109/50000000000000000000 : ℝ)^4 ≤ (2500226924835097/2500000000000000 : ℝ)^17 := by
      have hnat : (50019291456269081109 : ℕ)^4*2500000000000000^17 ≤ 2500226924835097^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50019291456269081109 50000000000000000000 2500226924835097 2500000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500226924835097/2500000000000000 : ℝ)) (X := (50019291456269081109/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029274529817260467/50000000000000000000 : ℝ) ≤ (5000688694159059/5000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (50029274529817260467/50000000000000000000 : ℝ)^4 ≤ (5000688694159059/5000000000000000 : ℝ)^17 := by
      have hnat : (50029274529817260467 : ℕ)^4*5000000000000000^17 ≤ 5000688694159059^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029274529817260467 50000000000000000000 5000688694159059 5000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000688694159059/5000000000000000 : ℝ)) (X := (50029274529817260467/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9308382720901751/100000000000000000000 : ℝ) ≤ ((8707737392925744083/8710000000000000000 : ℝ)+2*(46968897773/34840000000000 : ℝ)*(11259/100000 : ℝ))^(17/4 : ℝ) := by
    rw [show (8707737392925744083/8710000000000000000 : ℝ)+2*(46968897773/34840000000000 : ℝ)*(11259/100000 : ℝ)=(5000219005181329/5000000000000000 : ℝ) by norm_num, show 1+2*(9308382720901751/100000000000000000000 : ℝ)=(50009308382720901751/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29274529817260467/100000000000000000000 : ℝ)+(9308382720901751/100000000000000000000 : ℝ) ≤ ((8707737392925744083/8710000000000000000 : ℝ)+(46968897773/34840000000000 : ℝ)*((14743/100000 : ℝ)+(11259/100000 : ℝ)))^(17/4 : ℝ) := by
    rw [show (8707737392925744083/8710000000000000000 : ℝ)+(46968897773/34840000000000 : ℝ)*((14743/100000 : ℝ)+(11259/100000 : ℝ))=(2500226924835097/2500000000000000 : ℝ) by norm_num, show 1+(29274529817260467/100000000000000000000 : ℝ)+(9308382720901751/100000000000000000000 : ℝ)=(50019291456269081109/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29274529817260467/100000000000000000000 : ℝ) ≤ ((8707737392925744083/8710000000000000000 : ℝ)+2*(46968897773/34840000000000 : ℝ)*(14743/100000 : ℝ))^(17/4 : ℝ) := by
    rw [show (8707737392925744083/8710000000000000000 : ℝ)+2*(46968897773/34840000000000 : ℝ)*(14743/100000 : ℝ)=(5000688694159059/5000000000000000 : ℝ) by norm_num, show 1+2*(29274529817260467/100000000000000000000 : ℝ)=(50029274529817260467/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8707737392925744083/8710000000000000000 : ℝ)*(X 1 0+X 2 0)+(46968897773/34840000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (17/4 : ℝ)) (lo := (11259/100000 : ℝ)) (hi := (14743/100000 : ℝ)) (c := (8707737392925744083/8710000000000000000 : ℝ)) (alpha := (46968897773/34840000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8707737392925744083/8710000000000000000 : ℝ)*(X 0 1+X 2 1)+(46968897773/34840000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (17/4 : ℝ)) (lo := (11259/100000 : ℝ)) (hi := (14743/100000 : ℝ)) (c := (8707737392925744083/8710000000000000000 : ℝ)) (alpha := (46968897773/34840000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8707737392925744083/8710000000000000000 : ℝ)*(X 0 2+X 1 2)+(46968897773/34840000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (17/4 : ℝ)) (lo := (11259/100000 : ℝ)) (hi := (14743/100000 : ℝ)) (c := (8707737392925744083/8710000000000000000 : ℝ)) (alpha := (46968897773/34840000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2000716597/10000000000 : ℝ)*X 0 0+(541008327/1000000000 : ℝ)*X 0 1+(5123083/9765625 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337015179/2500000000 : ℝ)*X 1 0+(-13026629/62500000 : ℝ)*X 1 1+(2623018533/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674030251/5000000000 : ℝ)*X 2 0+(5246037157/10000000000 : ℝ)*X 2 1+(-1042130403/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((539182229/1250000000 : ℝ)*X 0 0+(414159937/1000000000 : ℝ)*X 0 1+(4491810949/10000000000 : ℝ)*X 0 2+(539182229/1250000000 : ℝ)*X 1 0+(414159937/1000000000 : ℝ)*X 1 1+(4491810949/10000000000 : ℝ)*X 1 2+(539182229/1250000000 : ℝ)*X 2 0+(414159937/1000000000 : ℝ)*X 2 1+(4491810949/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1000364197/5000000000 : ℝ)*X 0 0+(655828341/1250000000 : ℝ)*X 0 1+(1081898077/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652784267/5000000000 : ℝ)*X 1 0+(-960403571/5000000000 : ℝ)*X 1 1+(5409490363/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652784049/5000000000 : ℝ)*X 2 0+(2704745227/5000000000 : ℝ)*X 2 1+(-480201903/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4313482663/10000000000 : ℝ)*X 0 0+(4490551771/10000000000 : ℝ)*X 0 1+(33142921/80000000 : ℝ)*X 0 2+(4313482663/10000000000 : ℝ)*X 1 0+(4490551771/10000000000 : ℝ)*X 1 1+(33142921/80000000 : ℝ)*X 1 2+(4313482663/10000000000 : ℝ)*X 2 0+(4490551771/10000000000 : ℝ)*X 2 1+(33142921/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (84796127258022868920339543/16750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1486656019/100000000000000 : ℝ)*(base19) + (225342873/20000000000000 : ℝ)*(base23) + (1474309/400000000000 : ℝ)*(upper3) + (6204673/10000000000000 : ℝ)*(upper4) + (9245593/25000000000000 : ℝ)*(upper5) + (4475673347929309/100000000000000 : ℝ)*(major0) + (4475673347929309/100000000000000 : ℝ)*(major1) + (447567334792931/10000000000000 : ℝ)*(major2) + (6095877277565347/100000000000000 : ℝ)*(sp0) + (6095899239989733/100000000000000 : ℝ)*(sp1) + (3047949799965693/50000000000000 : ℝ)*(sp2) + (1427714491880971/50000000000000 : ℝ)*(sp3) + (5862270101/25000000000000 : ℝ)*(sp4) + (16816702403/100000000000000 : ℝ)*(sp7) + (1427722900232173/50000000000000 : ℝ)*(f.failure) + (6095900726645751/100000000000000 : ℝ)*(f.sum) + (32098674153/53600000000000000000000000 : ℝ)*base66 + (6941497329861528647/871000000000000000000000000000000 : ℝ)*base67 + (327759744676202273/87100000000000000000000000000000 : ℝ)*base69 + (8232900542935528647/871000000000000000000000000000000 : ℝ)*base71 + (388920774771/53600000000000000000000000 : ℝ)*base73 + (908033486903197727/87100000000000000000000000000000 : ℝ)*base76 + (8154886590268278647/871000000000000000000000000000000 : ℝ)*base77 + (14923247162618278647/871000000000000000000000000000000 : ℝ)*base79 + (1893266928843/1742000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (33052391/5000000000000000000000 : ℝ)*base89 + (33052391/5000000000000000000000 : ℝ)*base91 + (16947609/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1436182666848705835416860931/217750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (508751001/25000000000000 : ℝ)*(base19) + (1694533363/100000000000000 : ℝ)*(base23) + (38559979/25000000000000 : ℝ)*(upper2) + (15291959/6250000000000 : ℝ)*(upper3) + (36394573/12500000000000 : ℝ)*(upper5) + (4508123797773181/100000000000000 : ℝ)*(major0) + (4508123797773181/100000000000000 : ℝ)*(major1) + (4508123797773181/100000000000000 : ℝ)*(major2) + (8271365597/20000000000000 : ℝ)*(sp1) + (3193613587/12500000000000 : ℝ)*(sp2) + (3070049216630453/50000000000000 : ℝ)*(sp4) + (1535013760357229/25000000000000 : ℝ)*(sp5) + (191877224681839/3125000000000 : ℝ)*(sp6) + (2876148942433527/100000000000000 : ℝ)*(sp7) + (2876148942433527/100000000000000 : ℝ)*(f.failure) + (3070049216630453/50000000000000 : ℝ)*(f.sum) + (11279095130659/1742000000000000000000000000 : ℝ)*base65 + (2705554707530088023/871000000000000000000000000000000 : ℝ)*base67 + (2415936058730088023/871000000000000000000000000000000 : ℝ)*base69 + (5230595100210088023/871000000000000000000000000000000 : ℝ)*base71 + (3448072779923/1742000000000000000000000000 : ℝ)*base73 + (8387303273062088023/871000000000000000000000000000000 : ℝ)*base75 + (4747564550078088023/871000000000000000000000000000000 : ℝ)*base77 + (11791890756685911977/871000000000000000000000000000000 : ℝ)*base80 + (2126403308047/1742000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (41330491/10000000000000000000000 : ℝ)*base90 + (41330491/10000000000000000000000 : ℝ)*base92 + (41330491/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1393_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156741667/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14743/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11259/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (352/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7369/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1393_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1393_s7_0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2000719909/10000000000 : ℝ)*x 0 + (270502263/500000000 : ℝ)*x 1 + (5246072901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2000719909/10000000000 : ℝ)^4353 ≤ (6098194698329/50000000000000 : ℝ)^3329 := by
    have hnat : (2000719909 : ℕ)^4353*50000000000000^3329 ≤ 6098194698329^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2000719909 10000000000 6098194698329 50000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270502263/500000000 : ℝ)^4353 ≤ (44785097784579/100000000000000 : ℝ)^3329 := by
    have hnat : (270502263 : ℕ)^4353*100000000000000^3329 ≤ 44785097784579^3329*500000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270502263 500000000 44785097784579 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246072901/10000000000 : ℝ)^4353 ≤ (672164262589/1562500000000 : ℝ)^3329 := by
    have hnat : (5246072901 : ℕ)^4353*1562500000000^3329 ≤ 672164262589^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246072901 10000000000 672164262589 1562500000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2000719909/10000000000 : ℝ), (270502263/500000000 : ℝ), (5246072901/10000000000 : ℝ)] ![(6098194698329/50000000000000 : ℝ), (44785097784579/100000000000000 : ℝ), (672164262589/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2000719909/10000000000 : ℝ)|^4353 ≤ (6098194698329/50000000000000 : ℝ)^3329
        have hw : |(-2000719909/10000000000 : ℝ)|=(2000719909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270502263/500000000 : ℝ)|^4353 ≤ (44785097784579/100000000000000 : ℝ)^3329
        have hw : |(270502263/500000000 : ℝ)|=(270502263/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246072901/10000000000 : ℝ)|^4353 ≤ (672164262589/1562500000000 : ℝ)^3329
        have hw : |(5246072901/10000000000 : ℝ)|=(5246072901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_s7_1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348050827/10000000000 : ℝ)*x 0 + (-2084226339/10000000000 : ℝ)*x 1 + (1311518209/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348050827/10000000000 : ℝ)^4353 ≤ (44115225402307/100000000000000 : ℝ)^3329 := by
    have hnat : (5348050827 : ℕ)^4353*100000000000000^3329 ≤ 44115225402307^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348050827 10000000000 44115225402307 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2084226339/10000000000 : ℝ)^4353 ≤ (12866262472833/100000000000000 : ℝ)^3329 := by
    have hnat : (2084226339 : ℕ)^4353*100000000000000^3329 ≤ 12866262472833^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084226339 10000000000 12866262472833 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311518209/2500000000 : ℝ)^4353 ≤ (21509256054367/50000000000000 : ℝ)^3329 := by
    have hnat : (1311518209 : ℕ)^4353*50000000000000^3329 ≤ 21509256054367^3329*2500000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311518209 2500000000 21509256054367 50000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348050827/10000000000 : ℝ), (-2084226339/10000000000 : ℝ), (1311518209/2500000000 : ℝ)] ![(44115225402307/100000000000000 : ℝ), (12866262472833/100000000000000 : ℝ), (21509256054367/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348050827/10000000000 : ℝ)|^4353 ≤ (44115225402307/100000000000000 : ℝ)^3329
        have hw : |(5348050827/10000000000 : ℝ)|=(5348050827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2084226339/10000000000 : ℝ)|^4353 ≤ (12866262472833/100000000000000 : ℝ)^3329
        have hw : |(-2084226339/10000000000 : ℝ)|=(2084226339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311518209/2500000000 : ℝ)|^4353 ≤ (21509256054367/50000000000000 : ℝ)^3329
        have hw : |(1311518209/2500000000 : ℝ)|=(1311518209/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_s7_2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348051129/10000000000 : ℝ)*x 0 + (2623036351/5000000000 : ℝ)*x 1 + (-2084226113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348051129/10000000000 : ℝ)^4353 ≤ (22057614329867/50000000000000 : ℝ)^3329 := by
    have hnat : (5348051129 : ℕ)^4353*50000000000000^3329 ≤ 22057614329867^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348051129 10000000000 22057614329867 50000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623036351/5000000000 : ℝ)^4353 ≤ (43018510671919/100000000000000 : ℝ)^3329 := by
    have hnat : (2623036351 : ℕ)^4353*100000000000000^3329 ≤ 43018510671919^3329*5000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623036351 5000000000 43018510671919 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2084226113/10000000000 : ℝ)^4353 ≤ (3216565162139/25000000000000 : ℝ)^3329 := by
    have hnat : (2084226113 : ℕ)^4353*25000000000000^3329 ≤ 3216565162139^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084226113 10000000000 3216565162139 25000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348051129/10000000000 : ℝ), (2623036351/5000000000 : ℝ), (-2084226113/10000000000 : ℝ)] ![(22057614329867/50000000000000 : ℝ), (43018510671919/100000000000000 : ℝ), (3216565162139/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348051129/10000000000 : ℝ)|^4353 ≤ (22057614329867/50000000000000 : ℝ)^3329
        have hw : |(5348051129/10000000000 : ℝ)|=(5348051129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623036351/5000000000 : ℝ)|^4353 ≤ (43018510671919/100000000000000 : ℝ)^3329
        have hw : |(2623036351/5000000000 : ℝ)|=(2623036351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2084226113/10000000000 : ℝ)|^4353 ≤ (3216565162139/25000000000000 : ℝ)^3329
        have hw : |(-2084226113/10000000000 : ℝ)|=(2084226113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_s7_3 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (539182523/1250000000 : ℝ)*x 0 + (2070839111/5000000000 : ℝ)*x 1 + (2245865859/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539182523/1250000000 : ℝ)^4353 ≤ (16652071075129/50000000000000 : ℝ)^3329 := by
    have hnat : (539182523 : ℕ)^4353*50000000000000^3329 ≤ 16652071075129^3329*1250000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539182523 1250000000 16652071075129 50000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2070839111/5000000000 : ℝ)^4353 ≤ (15790280732349/50000000000000 : ℝ)^3329 := by
    have hnat : (2070839111 : ℕ)^4353*50000000000000^3329 ≤ 15790280732349^3329*5000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070839111 5000000000 15790280732349 50000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2245865859/5000000000 : ℝ)^4353 ≤ (280922370977/800000000000 : ℝ)^3329 := by
    have hnat : (2245865859 : ℕ)^4353*800000000000^3329 ≤ 280922370977^3329*5000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245865859 5000000000 280922370977 800000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(539182523/1250000000 : ℝ), (2070839111/5000000000 : ℝ), (2245865859/5000000000 : ℝ)] ![(16652071075129/50000000000000 : ℝ), (15790280732349/50000000000000 : ℝ), (280922370977/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(539182523/1250000000 : ℝ)|^4353 ≤ (16652071075129/50000000000000 : ℝ)^3329
        have hw : |(539182523/1250000000 : ℝ)|=(539182523/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2070839111/5000000000 : ℝ)|^4353 ≤ (15790280732349/50000000000000 : ℝ)^3329
        have hw : |(2070839111/5000000000 : ℝ)|=(2070839111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2245865859/5000000000 : ℝ)|^4353 ≤ (280922370977/800000000000 : ℝ)^3329
        have hw : |(2245865859/5000000000 : ℝ)|=(2245865859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_s7_4 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-50018291/250000000 : ℝ)*x 0 + (2623331087/5000000000 : ℝ)*x 1 + (5409452881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (50018291/250000000 : ℝ)^4353 ≤ (6098241453031/50000000000000 : ℝ)^3329 := by
    have hnat : (50018291 : ℕ)^4353*50000000000000^3329 ≤ 6098241453031^3329*250000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50018291 250000000 6098241453031 50000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623331087/5000000000 : ℝ)^4353 ≤ (43024831392963/100000000000000 : ℝ)^3329 := by
    have hnat : (2623331087 : ℕ)^4353*100000000000000^3329 ≤ 43024831392963^3329*5000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623331087 5000000000 43024831392963 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409452881/10000000000 : ℝ)^4353 ≤ (22389342845583/50000000000000 : ℝ)^3329 := by
    have hnat : (5409452881 : ℕ)^4353*50000000000000^3329 ≤ 22389342845583^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409452881 10000000000 22389342845583 50000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-50018291/250000000 : ℝ), (2623331087/5000000000 : ℝ), (5409452881/10000000000 : ℝ)] ![(6098241453031/50000000000000 : ℝ), (43024831392963/100000000000000 : ℝ), (22389342845583/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-50018291/250000000 : ℝ)|^4353 ≤ (6098241453031/50000000000000 : ℝ)^3329
        have hw : |(-50018291/250000000 : ℝ)|=(50018291/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623331087/5000000000 : ℝ)|^4353 ≤ (43024831392963/100000000000000 : ℝ)^3329
        have hw : |(2623331087/5000000000 : ℝ)|=(2623331087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409452881/10000000000 : ℝ)|^4353 ≤ (22389342845583/50000000000000 : ℝ)^3329
        have hw : |(5409452881/10000000000 : ℝ)|=(5409452881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_s7_5 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652788897/5000000000 : ℝ)*x 0 + (-1920846013/10000000000 : ℝ)*x 1 + (5409452889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652788897/5000000000 : ℝ)^4353 ≤ (873153280561/2000000000000 : ℝ)^3329 := by
    have hnat : (2652788897 : ℕ)^4353*2000000000000^3329 ≤ 873153280561^3329*5000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652788897 5000000000 873153280561 2000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1920846013/10000000000 : ℝ)^4353 ≤ (1156365018201/10000000000000 : ℝ)^3329 := by
    have hnat : (1920846013 : ℕ)^4353*10000000000000^3329 ≤ 1156365018201^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1920846013 10000000000 1156365018201 10000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409452889/10000000000 : ℝ)^4353 ≤ (44778685777759/100000000000000 : ℝ)^3329 := by
    have hnat : (5409452889 : ℕ)^4353*100000000000000^3329 ≤ 44778685777759^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409452889 10000000000 44778685777759 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652788897/5000000000 : ℝ), (-1920846013/10000000000 : ℝ), (5409452889/10000000000 : ℝ)] ![(873153280561/2000000000000 : ℝ), (1156365018201/10000000000000 : ℝ), (44778685777759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652788897/5000000000 : ℝ)|^4353 ≤ (873153280561/2000000000000 : ℝ)^3329
        have hw : |(2652788897/5000000000 : ℝ)|=(2652788897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1920846013/10000000000 : ℝ)|^4353 ≤ (1156365018201/10000000000000 : ℝ)^3329
        have hw : |(-1920846013/10000000000 : ℝ)|=(1920846013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409452889/10000000000 : ℝ)|^4353 ≤ (44778685777759/100000000000000 : ℝ)^3329
        have hw : |(5409452889/10000000000 : ℝ)|=(5409452889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_s7_6 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305577797/10000000000 : ℝ)*x 0 + (338090807/625000000 : ℝ)*x 1 + (-1920845977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305577797/10000000000 : ℝ)^4353 ≤ (4365766406033/10000000000000 : ℝ)^3329 := by
    have hnat : (5305577797 : ℕ)^4353*10000000000000^3329 ≤ 4365766406033^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305577797 10000000000 4365766406033 10000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338090807/625000000 : ℝ)^4353 ≤ (22389343013357/50000000000000 : ℝ)^3329 := by
    have hnat : (338090807 : ℕ)^4353*50000000000000^3329 ≤ 22389343013357^3329*625000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338090807 625000000 22389343013357 50000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1920845977/10000000000 : ℝ)^4353 ≤ (11563649898623/100000000000000 : ℝ)^3329 := by
    have hnat : (1920845977 : ℕ)^4353*100000000000000^3329 ≤ 11563649898623^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1920845977 10000000000 11563649898623 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305577797/10000000000 : ℝ), (338090807/625000000 : ℝ), (-1920845977/10000000000 : ℝ)] ![(4365766406033/10000000000000 : ℝ), (22389343013357/50000000000000 : ℝ), (11563649898623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305577797/10000000000 : ℝ)|^4353 ≤ (4365766406033/10000000000000 : ℝ)^3329
        have hw : |(5305577797/10000000000 : ℝ)|=(5305577797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338090807/625000000 : ℝ)|^4353 ≤ (22389343013357/50000000000000 : ℝ)^3329
        have hw : |(338090807/625000000 : ℝ)|=(338090807/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1920845977/10000000000 : ℝ)|^4353 ≤ (11563649898623/100000000000000 : ℝ)^3329
        have hw : |(-1920845977/10000000000 : ℝ)|=(1920845977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_s7_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4313485137/10000000000 : ℝ)*x 0 + (2245236867/5000000000 : ℝ)*x 1 + (828588523/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4313485137/10000000000 : ℝ)^4353 ≤ (33304394074803/100000000000000 : ℝ)^3329 := by
    have hnat : (4313485137 : ℕ)^4353*100000000000000^3329 ≤ 33304394074803^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4313485137 10000000000 33304394074803 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2245236867/5000000000 : ℝ)^4353 ≤ (3510243717629/10000000000000 : ℝ)^3329 := by
    have hnat : (2245236867 : ℕ)^4353*10000000000000^3329 ≤ 3510243717629^3329*5000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245236867 5000000000 3510243717629 10000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (828588523/2000000000 : ℝ)^4353 ≤ (15796584364199/50000000000000 : ℝ)^3329 := by
    have hnat : (828588523 : ℕ)^4353*50000000000000^3329 ≤ 15796584364199^3329*2000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      828588523 2000000000 15796584364199 50000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4313485137/10000000000 : ℝ), (2245236867/5000000000 : ℝ), (828588523/2000000000 : ℝ)] ![(33304394074803/100000000000000 : ℝ), (3510243717629/10000000000000 : ℝ), (15796584364199/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4313485137/10000000000 : ℝ)|^4353 ≤ (33304394074803/100000000000000 : ℝ)^3329
        have hw : |(4313485137/10000000000 : ℝ)|=(4313485137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2245236867/5000000000 : ℝ)|^4353 ≤ (3510243717629/10000000000000 : ℝ)^3329
        have hw : |(2245236867/5000000000 : ℝ)|=(2245236867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(828588523/2000000000 : ℝ)|^4353 ≤ (15796584364199/50000000000000 : ℝ)^3329
        have hw : |(828588523/2000000000 : ℝ)|=(828588523/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1393_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156741667/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7369/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (352/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (2253/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14737/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7369/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (352/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7369/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (352/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7369/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (352/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7369/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (352/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7369/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (352/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7369/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (352/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (352/3125 : ℝ) ^ (17/4 : ℝ) ≤ (9325963849242827/100000000000000000000 : ℝ) := by
    have hpowers : (352/3125 : ℝ)^17 ≤ (9325963849242827/100000000000000000000 : ℝ)^4 := by
      have hnat : (352 : ℕ)^17*100000000000000000000^4 ≤ 9325963849242827^4*3125^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        352 3125 9325963849242827 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (352/3125 : ℝ)) (X := (9325963849242827/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have hpowhi : (7369/50000 : ℝ) ^ (17/4 : ℝ) ≤ (29232357870583947/100000000000000000000 : ℝ) := by
    have hpowers : (7369/50000 : ℝ)^17 ≤ (29232357870583947/100000000000000000000 : ℝ)^4 := by
      have hnat : (7369 : ℕ)^17*100000000000000000000^4 ≤ 29232357870583947^4*50000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7369 50000 29232357870583947 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7369/50000 : ℝ)) (X := (29232357870583947/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009325963849242827/50000000000000000000 : ℝ) ≤ (5000219418795999/5000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (50009325963849242827/50000000000000000000 : ℝ)^4 ≤ (5000219418795999/5000000000000000 : ℝ)^17 := by
      have hnat : (50009325963849242827 : ℕ)^4*5000000000000000^17 ≤ 5000219418795999^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009325963849242827 50000000000000000000 5000219418795999 5000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000219418795999/5000000000000000 : ℝ)) (X := (50009325963849242827/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have hcorner10 : (50019279160859913387/50000000000000000000 : ℝ) ≤ (10000907120903501/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (50019279160859913387/50000000000000000000 : ℝ)^4 ≤ (10000907120903501/10000000000000000 : ℝ)^17 := by
      have hnat : (50019279160859913387 : ℕ)^4*10000000000000000^17 ≤ 10000907120903501^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50019279160859913387 50000000000000000000 10000907120903501 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000907120903501/10000000000000000 : ℝ)) (X := (50019279160859913387/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029232357870583947/50000000000000000000 : ℝ) ≤ (2500343851053751/2500000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (50029232357870583947/50000000000000000000 : ℝ)^4 ≤ (2500343851053751/2500000000000000 : ℝ)^17 := by
      have hnat : (50029232357870583947 : ℕ)^4*2500000000000000^17 ≤ 2500343851053751^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029232357870583947 50000000000000000000 2500343851053751 2500000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500343851053751/2500000000000000 : ℝ)) (X := (50029232357870583947/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9325963849242827/100000000000000000000 : ℝ) ≤ ((8682743758838265367/8685000000000000000 : ℝ)+2*(468283311503/347400000000000 : ℝ)*(352/3125 : ℝ))^(17/4 : ℝ) := by
    rw [show (8682743758838265367/8685000000000000000 : ℝ)+2*(468283311503/347400000000000 : ℝ)*(352/3125 : ℝ)=(5000219418795999/5000000000000000 : ℝ) by norm_num, show 1+2*(9325963849242827/100000000000000000000 : ℝ)=(50009325963849242827/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29232357870583947/100000000000000000000 : ℝ)+(9325963849242827/100000000000000000000 : ℝ) ≤ ((8682743758838265367/8685000000000000000 : ℝ)+(468283311503/347400000000000 : ℝ)*((7369/50000 : ℝ)+(352/3125 : ℝ)))^(17/4 : ℝ) := by
    rw [show (8682743758838265367/8685000000000000000 : ℝ)+(468283311503/347400000000000 : ℝ)*((7369/50000 : ℝ)+(352/3125 : ℝ))=(10000907120903501/10000000000000000 : ℝ) by norm_num, show 1+(29232357870583947/100000000000000000000 : ℝ)+(9325963849242827/100000000000000000000 : ℝ)=(50019279160859913387/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29232357870583947/100000000000000000000 : ℝ) ≤ ((8682743758838265367/8685000000000000000 : ℝ)+2*(468283311503/347400000000000 : ℝ)*(7369/50000 : ℝ))^(17/4 : ℝ) := by
    rw [show (8682743758838265367/8685000000000000000 : ℝ)+2*(468283311503/347400000000000 : ℝ)*(7369/50000 : ℝ)=(2500343851053751/2500000000000000 : ℝ) by norm_num, show 1+2*(29232357870583947/100000000000000000000 : ℝ)=(50029232357870583947/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8682743758838265367/8685000000000000000 : ℝ)*(X 1 0+X 2 0)+(468283311503/347400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (17/4 : ℝ)) (lo := (352/3125 : ℝ)) (hi := (7369/50000 : ℝ)) (c := (8682743758838265367/8685000000000000000 : ℝ)) (alpha := (468283311503/347400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8682743758838265367/8685000000000000000 : ℝ)*(X 0 1+X 2 1)+(468283311503/347400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (17/4 : ℝ)) (lo := (352/3125 : ℝ)) (hi := (7369/50000 : ℝ)) (c := (8682743758838265367/8685000000000000000 : ℝ)) (alpha := (468283311503/347400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8682743758838265367/8685000000000000000 : ℝ)*(X 0 2+X 1 2)+(468283311503/347400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (17/4 : ℝ)) (lo := (352/3125 : ℝ)) (hi := (7369/50000 : ℝ)) (c := (8682743758838265367/8685000000000000000 : ℝ)) (alpha := (468283311503/347400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2000719909/10000000000 : ℝ)*X 0 0+(270502263/500000000 : ℝ)*X 0 1+(5246072901/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348050827/10000000000 : ℝ)*X 1 0+(-2084226339/10000000000 : ℝ)*X 1 1+(1311518209/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348051129/10000000000 : ℝ)*X 2 0+(2623036351/5000000000 : ℝ)*X 2 1+(-2084226113/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((539182523/1250000000 : ℝ)*X 0 0+(2070839111/5000000000 : ℝ)*X 0 1+(2245865859/5000000000 : ℝ)*X 0 2+(539182523/1250000000 : ℝ)*X 1 0+(2070839111/5000000000 : ℝ)*X 1 1+(2245865859/5000000000 : ℝ)*X 1 2+(539182523/1250000000 : ℝ)*X 2 0+(2070839111/5000000000 : ℝ)*X 2 1+(2245865859/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-50018291/250000000 : ℝ)*X 0 0+(2623331087/5000000000 : ℝ)*X 0 1+(5409452881/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652788897/5000000000 : ℝ)*X 1 0+(-1920846013/10000000000 : ℝ)*X 1 1+(5409452889/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305577797/10000000000 : ℝ)*X 2 0+(338090807/625000000 : ℝ)*X 2 1+(-1920845977/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4313485137/10000000000 : ℝ)*X 0 0+(2245236867/5000000000 : ℝ)*X 0 1+(828588523/2000000000 : ℝ)*X 0 2+(4313485137/10000000000 : ℝ)*X 1 0+(2245236867/5000000000 : ℝ)*X 1 1+(828588523/2000000000 : ℝ)*X 1 2+(4313485137/10000000000 : ℝ)*X 2 0+(2245236867/5000000000 : ℝ)*X 2 1+(828588523/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4053901962758000568424427/904687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (310246359/100000000000000 : ℝ)*(base19) + (112546391/20000000000000 : ℝ)*(base23) + (34596723/50000000000000 : ℝ)*(lower2) + (48281621/50000000000000 : ℝ)*(upper5) + (2238828741415519/50000000000000 : ℝ)*(major0) + (2238828741415519/50000000000000 : ℝ)*(major1) + (13992679633847/312500000000 : ℝ)*(major2) + (3049295915969893/50000000000000 : ℝ)*(sp0) + (76232476534317/1250000000000 : ℝ)*(sp1) + (6098602590013969/100000000000000 : ℝ)*(sp2) + (571341738469913/20000000000000 : ℝ)*(sp3) + (5660403069/50000000000000 : ℝ)*(sp4) + (1179938551/25000000000000 : ℝ)*(sp5) + (742800003/25000000000000 : ℝ)*(sp7) + (2856711663549577/100000000000000 : ℝ)*(f.failure) + (1524650788186481/25000000000000 : ℝ)*(f.sum) + (11121396040639/5790000000000000000000000000 : ℝ)*base65 + (1548499654594469527/434250000000000000000000000000000 : ℝ)*base68 + (157830195946730521/10856250000000000000000000000000 : ℝ)*base69 + (1832786368023030473/434250000000000000000000000000000 : ℝ)*base71 + (525170060801/5790000000000000000000000000 : ℝ)*base74 + (212178607572830521/10856250000000000000000000000000 : ℝ)*base75 + (52899236587689497/48250000000000000000000000000000 : ℝ)*base77 + (717772434688060503/48250000000000000000000000000000 : ℝ)*base80 + (2231331243187/2171250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (36124859/10000000000000000000000 : ℝ)*base89 + (36124859/10000000000000000000000 : ℝ)*base91 + (163875141/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (34738211798176452883943/5790000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1037546691/100000000000000 : ℝ)*(base19) + (146937783/12500000000000 : ℝ)*(base23) + (353012327/100000000000000 : ℝ)*(lower1) + (64096319/50000000000000 : ℝ)*(upper3) + (53506057/100000000000000 : ℝ)*(lower4) + (86379/80000000000 : ℝ)*(upper5) + (4510131766976461/100000000000000 : ℝ)*(major0) + (4510131766976461/100000000000000 : ℝ)*(major1) + (4510131766976461/100000000000000 : ℝ)*(major2) + (4201339383/100000000000000 : ℝ)*(sp2) + (1535708330585007/25000000000000 : ℝ)*(sp4) + (6142832284793337/100000000000000 : ℝ)*(sp5) + (6142827945498381/100000000000000 : ℝ)*(sp6) + (2877430011623177/100000000000000 : ℝ)*(sp7) + (2877430011623177/100000000000000 : ℝ)*(f.failure) + (1535708330585007/25000000000000 : ℝ)*(f.sum) + (7998521763847/17370000000000000000000000000 : ℝ)*base66 + (631783262357511243/96500000000000000000000000000000 : ℝ)*base67 + (44814800623011243/96500000000000000000000000000000 : ℝ)*base69 + (7456841433712988757/96500000000000000000000000000000 : ℝ)*base72 + (20897192086807/17370000000000000000000000000 : ℝ)*base74 + (1832344137860511243/96500000000000000000000000000000 : ℝ)*base75 + (145229577111988757/96500000000000000000000000000000 : ℝ)*base78 + (266810983111488757/96500000000000000000000000000000 : ℝ)*base80 + (80395983722453/17370000000000000000000000000 : ℝ)*base81 + (38816059/10000000000000000000000 : ℝ)*base89 + (38816059/10000000000000000000000 : ℝ)*base91 + (38816059/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1393_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156741667/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7369/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (352/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2253/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14737/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1393_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1393_box_0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-918703891/5000000000 : ℝ)*x 0 + (1346947887/2500000000 : ℝ)*x 1 + (538779159/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (918703891/5000000000 : ℝ)^4353 ≤ (10911269117989/100000000000000 : ℝ)^3329 := by
    have hnat : (918703891 : ℕ)^4353*100000000000000^3329 ≤ 10911269117989^3329*5000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      918703891 5000000000 10911269117989 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1346947887/2500000000 : ℝ)^4353 ≤ (44544365208911/100000000000000 : ℝ)^3329 := by
    have hnat : (1346947887 : ℕ)^4353*100000000000000^3329 ≤ 44544365208911^3329*2500000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346947887 2500000000 44544365208911 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (538779159/1000000000 : ℝ)^4353 ≤ (11136091415741/25000000000000 : ℝ)^3329 := by
    have hnat : (538779159 : ℕ)^4353*25000000000000^3329 ≤ 11136091415741^3329*1000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538779159 1000000000 11136091415741 25000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-918703891/5000000000 : ℝ), (1346947887/2500000000 : ℝ), (538779159/1000000000 : ℝ)] ![(10911269117989/100000000000000 : ℝ), (44544365208911/100000000000000 : ℝ), (11136091415741/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-918703891/5000000000 : ℝ)|^4353 ≤ (10911269117989/100000000000000 : ℝ)^3329
        have hw : |(-918703891/5000000000 : ℝ)|=(918703891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1346947887/2500000000 : ℝ)|^4353 ≤ (44544365208911/100000000000000 : ℝ)^3329
        have hw : |(1346947887/2500000000 : ℝ)|=(1346947887/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(538779159/1000000000 : ℝ)|^4353 ≤ (11136091415741/25000000000000 : ℝ)^3329
        have hw : |(538779159/1000000000 : ℝ)|=(538779159/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_box_1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2642881001/5000000000 : ℝ)*x 0 + (-247178503/1250000000 : ℝ)*x 1 + (5387791667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642881001/5000000000 : ℝ)^4353 ≤ (5430571674547/12500000000000 : ℝ)^3329 := by
    have hnat : (2642881001 : ℕ)^4353*12500000000000^3329 ≤ 5430571674547^3329*5000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642881001 5000000000 5430571674547 12500000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (247178503/1250000000 : ℝ)^4353 ≤ (2402212018763/20000000000000 : ℝ)^3329 := by
    have hnat : (247178503 : ℕ)^4353*20000000000000^3329 ≤ 2402212018763^3329*1250000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      247178503 1250000000 2402212018763 20000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5387791667/10000000000 : ℝ)^4353 ≤ (22272183247697/50000000000000 : ℝ)^3329 := by
    have hnat : (5387791667 : ℕ)^4353*50000000000000^3329 ≤ 22272183247697^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387791667 10000000000 22272183247697 50000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642881001/5000000000 : ℝ), (-247178503/1250000000 : ℝ), (5387791667/10000000000 : ℝ)] ![(5430571674547/12500000000000 : ℝ), (2402212018763/20000000000000 : ℝ), (22272183247697/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642881001/5000000000 : ℝ)|^4353 ≤ (5430571674547/12500000000000 : ℝ)^3329
        have hw : |(2642881001/5000000000 : ℝ)|=(2642881001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-247178503/1250000000 : ℝ)|^4353 ≤ (2402212018763/20000000000000 : ℝ)^3329
        have hw : |(-247178503/1250000000 : ℝ)|=(247178503/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5387791667/10000000000 : ℝ)|^4353 ≤ (22272183247697/50000000000000 : ℝ)^3329
        have hw : |(5387791667/10000000000 : ℝ)|=(5387791667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_box_2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5285762327/10000000000 : ℝ)*x 0 + (2693895693/5000000000 : ℝ)*x 1 + (-988713983/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285762327/10000000000 : ℝ)^4353 ≤ (10861144222319/25000000000000 : ℝ)^3329 := by
    have hnat : (5285762327 : ℕ)^4353*25000000000000^3329 ≤ 10861144222319^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285762327 10000000000 10861144222319 25000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2693895693/5000000000 : ℝ)^4353 ≤ (22272181728783/50000000000000 : ℝ)^3329 := by
    have hnat : (2693895693 : ℕ)^4353*50000000000000^3329 ≤ 22272181728783^3329*5000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693895693 5000000000 22272181728783 50000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (988713983/5000000000 : ℝ)^4353 ≤ (11729550423/97656250000 : ℝ)^3329 := by
    have hnat : (988713983 : ℕ)^4353*97656250000^3329 ≤ 11729550423^3329*5000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      988713983 5000000000 11729550423 97656250000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285762327/10000000000 : ℝ), (2693895693/5000000000 : ℝ), (-988713983/5000000000 : ℝ)] ![(10861144222319/25000000000000 : ℝ), (22272181728783/50000000000000 : ℝ), (11729550423/97656250000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285762327/10000000000 : ℝ)|^4353 ≤ (10861144222319/25000000000000 : ℝ)^3329
        have hw : |(5285762327/10000000000 : ℝ)|=(5285762327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2693895693/5000000000 : ℝ)|^4353 ≤ (22272181728783/50000000000000 : ℝ)^3329
        have hw : |(2693895693/5000000000 : ℝ)|=(2693895693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-988713983/5000000000 : ℝ)|^4353 ≤ (11729550423/97656250000 : ℝ)^3329
        have hw : |(-988713983/5000000000 : ℝ)|=(988713983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_box_3 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4460502407/10000000000 : ℝ)*x 0 + (530464979/1250000000 : ℝ)*x 1 + (4243719341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4460502407/10000000000 : ℝ)^4353 ≤ (6959279290363/20000000000000 : ℝ)^3329 := by
    have hnat : (4460502407 : ℕ)^4353*20000000000000^3329 ≤ 6959279290363^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4460502407 10000000000 6959279290363 20000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (530464979/1250000000 : ℝ)^4353 ≤ (4075225529351/12500000000000 : ℝ)^3329 := by
    have hnat : (530464979 : ℕ)^4353*12500000000000^3329 ≤ 4075225529351^3329*1250000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530464979 1250000000 4075225529351 12500000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4243719341/10000000000 : ℝ)^4353 ≤ (32601799302487/100000000000000 : ℝ)^3329 := by
    have hnat : (4243719341 : ℕ)^4353*100000000000000^3329 ≤ 32601799302487^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4243719341 10000000000 32601799302487 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4460502407/10000000000 : ℝ), (530464979/1250000000 : ℝ), (4243719341/10000000000 : ℝ)] ![(6959279290363/20000000000000 : ℝ), (4075225529351/12500000000000 : ℝ), (32601799302487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4460502407/10000000000 : ℝ)|^4353 ≤ (6959279290363/20000000000000 : ℝ)^3329
        have hw : |(4460502407/10000000000 : ℝ)|=(4460502407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(530464979/1250000000 : ℝ)|^4353 ≤ (4075225529351/12500000000000 : ℝ)^3329
        have hw : |(530464979/1250000000 : ℝ)|=(530464979/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4243719341/10000000000 : ℝ)|^4353 ≤ (32601799302487/100000000000000 : ℝ)^3329
        have hw : |(4243719341/10000000000 : ℝ)|=(4243719341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_box_4 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2166774039/10000000000 : ℝ)*x 0 + (526594301/1000000000 : ℝ)*x 1 + (5265943029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2166774039/10000000000 : ℝ)^4353 ≤ (13536611780969/100000000000000 : ℝ)^3329 := by
    have hnat : (2166774039 : ℕ)^4353*100000000000000^3329 ≤ 13536611780969^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166774039 10000000000 13536611780969 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526594301/1000000000 : ℝ)^4353 ≤ (21615846999737/50000000000000 : ℝ)^3329 := by
    have hnat : (526594301 : ℕ)^4353*50000000000000^3329 ≤ 21615846999737^3329*1000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526594301 1000000000 21615846999737 50000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265943029/10000000000 : ℝ)^4353 ≤ (43231694203439/100000000000000 : ℝ)^3329 := by
    have hnat : (5265943029 : ℕ)^4353*100000000000000^3329 ≤ 43231694203439^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265943029 10000000000 43231694203439 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2166774039/10000000000 : ℝ), (526594301/1000000000 : ℝ), (5265943029/10000000000 : ℝ)] ![(13536611780969/100000000000000 : ℝ), (21615846999737/50000000000000 : ℝ), (43231694203439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2166774039/10000000000 : ℝ)|^4353 ≤ (13536611780969/100000000000000 : ℝ)^3329
        have hw : |(-2166774039/10000000000 : ℝ)|=(2166774039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526594301/1000000000 : ℝ)|^4353 ≤ (21615846999737/50000000000000 : ℝ)^3329
        have hw : |(526594301/1000000000 : ℝ)|=(526594301/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265943029/10000000000 : ℝ)|^4353 ≤ (43231694203439/100000000000000 : ℝ)^3329
        have hw : |(5265943029/10000000000 : ℝ)|=(5265943029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_box_5 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5371163973/10000000000 : ℝ)*x 0 + (-405333019/2000000000 : ℝ)*x 1 + (164560717/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5371163973/10000000000 : ℝ)^4353 ≤ (2772793350363/6250000000000 : ℝ)^3329 := by
    have hnat : (5371163973 : ℕ)^4353*6250000000000^3329 ≤ 2772793350363^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5371163973 10000000000 2772793350363 6250000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (405333019/2000000000 : ℝ)^4353 ≤ (12403613084421/100000000000000 : ℝ)^3329 := by
    have hnat : (405333019 : ℕ)^4353*100000000000000^3329 ≤ 12403613084421^3329*2000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      405333019 2000000000 12403613084421 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164560717/312500000 : ℝ)^4353 ≤ (21615846645483/50000000000000 : ℝ)^3329 := by
    have hnat : (164560717 : ℕ)^4353*50000000000000^3329 ≤ 21615846645483^3329*312500000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164560717 312500000 21615846645483 50000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5371163973/10000000000 : ℝ), (-405333019/2000000000 : ℝ), (164560717/312500000 : ℝ)] ![(2772793350363/6250000000000 : ℝ), (12403613084421/100000000000000 : ℝ), (21615846645483/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5371163973/10000000000 : ℝ)|^4353 ≤ (2772793350363/6250000000000 : ℝ)^3329
        have hw : |(5371163973/10000000000 : ℝ)|=(5371163973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-405333019/2000000000 : ℝ)|^4353 ≤ (12403613084421/100000000000000 : ℝ)^3329
        have hw : |(-405333019/2000000000 : ℝ)|=(405333019/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164560717/312500000 : ℝ)|^4353 ≤ (21615846645483/50000000000000 : ℝ)^3329
        have hw : |(164560717/312500000 : ℝ)|=(164560717/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_box_6 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167848873/312500000 : ℝ)*x 0 + (658242873/1250000000 : ℝ)*x 1 + (-2026665091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167848873/312500000 : ℝ)^4353 ≤ (44364693206189/100000000000000 : ℝ)^3329 := by
    have hnat : (167848873 : ℕ)^4353*100000000000000^3329 ≤ 44364693206189^3329*312500000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167848873 312500000 44364693206189 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658242873/1250000000 : ℝ)^4353 ≤ (8646338744073/20000000000000 : ℝ)^3329 := by
    have hnat : (658242873 : ℕ)^4353*20000000000000^3329 ≤ 8646338744073^3329*1250000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658242873 1250000000 8646338744073 20000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2026665091/10000000000 : ℝ)^4353 ≤ (12403613052409/100000000000000 : ℝ)^3329 := by
    have hnat : (2026665091 : ℕ)^4353*100000000000000^3329 ≤ 12403613052409^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2026665091 10000000000 12403613052409 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167848873/312500000 : ℝ), (658242873/1250000000 : ℝ), (-2026665091/10000000000 : ℝ)] ![(44364693206189/100000000000000 : ℝ), (8646338744073/20000000000000 : ℝ), (12403613052409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167848873/312500000 : ℝ)|^4353 ≤ (44364693206189/100000000000000 : ℝ)^3329
        have hw : |(167848873/312500000 : ℝ)|=(167848873/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658242873/1250000000 : ℝ)|^4353 ≤ (8646338744073/20000000000000 : ℝ)^3329
        have hw : |(658242873/1250000000 : ℝ)|=(658242873/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2026665091/10000000000 : ℝ)|^4353 ≤ (12403613052409/100000000000000 : ℝ)^3329
        have hw : |(-2026665091/10000000000 : ℝ)|=(2026665091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_box_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4165419253/10000000000 : ℝ)*x 0 + (4391209209/10000000000 : ℝ)*x 1 + (4391209201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4165419253/10000000000 : ℝ)^4353 ≤ (15908740302221/50000000000000 : ℝ)^3329 := by
    have hnat : (4165419253 : ℕ)^4353*50000000000000^3329 ≤ 15908740302221^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4165419253 10000000000 15908740302221 50000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4391209209/10000000000 : ℝ)^4353 ≤ (34091259729731/100000000000000 : ℝ)^3329 := by
    have hnat : (4391209209 : ℕ)^4353*100000000000000^3329 ≤ 34091259729731^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4391209209 10000000000 34091259729731 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4391209201/10000000000 : ℝ)^4353 ≤ (17045629824259/50000000000000 : ℝ)^3329 := by
    have hnat : (4391209201 : ℕ)^4353*50000000000000^3329 ≤ 17045629824259^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4391209201 10000000000 17045629824259 50000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4165419253/10000000000 : ℝ), (4391209209/10000000000 : ℝ), (4391209201/10000000000 : ℝ)] ![(15908740302221/50000000000000 : ℝ), (34091259729731/100000000000000 : ℝ), (17045629824259/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4165419253/10000000000 : ℝ)|^4353 ≤ (15908740302221/50000000000000 : ℝ)^3329
        have hw : |(4165419253/10000000000 : ℝ)|=(4165419253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4391209209/10000000000 : ℝ)|^4353 ≤ (34091259729731/100000000000000 : ℝ)^3329
        have hw : |(4391209209/10000000000 : ℝ)|=(4391209209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4391209201/10000000000 : ℝ)|^4353 ≤ (17045629824259/50000000000000 : ℝ)^3329
        have hw : |(4391209201/10000000000 : ℝ)|=(4391209201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_box_8 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2097481959/10000000000 : ℝ)*x 0 + (1295456079/2500000000 : ℝ)*x 1 + (270089337/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2097481959/10000000000 : ℝ)^4353 ≤ (12973366654297/100000000000000 : ℝ)^3329 := by
    have hnat : (2097481959 : ℕ)^4353*100000000000000^3329 ≤ 12973366654297^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097481959 10000000000 12973366654297 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1295456079/2500000000 : ℝ)^4353 ≤ (42330908829853/100000000000000 : ℝ)^3329 := by
    have hnat : (1295456079 : ℕ)^4353*100000000000000^3329 ≤ 42330908829853^3329*2500000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295456079 2500000000 42330908829853 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270089337/500000000 : ℝ)^4353 ≤ (44695724500937/100000000000000 : ℝ)^3329 := by
    have hnat : (270089337 : ℕ)^4353*100000000000000^3329 ≤ 44695724500937^3329*500000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270089337 500000000 44695724500937 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2097481959/10000000000 : ℝ), (1295456079/2500000000 : ℝ), (270089337/500000000 : ℝ)] ![(12973366654297/100000000000000 : ℝ), (42330908829853/100000000000000 : ℝ), (44695724500937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2097481959/10000000000 : ℝ)|^4353 ≤ (12973366654297/100000000000000 : ℝ)^3329
        have hw : |(-2097481959/10000000000 : ℝ)|=(2097481959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1295456079/2500000000 : ℝ)|^4353 ≤ (42330908829853/100000000000000 : ℝ)^3329
        have hw : |(1295456079/2500000000 : ℝ)|=(1295456079/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270089337/500000000 : ℝ)|^4353 ≤ (44695724500937/100000000000000 : ℝ)^3329
        have hw : |(270089337/500000000 : ℝ)|=(270089337/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_box_9 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055189927/2000000000 : ℝ)*x 0 + (-1971643823/10000000000 : ℝ)*x 1 + (675223219/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055189927/2000000000 : ℝ)^4353 ≤ (8667829246623/20000000000000 : ℝ)^3329 := by
    have hnat : (1055189927 : ℕ)^4353*20000000000000^3329 ≤ 8667829246623^3329*2000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055189927 2000000000 8667829246623 20000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1971643823/10000000000 : ℝ)^4353 ≤ (186955311543/1562500000000 : ℝ)^3329 := by
    have hnat : (1971643823 : ℕ)^4353*1562500000000^3329 ≤ 186955311543^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1971643823 10000000000 186955311543 1562500000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (675223219/1250000000 : ℝ)^4353 ≤ (11173928452841/25000000000000 : ℝ)^3329 := by
    have hnat : (675223219 : ℕ)^4353*25000000000000^3329 ≤ 11173928452841^3329*1250000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675223219 1250000000 11173928452841 25000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055189927/2000000000 : ℝ), (-1971643823/10000000000 : ℝ), (675223219/1250000000 : ℝ)] ![(8667829246623/20000000000000 : ℝ), (186955311543/1562500000000 : ℝ), (11173928452841/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055189927/2000000000 : ℝ)|^4353 ≤ (8667829246623/20000000000000 : ℝ)^3329
        have hw : |(1055189927/2000000000 : ℝ)|=(1055189927/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1971643823/10000000000 : ℝ)|^4353 ≤ (186955311543/1562500000000 : ℝ)^3329
        have hw : |(-1971643823/10000000000 : ℝ)|=(1971643823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(675223219/1250000000 : ℝ)|^4353 ≤ (11173928452841/25000000000000 : ℝ)^3329
        have hw : |(675223219/1250000000 : ℝ)|=(675223219/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_box_10 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055189789/2000000000 : ℝ)*x 0 + (2700893199/5000000000 : ℝ)*x 1 + (-1971643877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055189789/2000000000 : ℝ)^4353 ≤ (43339138821657/100000000000000 : ℝ)^3329 := by
    have hnat : (1055189789 : ℕ)^4353*100000000000000^3329 ≤ 43339138821657^3329*2000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055189789 2000000000 43339138821657 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2700893199/5000000000 : ℝ)^4353 ≤ (446957208007/1000000000000 : ℝ)^3329 := by
    have hnat : (2700893199 : ℕ)^4353*1000000000000^3329 ≤ 446957208007^3329*5000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700893199 5000000000 446957208007 1000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1971643877/10000000000 : ℝ)^4353 ≤ (11965140367259/100000000000000 : ℝ)^3329 := by
    have hnat : (1971643877 : ℕ)^4353*100000000000000^3329 ≤ 11965140367259^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1971643877 10000000000 11965140367259 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055189789/2000000000 : ℝ), (2700893199/5000000000 : ℝ), (-1971643877/10000000000 : ℝ)] ![(43339138821657/100000000000000 : ℝ), (446957208007/1000000000000 : ℝ), (11965140367259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055189789/2000000000 : ℝ)|^4353 ≤ (43339138821657/100000000000000 : ℝ)^3329
        have hw : |(1055189789/2000000000 : ℝ)|=(1055189789/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2700893199/5000000000 : ℝ)|^4353 ≤ (446957208007/1000000000000 : ℝ)^3329
        have hw : |(2700893199/5000000000 : ℝ)|=(2700893199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1971643877/10000000000 : ℝ)|^4353 ≤ (11965140367259/100000000000000 : ℝ)^3329
        have hw : |(-1971643877/10000000000 : ℝ)|=(1971643877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_box_11 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4493835967/10000000000 : ℝ)*x 0 + (845353011/2000000000 : ℝ)*x 1 + (264172881/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4493835967/10000000000 : ℝ)^4353 ≤ (87842021553/250000000000 : ℝ)^3329 := by
    have hnat : (4493835967 : ℕ)^4353*250000000000^3329 ≤ 87842021553^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493835967 10000000000 87842021553 250000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (845353011/2000000000 : ℝ)^4353 ≤ (1297263618529/4000000000000 : ℝ)^3329 := by
    have hnat : (845353011 : ℕ)^4353*4000000000000^3329 ≤ 1297263618529^3329*2000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845353011 2000000000 1297263618529 4000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (264172881/625000000 : ℝ)^4353 ≤ (32431600907679/100000000000000 : ℝ)^3329 := by
    have hnat : (264172881 : ℕ)^4353*100000000000000^3329 ≤ 32431600907679^3329*625000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264172881 625000000 32431600907679 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4493835967/10000000000 : ℝ), (845353011/2000000000 : ℝ), (264172881/625000000 : ℝ)] ![(87842021553/250000000000 : ℝ), (1297263618529/4000000000000 : ℝ), (32431600907679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4493835967/10000000000 : ℝ)|^4353 ≤ (87842021553/250000000000 : ℝ)^3329
        have hw : |(4493835967/10000000000 : ℝ)|=(4493835967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(845353011/2000000000 : ℝ)|^4353 ≤ (1297263618529/4000000000000 : ℝ)^3329
        have hw : |(845353011/2000000000 : ℝ)|=(845353011/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(264172881/625000000 : ℝ)|^4353 ≤ (32431600907679/100000000000000 : ℝ)^3329
        have hw : |(264172881/625000000 : ℝ)|=(264172881/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_box_12 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-953471401/5000000000 : ℝ)*x 0 + (1367453599/2500000000 : ℝ)*x 1 + (525483673/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (953471401/5000000000 : ℝ)^4353 ≤ (11454328114293/100000000000000 : ℝ)^3329 := by
    have hnat : (953471401 : ℕ)^4353*100000000000000^3329 ≤ 11454328114293^3329*5000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      953471401 5000000000 11454328114293 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1367453599/2500000000 : ℝ)^4353 ≤ (908663295909/2000000000000 : ℝ)^3329 := by
    have hnat : (1367453599 : ℕ)^4353*2000000000000^3329 ≤ 908663295909^3329*2500000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367453599 2500000000 908663295909 2000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (525483673/1000000000 : ℝ)^4353 ≤ (10778126768103/25000000000000 : ℝ)^3329 := by
    have hnat : (525483673 : ℕ)^4353*25000000000000^3329 ≤ 10778126768103^3329*1000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525483673 1000000000 10778126768103 25000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-953471401/5000000000 : ℝ), (1367453599/2500000000 : ℝ), (525483673/1000000000 : ℝ)] ![(11454328114293/100000000000000 : ℝ), (908663295909/2000000000000 : ℝ), (10778126768103/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-953471401/5000000000 : ℝ)|^4353 ≤ (11454328114293/100000000000000 : ℝ)^3329
        have hw : |(-953471401/5000000000 : ℝ)|=(953471401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1367453599/2500000000 : ℝ)|^4353 ≤ (908663295909/2000000000000 : ℝ)^3329
        have hw : |(1367453599/2500000000 : ℝ)|=(1367453599/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(525483673/1000000000 : ℝ)|^4353 ≤ (10778126768103/25000000000000 : ℝ)^3329
        have hw : |(525483673/1000000000 : ℝ)|=(525483673/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_box_13 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5378945579/10000000000 : ℝ)*x 0 + (-2031051821/10000000000 : ℝ)*x 1 + (5254837153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378945579/10000000000 : ℝ)^4353 ≤ (44448757578953/100000000000000 : ℝ)^3329 := by
    have hnat : (5378945579 : ℕ)^4353*100000000000000^3329 ≤ 44448757578953^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378945579 10000000000 44448757578953 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2031051821/10000000000 : ℝ)^4353 ≤ (2487746157203/20000000000000 : ℝ)^3329 := by
    have hnat : (2031051821 : ℕ)^4353*20000000000000^3329 ≤ 2487746157203^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2031051821 10000000000 2487746157203 20000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254837153/10000000000 : ℝ)^4353 ≤ (21556255805179/50000000000000 : ℝ)^3329 := by
    have hnat : (5254837153 : ℕ)^4353*50000000000000^3329 ≤ 21556255805179^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254837153 10000000000 21556255805179 50000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378945579/10000000000 : ℝ), (-2031051821/10000000000 : ℝ), (5254837153/10000000000 : ℝ)] ![(44448757578953/100000000000000 : ℝ), (2487746157203/20000000000000 : ℝ), (21556255805179/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378945579/10000000000 : ℝ)|^4353 ≤ (44448757578953/100000000000000 : ℝ)^3329
        have hw : |(5378945579/10000000000 : ℝ)|=(5378945579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2031051821/10000000000 : ℝ)|^4353 ≤ (2487746157203/20000000000000 : ℝ)^3329
        have hw : |(-2031051821/10000000000 : ℝ)|=(2031051821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254837153/10000000000 : ℝ)|^4353 ≤ (21556255805179/50000000000000 : ℝ)^3329
        have hw : |(5254837153/10000000000 : ℝ)|=(5254837153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_box_14 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2689472909/5000000000 : ℝ)*x 0 + (5254837591/10000000000 : ℝ)*x 1 + (-1015525457/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2689472909/5000000000 : ℝ)^4353 ≤ (44448760161423/100000000000000 : ℝ)^3329 := by
    have hnat : (2689472909 : ℕ)^4353*100000000000000^3329 ≤ 44448760161423^3329*5000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689472909 5000000000 44448760161423 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5254837591/10000000000 : ℝ)^4353 ≤ (5389064538653/12500000000000 : ℝ)^3329 := by
    have hnat : (5254837591 : ℕ)^4353*12500000000000^3329 ≤ 5389064538653^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254837591 10000000000 5389064538653 12500000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1015525457/5000000000 : ℝ)^4353 ≤ (12438723522661/100000000000000 : ℝ)^3329 := by
    have hnat : (1015525457 : ℕ)^4353*100000000000000^3329 ≤ 12438723522661^3329*5000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1015525457 5000000000 12438723522661 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2689472909/5000000000 : ℝ), (5254837591/10000000000 : ℝ), (-1015525457/5000000000 : ℝ)] ![(44448760161423/100000000000000 : ℝ), (5389064538653/12500000000000 : ℝ), (12438723522661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2689472909/5000000000 : ℝ)|^4353 ≤ (44448760161423/100000000000000 : ℝ)^3329
        have hw : |(2689472909/5000000000 : ℝ)|=(2689472909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5254837591/10000000000 : ℝ)|^4353 ≤ (5389064538653/12500000000000 : ℝ)^3329
        have hw : |(5254837591/10000000000 : ℝ)|=(5254837591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1015525457/5000000000 : ℝ)|^4353 ≤ (12438723522661/100000000000000 : ℝ)^3329
        have hw : |(-1015525457/5000000000 : ℝ)|=(1015525457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_box_15 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (206903711/500000000 : ℝ)*x 0 + (2202320623/5000000000 : ℝ)*x 1 + (4404641933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (206903711/500000000 : ℝ)^4353 ≤ (1577231622741/5000000000000 : ℝ)^3329 := by
    have hnat : (206903711 : ℕ)^4353*5000000000000^3329 ≤ 1577231622741^3329*500000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206903711 500000000 1577231622741 5000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2202320623/5000000000 : ℝ)^4353 ≤ (34227680279173/100000000000000 : ℝ)^3329 := by
    have hnat : (2202320623 : ℕ)^4353*100000000000000^3329 ≤ 34227680279173^3329*5000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2202320623 5000000000 34227680279173 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4404641933/10000000000 : ℝ)^4353 ≤ (17113843629933/50000000000000 : ℝ)^3329 := by
    have hnat : (4404641933 : ℕ)^4353*50000000000000^3329 ≤ 17113843629933^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4404641933 10000000000 17113843629933 50000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(206903711/500000000 : ℝ), (2202320623/5000000000 : ℝ), (4404641933/10000000000 : ℝ)] ![(1577231622741/5000000000000 : ℝ), (34227680279173/100000000000000 : ℝ), (17113843629933/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(206903711/500000000 : ℝ)|^4353 ≤ (1577231622741/5000000000000 : ℝ)^3329
        have hw : |(206903711/500000000 : ℝ)|=(206903711/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2202320623/5000000000 : ℝ)|^4353 ≤ (34227680279173/100000000000000 : ℝ)^3329
        have hw : |(2202320623/5000000000 : ℝ)|=(2202320623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4404641933/10000000000 : ℝ)|^4353 ≤ (17113843629933/50000000000000 : ℝ)^3329
        have hw : |(4404641933/10000000000 : ℝ)|=(4404641933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1393_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156741667/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14737/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2253/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62879/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59041/100000 : ℝ) ∧ (10031/12500 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84549/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14737/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2253/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14737/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2253/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14737/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2253/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14737/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2253/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14737/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2253/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14737/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2253/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2253/20000 : ℝ) ^ (17/4 : ℝ) ≤ (1166185389988027/12500000000000000000 : ℝ) := by
    have hpowers : (2253/20000 : ℝ)^17 ≤ (1166185389988027/12500000000000000000 : ℝ)^4 := by
      have hnat : (2253 : ℕ)^17*12500000000000000000^4 ≤ 1166185389988027^4*20000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2253 20000 1166185389988027 12500000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2253/20000 : ℝ)) (X := (1166185389988027/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have hpowhi : (14737/100000 : ℝ) ^ (17/4 : ℝ) ≤ (5844785811824509/20000000000000000000 : ℝ) := by
    have hpowers : (14737/100000 : ℝ)^17 ≤ (5844785811824509/20000000000000000000 : ℝ)^4 := by
      have hnat : (14737 : ℕ)^17*20000000000000000000^4 ≤ 5844785811824509^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14737 100000 5844785811824509 20000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14737/100000 : ℝ)) (X := (5844785811824509/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251166185389988027/6250000000000000000 : ℝ) ≤ (10000439003181113/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (6251166185389988027/6250000000000000000 : ℝ)^4 ≤ (10000439003181113/10000000000000000 : ℝ)^17 := by
      have hnat : (6251166185389988027 : ℕ)^4*10000000000000000^17 ≤ 10000439003181113^17*6250000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251166185389988027 6250000000000000000 10000439003181113 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000439003181113/10000000000000000 : ℝ)) (X := (6251166185389988027/6250000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have hcorner10 : (100038553412179026761/100000000000000000000 : ℝ) ≤ (10000907005418941/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (100038553412179026761/100000000000000000000 : ℝ)^4 ≤ (10000907005418941/10000000000000000 : ℝ)^17 := by
      have hnat : (100038553412179026761 : ℕ)^4*10000000000000000^17 ≤ 10000907005418941^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100038553412179026761 100000000000000000000 10000907005418941 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000907005418941/10000000000000000 : ℝ)) (X := (100038553412179026761/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have hcorner11 : (10005844785811824509/10000000000000000000 : ℝ) ≤ (10001375007656769/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (10005844785811824509/10000000000000000000 : ℝ)^4 ≤ (10001375007656769/10000000000000000 : ℝ)^17 := by
      have hnat : (10005844785811824509 : ℕ)^4*10000000000000000^17 ≤ 10001375007656769^17*10000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005844785811824509 10000000000000000000 10001375007656769 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001375007656769/10000000000000000 : ℝ)) (X := (10005844785811824509/10000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1166185389988027/12500000000000000000 : ℝ) ≤ ((4338872516078319937/4340000000000000000 : ℝ)+2*(117000559457/86800000000000 : ℝ)*(2253/20000 : ℝ))^(17/4 : ℝ) := by
    rw [show (4338872516078319937/4340000000000000000 : ℝ)+2*(117000559457/86800000000000 : ℝ)*(2253/20000 : ℝ)=(10000439003181113/10000000000000000 : ℝ) by norm_num, show 1+2*(1166185389988027/12500000000000000000 : ℝ)=(6251166185389988027/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5844785811824509/20000000000000000000 : ℝ)+(1166185389988027/12500000000000000000 : ℝ) ≤ ((4338872516078319937/4340000000000000000 : ℝ)+(117000559457/86800000000000 : ℝ)*((14737/100000 : ℝ)+(2253/20000 : ℝ)))^(17/4 : ℝ) := by
    rw [show (4338872516078319937/4340000000000000000 : ℝ)+(117000559457/86800000000000 : ℝ)*((14737/100000 : ℝ)+(2253/20000 : ℝ))=(10000907005418941/10000000000000000 : ℝ) by norm_num, show 1+(5844785811824509/20000000000000000000 : ℝ)+(1166185389988027/12500000000000000000 : ℝ)=(100038553412179026761/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5844785811824509/20000000000000000000 : ℝ) ≤ ((4338872516078319937/4340000000000000000 : ℝ)+2*(117000559457/86800000000000 : ℝ)*(14737/100000 : ℝ))^(17/4 : ℝ) := by
    rw [show (4338872516078319937/4340000000000000000 : ℝ)+2*(117000559457/86800000000000 : ℝ)*(14737/100000 : ℝ)=(10001375007656769/10000000000000000 : ℝ) by norm_num, show 1+2*(5844785811824509/20000000000000000000 : ℝ)=(10005844785811824509/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4338872516078319937/4340000000000000000 : ℝ)*(X 1 0+X 2 0)+(117000559457/86800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (17/4 : ℝ)) (lo := (2253/20000 : ℝ)) (hi := (14737/100000 : ℝ)) (c := (4338872516078319937/4340000000000000000 : ℝ)) (alpha := (117000559457/86800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4338872516078319937/4340000000000000000 : ℝ)*(X 0 1+X 2 1)+(117000559457/86800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (17/4 : ℝ)) (lo := (2253/20000 : ℝ)) (hi := (14737/100000 : ℝ)) (c := (4338872516078319937/4340000000000000000 : ℝ)) (alpha := (117000559457/86800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4338872516078319937/4340000000000000000 : ℝ)*(X 0 2+X 1 2)+(117000559457/86800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (17/4 : ℝ)) (lo := (2253/20000 : ℝ)) (hi := (14737/100000 : ℝ)) (c := (4338872516078319937/4340000000000000000 : ℝ)) (alpha := (117000559457/86800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-918703891/5000000000 : ℝ)*X 0 0+(1346947887/2500000000 : ℝ)*X 0 1+(538779159/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2642881001/5000000000 : ℝ)*X 1 0+(-247178503/1250000000 : ℝ)*X 1 1+(5387791667/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5285762327/10000000000 : ℝ)*X 2 0+(2693895693/5000000000 : ℝ)*X 2 1+(-988713983/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4460502407/10000000000 : ℝ)*X 0 0+(530464979/1250000000 : ℝ)*X 0 1+(4243719341/10000000000 : ℝ)*X 0 2+(4460502407/10000000000 : ℝ)*X 1 0+(530464979/1250000000 : ℝ)*X 1 1+(4243719341/10000000000 : ℝ)*X 1 2+(4460502407/10000000000 : ℝ)*X 2 0+(530464979/1250000000 : ℝ)*X 2 1+(4243719341/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2166774039/10000000000 : ℝ)*X 0 0+(526594301/1000000000 : ℝ)*X 0 1+(5265943029/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5371163973/10000000000 : ℝ)*X 1 0+(-405333019/2000000000 : ℝ)*X 1 1+(164560717/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((167848873/312500000 : ℝ)*X 2 0+(658242873/1250000000 : ℝ)*X 2 1+(-2026665091/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4165419253/10000000000 : ℝ)*X 0 0+(4391209209/10000000000 : ℝ)*X 0 1+(4391209201/10000000000 : ℝ)*X 0 2+(4165419253/10000000000 : ℝ)*X 1 0+(4391209209/10000000000 : ℝ)*X 1 1+(4391209201/10000000000 : ℝ)*X 1 2+(4165419253/10000000000 : ℝ)*X 2 0+(4391209209/10000000000 : ℝ)*X 2 1+(4391209201/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2097481959/10000000000 : ℝ)*X 0 0+(1295456079/2500000000 : ℝ)*X 0 1+(270089337/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1055189927/2000000000 : ℝ)*X 1 0+(-1971643823/10000000000 : ℝ)*X 1 1+(675223219/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1055189789/2000000000 : ℝ)*X 2 0+(2700893199/5000000000 : ℝ)*X 2 1+(-1971643877/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4493835967/10000000000 : ℝ)*X 0 0+(845353011/2000000000 : ℝ)*X 0 1+(264172881/625000000 : ℝ)*X 0 2+(4493835967/10000000000 : ℝ)*X 1 0+(845353011/2000000000 : ℝ)*X 1 1+(264172881/625000000 : ℝ)*X 1 2+(4493835967/10000000000 : ℝ)*X 2 0+(845353011/2000000000 : ℝ)*X 2 1+(264172881/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-953471401/5000000000 : ℝ)*X 0 0+(1367453599/2500000000 : ℝ)*X 0 1+(525483673/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5378945579/10000000000 : ℝ)*X 1 0+(-2031051821/10000000000 : ℝ)*X 1 1+(5254837153/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2689472909/5000000000 : ℝ)*X 2 0+(5254837591/10000000000 : ℝ)*X 2 1+(-1015525457/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((206903711/500000000 : ℝ)*X 0 0+(2202320623/5000000000 : ℝ)*X 0 1+(4404641933/10000000000 : ℝ)*X 0 2+(206903711/500000000 : ℝ)*X 1 0+(2202320623/5000000000 : ℝ)*X 1 1+(4404641933/10000000000 : ℝ)*X 1 2+(206903711/500000000 : ℝ)*X 2 0+(2202320623/5000000000 : ℝ)*X 2 1+(4404641933/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62879/100000 : ℝ) ≤ (-68220785512504014532175434181649/108500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1203523/12500000000000 : ℝ)*(lower0) + (24755491/100000000000000 : ℝ)*(lower2) + (7019277/50000000000000 : ℝ)*(lower3) + (4291307/12500000000000 : ℝ)*(lower4) + (3737173/50000000000000 : ℝ)*(lower5) + (1488679295964859/50000000000000 : ℝ)*(major0) + (1488679295964859/50000000000000 : ℝ)*(major1) + (1488679295964859/50000000000000 : ℝ)*(major2) + (1691332211/100000000000000 : ℝ)*(sp1) + (523265471/50000000000000 : ℝ)*(sp2) + (1019035912679333/25000000000000 : ℝ)*(sp4) + (25475887246157/625000000000 : ℝ)*(sp5) + (407614260418639/10000000000000 : ℝ)*(sp6) + (1899532299812607/100000000000000 : ℝ)*(sp7) + (1899532299812607/100000000000000 : ℝ)*(f.failure) + (1019035912679333/25000000000000 : ℝ)*(f.sum) + (757791490347/2170000000000000000000000000 : ℝ)*base66 + (1883819983478243883/217000000000000000000000000000000 : ℝ)*base67 + (9641390605756117/217000000000000000000000000000000 : ℝ)*base70 + (3240459808788243883/217000000000000000000000000000000 : ℝ)*base71 + (12791576155733/2170000000000000000000000000 : ℝ)*base73 + (1183381124981243883/217000000000000000000000000000000 : ℝ)*base75 + (755535492775756117/217000000000000000000000000000000 : ℝ)*base78 + (146169904194243883/217000000000000000000000000000000 : ℝ)*base79 + (2315399568913/2170000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (8795869/10000000000000000000000 : ℝ)*base89 + (8795869/10000000000000000000000 : ℝ)*base91 + (8795869/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (59041/100000 : ℝ) ≤ (915178903782726245686680071751/1550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1364433/20000000000000 : ℝ)*(upper3) + (127482359/100000000000000 : ℝ)*(upper4) + (60774701/100000000000000 : ℝ)*(lower5) + (304775469596787/10000000000000 : ℝ)*(major0) + (304775469596787/10000000000000 : ℝ)*(major1) + (304775469596787/10000000000000 : ℝ)*(major2) + (516422833373037/12500000000000 : ℝ)*(sp0) + (2065690851872109/50000000000000 : ℝ)*(sp1) + (2065691249261513/50000000000000 : ℝ)*(sp2) + (1944442802396751/100000000000000 : ℝ)*(sp3) + (1938810899/100000000000000 : ℝ)*(sp5) + (114403209/10000000000000 : ℝ)*(sp6) + (840117927/50000000000000 : ℝ)*(sp7) + (48778541/5000000000000 : ℝ)*(sp8) + (388888896526521/20000000000000 : ℝ)*(f.failure) + (1032845910638779/25000000000000 : ℝ)*(f.sum) + (357740020517/62000000000000000000000000 : ℝ)*base66 + (4845717518601083/6200000000000000000000000000000 : ℝ)*base68 + (9264139939598917/6200000000000000000000000000000 : ℝ)*base69 + (23298084581801083/6200000000000000000000000000000 : ℝ)*base72 + (14013721803/12400000000000000000000000 : ℝ)*base73 + (13808419916801083/6200000000000000000000000000000 : ℝ)*base76 + (8463974371601083/6200000000000000000000000000000 : ℝ)*base78 + (618689380201083/6200000000000000000000000000000 : ℝ)*base80 + (97159573981/62000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (11250507/2000000000000000000000 : ℝ)*base89 + (11250507/2000000000000000000000 : ℝ)*base91 + (11250507/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (10031/12500 : ℝ) ≤ (6219385012281801822788879920899/7750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11154939/4000000000000 : ℝ)*(upper2) + (382307201/100000000000000 : ℝ)*(lower3) + (204400921/100000000000000 : ℝ)*(lower5) + (1678768407481263/50000000000000 : ℝ)*(major0) + (1678768407481263/50000000000000 : ℝ)*(major1) + (3357536814962527/100000000000000 : ℝ)*(major2) + (4212587417/100000000000000 : ℝ)*(sp0) + (17739611239/50000000000000 : ℝ)*(sp2) + (87319672781/100000000000000 : ℝ)*(sp3) + (181849283604989/4000000000000 : ℝ)*(sp8) + (2273120225727321/50000000000000 : ℝ)*(sp9) + (1136551243058041/25000000000000 : ℝ)*(sp10) + (428399163146809/20000000000000 : ℝ)*(sp11) + (1659497/40000000000 : ℝ)*(sp12) + (1071041567703413/50000000000000 : ℝ)*(f.failure) + (2273120225727321/50000000000000 : ℝ)*(f.sum) + (28515281863381/8680000000000000000000000000 : ℝ)*base65 + (2700791127068184569/217000000000000000000000000000000 : ℝ)*base68 + (2945308261022899201/434000000000000000000000000000000 : ℝ)*base70 + (1622637730741184569/217000000000000000000000000000000 : ℝ)*base72 + (49427711715541/8680000000000000000000000000 : ℝ)*base73 + (1996100184741100799/434000000000000000000000000000000 : ℝ)*base75 + (286036075342801367/31000000000000000000000000000000 : ℝ)*base78 + (210806403091801367/31000000000000000000000000000000 : ℝ)*base80 + (94009156163/310000000000000000000000000 : ℝ)*base81 + (15209471/5000000000000000000000 : ℝ)*base89 + (15209471/5000000000000000000000 : ℝ)*base91 + (34790529/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-84549/100000 : ℝ) ≤ (-917326012329756608349606723/1085000000000000000000000000 : ℝ) := by norm_num
    linear_combination (115083313/100000000000000 : ℝ)*(lower0) + (102439987/50000000000000 : ℝ)*(lower1) + (137209951/50000000000000 : ℝ)*(lower2) + (194429019/50000000000000 : ℝ)*(upper5) + (53040564769497/1562500000000 : ℝ)*(major0) + (53040564769497/1562500000000 : ℝ)*(major1) + (53040564769497/1562500000000 : ℝ)*(major2) + (8456489509/50000000000000 : ℝ)*(sp0) + (20978384581/10000000000000 : ℝ)*(sp5) + (25153712841/20000000000000 : ℝ)*(sp7) + (2325815363985423/50000000000000 : ℝ)*(sp12) + (2325718928552027/50000000000000 : ℝ)*(sp13) + (581455955118733/12500000000000 : ℝ)*(sp14) + (216560093973207/10000000000000 : ℝ)*(sp15) + (1082863354148137/50000000000000 : ℝ)*(f.failure) + (581455955118733/12500000000000 : ℝ)*(f.sum) + (553174451181/1085000000000000000000000000 : ℝ)*base66 + (10390944391480439/6781250000000000000000000000000 : ℝ)*base67 + (31651529173832061/6781250000000000000000000000000 : ℝ)*base70 + (2930940661105439/6781250000000000000000000000000 : ℝ)*base71 + (3964621152679/1085000000000000000000000000 : ℝ)*base73 + (40757057371769561/6781250000000000000000000000000 : ℝ)*base76 + (6693257121980439/6781250000000000000000000000000 : ℝ)*base77 + (45843918966269561/6781250000000000000000000000000 : ℝ)*base80 + (5794115183551/1085000000000000000000000000 : ℝ)*base82 + (41675621/5000000000000000000000 : ℝ)*base90 + (41675621/5000000000000000000000 : ℝ)*base92 + (41675621/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1393_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156741667/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14737/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2253/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62879/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59041/100000 : ℝ) else (10031/12500 : ℝ) ≤ X j i ∧ X j i ≤ (84549/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1393_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1393_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156741667/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14743/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11259/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62879/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59041/100000 : ℝ) else (10031/12500 : ℝ) ≤ X j i ∧ X j i ≤ (84549/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1393_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1393_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1393_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156741667/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14743/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11259/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62879/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59041/100000 : ℝ) else (10031/12500 : ℝ) ≤ X j i ∧ X j i ≤ (84549/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1393_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
