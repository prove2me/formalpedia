-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1479_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:12:35.568447+00:00
-- url     : https://prove2.me/submissions/d0abbe45-5aa9-4309-999a-9f2a2e309c2c

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
theorem support_rectangle_w1479_s3_0 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-958578383/5000000000 : ℝ)*x 0 + (5442327477/10000000000 : ℝ)*x 1 + (2605753033/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (958578383/5000000000 : ℝ)^4455 ≤ (5855082593997/50000000000000 : ℝ)^3431 := by
    have hnat : (958578383 : ℕ)^4455*50000000000000^3431 ≤ 5855082593997^3431*5000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      958578383 5000000000 5855082593997 50000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5442327477/10000000000 : ℝ)^4455 ≤ (45386659105529/100000000000000 : ℝ)^3431 := by
    have hnat : (5442327477 : ℕ)^4455*100000000000000^3431 ≤ 45386659105529^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442327477 10000000000 45386659105529 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2605753033/5000000000 : ℝ)^4455 ≤ (21451587845809/50000000000000 : ℝ)^3431 := by
    have hnat : (2605753033 : ℕ)^4455*50000000000000^3431 ≤ 21451587845809^3431*5000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2605753033 5000000000 21451587845809 50000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-958578383/5000000000 : ℝ), (5442327477/10000000000 : ℝ), (2605753033/5000000000 : ℝ)] ![(5855082593997/50000000000000 : ℝ), (45386659105529/100000000000000 : ℝ), (21451587845809/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-958578383/5000000000 : ℝ)|^4455 ≤ (5855082593997/50000000000000 : ℝ)^3431
        have hw : |(-958578383/5000000000 : ℝ)|=(958578383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5442327477/10000000000 : ℝ)|^4455 ≤ (45386659105529/100000000000000 : ℝ)^3431
        have hw : |(5442327477/10000000000 : ℝ)|=(5442327477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2605753033/5000000000 : ℝ)|^4455 ≤ (21451587845809/50000000000000 : ℝ)^3431
        have hw : |(2605753033/5000000000 : ℝ)|=(2605753033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s3_1 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677298907/5000000000 : ℝ)*x 0 + (-2035571423/10000000000 : ℝ)*x 1 + (651438269/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677298907/5000000000 : ℝ)^4455 ≤ (44438967456167/100000000000000 : ℝ)^3431 := by
    have hnat : (2677298907 : ℕ)^4455*100000000000000^3431 ≤ 44438967456167^3431*5000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677298907 5000000000 44438967456167 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2035571423/10000000000 : ℝ)^4455 ≤ (12657855924849/100000000000000 : ℝ)^3431 := by
    have hnat : (2035571423 : ℕ)^4455*100000000000000^3431 ≤ 12657855924849^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2035571423 10000000000 12657855924849 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (651438269/1250000000 : ℝ)^4455 ≤ (21451588305453/50000000000000 : ℝ)^3431 := by
    have hnat : (651438269 : ℕ)^4455*50000000000000^3431 ≤ 21451588305453^3431*1250000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651438269 1250000000 21451588305453 50000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677298907/5000000000 : ℝ), (-2035571423/10000000000 : ℝ), (651438269/1250000000 : ℝ)] ![(44438967456167/100000000000000 : ℝ), (12657855924849/100000000000000 : ℝ), (21451588305453/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677298907/5000000000 : ℝ)|^4455 ≤ (44438967456167/100000000000000 : ℝ)^3431
        have hw : |(2677298907/5000000000 : ℝ)|=(2677298907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2035571423/10000000000 : ℝ)|^4455 ≤ (12657855924849/100000000000000 : ℝ)^3431
        have hw : |(-2035571423/10000000000 : ℝ)|=(2035571423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(651438269/1250000000 : ℝ)|^4455 ≤ (21451588305453/50000000000000 : ℝ)^3431
        have hw : |(651438269/1250000000 : ℝ)|=(651438269/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s3_2 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535459783/1000000000 : ℝ)*x 0 + (1302876493/2500000000 : ℝ)*x 1 + (-2035571639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535459783/1000000000 : ℝ)^4455 ≤ (8887793525717/20000000000000 : ℝ)^3431 := by
    have hnat : (535459783 : ℕ)^4455*20000000000000^3431 ≤ 8887793525717^3431*1000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535459783 1000000000 8887793525717 20000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1302876493/2500000000 : ℝ)^4455 ≤ (8580634937363/20000000000000 : ℝ)^3431 := by
    have hnat : (1302876493 : ℕ)^4455*20000000000000^3431 ≤ 8580634937363^3431*2500000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1302876493 2500000000 8580634937363 20000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2035571639/10000000000 : ℝ)^4455 ≤ (12657857668881/100000000000000 : ℝ)^3431 := by
    have hnat : (2035571639 : ℕ)^4455*100000000000000^3431 ≤ 12657857668881^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2035571639 10000000000 12657857668881 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535459783/1000000000 : ℝ), (1302876493/2500000000 : ℝ), (-2035571639/10000000000 : ℝ)] ![(8887793525717/20000000000000 : ℝ), (8580634937363/20000000000000 : ℝ), (12657857668881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535459783/1000000000 : ℝ)|^4455 ≤ (8887793525717/20000000000000 : ℝ)^3431
        have hw : |(535459783/1000000000 : ℝ)|=(535459783/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1302876493/2500000000 : ℝ)|^4455 ≤ (8580634937363/20000000000000 : ℝ)^3431
        have hw : |(1302876493/2500000000 : ℝ)|=(1302876493/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2035571639/10000000000 : ℝ)|^4455 ≤ (12657857668881/100000000000000 : ℝ)^3431
        have hw : |(-2035571639/10000000000 : ℝ)|=(2035571639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s3_3 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4284934361/10000000000 : ℝ)*x 0 + (161438369/400000000 : ℝ)*x 1 + (90944363/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4284934361/10000000000 : ℝ)^4455 ≤ (6654661534129/20000000000000 : ℝ)^3431 := by
    have hnat : (4284934361 : ℕ)^4455*20000000000000^3431 ≤ 6654661534129^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4284934361 10000000000 6654661534129 20000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (161438369/400000000 : ℝ)^4455 ≤ (30785024983153/100000000000000 : ℝ)^3431 := by
    have hnat : (161438369 : ℕ)^4455*100000000000000^3431 ≤ 30785024983153^3431*400000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161438369 400000000 30785024983153 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (90944363/200000000 : ℝ)^4455 ≤ (8985416832353/25000000000000 : ℝ)^3431 := by
    have hnat : (90944363 : ℕ)^4455*25000000000000^3431 ≤ 8985416832353^3431*200000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90944363 200000000 8985416832353 25000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4284934361/10000000000 : ℝ), (161438369/400000000 : ℝ), (90944363/200000000 : ℝ)] ![(6654661534129/20000000000000 : ℝ), (30785024983153/100000000000000 : ℝ), (8985416832353/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4284934361/10000000000 : ℝ)|^4455 ≤ (6654661534129/20000000000000 : ℝ)^3431
        have hw : |(4284934361/10000000000 : ℝ)|=(4284934361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(161438369/400000000 : ℝ)|^4455 ≤ (30785024983153/100000000000000 : ℝ)^3431
        have hw : |(161438369/400000000 : ℝ)|=(161438369/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(90944363/200000000 : ℝ)|^4455 ≤ (8985416832353/25000000000000 : ℝ)^3431
        have hw : |(90944363/200000000 : ℝ)|=(90944363/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s3_4 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-479297787/2500000000 : ℝ)*x 0 + (5212734537/10000000000 : ℝ)*x 1 + (2720544763/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (479297787/2500000000 : ℝ)^4455 ≤ (11710437875151/100000000000000 : ℝ)^3431 := by
    have hnat : (479297787 : ℕ)^4455*100000000000000^3431 ≤ 11710437875151^3431*2500000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      479297787 2500000000 11710437875151 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5212734537/10000000000 : ℝ)^4455 ≤ (42916307767001/100000000000000 : ℝ)^3431 := by
    have hnat : (5212734537 : ℕ)^4455*100000000000000^3431 ≤ 42916307767001^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5212734537 10000000000 42916307767001 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2720544763/5000000000 : ℝ)^4455 ≤ (45373254339213/100000000000000 : ℝ)^3431 := by
    have hnat : (2720544763 : ℕ)^4455*100000000000000^3431 ≤ 45373254339213^3431*5000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2720544763 5000000000 45373254339213 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-479297787/2500000000 : ℝ), (5212734537/10000000000 : ℝ), (2720544763/5000000000 : ℝ)] ![(11710437875151/100000000000000 : ℝ), (42916307767001/100000000000000 : ℝ), (45373254339213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-479297787/2500000000 : ℝ)|^4455 ≤ (11710437875151/100000000000000 : ℝ)^3431
        have hw : |(-479297787/2500000000 : ℝ)|=(479297787/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5212734537/10000000000 : ℝ)|^4455 ≤ (42916307767001/100000000000000 : ℝ)^3431
        have hw : |(5212734537/10000000000 : ℝ)|=(5212734537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2720544763/5000000000 : ℝ)|^4455 ≤ (45373254339213/100000000000000 : ℝ)^3431
        have hw : |(2720544763/5000000000 : ℝ)|=(2720544763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s3_5 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661790393/1250000000 : ℝ)*x 0 + (-1805988263/10000000000 : ℝ)*x 1 + (340068093/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661790393/1250000000 : ℝ)^4455 ≤ (21895265919849/50000000000000 : ℝ)^3431 := by
    have hnat : (661790393 : ℕ)^4455*50000000000000^3431 ≤ 21895265919849^3431*1250000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661790393 1250000000 21895265919849 50000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1805988263/10000000000 : ℝ)^4455 ≤ (10836214224467/100000000000000 : ℝ)^3431 := by
    have hnat : (1805988263 : ℕ)^4455*100000000000000^3431 ≤ 10836214224467^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1805988263 10000000000 10836214224467 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (340068093/625000000 : ℝ)^4455 ≤ (11343313481939/25000000000000 : ℝ)^3431 := by
    have hnat : (340068093 : ℕ)^4455*25000000000000^3431 ≤ 11343313481939^3431*625000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340068093 625000000 11343313481939 25000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661790393/1250000000 : ℝ), (-1805988263/10000000000 : ℝ), (340068093/625000000 : ℝ)] ![(21895265919849/50000000000000 : ℝ), (10836214224467/100000000000000 : ℝ), (11343313481939/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661790393/1250000000 : ℝ)|^4455 ≤ (21895265919849/50000000000000 : ℝ)^3431
        have hw : |(661790393/1250000000 : ℝ)|=(661790393/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1805988263/10000000000 : ℝ)|^4455 ≤ (10836214224467/100000000000000 : ℝ)^3431
        have hw : |(-1805988263/10000000000 : ℝ)|=(1805988263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(340068093/625000000 : ℝ)|^4455 ≤ (11343313481939/25000000000000 : ℝ)^3431
        have hw : |(340068093/625000000 : ℝ)|=(340068093/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s3_6 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058864637/2000000000 : ℝ)*x 0 + (136027237/250000000 : ℝ)*x 1 + (-1805988217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058864637/2000000000 : ℝ)^4455 ≤ (43790532280031/100000000000000 : ℝ)^3431 := by
    have hnat : (1058864637 : ℕ)^4455*100000000000000^3431 ≤ 43790532280031^3431*2000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058864637 2000000000 43790532280031 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (136027237/250000000 : ℝ)^4455 ≤ (45373253841133/100000000000000 : ℝ)^3431 := by
    have hnat : (136027237 : ℕ)^4455*100000000000000^3431 ≤ 45373253841133^3431*250000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136027237 250000000 45373253841133 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1805988217/10000000000 : ℝ)^4455 ≤ (2709053466521/25000000000000 : ℝ)^3431 := by
    have hnat : (1805988217 : ℕ)^4455*25000000000000^3431 ≤ 2709053466521^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1805988217 10000000000 2709053466521 25000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058864637/2000000000 : ℝ), (136027237/250000000 : ℝ), (-1805988217/10000000000 : ℝ)] ![(43790532280031/100000000000000 : ℝ), (45373253841133/100000000000000 : ℝ), (2709053466521/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058864637/2000000000 : ℝ)|^4455 ≤ (43790532280031/100000000000000 : ℝ)^3431
        have hw : |(1058864637/2000000000 : ℝ)|=(1058864637/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(136027237/250000000 : ℝ)|^4455 ≤ (45373253841133/100000000000000 : ℝ)^3431
        have hw : |(136027237/250000000 : ℝ)|=(136027237/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1805988217/10000000000 : ℝ)|^4455 ≤ (2709053466521/25000000000000 : ℝ)^3431
        have hw : |(-1805988217/10000000000 : ℝ)|=(1805988217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s3_7 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4285010257/10000000000 : ℝ)*x 0 + (908899483/2000000000 : ℝ)*x 1 + (4038700761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4285010257/10000000000 : ℝ)^4455 ≤ (16637036456349/50000000000000 : ℝ)^3431 := by
    have hnat : (4285010257 : ℕ)^4455*50000000000000^3431 ≤ 16637036456349^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4285010257 10000000000 16637036456349 50000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (908899483/2000000000 : ℝ)^4455 ≤ (8978436648067/25000000000000 : ℝ)^3431 := by
    have hnat : (908899483 : ℕ)^4455*25000000000000^3431 ≤ 8978436648067^3431*2000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      908899483 2000000000 8978436648067 25000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4038700761/10000000000 : ℝ)^4455 ≤ (30812180476533/100000000000000 : ℝ)^3431 := by
    have hnat : (4038700761 : ℕ)^4455*100000000000000^3431 ≤ 30812180476533^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4038700761 10000000000 30812180476533 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4285010257/10000000000 : ℝ), (908899483/2000000000 : ℝ), (4038700761/10000000000 : ℝ)] ![(16637036456349/50000000000000 : ℝ), (8978436648067/25000000000000 : ℝ), (30812180476533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4285010257/10000000000 : ℝ)|^4455 ≤ (16637036456349/50000000000000 : ℝ)^3431
        have hw : |(4285010257/10000000000 : ℝ)|=(4285010257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(908899483/2000000000 : ℝ)|^4455 ≤ (8978436648067/25000000000000 : ℝ)^3431
        have hw : |(908899483/2000000000 : ℝ)|=(908899483/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4038700761/10000000000 : ℝ)|^4455 ≤ (30812180476533/100000000000000 : ℝ)^3431
        have hw : |(4038700761/10000000000 : ℝ)|=(4038700761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1479_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32149573/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2017/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (407/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (1069/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (623/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2017/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (407/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2017/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (407/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2017/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (407/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2017/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (407/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2017/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (407/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2017/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (407/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (407/4000 : ℝ) ^ (4453/1024 : ℝ) ≤ (966410411358259/20000000000000000000 : ℝ) := by
    have hpowers : (407/4000 : ℝ)^4453 ≤ (966410411358259/20000000000000000000 : ℝ)^1024 := by
      have hnat : (407 : ℕ)^4453*20000000000000000000^1024 ≤ 966410411358259^1024*4000^4453 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        407 4000 966410411358259 20000000000000000000 4453 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (407/4000 : ℝ)) (X := (966410411358259/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4453 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2017/12500 : ℝ) ^ (4453/1024 : ℝ) ≤ (35891796127192193/100000000000000000000 : ℝ) := by
    have hpowers : (2017/12500 : ℝ)^4453 ≤ (35891796127192193/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2017 : ℕ)^4453*100000000000000000000^1024 ≤ 35891796127192193^1024*12500^4453 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2017 12500 35891796127192193 100000000000000000000 4453 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2017/12500 : ℝ)) (X := (35891796127192193/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4453 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000966410411358259/10000000000000000000 : ℝ) ≤ (10000222224891373/10000000000000000 : ℝ) ^ (4453/1024 : ℝ) := by
    have hpowers : (10000966410411358259/10000000000000000000 : ℝ)^1024 ≤ (10000222224891373/10000000000000000 : ℝ)^4453 := by
      have hnat : (10000966410411358259 : ℕ)^1024*10000000000000000^4453 ≤ 10000222224891373^4453*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000966410411358259 10000000000000000000 10000222224891373 10000000000000000 1024 4453 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000222224891373/10000000000000000 : ℝ)) (X := (10000966410411358259/10000000000000000000 : ℝ)) (by norm_num) 4453 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (781568155063937371/781250000000000000 : ℝ) ≤ (1000093632794851/1000000000000000 : ℝ) ^ (4453/1024 : ℝ) := by
    have hpowers : (781568155063937371/781250000000000000 : ℝ)^1024 ≤ (1000093632794851/1000000000000000 : ℝ)^4453 := by
      have hnat : (781568155063937371 : ℕ)^1024*1000000000000000^4453 ≤ 1000093632794851^4453*781250000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781568155063937371 781250000000000000 1000093632794851 1000000000000000 1024 4453 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000093632794851/1000000000000000 : ℝ)) (X := (781568155063937371/781250000000000000 : ℝ)) (by norm_num) 4453 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035891796127192193/50000000000000000000 : ℝ) ≤ (10001650431005647/10000000000000000 : ℝ) ^ (4453/1024 : ℝ) := by
    have hpowers : (50035891796127192193/50000000000000000000 : ℝ)^1024 ≤ (10001650431005647/10000000000000000 : ℝ)^4453 := by
      have hnat : (50035891796127192193 : ℕ)^1024*10000000000000000^4453 ≤ 10001650431005647^4453*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035891796127192193 50000000000000000000 10001650431005647 10000000000000000 1024 4453 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001650431005647/10000000000000000 : ℝ)) (X := (50035891796127192193/50000000000000000000 : ℝ)) (by norm_num) 4453 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(966410411358259/20000000000000000000 : ℝ) ≤ ((19865597561788245501/19870000000000000000 : ℝ)+2*(238034352379/198700000000000 : ℝ)*(407/4000 : ℝ))^(4453/1024 : ℝ) := by
    rw [show (19865597561788245501/19870000000000000000 : ℝ)+2*(238034352379/198700000000000 : ℝ)*(407/4000 : ℝ)=(10000222224891373/10000000000000000 : ℝ) by norm_num, show 1+2*(966410411358259/20000000000000000000 : ℝ)=(10000966410411358259/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35891796127192193/100000000000000000000 : ℝ)+(966410411358259/20000000000000000000 : ℝ) ≤ ((19865597561788245501/19870000000000000000 : ℝ)+(238034352379/198700000000000 : ℝ)*((2017/12500 : ℝ)+(407/4000 : ℝ)))^(4453/1024 : ℝ) := by
    rw [show (19865597561788245501/19870000000000000000 : ℝ)+(238034352379/198700000000000 : ℝ)*((2017/12500 : ℝ)+(407/4000 : ℝ))=(1000093632794851/1000000000000000 : ℝ) by norm_num, show 1+(35891796127192193/100000000000000000000 : ℝ)+(966410411358259/20000000000000000000 : ℝ)=(781568155063937371/781250000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35891796127192193/100000000000000000000 : ℝ) ≤ ((19865597561788245501/19870000000000000000 : ℝ)+2*(238034352379/198700000000000 : ℝ)*(2017/12500 : ℝ))^(4453/1024 : ℝ) := by
    rw [show (19865597561788245501/19870000000000000000 : ℝ)+2*(238034352379/198700000000000 : ℝ)*(2017/12500 : ℝ)=(10001650431005647/10000000000000000 : ℝ) by norm_num, show 1+2*(35891796127192193/100000000000000000000 : ℝ)=(50035891796127192193/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19865597561788245501/19870000000000000000 : ℝ)*(X 1 0+X 2 0)+(238034352379/198700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4453/1024 : ℝ)) (lo := (407/4000 : ℝ)) (hi := (2017/12500 : ℝ)) (c := (19865597561788245501/19870000000000000000 : ℝ)) (alpha := (238034352379/198700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19865597561788245501/19870000000000000000 : ℝ)*(X 0 1+X 2 1)+(238034352379/198700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4453/1024 : ℝ)) (lo := (407/4000 : ℝ)) (hi := (2017/12500 : ℝ)) (c := (19865597561788245501/19870000000000000000 : ℝ)) (alpha := (238034352379/198700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19865597561788245501/19870000000000000000 : ℝ)*(X 0 2+X 1 2)+(238034352379/198700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4453/1024 : ℝ)) (lo := (407/4000 : ℝ)) (hi := (2017/12500 : ℝ)) (c := (19865597561788245501/19870000000000000000 : ℝ)) (alpha := (238034352379/198700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-958578383/5000000000 : ℝ)*X 0 0+(5442327477/10000000000 : ℝ)*X 0 1+(2605753033/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677298907/5000000000 : ℝ)*X 1 0+(-2035571423/10000000000 : ℝ)*X 1 1+(651438269/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((535459783/1000000000 : ℝ)*X 2 0+(1302876493/2500000000 : ℝ)*X 2 1+(-2035571639/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4284934361/10000000000 : ℝ)*X 0 0+(161438369/400000000 : ℝ)*X 0 1+(90944363/200000000 : ℝ)*X 0 2+(4284934361/10000000000 : ℝ)*X 1 0+(161438369/400000000 : ℝ)*X 1 1+(90944363/200000000 : ℝ)*X 1 2+(4284934361/10000000000 : ℝ)*X 2 0+(161438369/400000000 : ℝ)*X 2 1+(90944363/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-479297787/2500000000 : ℝ)*X 0 0+(5212734537/10000000000 : ℝ)*X 0 1+(2720544763/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((661790393/1250000000 : ℝ)*X 1 0+(-1805988263/10000000000 : ℝ)*X 1 1+(340068093/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1058864637/2000000000 : ℝ)*X 2 0+(136027237/250000000 : ℝ)*X 2 1+(-1805988217/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4285010257/10000000000 : ℝ)*X 0 0+(908899483/2000000000 : ℝ)*X 0 1+(4038700761/10000000000 : ℝ)*X 0 2+(4285010257/10000000000 : ℝ)*X 1 0+(908899483/2000000000 : ℝ)*X 1 1+(4038700761/10000000000 : ℝ)*X 1 2+(4285010257/10000000000 : ℝ)*X 2 0+(908899483/2000000000 : ℝ)*X 2 1+(4038700761/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (66326133375391074278973/9935000000000000000000000000 : ℝ) := by norm_num
    linear_combination (400703097/25000000000000 : ℝ)*(base19) + (758259263/50000000000000 : ℝ)*(base23) + (30453161/50000000000000 : ℝ)*(lower2) + (268343833/100000000000000 : ℝ)*(upper3) + (7767581/100000000000000 : ℝ)*(lower4) + (786048061953379/25000000000000 : ℝ)*(major0) + (786048061953379/25000000000000 : ℝ)*(major1) + (786048061953379/25000000000000 : ℝ)*(major2) + (541547912278871/12500000000000 : ℝ)*(sp0) + (2166202530183923/50000000000000 : ℝ)*(sp1) + (1083101286665427/25000000000000 : ℝ)*(sp2) + (244495654845073/12500000000000 : ℝ)*(sp3) + (11682474633/50000000000000 : ℝ)*(sp4) + (12371152627/100000000000000 : ℝ)*(sp7) + (1955977609913211/100000000000000 : ℝ)*(f.failure) + (2166203331590117/50000000000000 : ℝ)*(f.sum) + (11850116066519/9935000000000000000000000000 : ℝ)*base65 + (788238952272652121/496750000000000000000000000000000 : ℝ)*base68 + (1002577400423347879/496750000000000000000000000000000 : ℝ)*base69 + (76127694105347879/496750000000000000000000000000000 : ℝ)*base71 + (14797408201881/9935000000000000000000000000 : ℝ)*base74 + (2602311910015652121/496750000000000000000000000000000 : ℝ)*base76 + (1480238762342347879/496750000000000000000000000000000 : ℝ)*base77 + (5922653210329152121/496750000000000000000000000000000 : ℝ)*base80 + (86537311339/9935000000000000000000000000 : ℝ)*base81 + (19291097/2000000000000000000000 : ℝ)*base90 + (19291097/2000000000000000000000 : ℝ)*base92 + (19291097/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5333212250902667646358955889/496750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2109906891/100000000000000 : ℝ)*(base19) + (1128524441/50000000000000 : ℝ)*(base23) + (3988769/1562500000000 : ℝ)*(upper3) + (43749351/100000000000000 : ℝ)*(lower4) + (58587931/25000000000000 : ℝ)*(upper5) + (1589056326211821/50000000000000 : ℝ)*(major0) + (1589056326211821/50000000000000 : ℝ)*(major1) + (1589056326211821/50000000000000 : ℝ)*(major2) + (6010590427/20000000000000 : ℝ)*(sp1) + (32740311197/100000000000000 : ℝ)*(sp2) + (437914571645093/10000000000000 : ℝ)*(sp4) + (4379113553591903/100000000000000 : ℝ)*(sp5) + (87582214381817/2000000000000 : ℝ)*(sp6) + (494269807630671/25000000000000 : ℝ)*(sp7) + (494269807630671/25000000000000 : ℝ)*(f.failure) + (437914571645093/10000000000000 : ℝ)*(f.sum) + (17146859601969/4967500000000000000000000000 : ℝ)*base65 + (11877885502252832679/993500000000000000000000000000000 : ℝ)*base68 + (5851901098431832679/993500000000000000000000000000000 : ℝ)*base70 + (4761121558392832679/993500000000000000000000000000000 : ℝ)*base72 + (2821278238337/620937500000000000000000000 : ℝ)*base74 + (142545710905832679/993500000000000000000000000000000 : ℝ)*base76 + (10280733191445832679/993500000000000000000000000000000 : ℝ)*base78 + (7433420605271832679/993500000000000000000000000000000 : ℝ)*base80 + (7034927463267/9935000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (4353483/500000000000000000000 : ℝ)*base89 + (4353483/500000000000000000000 : ℝ)*base91 + (4353483/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1479_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32149573/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2017/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (407/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1069/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (623/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1479_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1479_s4_0 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-479448363/2500000000 : ℝ)*x 0 + (5438206283/10000000000 : ℝ)*x 1 + (521520763/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (479448363/2500000000 : ℝ)^4455 ≤ (585760752323/5000000000000 : ℝ)^3431 := by
    have hnat : (479448363 : ℕ)^4455*5000000000000^3431 ≤ 585760752323^3431*2500000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      479448363 2500000000 585760752323 5000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5438206283/10000000000 : ℝ)^4455 ≤ (45342037570503/100000000000000 : ℝ)^3431 := by
    have hnat : (5438206283 : ℕ)^4455*100000000000000^3431 ≤ 45342037570503^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438206283 10000000000 45342037570503 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521520763/1000000000 : ℝ)^4455 ≤ (1073568684241/2500000000000 : ℝ)^3431 := by
    have hnat : (521520763 : ℕ)^4455*2500000000000^3431 ≤ 1073568684241^3431*1000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521520763 1000000000 1073568684241 2500000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-479448363/2500000000 : ℝ), (5438206283/10000000000 : ℝ), (521520763/1000000000 : ℝ)] ![(585760752323/5000000000000 : ℝ), (45342037570503/100000000000000 : ℝ), (1073568684241/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-479448363/2500000000 : ℝ)|^4455 ≤ (585760752323/5000000000000 : ℝ)^3431
        have hw : |(-479448363/2500000000 : ℝ)|=(479448363/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5438206283/10000000000 : ℝ)|^4455 ≤ (45342037570503/100000000000000 : ℝ)^3431
        have hw : |(5438206283/10000000000 : ℝ)|=(5438206283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(521520763/1000000000 : ℝ)|^4455 ≤ (1073568684241/2500000000000 : ℝ)^3431
        have hw : |(521520763/1000000000 : ℝ)|=(521520763/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s4_1 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676763977/5000000000 : ℝ)*x 0 + (-1016048221/5000000000 : ℝ)*x 1 + (208608337/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676763977/5000000000 : ℝ)^4455 ≤ (8885487763147/20000000000000 : ℝ)^3431 := by
    have hnat : (2676763977 : ℕ)^4455*20000000000000^3431 ≤ 8885487763147^3431*5000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676763977 5000000000 8885487763147 20000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1016048221/5000000000 : ℝ)^4455 ≤ (12629805300487/100000000000000 : ℝ)^3431 := by
    have hnat : (1016048221 : ℕ)^4455*100000000000000^3431 ≤ 12629805300487^3431*5000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016048221 5000000000 12629805300487 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208608337/400000000 : ℝ)^4455 ≤ (42942755869511/100000000000000 : ℝ)^3431 := by
    have hnat : (208608337 : ℕ)^4455*100000000000000^3431 ≤ 42942755869511^3431*400000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208608337 400000000 42942755869511 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676763977/5000000000 : ℝ), (-1016048221/5000000000 : ℝ), (208608337/400000000 : ℝ)] ![(8885487763147/20000000000000 : ℝ), (12629805300487/100000000000000 : ℝ), (42942755869511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676763977/5000000000 : ℝ)|^4455 ≤ (8885487763147/20000000000000 : ℝ)^3431
        have hw : |(2676763977/5000000000 : ℝ)|=(2676763977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1016048221/5000000000 : ℝ)|^4455 ≤ (12629805300487/100000000000000 : ℝ)^3431
        have hw : |(-1016048221/5000000000 : ℝ)|=(1016048221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(208608337/400000000 : ℝ)|^4455 ≤ (42942755869511/100000000000000 : ℝ)^3431
        have hw : |(208608337/400000000 : ℝ)|=(208608337/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s4_2 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353528257/10000000000 : ℝ)*x 0 + (2607603869/5000000000 : ℝ)*x 1 + (-508024237/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353528257/10000000000 : ℝ)^4455 ≤ (44427442080717/100000000000000 : ℝ)^3431 := by
    have hnat : (5353528257 : ℕ)^4455*100000000000000^3431 ≤ 44427442080717^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353528257 10000000000 44427442080717 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2607603869/5000000000 : ℝ)^4455 ≤ (42942748524339/100000000000000 : ℝ)^3431 := by
    have hnat : (2607603869 : ℕ)^4455*100000000000000^3431 ≤ 42942748524339^3431*5000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607603869 5000000000 42942748524339 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (508024237/2500000000 : ℝ)^4455 ≤ (12629809383961/100000000000000 : ℝ)^3431 := by
    have hnat : (508024237 : ℕ)^4455*100000000000000^3431 ≤ 12629809383961^3431*2500000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508024237 2500000000 12629809383961 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353528257/10000000000 : ℝ), (2607603869/5000000000 : ℝ), (-508024237/2500000000 : ℝ)] ![(44427442080717/100000000000000 : ℝ), (42942748524339/100000000000000 : ℝ), (12629809383961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353528257/10000000000 : ℝ)|^4455 ≤ (44427442080717/100000000000000 : ℝ)^3431
        have hw : |(5353528257/10000000000 : ℝ)|=(5353528257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2607603869/5000000000 : ℝ)|^4455 ≤ (42942748524339/100000000000000 : ℝ)^3431
        have hw : |(2607603869/5000000000 : ℝ)|=(2607603869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-508024237/2500000000 : ℝ)|^4455 ≤ (12629809383961/100000000000000 : ℝ)^3431
        have hw : |(-508024237/2500000000 : ℝ)|=(508024237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s4_3 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (85706631/200000000 : ℝ)*x 0 + (80891523/200000000 : ℝ)*x 1 + (283656701/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (85706631/200000000 : ℝ)^4455 ≤ (16638656240763/50000000000000 : ℝ)^3431 := by
    have hnat : (85706631 : ℕ)^4455*50000000000000^3431 ≤ 16638656240763^3431*200000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85706631 200000000 16638656240763 50000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (80891523/200000000 : ℝ)^4455 ≤ (15435197986973/50000000000000 : ℝ)^3431 := by
    have hnat : (80891523 : ℕ)^4455*50000000000000^3431 ≤ 15435197986973^3431*200000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80891523 200000000 15435197986973 50000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (283656701/625000000 : ℝ)^4455 ≤ (3585229153421/10000000000000 : ℝ)^3431 := by
    have hnat : (283656701 : ℕ)^4455*10000000000000^3431 ≤ 3585229153421^3431*625000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283656701 625000000 3585229153421 10000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(85706631/200000000 : ℝ), (80891523/200000000 : ℝ), (283656701/625000000 : ℝ)] ![(16638656240763/50000000000000 : ℝ), (15435197986973/50000000000000 : ℝ), (3585229153421/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(85706631/200000000 : ℝ)|^4455 ≤ (16638656240763/50000000000000 : ℝ)^3431
        have hw : |(85706631/200000000 : ℝ)|=(85706631/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(80891523/200000000 : ℝ)|^4455 ≤ (15435197986973/50000000000000 : ℝ)^3431
        have hw : |(80891523/200000000 : ℝ)|=(80891523/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(283656701/625000000 : ℝ)|^4455 ≤ (3585229153421/10000000000000 : ℝ)^3431
        have hw : |(283656701/625000000 : ℝ)|=(283656701/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s4_4 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-119864011/625000000 : ℝ)*x 0 + (5216354751/10000000000 : ℝ)*x 1 + (5437050823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (119864011/625000000 : ℝ)^4455 ≤ (468618349829/4000000000000 : ℝ)^3431 := by
    have hnat : (119864011 : ℕ)^4455*4000000000000^3431 ≤ 468618349829^3431*625000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119864011 625000000 468618349829 4000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216354751/10000000000 : ℝ)^4455 ≤ (21477506200987/50000000000000 : ℝ)^3431 := by
    have hnat : (5216354751 : ℕ)^4455*50000000000000^3431 ≤ 21477506200987^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216354751 10000000000 21477506200987 50000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5437050823/10000000000 : ℝ)^4455 ≤ (1813181153307/4000000000000 : ℝ)^3431 := by
    have hnat : (5437050823 : ℕ)^4455*4000000000000^3431 ≤ 1813181153307^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437050823 10000000000 1813181153307 4000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-119864011/625000000 : ℝ), (5216354751/10000000000 : ℝ), (5437050823/10000000000 : ℝ)] ![(468618349829/4000000000000 : ℝ), (21477506200987/50000000000000 : ℝ), (1813181153307/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-119864011/625000000 : ℝ)|^4455 ≤ (468618349829/4000000000000 : ℝ)^3431
        have hw : |(-119864011/625000000 : ℝ)|=(119864011/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216354751/10000000000 : ℝ)|^4455 ≤ (21477506200987/50000000000000 : ℝ)^3431
        have hw : |(5216354751/10000000000 : ℝ)|=(5216354751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5437050823/10000000000 : ℝ)|^4455 ≤ (1813181153307/4000000000000 : ℝ)^3431
        have hw : |(5437050823/10000000000 : ℝ)|=(5437050823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s4_5 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295299047/10000000000 : ℝ)*x 0 + (-905126897/5000000000 : ℝ)*x 1 + (2718525393/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295299047/10000000000 : ℝ)^4455 ≤ (8760202628961/20000000000000 : ℝ)^3431 := by
    have hnat : (5295299047 : ℕ)^4455*20000000000000^3431 ≤ 8760202628961^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295299047 10000000000 8760202628961 20000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (905126897/5000000000 : ℝ)^4455 ≤ (1358682301377/12500000000000 : ℝ)^3431 := by
    have hnat : (905126897 : ℕ)^4455*12500000000000^3431 ≤ 1358682301377^3431*5000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      905126897 5000000000 1358682301377 12500000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2718525393/5000000000 : ℝ)^4455 ≤ (9065905686427/20000000000000 : ℝ)^3431 := by
    have hnat : (2718525393 : ℕ)^4455*20000000000000^3431 ≤ 9065905686427^3431*5000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718525393 5000000000 9065905686427 20000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295299047/10000000000 : ℝ), (-905126897/5000000000 : ℝ), (2718525393/5000000000 : ℝ)] ![(8760202628961/20000000000000 : ℝ), (1358682301377/12500000000000 : ℝ), (9065905686427/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295299047/10000000000 : ℝ)|^4455 ≤ (8760202628961/20000000000000 : ℝ)^3431
        have hw : |(5295299047/10000000000 : ℝ)|=(5295299047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-905126897/5000000000 : ℝ)|^4455 ≤ (1358682301377/12500000000000 : ℝ)^3431
        have hw : |(-905126897/5000000000 : ℝ)|=(905126897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2718525393/5000000000 : ℝ)|^4455 ≤ (9065905686427/20000000000000 : ℝ)^3431
        have hw : |(2718525393/5000000000 : ℝ)|=(2718525393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s4_6 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (330956187/625000000 : ℝ)*x 0 + (5437050813/10000000000 : ℝ)*x 1 + (-226281729/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330956187/625000000 : ℝ)^4455 ≤ (43801012554083/100000000000000 : ℝ)^3431 := by
    have hnat : (330956187 : ℕ)^4455*100000000000000^3431 ≤ 43801012554083^3431*625000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330956187 625000000 43801012554083 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5437050813/10000000000 : ℝ)^4455 ≤ (45329528724421/100000000000000 : ℝ)^3431 := by
    have hnat : (5437050813 : ℕ)^4455*100000000000000^3431 ≤ 45329528724421^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437050813 10000000000 45329528724421 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (226281729/1250000000 : ℝ)^4455 ≤ (135868233841/1250000000000 : ℝ)^3431 := by
    have hnat : (226281729 : ℕ)^4455*1250000000000^3431 ≤ 135868233841^3431*1250000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226281729 1250000000 135868233841 1250000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330956187/625000000 : ℝ), (5437050813/10000000000 : ℝ), (-226281729/1250000000 : ℝ)] ![(43801012554083/100000000000000 : ℝ), (45329528724421/100000000000000 : ℝ), (135868233841/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330956187/625000000 : ℝ)|^4455 ≤ (43801012554083/100000000000000 : ℝ)^3431
        have hw : |(330956187/625000000 : ℝ)|=(330956187/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5437050813/10000000000 : ℝ)|^4455 ≤ (45329528724421/100000000000000 : ℝ)^3431
        have hw : |(5437050813/10000000000 : ℝ)|=(5437050813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-226281729/1250000000 : ℝ)|^4455 ≤ (135868233841/1250000000000 : ℝ)^3431
        have hw : |(-226281729/1250000000 : ℝ)|=(226281729/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s4_7 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (214269957/500000000 : ℝ)*x 0 + (566995953/1250000000 : ℝ)*x 1 + (1011783841/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214269957/500000000 : ℝ)^4455 ≤ (8319498498683/25000000000000 : ℝ)^3431 := by
    have hnat : (214269957 : ℕ)^4455*25000000000000^3431 ≤ 8319498498683^3431*500000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214269957 500000000 8319498498683 25000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (566995953/1250000000 : ℝ)^4455 ≤ (8956561120829/25000000000000 : ℝ)^3431 := by
    have hnat : (566995953 : ℕ)^4455*25000000000000^3431 ≤ 8956561120829^3431*1250000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566995953 1250000000 8956561120829 25000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1011783841/2500000000 : ℝ)^4455 ≤ (1544788074717/5000000000000 : ℝ)^3431 := by
    have hnat : (1011783841 : ℕ)^4455*5000000000000^3431 ≤ 1544788074717^3431*2500000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1011783841 2500000000 1544788074717 5000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214269957/500000000 : ℝ), (566995953/1250000000 : ℝ), (1011783841/2500000000 : ℝ)] ![(8319498498683/25000000000000 : ℝ), (8956561120829/25000000000000 : ℝ), (1544788074717/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214269957/500000000 : ℝ)|^4455 ≤ (8319498498683/25000000000000 : ℝ)^3431
        have hw : |(214269957/500000000 : ℝ)|=(214269957/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(566995953/1250000000 : ℝ)|^4455 ≤ (8956561120829/25000000000000 : ℝ)^3431
        have hw : |(566995953/1250000000 : ℝ)|=(566995953/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1011783841/2500000000 : ℝ)|^4455 ≤ (1544788074717/5000000000000 : ℝ)^3431
        have hw : |(1011783841/2500000000 : ℝ)|=(1011783841/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1479_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32149573/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (623/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1069/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (10769/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15489/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (623/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1069/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (623/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1069/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (623/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1069/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (623/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1069/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (623/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1069/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (623/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1069/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1069/10000 : ℝ) ^ (4453/1024 : ℝ) ≤ (748670291978443/12500000000000000000 : ℝ) := by
    have hpowers : (1069/10000 : ℝ)^4453 ≤ (748670291978443/12500000000000000000 : ℝ)^1024 := by
      have hnat : (1069 : ℕ)^4453*12500000000000000000^1024 ≤ 748670291978443^1024*10000^4453 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1069 10000 748670291978443 12500000000000000000 4453 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1069/10000 : ℝ)) (X := (748670291978443/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4453 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (623/4000 : ℝ) ^ (4453/1024 : ℝ) ≤ (15386369131166531/50000000000000000000 : ℝ) := by
    have hpowers : (623/4000 : ℝ)^4453 ≤ (15386369131166531/50000000000000000000 : ℝ)^1024 := by
      have hnat : (623 : ℕ)^4453*50000000000000000000^1024 ≤ 15386369131166531^1024*4000^4453 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        623 4000 15386369131166531 50000000000000000000 4453 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (623/4000 : ℝ)) (X := (15386369131166531/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4453 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250748670291978443/6250000000000000000 : ℝ) ≤ (5000137723426657/5000000000000000 : ℝ) ^ (4453/1024 : ℝ) := by
    have hpowers : (6250748670291978443/6250000000000000000 : ℝ)^1024 ≤ (5000137723426657/5000000000000000 : ℝ)^4453 := by
      have hnat : (6250748670291978443 : ℕ)^1024*5000000000000000^4453 ≤ 5000137723426657^4453*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250748670291978443 6250000000000000000 5000137723426657 5000000000000000 1024 4453 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000137723426657/5000000000000000 : ℝ)) (X := (6250748670291978443/6250000000000000000 : ℝ)) (by norm_num) 4453 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018381050299080303/50000000000000000000 : ℝ) ≤ (2000169050365633/2000000000000000 : ℝ) ^ (4453/1024 : ℝ) := by
    have hpowers : (50018381050299080303/50000000000000000000 : ℝ)^1024 ≤ (2000169050365633/2000000000000000 : ℝ)^4453 := by
      have hnat : (50018381050299080303 : ℕ)^1024*2000000000000000^4453 ≤ 2000169050365633^4453*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018381050299080303 50000000000000000000 2000169050365633 2000000000000000 1024 4453 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000169050365633/2000000000000000 : ℝ)) (X := (50018381050299080303/50000000000000000000 : ℝ)) (by norm_num) 4453 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015386369131166531/25000000000000000000 : ℝ) ≤ (1250176882100377/1250000000000000 : ℝ) ^ (4453/1024 : ℝ) := by
    have hpowers : (25015386369131166531/25000000000000000000 : ℝ)^1024 ≤ (1250176882100377/1250000000000000 : ℝ)^4453 := by
      have hnat : (25015386369131166531 : ℕ)^1024*1250000000000000^4453 ≤ 1250176882100377^4453*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015386369131166531 25000000000000000000 1250176882100377 1250000000000000 1024 4453 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250176882100377/1250000000000000 : ℝ)) (X := (25015386369131166531/25000000000000000000 : ℝ)) (by norm_num) 4453 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(748670291978443/12500000000000000000 : ℝ) ≤ ((4883916312751612451/4885000000000000000 : ℝ)+2*(569804974851/488500000000000 : ℝ)*(1069/10000 : ℝ))^(4453/1024 : ℝ) := by
    rw [show (4883916312751612451/4885000000000000000 : ℝ)+2*(569804974851/488500000000000 : ℝ)*(1069/10000 : ℝ)=(5000137723426657/5000000000000000 : ℝ) by norm_num, show 1+2*(748670291978443/12500000000000000000 : ℝ)=(6250748670291978443/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15386369131166531/50000000000000000000 : ℝ)+(748670291978443/12500000000000000000 : ℝ) ≤ ((4883916312751612451/4885000000000000000 : ℝ)+(569804974851/488500000000000 : ℝ)*((623/4000 : ℝ)+(1069/10000 : ℝ)))^(4453/1024 : ℝ) := by
    rw [show (4883916312751612451/4885000000000000000 : ℝ)+(569804974851/488500000000000 : ℝ)*((623/4000 : ℝ)+(1069/10000 : ℝ))=(2000169050365633/2000000000000000 : ℝ) by norm_num, show 1+(15386369131166531/50000000000000000000 : ℝ)+(748670291978443/12500000000000000000 : ℝ)=(50018381050299080303/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15386369131166531/50000000000000000000 : ℝ) ≤ ((4883916312751612451/4885000000000000000 : ℝ)+2*(569804974851/488500000000000 : ℝ)*(623/4000 : ℝ))^(4453/1024 : ℝ) := by
    rw [show (4883916312751612451/4885000000000000000 : ℝ)+2*(569804974851/488500000000000 : ℝ)*(623/4000 : ℝ)=(1250176882100377/1250000000000000 : ℝ) by norm_num, show 1+2*(15386369131166531/50000000000000000000 : ℝ)=(25015386369131166531/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4883916312751612451/4885000000000000000 : ℝ)*(X 1 0+X 2 0)+(569804974851/488500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4453/1024 : ℝ)) (lo := (1069/10000 : ℝ)) (hi := (623/4000 : ℝ)) (c := (4883916312751612451/4885000000000000000 : ℝ)) (alpha := (569804974851/488500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4883916312751612451/4885000000000000000 : ℝ)*(X 0 1+X 2 1)+(569804974851/488500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4453/1024 : ℝ)) (lo := (1069/10000 : ℝ)) (hi := (623/4000 : ℝ)) (c := (4883916312751612451/4885000000000000000 : ℝ)) (alpha := (569804974851/488500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4883916312751612451/4885000000000000000 : ℝ)*(X 0 2+X 1 2)+(569804974851/488500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4453/1024 : ℝ)) (lo := (1069/10000 : ℝ)) (hi := (623/4000 : ℝ)) (c := (4883916312751612451/4885000000000000000 : ℝ)) (alpha := (569804974851/488500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-479448363/2500000000 : ℝ)*X 0 0+(5438206283/10000000000 : ℝ)*X 0 1+(521520763/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676763977/5000000000 : ℝ)*X 1 0+(-1016048221/5000000000 : ℝ)*X 1 1+(208608337/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353528257/10000000000 : ℝ)*X 2 0+(2607603869/5000000000 : ℝ)*X 2 1+(-508024237/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((85706631/200000000 : ℝ)*X 0 0+(80891523/200000000 : ℝ)*X 0 1+(283656701/625000000 : ℝ)*X 0 2+(85706631/200000000 : ℝ)*X 1 0+(80891523/200000000 : ℝ)*X 1 1+(283656701/625000000 : ℝ)*X 1 2+(85706631/200000000 : ℝ)*X 2 0+(80891523/200000000 : ℝ)*X 2 1+(283656701/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-119864011/625000000 : ℝ)*X 0 0+(5216354751/10000000000 : ℝ)*X 0 1+(5437050823/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5295299047/10000000000 : ℝ)*X 1 0+(-905126897/5000000000 : ℝ)*X 1 1+(2718525393/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((330956187/625000000 : ℝ)*X 2 0+(5437050813/10000000000 : ℝ)*X 2 1+(-226281729/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((214269957/500000000 : ℝ)*X 0 0+(566995953/1250000000 : ℝ)*X 0 1+(1011783841/2500000000 : ℝ)*X 0 2+(214269957/500000000 : ℝ)*X 1 0+(566995953/1250000000 : ℝ)*X 1 1+(1011783841/2500000000 : ℝ)*X 1 2+(214269957/500000000 : ℝ)*X 2 0+(566995953/1250000000 : ℝ)*X 2 1+(1011783841/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2326749270346470955291282161/244250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (95753491/5000000000000 : ℝ)*(base19) + (376283079/20000000000000 : ℝ)*(base23) + (1923679/1250000000000 : ℝ)*(lower2) + (64895841/10000000000000 : ℝ)*(upper3) + (7585001/100000000000000 : ℝ)*(upper5) + (3254501249898263/100000000000000 : ℝ)*(major0) + (3254501249898263/100000000000000 : ℝ)*(major1) + (3254501249898263/100000000000000 : ℝ)*(major2) + (1121093518878393/25000000000000 : ℝ)*(sp0) + (2242200141337539/50000000000000 : ℝ)*(sp1) + (140137509885297/3125000000000 : ℝ)*(sp2) + (2024582783208139/100000000000000 : ℝ)*(sp3) + (14061115663/50000000000000 : ℝ)*(sp4) + (2150163363/12500000000000 : ℝ)*(sp7) + (2024599984515043/100000000000000 : ℝ)*(f.failure) + (2242201098872449/50000000000000 : ℝ)*(f.sum) + (7062057614437/24425000000000000000000000000 : ℝ)*base66 + (2927393596744202613/488500000000000000000000000000000 : ℝ)*base67 + (1324109196779202613/488500000000000000000000000000000 : ℝ)*base69 + (1609413379645202613/488500000000000000000000000000000 : ℝ)*base71 + (73393687704063/24425000000000000000000000000 : ℝ)*base73 + (3358469160437202613/488500000000000000000000000000000 : ℝ)*base75 + (1426450041020797387/488500000000000000000000000000000 : ℝ)*base78 + (597231236880797387/488500000000000000000000000000000 : ℝ)*base80 + (42999786200587/24425000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (15473361/2000000000000000000000 : ℝ)*base90 + (15473361/2000000000000000000000 : ℝ)*base92 + (15473361/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (631789597943639746712053539/61062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (864698341/50000000000000 : ℝ)*(base19) + (1811910023/100000000000000 : ℝ)*(base23) + (203078203/100000000000000 : ℝ)*(upper3) + (32748541/50000000000000 : ℝ)*(lower4) + (111519881/50000000000000 : ℝ)*(upper5) + (822101072859221/25000000000000 : ℝ)*(major0) + (822101072859221/25000000000000 : ℝ)*(major1) + (822101072859221/25000000000000 : ℝ)*(major2) + (1603817861/6250000000000 : ℝ)*(sp1) + (818633857/3125000000000 : ℝ)*(sp2) + (566389679286813/12500000000000 : ℝ)*(sp4) + (2265545021906023/50000000000000 : ℝ)*(sp5) + (4531089426101057/100000000000000 : ℝ)*(sp6) + (1022845401846203/50000000000000 : ℝ)*(sp7) + (1022845401846203/50000000000000 : ℝ)*(f.failure) + (566389679286813/12500000000000 : ℝ)*(f.sum) + (4176310841879/6106250000000000000000000000 : ℝ)*base66 + (1111890109252529329/122125000000000000000000000000000 : ℝ)*base68 + (1413498646909529329/122125000000000000000000000000000 : ℝ)*base70 + (423579132310779329/122125000000000000000000000000000 : ℝ)*base72 + (18404267863173/3053125000000000000000000000 : ℝ)*base73 + (1582746086688029329/122125000000000000000000000000000 : ℝ)*base76 + (75308436428529329/122125000000000000000000000000000 : ℝ)*base78 + (3407150805099154329/122125000000000000000000000000000 : ℝ)*base80 + (2785021759029/6106250000000000000000000000 : ℝ)*base82 + (1878681/1000000000000000000000 : ℝ)*base90 + (1878681/1000000000000000000000 : ℝ)*base92 + (1878681/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1479_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32149573/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (623/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1069/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10769/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1479_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1479_s5_0 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1917880943/10000000000 : ℝ)*x 0 + (271881969/500000000 : ℝ)*x 1 + (5215716737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1917880943/10000000000 : ℝ)^4455 ≤ (11715909018161/100000000000000 : ℝ)^3431 := by
    have hnat : (1917880943 : ℕ)^4455*100000000000000^3431 ≤ 11715909018161^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1917880943 10000000000 11715909018161 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (271881969/500000000 : ℝ)^4455 ≤ (45335900313013/100000000000000 : ℝ)^3431 := by
    have hnat : (271881969 : ℕ)^4455*100000000000000^3431 ≤ 45335900313013^3431*500000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271881969 500000000 45335900313013 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215716737/10000000000 : ℝ)^4455 ≤ (53685238311/125000000000 : ℝ)^3431 := by
    have hnat : (5215716737 : ℕ)^4455*125000000000^3431 ≤ 53685238311^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215716737 10000000000 53685238311 125000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1917880943/10000000000 : ℝ), (271881969/500000000 : ℝ), (5215716737/10000000000 : ℝ)] ![(11715909018161/100000000000000 : ℝ), (45335900313013/100000000000000 : ℝ), (53685238311/125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1917880943/10000000000 : ℝ)|^4455 ≤ (11715909018161/100000000000000 : ℝ)^3431
        have hw : |(-1917880943/10000000000 : ℝ)|=(1917880943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(271881969/500000000 : ℝ)|^4455 ≤ (45335900313013/100000000000000 : ℝ)^3431
        have hw : |(271881969/500000000 : ℝ)|=(271881969/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215716737/10000000000 : ℝ)|^4455 ≤ (53685238311/125000000000 : ℝ)^3431
        have hw : |(5215716737/10000000000 : ℝ)|=(5215716737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s5_1 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676690347/5000000000 : ℝ)*x 0 + (-203161959/1000000000 : ℝ)*x 1 + (1303929187/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676690347/5000000000 : ℝ)^4455 ≤ (8885170403867/20000000000000 : ℝ)^3431 := by
    have hnat : (2676690347 : ℕ)^4455*20000000000000^3431 ≤ 8885170403867^3431*5000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676690347 5000000000 8885170403867 20000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (203161959/1000000000 : ℝ)^4455 ≤ (394561162133/3125000000000 : ℝ)^3431 := by
    have hnat : (203161959 : ℕ)^4455*3125000000000^3431 ≤ 394561162133^3431*1000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203161959 1000000000 394561162133 3125000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1303929187/2500000000 : ℝ)^4455 ≤ (10737047691603/25000000000000 : ℝ)^3431 := by
    have hnat : (1303929187 : ℕ)^4455*25000000000000^3431 ≤ 10737047691603^3431*2500000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303929187 2500000000 10737047691603 25000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676690347/5000000000 : ℝ), (-203161959/1000000000 : ℝ), (1303929187/2500000000 : ℝ)] ![(8885170403867/20000000000000 : ℝ), (394561162133/3125000000000 : ℝ), (10737047691603/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676690347/5000000000 : ℝ)|^4455 ≤ (8885170403867/20000000000000 : ℝ)^3431
        have hw : |(2676690347/5000000000 : ℝ)|=(2676690347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-203161959/1000000000 : ℝ)|^4455 ≤ (394561162133/3125000000000 : ℝ)^3431
        have hw : |(-203161959/1000000000 : ℝ)|=(203161959/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1303929187/2500000000 : ℝ)|^4455 ≤ (10737047691603/25000000000000 : ℝ)^3431
        have hw : |(1303929187/2500000000 : ℝ)|=(1303929187/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s5_2 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338345173/2500000000 : ℝ)*x 0 + (5215716757/10000000000 : ℝ)*x 1 + (-1015809791/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338345173/2500000000 : ℝ)^4455 ≤ (5553231499723/12500000000000 : ℝ)^3431 := by
    have hnat : (1338345173 : ℕ)^4455*12500000000000^3431 ≤ 5553231499723^3431*2500000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338345173 2500000000 5553231499723 12500000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215716757/10000000000 : ℝ)^4455 ≤ (536852385783/1250000000000 : ℝ)^3431 := by
    have hnat : (5215716757 : ℕ)^4455*1250000000000^3431 ≤ 536852385783^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215716757 10000000000 536852385783 1250000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1015809791/5000000000 : ℝ)^4455 ≤ (126259571237/1000000000000 : ℝ)^3431 := by
    have hnat : (1015809791 : ℕ)^4455*1000000000000^3431 ≤ 126259571237^3431*5000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1015809791 5000000000 126259571237 1000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338345173/2500000000 : ℝ), (5215716757/10000000000 : ℝ), (-1015809791/5000000000 : ℝ)] ![(5553231499723/12500000000000 : ℝ), (536852385783/1250000000000 : ℝ), (126259571237/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338345173/2500000000 : ℝ)|^4455 ≤ (5553231499723/12500000000000 : ℝ)^3431
        have hw : |(1338345173/2500000000 : ℝ)|=(1338345173/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215716757/10000000000 : ℝ)|^4455 ≤ (536852385783/1250000000000 : ℝ)^3431
        have hw : |(5215716757/10000000000 : ℝ)|=(5215716757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1015809791/5000000000 : ℝ)|^4455 ≤ (126259571237/1000000000000 : ℝ)^3431
        have hw : |(-1015809791/5000000000 : ℝ)|=(1015809791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s5_3 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2142692057/5000000000 : ℝ)*x 0 + (404576129/1000000000 : ℝ)*x 1 + (453731037/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2142692057/5000000000 : ℝ)^4455 ≤ (33277842486577/100000000000000 : ℝ)^3431 := by
    have hnat : (2142692057 : ℕ)^4455*100000000000000^3431 ≤ 33277842486577^3431*5000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142692057 5000000000 33277842486577 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (404576129/1000000000 : ℝ)^4455 ≤ (3088214183391/10000000000000 : ℝ)^3431 := by
    have hnat : (404576129 : ℕ)^4455*10000000000000^3431 ≤ 3088214183391^3431*1000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404576129 1000000000 3088214183391 10000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (453731037/1000000000 : ℝ)^4455 ≤ (716800313409/2000000000000 : ℝ)^3431 := by
    have hnat : (453731037 : ℕ)^4455*2000000000000^3431 ≤ 716800313409^3431*1000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453731037 1000000000 716800313409 2000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2142692057/5000000000 : ℝ), (404576129/1000000000 : ℝ), (453731037/1000000000 : ℝ)] ![(33277842486577/100000000000000 : ℝ), (3088214183391/10000000000000 : ℝ), (716800313409/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2142692057/5000000000 : ℝ)|^4455 ≤ (33277842486577/100000000000000 : ℝ)^3431
        have hw : |(2142692057/5000000000 : ℝ)|=(2142692057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(404576129/1000000000 : ℝ)|^4455 ≤ (3088214183391/10000000000000 : ℝ)^3431
        have hw : |(404576129/1000000000 : ℝ)|=(404576129/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(453731037/1000000000 : ℝ)|^4455 ≤ (716800313409/2000000000000 : ℝ)^3431
        have hw : |(453731037/1000000000 : ℝ)|=(453731037/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s5_4 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1917911429/10000000000 : ℝ)*x 0 + (2608426251/5000000000 : ℝ)*x 1 + (1359123811/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1917911429/10000000000 : ℝ)^4455 ≤ (468646033317/4000000000000 : ℝ)^3431 := by
    have hnat : (1917911429 : ℕ)^4455*4000000000000^3431 ≤ 468646033317^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1917911429 10000000000 468646033317 4000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608426251/5000000000 : ℝ)^4455 ≤ (42960334612447/100000000000000 : ℝ)^3431 := by
    have hnat : (2608426251 : ℕ)^4455*100000000000000^3431 ≤ 42960334612447^3431*5000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608426251 5000000000 42960334612447 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1359123811/2500000000 : ℝ)^4455 ≤ (4532351454771/10000000000000 : ℝ)^3431 := by
    have hnat : (1359123811 : ℕ)^4455*10000000000000^3431 ≤ 4532351454771^3431*2500000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359123811 2500000000 4532351454771 10000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1917911429/10000000000 : ℝ), (2608426251/5000000000 : ℝ), (1359123811/2500000000 : ℝ)] ![(468646033317/4000000000000 : ℝ), (42960334612447/100000000000000 : ℝ), (4532351454771/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1917911429/10000000000 : ℝ)|^4455 ≤ (468646033317/4000000000000 : ℝ)^3431
        have hw : |(-1917911429/10000000000 : ℝ)|=(1917911429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608426251/5000000000 : ℝ)|^4455 ≤ (42960334612447/100000000000000 : ℝ)^3431
        have hw : |(2608426251/5000000000 : ℝ)|=(2608426251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1359123811/2500000000 : ℝ)|^4455 ≤ (4532351454771/10000000000000 : ℝ)^3431
        have hw : |(1359123811/2500000000 : ℝ)|=(1359123811/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s5_5 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295432601/10000000000 : ℝ)*x 0 + (-1810841231/10000000000 : ℝ)*x 1 + (2718247591/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295432601/10000000000 : ℝ)^4455 ≤ (43802447574243/100000000000000 : ℝ)^3431 := by
    have hnat : (5295432601 : ℕ)^4455*100000000000000^3431 ≤ 43802447574243^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295432601 10000000000 43802447574243 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1810841231/10000000000 : ℝ)^4455 ≤ (1087403854049/10000000000000 : ℝ)^3431 := by
    have hnat : (1810841231 : ℕ)^4455*10000000000000^3431 ≤ 1087403854049^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1810841231 10000000000 1087403854049 10000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2718247591/5000000000 : ℝ)^4455 ≤ (22661756938277/50000000000000 : ℝ)^3431 := by
    have hnat : (2718247591 : ℕ)^4455*50000000000000^3431 ≤ 22661756938277^3431*5000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718247591 5000000000 22661756938277 50000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295432601/10000000000 : ℝ), (-1810841231/10000000000 : ℝ), (2718247591/5000000000 : ℝ)] ![(43802447574243/100000000000000 : ℝ), (1087403854049/10000000000000 : ℝ), (22661756938277/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295432601/10000000000 : ℝ)|^4455 ≤ (43802447574243/100000000000000 : ℝ)^3431
        have hw : |(5295432601/10000000000 : ℝ)|=(5295432601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1810841231/10000000000 : ℝ)|^4455 ≤ (1087403854049/10000000000000 : ℝ)^3431
        have hw : |(-1810841231/10000000000 : ℝ)|=(1810841231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2718247591/5000000000 : ℝ)|^4455 ≤ (22661756938277/50000000000000 : ℝ)^3431
        have hw : |(2718247591/5000000000 : ℝ)|=(2718247591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s5_6 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165482267/312500000 : ℝ)*x 0 + (5436495203/10000000000 : ℝ)*x 1 + (-5658879/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165482267/312500000 : ℝ)^4455 ≤ (8760489392407/20000000000000 : ℝ)^3431 := by
    have hnat : (165482267 : ℕ)^4455*20000000000000^3431 ≤ 8760489392407^3431*312500000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165482267 312500000 8760489392407 20000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5436495203/10000000000 : ℝ)^4455 ≤ (45323514103881/100000000000000 : ℝ)^3431 := by
    have hnat : (5436495203 : ℕ)^4455*100000000000000^3431 ≤ 45323514103881^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436495203 10000000000 45323514103881 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5658879/31250000 : ℝ)^4455 ≤ (1359254865319/12500000000000 : ℝ)^3431 := by
    have hnat : (5658879 : ℕ)^4455*12500000000000^3431 ≤ 1359254865319^3431*31250000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5658879 31250000 1359254865319 12500000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165482267/312500000 : ℝ), (5436495203/10000000000 : ℝ), (-5658879/31250000 : ℝ)] ![(8760489392407/20000000000000 : ℝ), (45323514103881/100000000000000 : ℝ), (1359254865319/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165482267/312500000 : ℝ)|^4455 ≤ (8760489392407/20000000000000 : ℝ)^3431
        have hw : |(165482267/312500000 : ℝ)|=(165482267/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5436495203/10000000000 : ℝ)|^4455 ≤ (45323514103881/100000000000000 : ℝ)^3431
        have hw : |(5436495203/10000000000 : ℝ)|=(5436495203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5658879/31250000 : ℝ)|^4455 ≤ (1359254865319/12500000000000 : ℝ)^3431
        have hw : |(-5658879/31250000 : ℝ)|=(5658879/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s5_7 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2142725843/5000000000 : ℝ)*x 0 + (4534794591/10000000000 : ℝ)*x 1 + (4048295459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2142725843/5000000000 : ℝ)^4455 ≤ (16639261910391/50000000000000 : ℝ)^3431 := by
    have hnat : (2142725843 : ℕ)^4455*50000000000000^3431 ≤ 16639261910391^3431*5000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142725843 5000000000 16639261910391 50000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4534794591/10000000000 : ℝ)^4455 ≤ (35814214866381/100000000000000 : ℝ)^3431 := by
    have hnat : (4534794591 : ℕ)^4455*100000000000000^3431 ≤ 35814214866381^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4534794591 10000000000 35814214866381 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4048295459/10000000000 : ℝ)^4455 ≤ (30907261294523/100000000000000 : ℝ)^3431 := by
    have hnat : (4048295459 : ℕ)^4455*100000000000000^3431 ≤ 30907261294523^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4048295459 10000000000 30907261294523 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2142725843/5000000000 : ℝ), (4534794591/10000000000 : ℝ), (4048295459/10000000000 : ℝ)] ![(16639261910391/50000000000000 : ℝ), (35814214866381/100000000000000 : ℝ), (30907261294523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2142725843/5000000000 : ℝ)|^4455 ≤ (16639261910391/50000000000000 : ℝ)^3431
        have hw : |(2142725843/5000000000 : ℝ)|=(2142725843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4534794591/10000000000 : ℝ)|^4455 ≤ (35814214866381/100000000000000 : ℝ)^3431
        have hw : |(4534794591/10000000000 : ℝ)|=(4534794591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4048295459/10000000000 : ℝ)|^4455 ≤ (30907261294523/100000000000000 : ℝ)^3431
        have hw : |(4048295459/10000000000 : ℝ)|=(4048295459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1479_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32149573/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10769/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (539/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15477/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10769/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10769/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10769/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10769/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10769/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10769/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10769/100000 : ℝ) ^ (4453/1024 : ℝ) ≤ (193257389655283/3125000000000000000 : ℝ) := by
    have hpowers : (10769/100000 : ℝ)^4453 ≤ (193257389655283/3125000000000000000 : ℝ)^1024 := by
      have hnat : (10769 : ℕ)^4453*3125000000000000000^1024 ≤ 193257389655283^1024*100000^4453 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10769 100000 193257389655283 3125000000000000000 4453 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10769/100000 : ℝ)) (X := (193257389655283/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4453 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15489/100000 : ℝ) ^ (4453/1024 : ℝ) ≤ (30040633847278789/100000000000000000000 : ℝ) := by
    have hpowers : (15489/100000 : ℝ)^4453 ≤ (30040633847278789/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15489 : ℕ)^4453*100000000000000000000^1024 ≤ 30040633847278789^1024*100000^4453 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15489 100000 30040633847278789 100000000000000000000 4453 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15489/100000 : ℝ)) (X := (30040633847278789/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4453 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562693257389655283/1562500000000000000 : ℝ) ≤ (1000028440856039/1000000000000000 : ℝ) ^ (4453/1024 : ℝ) := by
    have hpowers : (1562693257389655283/1562500000000000000 : ℝ)^1024 ≤ (1000028440856039/1000000000000000 : ℝ)^4453 := by
      have hnat : (1562693257389655283 : ℕ)^1024*1000000000000000^4453 ≤ 1000028440856039^4453*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562693257389655283 1562500000000000000 1000028440856039 1000000000000000 1024 4453 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000028440856039/1000000000000000 : ℝ)) (X := (1562693257389655283/1562500000000000000 : ℝ)) (by norm_num) 4453 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20007244974063249569/20000000000000000000 : ℝ) ≤ (10000832901294473/10000000000000000 : ℝ) ^ (4453/1024 : ℝ) := by
    have hpowers : (20007244974063249569/20000000000000000000 : ℝ)^1024 ≤ (10000832901294473/10000000000000000 : ℝ)^4453 := by
      have hnat : (20007244974063249569 : ℕ)^1024*10000000000000000^4453 ≤ 10000832901294473^4453*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20007244974063249569 20000000000000000000 10000832901294473 10000000000000000 1024 4453 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000832901294473/10000000000000000 : ℝ)) (X := (20007244974063249569/20000000000000000000 : ℝ)) (by norm_num) 4453 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030040633847278789/50000000000000000000 : ℝ) ≤ (2500345348507139/2500000000000000 : ℝ) ^ (4453/1024 : ℝ) := by
    have hpowers : (50030040633847278789/50000000000000000000 : ℝ)^1024 ≤ (2500345348507139/2500000000000000 : ℝ)^4453 := by
      have hnat : (50030040633847278789 : ℕ)^1024*2500000000000000^4453 ≤ 2500345348507139^4453*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030040633847278789 50000000000000000000 2500345348507139 2500000000000000 1024 4453 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500345348507139/2500000000000000 : ℝ)) (X := (50030040633847278789/50000000000000000000 : ℝ)) (by norm_num) 4453 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(193257389655283/3125000000000000000 : ℝ) ≤ ((23594764485949180573/23600000000000000000 : ℝ)+2*(548492734083/472000000000000 : ℝ)*(10769/100000 : ℝ))^(4453/1024 : ℝ) := by
    rw [show (23594764485949180573/23600000000000000000 : ℝ)+2*(548492734083/472000000000000 : ℝ)*(10769/100000 : ℝ)=(1000028440856039/1000000000000000 : ℝ) by norm_num, show 1+2*(193257389655283/3125000000000000000 : ℝ)=(1562693257389655283/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30040633847278789/100000000000000000000 : ℝ)+(193257389655283/3125000000000000000 : ℝ) ≤ ((23594764485949180573/23600000000000000000 : ℝ)+(548492734083/472000000000000 : ℝ)*((15489/100000 : ℝ)+(10769/100000 : ℝ)))^(4453/1024 : ℝ) := by
    rw [show (23594764485949180573/23600000000000000000 : ℝ)+(548492734083/472000000000000 : ℝ)*((15489/100000 : ℝ)+(10769/100000 : ℝ))=(10000832901294473/10000000000000000 : ℝ) by norm_num, show 1+(30040633847278789/100000000000000000000 : ℝ)+(193257389655283/3125000000000000000 : ℝ)=(20007244974063249569/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30040633847278789/100000000000000000000 : ℝ) ≤ ((23594764485949180573/23600000000000000000 : ℝ)+2*(548492734083/472000000000000 : ℝ)*(15489/100000 : ℝ))^(4453/1024 : ℝ) := by
    rw [show (23594764485949180573/23600000000000000000 : ℝ)+2*(548492734083/472000000000000 : ℝ)*(15489/100000 : ℝ)=(2500345348507139/2500000000000000 : ℝ) by norm_num, show 1+2*(30040633847278789/100000000000000000000 : ℝ)=(50030040633847278789/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23594764485949180573/23600000000000000000 : ℝ)*(X 1 0+X 2 0)+(548492734083/472000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4453/1024 : ℝ)) (lo := (10769/100000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (23594764485949180573/23600000000000000000 : ℝ)) (alpha := (548492734083/472000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23594764485949180573/23600000000000000000 : ℝ)*(X 0 1+X 2 1)+(548492734083/472000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4453/1024 : ℝ)) (lo := (10769/100000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (23594764485949180573/23600000000000000000 : ℝ)) (alpha := (548492734083/472000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23594764485949180573/23600000000000000000 : ℝ)*(X 0 2+X 1 2)+(548492734083/472000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4453/1024 : ℝ)) (lo := (10769/100000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (23594764485949180573/23600000000000000000 : ℝ)) (alpha := (548492734083/472000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1917880943/10000000000 : ℝ)*X 0 0+(271881969/500000000 : ℝ)*X 0 1+(5215716737/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676690347/5000000000 : ℝ)*X 1 0+(-203161959/1000000000 : ℝ)*X 1 1+(1303929187/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338345173/2500000000 : ℝ)*X 2 0+(5215716757/10000000000 : ℝ)*X 2 1+(-1015809791/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2142692057/5000000000 : ℝ)*X 0 0+(404576129/1000000000 : ℝ)*X 0 1+(453731037/1000000000 : ℝ)*X 0 2+(2142692057/5000000000 : ℝ)*X 1 0+(404576129/1000000000 : ℝ)*X 1 1+(453731037/1000000000 : ℝ)*X 1 2+(2142692057/5000000000 : ℝ)*X 2 0+(404576129/1000000000 : ℝ)*X 2 1+(453731037/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1917911429/10000000000 : ℝ)*X 0 0+(2608426251/5000000000 : ℝ)*X 0 1+(1359123811/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5295432601/10000000000 : ℝ)*X 1 0+(-1810841231/10000000000 : ℝ)*X 1 1+(2718247591/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((165482267/312500000 : ℝ)*X 2 0+(5436495203/10000000000 : ℝ)*X 2 1+(-5658879/31250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2142725843/5000000000 : ℝ)*X 0 0+(4534794591/10000000000 : ℝ)*X 0 1+(4048295459/10000000000 : ℝ)*X 0 2+(2142725843/5000000000 : ℝ)*X 1 0+(4534794591/10000000000 : ℝ)*X 1 1+(4048295459/10000000000 : ℝ)*X 1 2+(2142725843/5000000000 : ℝ)*X 2 0+(4534794591/10000000000 : ℝ)*X 2 1+(4048295459/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (42874830854488521134367093/4720000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1629495933/100000000000000 : ℝ)*(base19) + (1535379781/100000000000000 : ℝ)*(base23) + (9896547/20000000000000 : ℝ)*(lower2) + (219911331/100000000000000 : ℝ)*(upper3) + (1245121/781250000000 : ℝ)*(upper5) + (13081069380751/400000000000 : ℝ)*(major0) + (13081069380751/400000000000 : ℝ)*(major1) + (13081069380751/400000000000 : ℝ)*(major2) + (4506100862416999/100000000000000 : ℝ)*(sp0) + (2253062403991951/50000000000000 : ℝ)*(sp1) + (4506124902100053/100000000000000 : ℝ)*(sp2) + (2034395878699171/100000000000000 : ℝ)*(sp3) + (6393765709/25000000000000 : ℝ)*(sp4) + (23576969/195312500000 : ℝ)*(sp7) + (20344079501073/1000000000000 : ℝ)*(f.failure) + (901225287495967/20000000000000 : ℝ)*(f.sum) + (1429736657993/472000000000000000000000000 : ℝ)*base65 + (95007034522800323/9440000000000000000000000000000 : ℝ)*base67 + (85110178746640323/9440000000000000000000000000000 : ℝ)*base69 + (24379798228400323/9440000000000000000000000000000 : ℝ)*base71 + (2644798962289/472000000000000000000000000 : ℝ)*base73 + (152105609068080323/9440000000000000000000000000000 : ℝ)*base75 + (156985473013680323/9440000000000000000000000000000 : ℝ)*base77 + (280172145257040323/9440000000000000000000000000000 : ℝ)*base79 + (150323733407/472000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (8171/20000000000000000000 : ℝ)*base90 + (8171/20000000000000000000 : ℝ)*base92 + (8171/20000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6333117578214223597533/737500000000000000000000000 : ℝ) := by norm_num
    linear_combination (13612183/1000000000000 : ℝ)*(base19) + (1415580429/100000000000000 : ℝ)*(base23) + (45718803/25000000000000 : ℝ)*(upper3) + (13959951/25000000000000 : ℝ)*(lower4) + (211611057/100000000000000 : ℝ)*(upper5) + (103255454984483/3125000000000 : ℝ)*(major0) + (103255454984483/3125000000000 : ℝ)*(major1) + (103255454984483/3125000000000 : ℝ)*(major2) + (18574720021/100000000000000 : ℝ)*(sp1) + (2298077709/12500000000000 : ℝ)*(sp2) + (2276423733813691/50000000000000 : ℝ)*(sp4) + (2276413765844531/50000000000000 : ℝ)*(sp5) + (2276413833712641/50000000000000 : ℝ)*(sp6) + (1027750682568461/50000000000000 : ℝ)*(sp7) + (1027750682568461/50000000000000 : ℝ)*(f.failure) + (2276423733813691/50000000000000 : ℝ)*(f.sum) + (1112002114059/184375000000000000000000000 : ℝ)*base66 + (82923912366998759/73750000000000000000000000000000 : ℝ)*base67 + (716457819041998759/73750000000000000000000000000000 : ℝ)*base69 + (256970416455501241/73750000000000000000000000000000 : ℝ)*base72 + (116809217241/184375000000000000000000000 : ℝ)*base73 + (361659490028001241/73750000000000000000000000000000 : ℝ)*base76 + (199013949160501241/73750000000000000000000000000000 : ℝ)*base78 + (162627736149498759/73750000000000000000000000000000 : ℝ)*base79 + (135624143191/184375000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (4417153/1000000000000000000000 : ℝ)*base89 + (4417153/1000000000000000000000 : ℝ)*base91 + (4417153/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1479_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32149573/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10769/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (539/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15477/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1479_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1479_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32149573/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2017/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (407/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (539/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15477/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1479_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1479_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1479_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32149573/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2017/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (407/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (539/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15477/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1479_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
