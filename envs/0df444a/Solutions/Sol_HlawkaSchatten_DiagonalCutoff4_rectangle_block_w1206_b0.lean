-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1206_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:04:50.226391+00:00
-- url     : https://prove2.me/submissions/77048af8-3c66-4522-833e-68e5415dab1b

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
theorem support_rectangle_w1206_s0_0 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-187171919/1000000000 : ℝ)*x 0 + (3019827893/5000000000 : ℝ)*x 1 + (957702599/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (187171919/1000000000 : ℝ)^8399 ≤ (2180674994733/20000000000000 : ℝ)^6351 := by
    have hnat : (187171919 : ℕ)^8399*20000000000000^6351 ≤ 2180674994733^6351*1000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187171919 1000000000 2180674994733 20000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3019827893/5000000000 : ℝ)^8399 ≤ (51332856083739/100000000000000 : ℝ)^6351 := by
    have hnat : (3019827893 : ℕ)^8399*100000000000000^6351 ≤ 51332856083739^6351*5000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3019827893 5000000000 51332856083739 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (957702599/2000000000 : ℝ)^8399 ≤ (9440942229831/25000000000000 : ℝ)^6351 := by
    have hnat : (957702599 : ℕ)^8399*25000000000000^6351 ≤ 9440942229831^6351*2000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      957702599 2000000000 9440942229831 25000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-187171919/1000000000 : ℝ), (3019827893/5000000000 : ℝ), (957702599/2000000000 : ℝ)] ![(2180674994733/20000000000000 : ℝ), (51332856083739/100000000000000 : ℝ), (9440942229831/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-187171919/1000000000 : ℝ)|^8399 ≤ (2180674994733/20000000000000 : ℝ)^6351
        have hw : |(-187171919/1000000000 : ℝ)|=(187171919/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3019827893/5000000000 : ℝ)|^8399 ≤ (51332856083739/100000000000000 : ℝ)^6351
        have hw : |(3019827893/5000000000 : ℝ)|=(3019827893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(957702599/2000000000 : ℝ)|^8399 ≤ (9440942229831/25000000000000 : ℝ)^6351
        have hw : |(957702599/2000000000 : ℝ)|=(957702599/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s0_1 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5513187383/10000000000 : ℝ)*x 0 + (-12939759/50000000 : ℝ)*x 1 + (2394256493/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5513187383/10000000000 : ℝ)^8399 ≤ (22750093593741/50000000000000 : ℝ)^6351 := by
    have hnat : (5513187383 : ℕ)^8399*50000000000000^6351 ≤ 22750093593741^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5513187383 10000000000 22750093593741 50000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (12939759/50000000 : ℝ)^8399 ≤ (16736043969111/100000000000000 : ℝ)^6351 := by
    have hnat : (12939759 : ℕ)^8399*100000000000000^6351 ≤ 16736043969111^6351*50000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12939759 50000000 16736043969111 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2394256493/5000000000 : ℝ)^8399 ≤ (37763768825459/100000000000000 : ℝ)^6351 := by
    have hnat : (2394256493 : ℕ)^8399*100000000000000^6351 ≤ 37763768825459^6351*5000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2394256493 5000000000 37763768825459 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5513187383/10000000000 : ℝ), (-12939759/50000000 : ℝ), (2394256493/5000000000 : ℝ)] ![(22750093593741/50000000000000 : ℝ), (16736043969111/100000000000000 : ℝ), (37763768825459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5513187383/10000000000 : ℝ)|^8399 ≤ (22750093593741/50000000000000 : ℝ)^6351
        have hw : |(5513187383/10000000000 : ℝ)|=(5513187383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-12939759/50000000 : ℝ)|^8399 ≤ (16736043969111/100000000000000 : ℝ)^6351
        have hw : |(-12939759/50000000 : ℝ)|=(12939759/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2394256493/5000000000 : ℝ)|^8399 ≤ (37763768825459/100000000000000 : ℝ)^6351
        have hw : |(2394256493/5000000000 : ℝ)|=(2394256493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s0_2 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1378296953/2500000000 : ℝ)*x 0 + (4788512557/10000000000 : ℝ)*x 1 + (-2587951777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1378296953/2500000000 : ℝ)^8399 ≤ (45500191869717/100000000000000 : ℝ)^6351 := by
    have hnat : (1378296953 : ℕ)^8399*100000000000000^6351 ≤ 45500191869717^6351*2500000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1378296953 2500000000 45500191869717 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4788512557/10000000000 : ℝ)^8399 ≤ (18881882175619/50000000000000 : ℝ)^6351 := by
    have hnat : (4788512557 : ℕ)^8399*50000000000000^6351 ≤ 18881882175619^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4788512557 10000000000 18881882175619 50000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2587951777/10000000000 : ℝ)^8399 ≤ (16736043772409/100000000000000 : ℝ)^6351 := by
    have hnat : (2587951777 : ℕ)^8399*100000000000000^6351 ≤ 16736043772409^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587951777 10000000000 16736043772409 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1378296953/2500000000 : ℝ), (4788512557/10000000000 : ℝ), (-2587951777/10000000000 : ℝ)] ![(45500191869717/100000000000000 : ℝ), (18881882175619/50000000000000 : ℝ), (16736043772409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1378296953/2500000000 : ℝ)|^8399 ≤ (45500191869717/100000000000000 : ℝ)^6351
        have hw : |(1378296953/2500000000 : ℝ)|=(1378296953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4788512557/10000000000 : ℝ)|^8399 ≤ (18881882175619/50000000000000 : ℝ)^6351
        have hw : |(4788512557/10000000000 : ℝ)|=(4788512557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2587951777/10000000000 : ℝ)|^8399 ≤ (16736043772409/100000000000000 : ℝ)^6351
        have hw : |(-2587951777/10000000000 : ℝ)|=(2587951777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s0_3 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1048965933/2500000000 : ℝ)*x 0 + (779574347/2500000000 : ℝ)*x 1 + (1127739769/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1048965933/2500000000 : ℝ)^8399 ≤ (7927440786511/25000000000000 : ℝ)^6351 := by
    have hnat : (1048965933 : ℕ)^8399*25000000000000^6351 ≤ 7927440786511^6351*2500000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048965933 2500000000 7927440786511 25000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (779574347/2500000000 : ℝ)^8399 ≤ (4182651799/19531250000 : ℝ)^6351 := by
    have hnat : (779574347 : ℕ)^8399*19531250000^6351 ≤ 4182651799^6351*2500000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      779574347 2500000000 4182651799 19531250000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1127739769/2000000000 : ℝ)^8399 ≤ (46875059624309/100000000000000 : ℝ)^6351 := by
    have hnat : (1127739769 : ℕ)^8399*100000000000000^6351 ≤ 46875059624309^6351*2000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127739769 2000000000 46875059624309 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1048965933/2500000000 : ℝ), (779574347/2500000000 : ℝ), (1127739769/2000000000 : ℝ)] ![(7927440786511/25000000000000 : ℝ), (4182651799/19531250000 : ℝ), (46875059624309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1048965933/2500000000 : ℝ)|^8399 ≤ (7927440786511/25000000000000 : ℝ)^6351
        have hw : |(1048965933/2500000000 : ℝ)|=(1048965933/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(779574347/2500000000 : ℝ)|^8399 ≤ (4182651799/19531250000 : ℝ)^6351
        have hw : |(779574347/2500000000 : ℝ)|=(779574347/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1127739769/2000000000 : ℝ)|^8399 ≤ (46875059624309/100000000000000 : ℝ)^6351
        have hw : |(1127739769/2000000000 : ℝ)|=(1127739769/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s0_4 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1876679443/10000000000 : ℝ)*x 0 + (15064859/31250000 : ℝ)*x 1 + (750784481/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1876679443/10000000000 : ℝ)^8399 ≤ (10941604152579/100000000000000 : ℝ)^6351 := by
    have hnat : (1876679443 : ℕ)^8399*100000000000000^6351 ≤ 10941604152579^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1876679443 10000000000 10941604152579 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (15064859/31250000 : ℝ)^8399 ≤ (4762549694951/12500000000000 : ℝ)^6351 := by
    have hnat : (15064859 : ℕ)^8399*12500000000000^6351 ≤ 4762549694951^6351*31250000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15064859 31250000 4762549694951 12500000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (750784481/1250000000 : ℝ)^8399 ≤ (3184874891571/6250000000000 : ℝ)^6351 := by
    have hnat : (750784481 : ℕ)^8399*6250000000000^6351 ≤ 3184874891571^6351*1250000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      750784481 1250000000 3184874891571 6250000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1876679443/10000000000 : ℝ), (15064859/31250000 : ℝ), (750784481/1250000000 : ℝ)] ![(10941604152579/100000000000000 : ℝ), (4762549694951/12500000000000 : ℝ), (3184874891571/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1876679443/10000000000 : ℝ)|^8399 ≤ (10941604152579/100000000000000 : ℝ)^6351
        have hw : |(-1876679443/10000000000 : ℝ)|=(1876679443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(15064859/31250000 : ℝ)|^8399 ≤ (4762549694951/12500000000000 : ℝ)^6351
        have hw : |(15064859/31250000 : ℝ)|=(15064859/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(750784481/1250000000 : ℝ)|^8399 ≤ (3184874891571/6250000000000 : ℝ)^6351
        have hw : |(750784481/1250000000 : ℝ)|=(750784481/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s0_5 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (646615811/1250000000 : ℝ)*x 0 + (-1370187049/10000000000 : ℝ)*x 1 + (6006277451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (646615811/1250000000 : ℝ)^8399 ≤ (41823961654781/100000000000000 : ℝ)^6351 := by
    have hnat : (646615811 : ℕ)^8399*100000000000000^6351 ≤ 41823961654781^6351*1250000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646615811 1250000000 41823961654781 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1370187049/10000000000 : ℝ)^8399 ≤ (7218022084359/100000000000000 : ℝ)^6351 := by
    have hnat : (1370187049 : ℕ)^8399*100000000000000^6351 ≤ 7218022084359^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1370187049 10000000000 7218022084359 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6006277451/10000000000 : ℝ)^8399 ≤ (1592438007837/3125000000000 : ℝ)^6351 := by
    have hnat : (6006277451 : ℕ)^8399*3125000000000^6351 ≤ 1592438007837^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6006277451 10000000000 1592438007837 3125000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(646615811/1250000000 : ℝ), (-1370187049/10000000000 : ℝ), (6006277451/10000000000 : ℝ)] ![(41823961654781/100000000000000 : ℝ), (7218022084359/100000000000000 : ℝ), (1592438007837/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(646615811/1250000000 : ℝ)|^8399 ≤ (41823961654781/100000000000000 : ℝ)^6351
        have hw : |(646615811/1250000000 : ℝ)|=(646615811/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1370187049/10000000000 : ℝ)|^8399 ≤ (7218022084359/100000000000000 : ℝ)^6351
        have hw : |(-1370187049/10000000000 : ℝ)|=(1370187049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6006277451/10000000000 : ℝ)|^8399 ≤ (1592438007837/3125000000000 : ℝ)^6351
        have hw : |(6006277451/10000000000 : ℝ)|=(6006277451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s0_6 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (646615909/1250000000 : ℝ)*x 0 + (6006276351/10000000000 : ℝ)*x 1 + (-1370187617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (646615909/1250000000 : ℝ)^8399 ≤ (20911985018803/50000000000000 : ℝ)^6351 := by
    have hnat : (646615909 : ℕ)^8399*50000000000000^6351 ≤ 20911985018803^6351*1250000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646615909 1250000000 20911985018803 50000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6006276351/10000000000 : ℝ)^8399 ≤ (6369750488599/12500000000000 : ℝ)^6351 := by
    have hnat : (6006276351 : ℕ)^8399*12500000000000^6351 ≤ 6369750488599^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6006276351 10000000000 6369750488599 12500000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1370187617/10000000000 : ℝ)^8399 ≤ (1443605208283/20000000000000 : ℝ)^6351 := by
    have hnat : (1370187617 : ℕ)^8399*20000000000000^6351 ≤ 1443605208283^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1370187617 10000000000 1443605208283 20000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(646615909/1250000000 : ℝ), (6006276351/10000000000 : ℝ), (-1370187617/10000000000 : ℝ)] ![(20911985018803/50000000000000 : ℝ), (6369750488599/12500000000000 : ℝ), (1443605208283/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(646615909/1250000000 : ℝ)|^8399 ≤ (20911985018803/50000000000000 : ℝ)^6351
        have hw : |(646615909/1250000000 : ℝ)|=(646615909/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6006276351/10000000000 : ℝ)|^8399 ≤ (6369750488599/12500000000000 : ℝ)^6351
        have hw : |(6006276351/10000000000 : ℝ)|=(6006276351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1370187617/10000000000 : ℝ)|^8399 ≤ (1443605208283/20000000000000 : ℝ)^6351
        have hw : |(-1370187617/10000000000 : ℝ)|=(1370187617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s0_7 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1051463807/2500000000 : ℝ)*x 0 + (5573751531/10000000000 : ℝ)*x 1 + (3185536711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051463807/2500000000 : ℝ)^8399 ≤ (31809660557071/100000000000000 : ℝ)^6351 := by
    have hnat : (1051463807 : ℕ)^8399*100000000000000^6351 ≤ 31809660557071^6351*2500000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051463807 2500000000 31809660557071 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5573751531/10000000000 : ℝ)^8399 ≤ (9232474078477/20000000000000 : ℝ)^6351 := by
    have hnat : (5573751531 : ℕ)^8399*20000000000000^6351 ≤ 9232474078477^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5573751531 10000000000 9232474078477 20000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3185536711/10000000000 : ℝ)^8399 ≤ (4405593806563/20000000000000 : ℝ)^6351 := by
    have hnat : (3185536711 : ℕ)^8399*20000000000000^6351 ≤ 4405593806563^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3185536711 10000000000 4405593806563 20000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051463807/2500000000 : ℝ), (5573751531/10000000000 : ℝ), (3185536711/10000000000 : ℝ)] ![(31809660557071/100000000000000 : ℝ), (9232474078477/20000000000000 : ℝ), (4405593806563/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051463807/2500000000 : ℝ)|^8399 ≤ (31809660557071/100000000000000 : ℝ)^6351
        have hw : |(1051463807/2500000000 : ℝ)|=(1051463807/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5573751531/10000000000 : ℝ)|^8399 ≤ (9232474078477/20000000000000 : ℝ)^6351
        have hw : |(5573751531/10000000000 : ℝ)|=(5573751531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3185536711/10000000000 : ℝ)|^8399 ≤ (4405593806563/20000000000000 : ℝ)^6351
        have hw : |(3185536711/10000000000 : ℝ)|=(3185536711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1206_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37680987/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (337/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6893/25000 : ℝ)*pair X 0 0 := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (4199/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4199 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4199*1^1024 ≤ 0^1024*1^4199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4199 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4199 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4199/1024 : ℝ) ≤ (466920338968598377/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4199 ≤ (466920338968598377/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4199*20000000000000000000^1024 ≤ 466920338968598377^1024*5^4199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 466920338968598377 20000000000000000000 4199 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (466920338968598377/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4199 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4199/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4199 := by
      have hnat : (1 : ℕ)^1024*1^4199 ≤ 1^4199*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4199 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20466920338968598377/20000000000000000000 : ℝ) ≤ (10056437613939069/10000000000000000 : ℝ) ^ (4199/1024 : ℝ) := by
    have hpowers : (20466920338968598377/20000000000000000000 : ℝ)^1024 ≤ (10056437613939069/10000000000000000 : ℝ)^4199 := by
      have hnat : (20466920338968598377 : ℕ)^1024*10000000000000000^4199 ≤ 10056437613939069^4199*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20466920338968598377 20000000000000000000 10056437613939069 10000000000000000 1024 4199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10056437613939069/10000000000000000 : ℝ)) (X := (20466920338968598377/20000000000000000000 : ℝ)) (by norm_num) 4199 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10466920338968598377/10000000000000000000 : ℝ) ≤ (5056437613939069/5000000000000000 : ℝ) ^ (4199/1024 : ℝ) := by
    have hpowers : (10466920338968598377/10000000000000000000 : ℝ)^1024 ≤ (5056437613939069/5000000000000000 : ℝ)^4199 := by
      have hnat : (10466920338968598377 : ℕ)^1024*5000000000000000^4199 ≤ 5056437613939069^4199*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10466920338968598377 10000000000000000000 5056437613939069 5000000000000000 1024 4199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5056437613939069/5000000000000000 : ℝ)) (X := (10466920338968598377/10000000000000000000 : ℝ)) (by norm_num) 4199 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(56437613939069/4000000000000000 : ℝ)*(0 : ℝ))^(4199/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(56437613939069/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(466920338968598377/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(56437613939069/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4199/1024 : ℝ) := by
    rw [show (1 : ℝ)+(56437613939069/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10056437613939069/10000000000000000 : ℝ) by norm_num, show 1+(466920338968598377/20000000000000000000 : ℝ)+(0 : ℝ)=(20466920338968598377/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(466920338968598377/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(56437613939069/4000000000000000 : ℝ)*(2/5 : ℝ))^(4199/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(56437613939069/4000000000000000 : ℝ)*(2/5 : ℝ)=(5056437613939069/5000000000000000 : ℝ) by norm_num, show 1+2*(466920338968598377/20000000000000000000 : ℝ)=(10466920338968598377/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(56437613939069/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4199/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (56437613939069/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(56437613939069/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4199/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (56437613939069/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(56437613939069/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4199/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (56437613939069/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-187171919/1000000000 : ℝ)*X 0 0+(3019827893/5000000000 : ℝ)*X 0 1+(957702599/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5513187383/10000000000 : ℝ)*X 1 0+(-12939759/50000000 : ℝ)*X 1 1+(2394256493/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1378296953/2500000000 : ℝ)*X 2 0+(4788512557/10000000000 : ℝ)*X 2 1+(-2587951777/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1048965933/2500000000 : ℝ)*X 0 0+(779574347/2500000000 : ℝ)*X 0 1+(1127739769/2000000000 : ℝ)*X 0 2+(1048965933/2500000000 : ℝ)*X 1 0+(779574347/2500000000 : ℝ)*X 1 1+(1127739769/2000000000 : ℝ)*X 1 2+(1048965933/2500000000 : ℝ)*X 2 0+(779574347/2500000000 : ℝ)*X 2 1+(1127739769/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1876679443/10000000000 : ℝ)*X 0 0+(15064859/31250000 : ℝ)*X 0 1+(750784481/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((646615811/1250000000 : ℝ)*X 1 0+(-1370187049/10000000000 : ℝ)*X 1 1+(6006277451/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((646615909/1250000000 : ℝ)*X 2 0+(6006276351/10000000000 : ℝ)*X 2 1+(-1370187617/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1051463807/2500000000 : ℝ)*X 0 0+(5573751531/10000000000 : ℝ)*X 0 1+(3185536711/10000000000 : ℝ)*X 0 2+(1051463807/2500000000 : ℝ)*X 1 0+(5573751531/10000000000 : ℝ)*X 1 1+(3185536711/10000000000 : ℝ)*X 1 2+(1051463807/2500000000 : ℝ)*X 2 0+(5573751531/10000000000 : ℝ)*X 2 1+(3185536711/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (99811913098179893129451/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10021583/25000000000000 : ℝ)*(base1) + (23563713/2000000000000 : ℝ)*(base19) + (1142935839/100000000000000 : ℝ)*(base23) + (24361021/25000000000000 : ℝ)*(base24) + (59610221/20000000000000 : ℝ)*(upper3) + (119604122075693/20000000000000 : ℝ)*(major0) + (119604122075693/20000000000000 : ℝ)*(major1) + (119604122075693/20000000000000 : ℝ)*(major2) + (399636586870339/50000000000000 : ℝ)*(sp0) + (799274386517363/100000000000000 : ℝ)*(sp1) + (79927432432309/10000000000000 : ℝ)*(sp2) + (396763330340021/100000000000000 : ℝ)*(sp3) + (607762167/25000000000000 : ℝ)*(sp4) + (2119274371/100000000000000 : ℝ)*(sp7) + (99191372425181/25000000000000 : ℝ)*(f.failure) + (799275564703013/100000000000000 : ℝ)*(f.sum) + (4976819309817/40000000000000000000000000000 : ℝ)*base65 + (160944883810183/80000000000000000000000000000 : ℝ)*base68 + (250924940050183/80000000000000000000000000000 : ℝ)*base70 + (187089428829817/80000000000000000000000000000 : ℝ)*base71 + (90420642010183/40000000000000000000000000000 : ℝ)*base74 + (8603472429817/80000000000000000000000000000 : ℝ)*base75 + (127802415250183/80000000000000000000000000000 : ℝ)*base78 + (6167154370183/80000000000000000000000000000 : ℝ)*base80 + (129816835890183/40000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (2516353/625000000000000000000 : ℝ)*base90 + (2516353/625000000000000000000 : ℝ)*base92 + (2516353/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1666140497452894489737459/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15183617/100000000000000 : ℝ)*(base1) + (138525841/6250000000000 : ℝ)*(base19) + (1184626241/50000000000000 : ℝ)*(base23) + (200197897/50000000000000 : ℝ)*(upper3) + (148265821/100000000000000 : ℝ)*(upper5) + (631116689408521/100000000000000 : ℝ)*(major0) + (631116689408521/100000000000000 : ℝ)*(major1) + (631116689408521/100000000000000 : ℝ)*(major2) + (4013079/80000000000 : ℝ)*(sp1) + (1349100563/25000000000000 : ℝ)*(sp2) + (421754775312217/50000000000000 : ℝ)*(sp4) + (84350230267861/10000000000000 : ℝ)*(sp5) + (421750884893041/50000000000000 : ℝ)*(sp6) + (418723550502521/100000000000000 : ℝ)*(sp7) + (209361782843069/50000000000000 : ℝ)*(f.failure) + (52719345965051/6250000000000 : ℝ)*(f.sum) + (50762638206949/200000000000000000000000000000 : ℝ)*base65 + (27167515006949/400000000000000000000000000000 : ℝ)*base67 + (2733060841793051/400000000000000000000000000000 : ℝ)*base70 + (536357456206949/400000000000000000000000000000 : ℝ)*base71 + (261198991206949/200000000000000000000000000000 : ℝ)*base73 + (238930927006949/400000000000000000000000000000 : ℝ)*base75 + (11662257006949/400000000000000000000000000000 : ℝ)*base77 + (140012624606949/400000000000000000000000000000 : ℝ)*base79 + (850093463193051/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (6470897/1250000000000000000000 : ℝ)*base90 + (6470897/1250000000000000000000 : ℝ)*base92 + (6470897/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1206_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37680987/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (337/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6893/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1206_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1206_s1_0 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-414348481/2000000000 : ℝ)*x 0 + (5684752631/10000000000 : ℝ)*x 1 + (5015377119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (414348481/2000000000 : ℝ)^8399 ≤ (6235126960577/50000000000000 : ℝ)^6351 := by
    have hnat : (414348481 : ℕ)^8399*50000000000000^6351 ≤ 6235126960577^6351*2000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414348481 2000000000 6235126960577 50000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5684752631/10000000000 : ℝ)^8399 ≤ (47382031917477/100000000000000 : ℝ)^6351 := by
    have hnat : (5684752631 : ℕ)^8399*100000000000000^6351 ≤ 47382031917477^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5684752631 10000000000 47382031917477 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5015377119/10000000000 : ℝ)^8399 ≤ (40147714142779/100000000000000 : ℝ)^6351 := by
    have hnat : (5015377119 : ℕ)^8399*100000000000000^6351 ≤ 40147714142779^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5015377119 10000000000 40147714142779 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-414348481/2000000000 : ℝ), (5684752631/10000000000 : ℝ), (5015377119/10000000000 : ℝ)] ![(6235126960577/50000000000000 : ℝ), (47382031917477/100000000000000 : ℝ), (40147714142779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-414348481/2000000000 : ℝ)|^8399 ≤ (6235126960577/50000000000000 : ℝ)^6351
        have hw : |(-414348481/2000000000 : ℝ)|=(414348481/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5684752631/10000000000 : ℝ)|^8399 ≤ (47382031917477/100000000000000 : ℝ)^6351
        have hw : |(5684752631/10000000000 : ℝ)|=(5684752631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5015377119/10000000000 : ℝ)|^8399 ≤ (40147714142779/100000000000000 : ℝ)^6351
        have hw : |(5015377119/10000000000 : ℝ)|=(5015377119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s1_1 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (67695267/125000000 : ℝ)*x 0 + (-2431817281/10000000000 : ℝ)*x 1 + (5015377573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67695267/125000000 : ℝ)^8399 ≤ (8887674594493/20000000000000 : ℝ)^6351 := by
    have hnat : (67695267 : ℕ)^8399*20000000000000^6351 ≤ 8887674594493^6351*125000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67695267 125000000 8887674594493 20000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2431817281/10000000000 : ℝ)^8399 ≤ (3853477018247/25000000000000 : ℝ)^6351 := by
    have hnat : (2431817281 : ℕ)^8399*25000000000000^6351 ≤ 3853477018247^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2431817281 10000000000 3853477018247 25000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5015377573/10000000000 : ℝ)^8399 ≤ (20073859474471/50000000000000 : ℝ)^6351 := by
    have hnat : (5015377573 : ℕ)^8399*50000000000000^6351 ≤ 20073859474471^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5015377573 10000000000 20073859474471 50000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(67695267/125000000 : ℝ), (-2431817281/10000000000 : ℝ), (5015377573/10000000000 : ℝ)] ![(8887674594493/20000000000000 : ℝ), (3853477018247/25000000000000 : ℝ), (20073859474471/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(67695267/125000000 : ℝ)|^8399 ≤ (8887674594493/20000000000000 : ℝ)^6351
        have hw : |(67695267/125000000 : ℝ)|=(67695267/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2431817281/10000000000 : ℝ)|^8399 ≤ (3853477018247/25000000000000 : ℝ)^6351
        have hw : |(-2431817281/10000000000 : ℝ)|=(2431817281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5015377573/10000000000 : ℝ)|^8399 ≤ (20073859474471/50000000000000 : ℝ)^6351
        have hw : |(5015377573/10000000000 : ℝ)|=(5015377573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s1_2 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (676952517/1250000000 : ℝ)*x 0 + (1003075671/2000000000 : ℝ)*x 1 + (-2431817877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (676952517/1250000000 : ℝ)^8399 ≤ (2221917984503/5000000000000 : ℝ)^6351 := by
    have hnat : (676952517 : ℕ)^8399*5000000000000^6351 ≤ 2221917984503^6351*1250000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676952517 1250000000 2221917984503 5000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1003075671/2000000000 : ℝ)^8399 ≤ (40147727227401/100000000000000 : ℝ)^6351 := by
    have hnat : (1003075671 : ℕ)^8399*100000000000000^6351 ≤ 40147727227401^6351*2000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003075671 2000000000 40147727227401 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2431817877/10000000000 : ℝ)^8399 ≤ (7706956534443/50000000000000 : ℝ)^6351 := by
    have hnat : (2431817877 : ℕ)^8399*50000000000000^6351 ≤ 7706956534443^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2431817877 10000000000 7706956534443 50000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(676952517/1250000000 : ℝ), (1003075671/2000000000 : ℝ), (-2431817877/10000000000 : ℝ)] ![(2221917984503/5000000000000 : ℝ), (40147727227401/100000000000000 : ℝ), (7706956534443/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(676952517/1250000000 : ℝ)|^8399 ≤ (2221917984503/5000000000000 : ℝ)^6351
        have hw : |(676952517/1250000000 : ℝ)|=(676952517/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1003075671/2000000000 : ℝ)|^8399 ≤ (40147727227401/100000000000000 : ℝ)^6351
        have hw : |(1003075671/2000000000 : ℝ)|=(1003075671/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2431817877/10000000000 : ℝ)|^8399 ≤ (7706956534443/50000000000000 : ℝ)^6351
        have hw : |(-2431817877/10000000000 : ℝ)|=(2431817877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s1_3 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (538995803/1250000000 : ℝ)*x 0 + (3688889363/10000000000 : ℝ)*x 1 + (2518666519/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538995803/1250000000 : ℝ)^8399 ≤ (6575057176353/20000000000000 : ℝ)^6351 := by
    have hnat : (538995803 : ℕ)^8399*20000000000000^6351 ≤ 6575057176353^6351*1250000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538995803 1250000000 6575057176353 20000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3688889363/10000000000 : ℝ)^8399 ≤ (26744404933611/100000000000000 : ℝ)^6351 := by
    have hnat : (3688889363 : ℕ)^8399*100000000000000^6351 ≤ 26744404933611^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3688889363 10000000000 26744404933611 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2518666519/5000000000 : ℝ)^8399 ≤ (807606183653/2000000000000 : ℝ)^6351 := by
    have hnat : (2518666519 : ℕ)^8399*2000000000000^6351 ≤ 807606183653^6351*5000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2518666519 5000000000 807606183653 2000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538995803/1250000000 : ℝ), (3688889363/10000000000 : ℝ), (2518666519/5000000000 : ℝ)] ![(6575057176353/20000000000000 : ℝ), (26744404933611/100000000000000 : ℝ), (807606183653/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538995803/1250000000 : ℝ)|^8399 ≤ (6575057176353/20000000000000 : ℝ)^6351
        have hw : |(538995803/1250000000 : ℝ)|=(538995803/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3688889363/10000000000 : ℝ)|^8399 ≤ (26744404933611/100000000000000 : ℝ)^6351
        have hw : |(3688889363/10000000000 : ℝ)|=(3688889363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2518666519/5000000000 : ℝ)|^8399 ≤ (807606183653/2000000000000 : ℝ)^6351
        have hw : |(2518666519/5000000000 : ℝ)|=(2518666519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s1_4 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2072461121/10000000000 : ℝ)*x 0 + (1004858803/2000000000 : ℝ)*x 1 + (5675664927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2072461121/10000000000 : ℝ)^8399 ≤ (6237987688907/50000000000000 : ℝ)^6351 := by
    have hnat : (2072461121 : ℕ)^8399*50000000000000^6351 ≤ 6237987688907^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072461121 10000000000 6237987688907 50000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1004858803/2000000000 : ℝ)^8399 ≤ (20121068900941/50000000000000 : ℝ)^6351 := by
    have hnat : (1004858803 : ℕ)^8399*50000000000000^6351 ≤ 20121068900941^6351*2000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004858803 2000000000 20121068900941 50000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5675664927/10000000000 : ℝ)^8399 ≤ (47281886805529/100000000000000 : ℝ)^6351 := by
    have hnat : (5675664927 : ℕ)^8399*100000000000000^6351 ≤ 47281886805529^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5675664927 10000000000 47281886805529 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2072461121/10000000000 : ℝ), (1004858803/2000000000 : ℝ), (5675664927/10000000000 : ℝ)] ![(6237987688907/50000000000000 : ℝ), (20121068900941/50000000000000 : ℝ), (47281886805529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2072461121/10000000000 : ℝ)|^8399 ≤ (6237987688907/50000000000000 : ℝ)^6351
        have hw : |(-2072461121/10000000000 : ℝ)|=(2072461121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1004858803/2000000000 : ℝ)|^8399 ≤ (20121068900941/50000000000000 : ℝ)^6351
        have hw : |(1004858803/2000000000 : ℝ)|=(1004858803/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5675664927/10000000000 : ℝ)|^8399 ≤ (47281886805529/100000000000000 : ℝ)^6351
        have hw : |(5675664927/10000000000 : ℝ)|=(5675664927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s1_5 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (262173261/500000000 : ℝ)*x 0 + (-1771532269/10000000000 : ℝ)*x 1 + (28378313/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262173261/500000000 : ℝ)^8399 ≤ (42579841662469/100000000000000 : ℝ)^6351 := by
    have hnat : (262173261 : ℕ)^8399*100000000000000^6351 ≤ 42579841662469^6351*500000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262173261 500000000 42579841662469 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1771532269/10000000000 : ℝ)^8399 ≤ (10138297154073/100000000000000 : ℝ)^6351 := by
    have hnat : (1771532269 : ℕ)^8399*100000000000000^6351 ≤ 10138297154073^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1771532269 10000000000 10138297154073 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (28378313/50000000 : ℝ)^8399 ≤ (47281861168961/100000000000000 : ℝ)^6351 := by
    have hnat : (28378313 : ℕ)^8399*100000000000000^6351 ≤ 47281861168961^6351*50000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28378313 50000000 47281861168961 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(262173261/500000000 : ℝ), (-1771532269/10000000000 : ℝ), (28378313/50000000 : ℝ)] ![(42579841662469/100000000000000 : ℝ), (10138297154073/100000000000000 : ℝ), (47281861168961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(262173261/500000000 : ℝ)|^8399 ≤ (42579841662469/100000000000000 : ℝ)^6351
        have hw : |(262173261/500000000 : ℝ)|=(262173261/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1771532269/10000000000 : ℝ)|^8399 ≤ (10138297154073/100000000000000 : ℝ)^6351
        have hw : |(-1771532269/10000000000 : ℝ)|=(1771532269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(28378313/50000000 : ℝ)|^8399 ≤ (47281861168961/100000000000000 : ℝ)^6351
        have hw : |(28378313/50000000 : ℝ)|=(28378313/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s1_6 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2621732673/5000000000 : ℝ)*x 0 + (2837831537/5000000000 : ℝ)*x 1 + (-8857657/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2621732673/5000000000 : ℝ)^8399 ≤ (8515968603121/20000000000000 : ℝ)^6351 := by
    have hnat : (2621732673 : ℕ)^8399*20000000000000^6351 ≤ 8515968603121^6351*5000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621732673 5000000000 8515968603121 20000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2837831537/5000000000 : ℝ)^8399 ≤ (47281866391021/100000000000000 : ℝ)^6351 := by
    have hnat : (2837831537 : ℕ)^8399*100000000000000^6351 ≤ 47281866391021^6351*5000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2837831537 5000000000 47281866391021 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8857657/50000000 : ℝ)^8399 ≤ (5069145288587/50000000000000 : ℝ)^6351 := by
    have hnat : (8857657 : ℕ)^8399*50000000000000^6351 ≤ 5069145288587^6351*50000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8857657 50000000 5069145288587 50000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2621732673/5000000000 : ℝ), (2837831537/5000000000 : ℝ), (-8857657/50000000 : ℝ)] ![(8515968603121/20000000000000 : ℝ), (47281866391021/100000000000000 : ℝ), (5069145288587/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2621732673/5000000000 : ℝ)|^8399 ≤ (8515968603121/20000000000000 : ℝ)^6351
        have hw : |(2621732673/5000000000 : ℝ)|=(2621732673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2837831537/5000000000 : ℝ)|^8399 ≤ (47281866391021/100000000000000 : ℝ)^6351
        have hw : |(2837831537/5000000000 : ℝ)|=(2837831537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8857657/50000000 : ℝ)|^8399 ≤ (5069145288587/50000000000000 : ℝ)^6351
        have hw : |(-8857657/50000000 : ℝ)|=(8857657/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s1_7 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (539177159/1250000000 : ℝ)*x 0 + (5019368229/10000000000 : ℝ)*x 1 + (1853600453/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539177159/1250000000 : ℝ)^8399 ≤ (8222478808611/25000000000000 : ℝ)^6351 := by
    have hnat : (539177159 : ℕ)^8399*25000000000000^6351 ≤ 8222478808611^6351*1250000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539177159 1250000000 8222478808611 25000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5019368229/10000000000 : ℝ)^8399 ≤ (40189970504767/100000000000000 : ℝ)^6351 := by
    have hnat : (5019368229 : ℕ)^8399*100000000000000^6351 ≤ 40189970504767^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5019368229 10000000000 40189970504767 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1853600453/5000000000 : ℝ)^8399 ≤ (13460057124087/50000000000000 : ℝ)^6351 := by
    have hnat : (1853600453 : ℕ)^8399*50000000000000^6351 ≤ 13460057124087^6351*5000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1853600453 5000000000 13460057124087 50000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(539177159/1250000000 : ℝ), (5019368229/10000000000 : ℝ), (1853600453/5000000000 : ℝ)] ![(8222478808611/25000000000000 : ℝ), (40189970504767/100000000000000 : ℝ), (13460057124087/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(539177159/1250000000 : ℝ)|^8399 ≤ (8222478808611/25000000000000 : ℝ)^6351
        have hw : |(539177159/1250000000 : ℝ)|=(539177159/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5019368229/10000000000 : ℝ)|^8399 ≤ (40189970504767/100000000000000 : ℝ)^6351
        have hw : |(5019368229/10000000000 : ℝ)|=(5019368229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1853600453/5000000000 : ℝ)|^8399 ≤ (13460057124087/50000000000000 : ℝ)^6351
        have hw : |(1853600453/5000000000 : ℝ)|=(1853600453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1206_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37680987/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6893/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (337/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (3/50 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20153/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6893/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (337/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6893/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (337/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6893/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (337/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6893/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (337/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6893/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (337/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6893/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (337/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (337/50000 : ℝ) ^ (4199/1024 : ℝ) ≤ (124805379791/100000000000000000000 : ℝ) := by
    have hpowers : (337/50000 : ℝ)^4199 ≤ (124805379791/100000000000000000000 : ℝ)^1024 := by
      have hnat : (337 : ℕ)^4199*100000000000000000000^1024 ≤ 124805379791^1024*50000^4199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        337 50000 124805379791 100000000000000000000 4199 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (337/50000 : ℝ)) (X := (124805379791/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4199 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (6893/25000 : ℝ) ^ (4199/1024 : ℝ) ≤ (507682339000124181/100000000000000000000 : ℝ) := by
    have hpowers : (6893/25000 : ℝ)^4199 ≤ (507682339000124181/100000000000000000000 : ℝ)^1024 := by
      have hnat : (6893 : ℕ)^4199*100000000000000000000^1024 ≤ 507682339000124181^1024*25000^4199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6893 25000 507682339000124181 100000000000000000000 4199 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6893/25000 : ℝ)) (X := (507682339000124181/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4199 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000124805379791/50000000000000000000 : ℝ) ≤ (5000000003043599/5000000000000000 : ℝ) ^ (4199/1024 : ℝ) := by
    have hpowers : (50000000124805379791/50000000000000000000 : ℝ)^1024 ≤ (5000000003043599/5000000000000000 : ℝ)^4199 := by
      have hnat : (50000000124805379791 : ℕ)^1024*5000000000000000^4199 ≤ 5000000003043599^4199*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000124805379791 50000000000000000000 5000000003043599 5000000000000000 1024 4199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000003043599/5000000000000000 : ℝ)) (X := (50000000124805379791/50000000000000000000 : ℝ)) (by norm_num) 4199 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25126920615951375993/25000000000000000000 : ℝ) ≤ (10012357036868999/10000000000000000 : ℝ) ^ (4199/1024 : ℝ) := by
    have hpowers : (25126920615951375993/25000000000000000000 : ℝ)^1024 ≤ (10012357036868999/10000000000000000 : ℝ)^4199 := by
      have hnat : (25126920615951375993 : ℕ)^1024*10000000000000000^4199 ≤ 10012357036868999^4199*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25126920615951375993 25000000000000000000 10012357036868999 10000000000000000 1024 4199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10012357036868999/10000000000000000 : ℝ)) (X := (25126920615951375993/25000000000000000000 : ℝ)) (by norm_num) 4199 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50507682339000124181/50000000000000000000 : ℝ) ≤ (25061785169127/25000000000000 : ℝ) ^ (4199/1024 : ℝ) := by
    have hpowers : (50507682339000124181/50000000000000000000 : ℝ)^1024 ≤ (25061785169127/25000000000000 : ℝ)^4199 := by
      have hnat : (50507682339000124181 : ℕ)^1024*25000000000000^4199 ≤ 25061785169127^4199*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50507682339000124181 50000000000000000000 25061785169127 25000000000000 1024 4199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (25061785169127/25000000000000 : ℝ)) (X := (50507682339000124181/50000000000000000000 : ℝ)) (by norm_num) 4199 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(124805379791/100000000000000000000 : ℝ) ≤ ((33620417860779948007/33622500000000000000 : ℝ)+2*(12357030781801/2689800000000000 : ℝ)*(337/50000 : ℝ))^(4199/1024 : ℝ) := by
    rw [show (33620417860779948007/33622500000000000000 : ℝ)+2*(12357030781801/2689800000000000 : ℝ)*(337/50000 : ℝ)=(5000000003043599/5000000000000000 : ℝ) by norm_num, show 1+2*(124805379791/100000000000000000000 : ℝ)=(50000000124805379791/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(507682339000124181/100000000000000000000 : ℝ)+(124805379791/100000000000000000000 : ℝ) ≤ ((33620417860779948007/33622500000000000000 : ℝ)+(12357030781801/2689800000000000 : ℝ)*((6893/25000 : ℝ)+(337/50000 : ℝ)))^(4199/1024 : ℝ) := by
    rw [show (33620417860779948007/33622500000000000000 : ℝ)+(12357030781801/2689800000000000 : ℝ)*((6893/25000 : ℝ)+(337/50000 : ℝ))=(10012357036868999/10000000000000000 : ℝ) by norm_num, show 1+(507682339000124181/100000000000000000000 : ℝ)+(124805379791/100000000000000000000 : ℝ)=(25126920615951375993/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(507682339000124181/100000000000000000000 : ℝ) ≤ ((33620417860779948007/33622500000000000000 : ℝ)+2*(12357030781801/2689800000000000 : ℝ)*(6893/25000 : ℝ))^(4199/1024 : ℝ) := by
    rw [show (33620417860779948007/33622500000000000000 : ℝ)+2*(12357030781801/2689800000000000 : ℝ)*(6893/25000 : ℝ)=(25061785169127/25000000000000 : ℝ) by norm_num, show 1+2*(507682339000124181/100000000000000000000 : ℝ)=(50507682339000124181/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (33620417860779948007/33622500000000000000 : ℝ)*(X 1 0+X 2 0)+(12357030781801/2689800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4199/1024 : ℝ)) (lo := (337/50000 : ℝ)) (hi := (6893/25000 : ℝ)) (c := (33620417860779948007/33622500000000000000 : ℝ)) (alpha := (12357030781801/2689800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (33620417860779948007/33622500000000000000 : ℝ)*(X 0 1+X 2 1)+(12357030781801/2689800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4199/1024 : ℝ)) (lo := (337/50000 : ℝ)) (hi := (6893/25000 : ℝ)) (c := (33620417860779948007/33622500000000000000 : ℝ)) (alpha := (12357030781801/2689800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (33620417860779948007/33622500000000000000 : ℝ)*(X 0 2+X 1 2)+(12357030781801/2689800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4199/1024 : ℝ)) (lo := (337/50000 : ℝ)) (hi := (6893/25000 : ℝ)) (c := (33620417860779948007/33622500000000000000 : ℝ)) (alpha := (12357030781801/2689800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-414348481/2000000000 : ℝ)*X 0 0+(5684752631/10000000000 : ℝ)*X 0 1+(5015377119/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((67695267/125000000 : ℝ)*X 1 0+(-2431817281/10000000000 : ℝ)*X 1 1+(5015377573/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((676952517/1250000000 : ℝ)*X 2 0+(1003075671/2000000000 : ℝ)*X 2 1+(-2431817877/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((538995803/1250000000 : ℝ)*X 0 0+(3688889363/10000000000 : ℝ)*X 0 1+(2518666519/5000000000 : ℝ)*X 0 2+(538995803/1250000000 : ℝ)*X 1 0+(3688889363/10000000000 : ℝ)*X 1 1+(2518666519/5000000000 : ℝ)*X 1 2+(538995803/1250000000 : ℝ)*X 2 0+(3688889363/10000000000 : ℝ)*X 2 1+(2518666519/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2072461121/10000000000 : ℝ)*X 0 0+(1004858803/2000000000 : ℝ)*X 0 1+(5675664927/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((262173261/500000000 : ℝ)*X 1 0+(-1771532269/10000000000 : ℝ)*X 1 1+(28378313/50000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2621732673/5000000000 : ℝ)*X 2 0+(2837831537/5000000000 : ℝ)*X 2 1+(-8857657/50000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((539177159/1250000000 : ℝ)*X 0 0+(5019368229/10000000000 : ℝ)*X 0 1+(1853600453/5000000000 : ℝ)*X 0 2+(539177159/1250000000 : ℝ)*X 1 0+(5019368229/10000000000 : ℝ)*X 1 1+(1853600453/5000000000 : ℝ)*X 1 2+(539177159/1250000000 : ℝ)*X 2 0+(5019368229/10000000000 : ℝ)*X 2 1+(1853600453/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (251882554722868776944361/44830000000000000000000000000 : ℝ) := by norm_num
    linear_combination (183553043/12500000000000 : ℝ)*(base19) + (11015431/1000000000000 : ℝ)*(base23) + (18114187/100000000000000 : ℝ)*(upper2) + (165642589/50000000000000 : ℝ)*(upper3) + (33944111/100000000000000 : ℝ)*(upper4) + (1117776516635737/100000000000000 : ℝ)*(major0) + (1117776516635737/100000000000000 : ℝ)*(major1) + (1117776516635737/100000000000000 : ℝ)*(major2) + (18674257873563/1250000000000 : ℝ)*(sp0) + (1493946256762707/100000000000000 : ℝ)*(sp1) + (29878932472879/2000000000000 : ℝ)*(sp2) + (370799879668869/50000000000000 : ℝ)*(sp3) + (709530201/10000000000000 : ℝ)*(sp4) + (5361459481/100000000000000 : ℝ)*(sp7) + (741605120797219/100000000000000 : ℝ)*(f.failure) + (29878954503741/2000000000000 : ℝ)*(f.sum) + (477586210197323/134490000000000000000000000000 : ℝ)*base66 + (5792267870781029553/1120750000000000000000000000000000 : ℝ)*base67 + (1811976527779220447/1120750000000000000000000000000000 : ℝ)*base70 + (6985812884312220447/1120750000000000000000000000000000 : ℝ)*base72 + (148298210045903/134490000000000000000000000000 : ℝ)*base74 + (46310083809970447/1120750000000000000000000000000000 : ℝ)*base76 + (5528531287327779553/1120750000000000000000000000000000 : ℝ)*base77 + (10018961468686029553/1120750000000000000000000000000000 : ℝ)*base79 + (947735457300863/134490000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (13775153/2500000000000000000000 : ℝ)*base89 + (13775153/2500000000000000000000 : ℝ)*base91 + (13775153/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1432561741164353833607058919/560375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (67134741/25000000000000 : ℝ)*(base19) + (173069241/25000000000000 : ℝ)*(base23) + (43046633/50000000000000 : ℝ)*(lower3) + (153572203/100000000000000 : ℝ)*(lower4) + (1148663322115139/100000000000000 : ℝ)*(major0) + (1148663322115139/100000000000000 : ℝ)*(major1) + (1148663322115139/100000000000000 : ℝ)*(major2) + (1291898093/50000000000000 : ℝ)*(sp0) + (235893063/100000000000000 : ℝ)*(sp1) + (619564627/20000000000000 : ℝ)*(sp2) + (153522655317283/10000000000000 : ℝ)*(sp4) + (153522863253699/10000000000000 : ℝ)*(sp5) + (1535225346868917/100000000000000 : ℝ)*(sp6) + (762097422046787/100000000000000 : ℝ)*(sp7) + (762097422046787/100000000000000 : ℝ)*(f.failure) + (191903642121127/12500000000000 : ℝ)*(f.sum) + (309139251649621/134490000000000000000000000000 : ℝ)*base66 + (6508403596707811509/1120750000000000000000000000000000 : ℝ)*base68 + (387519963843061509/1120750000000000000000000000000000 : ℝ)*base70 + (11458095670186561509/1120750000000000000000000000000000 : ℝ)*base72 + (9345293677561/134490000000000000000000000000 : ℝ)*base74 + (13648064231859311509/1120750000000000000000000000000000 : ℝ)*base76 + (6391838498998061509/1120750000000000000000000000000000 : ℝ)*base78 + (3450589606723061509/1120750000000000000000000000000000 : ℝ)*base80 + (409277342662109/134490000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (19338769/2500000000000000000000 : ℝ)*base89 + (19338769/2500000000000000000000 : ℝ)*base91 + (19338769/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1206_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37680987/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6893/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (337/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3/50 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20153/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1206_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1206_s2_0 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-424323457/2000000000 : ℝ)*x 0 + (5499047517/10000000000 : ℝ)*x 1 + (16154087/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (424323457/2000000000 : ℝ)^8399 ≤ (6434400808459/50000000000000 : ℝ)^6351 := by
    have hnat : (424323457 : ℕ)^8399*50000000000000^6351 ≤ 6434400808459^6351*2000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424323457 2000000000 6434400808459 50000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5499047517/10000000000 : ℝ)^8399 ≤ (11336481074691/25000000000000 : ℝ)^6351 := by
    have hnat : (5499047517 : ℕ)^8399*25000000000000^6351 ≤ 11336481074691^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5499047517 10000000000 11336481074691 25000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16154087/31250000 : ℝ)^8399 ≤ (2089263703247/5000000000000 : ℝ)^6351 := by
    have hnat : (16154087 : ℕ)^8399*5000000000000^6351 ≤ 2089263703247^6351*31250000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16154087 31250000 2089263703247 5000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-424323457/2000000000 : ℝ), (5499047517/10000000000 : ℝ), (16154087/31250000 : ℝ)] ![(6434400808459/50000000000000 : ℝ), (11336481074691/25000000000000 : ℝ), (2089263703247/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-424323457/2000000000 : ℝ)|^8399 ≤ (6434400808459/50000000000000 : ℝ)^6351
        have hw : |(-424323457/2000000000 : ℝ)|=(424323457/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5499047517/10000000000 : ℝ)|^8399 ≤ (11336481074691/25000000000000 : ℝ)^6351
        have hw : |(5499047517/10000000000 : ℝ)|=(5499047517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(16154087/31250000 : ℝ)|^8399 ≤ (2089263703247/5000000000000 : ℝ)^6351
        have hw : |(16154087/31250000 : ℝ)|=(16154087/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s2_1 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2685580347/5000000000 : ℝ)*x 0 + (-2292634501/10000000000 : ℝ)*x 1 + (5169312523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685580347/5000000000 : ℝ)^8399 ≤ (8791308343577/20000000000000 : ℝ)^6351 := by
    have hnat : (2685580347 : ℕ)^8399*20000000000000^6351 ≤ 8791308343577^6351*5000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685580347 5000000000 8791308343577 20000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2292634501/10000000000 : ℝ)^8399 ≤ (14258134140941/100000000000000 : ℝ)^6351 := by
    have hnat : (2292634501 : ℕ)^8399*100000000000000^6351 ≤ 14258134140941^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2292634501 10000000000 14258134140941 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5169312523/10000000000 : ℝ)^8399 ≤ (20892662063029/50000000000000 : ℝ)^6351 := by
    have hnat : (5169312523 : ℕ)^8399*50000000000000^6351 ≤ 20892662063029^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5169312523 10000000000 20892662063029 50000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685580347/5000000000 : ℝ), (-2292634501/10000000000 : ℝ), (5169312523/10000000000 : ℝ)] ![(8791308343577/20000000000000 : ℝ), (14258134140941/100000000000000 : ℝ), (20892662063029/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685580347/5000000000 : ℝ)|^8399 ≤ (8791308343577/20000000000000 : ℝ)^6351
        have hw : |(2685580347/5000000000 : ℝ)|=(2685580347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2292634501/10000000000 : ℝ)|^8399 ≤ (14258134140941/100000000000000 : ℝ)^6351
        have hw : |(-2292634501/10000000000 : ℝ)|=(2292634501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5169312523/10000000000 : ℝ)|^8399 ≤ (20892662063029/50000000000000 : ℝ)^6351
        have hw : |(5169312523/10000000000 : ℝ)|=(5169312523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s2_2 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1342790701/2500000000 : ℝ)*x 0 + (6461637/12500000 : ℝ)*x 1 + (-2292635523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342790701/2500000000 : ℝ)^8399 ≤ (21978282277029/50000000000000 : ℝ)^6351 := by
    have hnat : (1342790701 : ℕ)^8399*50000000000000^6351 ≤ 21978282277029^6351*2500000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342790701 2500000000 21978282277029 50000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6461637/12500000 : ℝ)^8399 ≤ (41785292879281/100000000000000 : ℝ)^6351 := by
    have hnat : (6461637 : ℕ)^8399*100000000000000^6351 ≤ 41785292879281^6351*12500000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6461637 12500000 41785292879281 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2292635523/10000000000 : ℝ)^8399 ≤ (7129071273227/50000000000000 : ℝ)^6351 := by
    have hnat : (2292635523 : ℕ)^8399*50000000000000^6351 ≤ 7129071273227^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2292635523 10000000000 7129071273227 50000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342790701/2500000000 : ℝ), (6461637/12500000 : ℝ), (-2292635523/10000000000 : ℝ)] ![(21978282277029/50000000000000 : ℝ), (41785292879281/100000000000000 : ℝ), (7129071273227/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342790701/2500000000 : ℝ)|^8399 ≤ (21978282277029/50000000000000 : ℝ)^6351
        have hw : |(1342790701/2500000000 : ℝ)|=(1342790701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6461637/12500000 : ℝ)|^8399 ≤ (41785292879281/100000000000000 : ℝ)^6351
        have hw : |(6461637/12500000 : ℝ)|=(6461637/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2292635523/10000000000 : ℝ)|^8399 ≤ (7129071273227/50000000000000 : ℝ)^6351
        have hw : |(-2292635523/10000000000 : ℝ)|=(2292635523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s2_3 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (869266697/2000000000 : ℝ)*x 0 + (4026600423/10000000000 : ℝ)*x 1 + (293178169/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (869266697/2000000000 : ℝ)^8399 ≤ (1661112268479/5000000000000 : ℝ)^6351 := by
    have hnat : (869266697 : ℕ)^8399*5000000000000^6351 ≤ 1661112268479^6351*2000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869266697 2000000000 1661112268479 5000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4026600423/10000000000 : ℝ)^8399 ≤ (30029181696373/100000000000000 : ℝ)^6351 := by
    have hnat : (4026600423 : ℕ)^8399*100000000000000^6351 ≤ 30029181696373^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4026600423 10000000000 30029181696373 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (293178169/625000000 : ℝ)^8399 ≤ (36748572925723/100000000000000 : ℝ)^6351 := by
    have hnat : (293178169 : ℕ)^8399*100000000000000^6351 ≤ 36748572925723^6351*625000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      293178169 625000000 36748572925723 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(869266697/2000000000 : ℝ), (4026600423/10000000000 : ℝ), (293178169/625000000 : ℝ)] ![(1661112268479/5000000000000 : ℝ), (30029181696373/100000000000000 : ℝ), (36748572925723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(869266697/2000000000 : ℝ)|^8399 ≤ (1661112268479/5000000000000 : ℝ)^6351
        have hw : |(869266697/2000000000 : ℝ)|=(869266697/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4026600423/10000000000 : ℝ)|^8399 ≤ (30029181696373/100000000000000 : ℝ)^6351
        have hw : |(4026600423/10000000000 : ℝ)|=(4026600423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(293178169/625000000 : ℝ)|^8399 ≤ (36748572925723/100000000000000 : ℝ)^6351
        have hw : |(293178169/625000000 : ℝ)|=(293178169/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s2_4 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2121702319/10000000000 : ℝ)*x 0 + (2585741579/5000000000 : ℝ)*x 1 + (687106539/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2121702319/10000000000 : ℝ)^8399 ≤ (2573896744607/20000000000000 : ℝ)^6351 := by
    have hnat : (2121702319 : ℕ)^8399*20000000000000^6351 ≤ 2573896744607^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121702319 10000000000 2573896744607 20000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2585741579/5000000000 : ℝ)^8399 ≤ (8361705943647/20000000000000 : ℝ)^6351 := by
    have hnat : (2585741579 : ℕ)^8399*20000000000000^6351 ≤ 8361705943647^6351*5000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2585741579 5000000000 8361705943647 20000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (687106539/1250000000 : ℝ)^8399 ≤ (283262415911/625000000000 : ℝ)^6351 := by
    have hnat : (687106539 : ℕ)^8399*625000000000^6351 ≤ 283262415911^6351*1250000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      687106539 1250000000 283262415911 625000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2121702319/10000000000 : ℝ), (2585741579/5000000000 : ℝ), (687106539/1250000000 : ℝ)] ![(2573896744607/20000000000000 : ℝ), (8361705943647/20000000000000 : ℝ), (283262415911/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2121702319/10000000000 : ℝ)|^8399 ≤ (2573896744607/20000000000000 : ℝ)^6351
        have hw : |(-2121702319/10000000000 : ℝ)|=(2121702319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2585741579/5000000000 : ℝ)|^8399 ≤ (8361705943647/20000000000000 : ℝ)^6351
        have hw : |(2585741579/5000000000 : ℝ)|=(2585741579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(687106539/1250000000 : ℝ)|^8399 ≤ (283262415911/625000000000 : ℝ)^6351
        have hw : |(687106539/1250000000 : ℝ)|=(687106539/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s2_5 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2643573713/5000000000 : ℝ)*x 0 + (-982546507/5000000000 : ℝ)*x 1 + (5496852337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643573713/5000000000 : ℝ)^8399 ≤ (8609916333203/20000000000000 : ℝ)^6351 := by
    have hnat : (2643573713 : ℕ)^8399*20000000000000^6351 ≤ 8609916333203^6351*5000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643573713 5000000000 8609916333203 20000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (982546507/5000000000 : ℝ)^8399 ≤ (1453553938611/12500000000000 : ℝ)^6351 := by
    have hnat : (982546507 : ℕ)^8399*12500000000000^6351 ≤ 1453553938611^6351*5000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      982546507 5000000000 1453553938611 12500000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5496852337/10000000000 : ℝ)^8399 ≤ (45321986818357/100000000000000 : ℝ)^6351 := by
    have hnat : (5496852337 : ℕ)^8399*100000000000000^6351 ≤ 45321986818357^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5496852337 10000000000 45321986818357 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643573713/5000000000 : ℝ), (-982546507/5000000000 : ℝ), (5496852337/10000000000 : ℝ)] ![(8609916333203/20000000000000 : ℝ), (1453553938611/12500000000000 : ℝ), (45321986818357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643573713/5000000000 : ℝ)|^8399 ≤ (8609916333203/20000000000000 : ℝ)^6351
        have hw : |(2643573713/5000000000 : ℝ)|=(2643573713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-982546507/5000000000 : ℝ)|^8399 ≤ (1453553938611/12500000000000 : ℝ)^6351
        have hw : |(-982546507/5000000000 : ℝ)|=(982546507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5496852337/10000000000 : ℝ)|^8399 ≤ (45321986818357/100000000000000 : ℝ)^6351
        have hw : |(5496852337/10000000000 : ℝ)|=(5496852337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s2_6 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5287147603/10000000000 : ℝ)*x 0 + (5496852363/10000000000 : ℝ)*x 1 + (-1965092733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287147603/10000000000 : ℝ)^8399 ≤ (21524791785971/50000000000000 : ℝ)^6351 := by
    have hnat : (5287147603 : ℕ)^8399*50000000000000^6351 ≤ 21524791785971^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287147603 10000000000 21524791785971 50000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5496852363/10000000000 : ℝ)^8399 ≤ (45321987101857/100000000000000 : ℝ)^6351 := by
    have hnat : (5496852363 : ℕ)^8399*100000000000000^6351 ≤ 45321987101857^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5496852363 10000000000 45321987101857 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1965092733/10000000000 : ℝ)^8399 ≤ (1453553663733/12500000000000 : ℝ)^6351 := by
    have hnat : (1965092733 : ℕ)^8399*12500000000000^6351 ≤ 1453553663733^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1965092733 10000000000 1453553663733 12500000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287147603/10000000000 : ℝ), (5496852363/10000000000 : ℝ), (-1965092733/10000000000 : ℝ)] ![(21524791785971/50000000000000 : ℝ), (45321987101857/100000000000000 : ℝ), (1453553663733/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287147603/10000000000 : ℝ)|^8399 ≤ (21524791785971/50000000000000 : ℝ)^6351
        have hw : |(5287147603/10000000000 : ℝ)|=(5287147603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5496852363/10000000000 : ℝ)|^8399 ≤ (45321987101857/100000000000000 : ℝ)^6351
        have hw : |(5496852363/10000000000 : ℝ)|=(5496852363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1965092733/10000000000 : ℝ)|^8399 ≤ (1453553663733/12500000000000 : ℝ)^6351
        have hw : |(-1965092733/10000000000 : ℝ)|=(1965092733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s2_7 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4346507231/10000000000 : ℝ)*x 0 + (468647127/1000000000 : ℝ)*x 1 + (1007755333/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4346507231/10000000000 : ℝ)^8399 ≤ (33224001711303/100000000000000 : ℝ)^6351 := by
    have hnat : (4346507231 : ℕ)^8399*100000000000000^6351 ≤ 33224001711303^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4346507231 10000000000 33224001711303 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (468647127/1000000000 : ℝ)^8399 ≤ (9175801824391/25000000000000 : ℝ)^6351 := by
    have hnat : (468647127 : ℕ)^8399*25000000000000^6351 ≤ 9175801824391^6351*1000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      468647127 1000000000 9175801824391 25000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1007755333/2500000000 : ℝ)^8399 ≤ (7518197742711/25000000000000 : ℝ)^6351 := by
    have hnat : (1007755333 : ℕ)^8399*25000000000000^6351 ≤ 7518197742711^6351*2500000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007755333 2500000000 7518197742711 25000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4346507231/10000000000 : ℝ), (468647127/1000000000 : ℝ), (1007755333/2500000000 : ℝ)] ![(33224001711303/100000000000000 : ℝ), (9175801824391/25000000000000 : ℝ), (7518197742711/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4346507231/10000000000 : ℝ)|^8399 ≤ (33224001711303/100000000000000 : ℝ)^6351
        have hw : |(4346507231/10000000000 : ℝ)|=(4346507231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(468647127/1000000000 : ℝ)|^8399 ≤ (9175801824391/25000000000000 : ℝ)^6351
        have hw : |(468647127/1000000000 : ℝ)|=(468647127/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1007755333/2500000000 : ℝ)|^8399 ≤ (7518197742711/25000000000000 : ℝ)^6351
        have hw : |(1007755333/2500000000 : ℝ)|=(1007755333/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1206_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37680987/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20153/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3/50 : ℝ)*pair X i i ≤ pair X i h) :
    (187/2000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16319/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20153/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3/50 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20153/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3/50 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20153/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3/50 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20153/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3/50 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20153/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3/50 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20153/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3/50 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3/50 : ℝ) ^ (4199/1024 : ℝ) ≤ (122071480722087/12500000000000000000 : ℝ) := by
    have hpowers : (3/50 : ℝ)^4199 ≤ (122071480722087/12500000000000000000 : ℝ)^1024 := by
      have hnat : (3 : ℕ)^4199*12500000000000000000^1024 ≤ 122071480722087^1024*50^4199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 50 122071480722087 12500000000000000000 4199 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3/50 : ℝ)) (X := (122071480722087/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4199 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (20153/100000 : ℝ) ^ (4199/1024 : ℝ) ≤ (8775365091241809/6250000000000000000 : ℝ) := by
    have hpowers : (20153/100000 : ℝ)^4199 ≤ (8775365091241809/6250000000000000000 : ℝ)^1024 := by
      have hnat : (20153 : ℕ)^4199*6250000000000000000^1024 ≤ 8775365091241809^1024*100000^4199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20153 100000 8775365091241809 6250000000000000000 4199 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20153/100000 : ℝ)) (X := (8775365091241809/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4199 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250122071480722087/6250000000000000000 : ℝ) ≤ (625002976905769/625000000000000 : ℝ) ^ (4199/1024 : ℝ) := by
    have hpowers : (6250122071480722087/6250000000000000000 : ℝ)^1024 ≤ (625002976905769/625000000000000 : ℝ)^4199 := by
      have hnat : (6250122071480722087 : ℕ)^1024*625000000000000^4199 ≤ 625002976905769^4199*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250122071480722087 6250000000000000000 625002976905769 625000000000000 1024 4199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625002976905769/625000000000000 : ℝ)) (X := (6250122071480722087/6250000000000000000 : ℝ)) (by norm_num) 4199 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2503534560332641141/2500000000000000000 : ℝ) ≤ (10003446017382373/10000000000000000 : ℝ) ^ (4199/1024 : ℝ) := by
    have hpowers : (2503534560332641141/2500000000000000000 : ℝ)^1024 ≤ (10003446017382373/10000000000000000 : ℝ)^4199 := by
      have hnat : (2503534560332641141 : ℕ)^1024*10000000000000000^4199 ≤ 10003446017382373^4199*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2503534560332641141 2500000000000000000 10003446017382373 10000000000000000 1024 4199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003446017382373/10000000000000000 : ℝ)) (X := (2503534560332641141/2500000000000000000 : ℝ)) (by norm_num) 4199 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3133775365091241809/3125000000000000000 : ℝ) ≤ (5003422202136221/5000000000000000 : ℝ) ^ (4199/1024 : ℝ) := by
    have hpowers : (3133775365091241809/3125000000000000000 : ℝ)^1024 ≤ (5003422202136221/5000000000000000 : ℝ)^4199 := by
      have hnat : (3133775365091241809 : ℕ)^1024*5000000000000000^4199 ≤ 5003422202136221^4199*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3133775365091241809 3125000000000000000 5003422202136221 5000000000000000 1024 4199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003422202136221/5000000000000000 : ℝ)) (X := (3133775365091241809/3125000000000000000 : ℝ)) (by norm_num) 4199 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(122071480722087/12500000000000000000 : ℝ) ≤ ((8843118341979796907/8845625000000000000 : ℝ)+2*(3398386890069/1415300000000000 : ℝ)*(3/50 : ℝ))^(4199/1024 : ℝ) := by
    rw [show (8843118341979796907/8845625000000000000 : ℝ)+2*(3398386890069/1415300000000000 : ℝ)*(3/50 : ℝ)=(625002976905769/625000000000000 : ℝ) by norm_num, show 1+2*(122071480722087/12500000000000000000 : ℝ)=(6250122071480722087/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8775365091241809/6250000000000000000 : ℝ)+(122071480722087/12500000000000000000 : ℝ) ≤ ((8843118341979796907/8845625000000000000 : ℝ)+(3398386890069/1415300000000000 : ℝ)*((20153/100000 : ℝ)+(3/50 : ℝ)))^(4199/1024 : ℝ) := by
    rw [show (8843118341979796907/8845625000000000000 : ℝ)+(3398386890069/1415300000000000 : ℝ)*((20153/100000 : ℝ)+(3/50 : ℝ))=(10003446017382373/10000000000000000 : ℝ) by norm_num, show 1+(8775365091241809/6250000000000000000 : ℝ)+(122071480722087/12500000000000000000 : ℝ)=(2503534560332641141/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8775365091241809/6250000000000000000 : ℝ) ≤ ((8843118341979796907/8845625000000000000 : ℝ)+2*(3398386890069/1415300000000000 : ℝ)*(20153/100000 : ℝ))^(4199/1024 : ℝ) := by
    rw [show (8843118341979796907/8845625000000000000 : ℝ)+2*(3398386890069/1415300000000000 : ℝ)*(20153/100000 : ℝ)=(5003422202136221/5000000000000000 : ℝ) by norm_num, show 1+2*(8775365091241809/6250000000000000000 : ℝ)=(3133775365091241809/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8843118341979796907/8845625000000000000 : ℝ)*(X 1 0+X 2 0)+(3398386890069/1415300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4199/1024 : ℝ)) (lo := (3/50 : ℝ)) (hi := (20153/100000 : ℝ)) (c := (8843118341979796907/8845625000000000000 : ℝ)) (alpha := (3398386890069/1415300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8843118341979796907/8845625000000000000 : ℝ)*(X 0 1+X 2 1)+(3398386890069/1415300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4199/1024 : ℝ)) (lo := (3/50 : ℝ)) (hi := (20153/100000 : ℝ)) (c := (8843118341979796907/8845625000000000000 : ℝ)) (alpha := (3398386890069/1415300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8843118341979796907/8845625000000000000 : ℝ)*(X 0 2+X 1 2)+(3398386890069/1415300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4199/1024 : ℝ)) (lo := (3/50 : ℝ)) (hi := (20153/100000 : ℝ)) (c := (8843118341979796907/8845625000000000000 : ℝ)) (alpha := (3398386890069/1415300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-424323457/2000000000 : ℝ)*X 0 0+(5499047517/10000000000 : ℝ)*X 0 1+(16154087/31250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2685580347/5000000000 : ℝ)*X 1 0+(-2292634501/10000000000 : ℝ)*X 1 1+(5169312523/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1342790701/2500000000 : ℝ)*X 2 0+(6461637/12500000 : ℝ)*X 2 1+(-2292635523/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((869266697/2000000000 : ℝ)*X 0 0+(4026600423/10000000000 : ℝ)*X 0 1+(293178169/625000000 : ℝ)*X 0 2+(869266697/2000000000 : ℝ)*X 1 0+(4026600423/10000000000 : ℝ)*X 1 1+(293178169/625000000 : ℝ)*X 1 2+(869266697/2000000000 : ℝ)*X 2 0+(4026600423/10000000000 : ℝ)*X 2 1+(293178169/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2121702319/10000000000 : ℝ)*X 0 0+(2585741579/5000000000 : ℝ)*X 0 1+(687106539/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2643573713/5000000000 : ℝ)*X 1 0+(-982546507/5000000000 : ℝ)*X 1 1+(5496852337/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5287147603/10000000000 : ℝ)*X 2 0+(5496852363/10000000000 : ℝ)*X 2 1+(-1965092733/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4346507231/10000000000 : ℝ)*X 0 0+(468647127/1000000000 : ℝ)*X 0 1+(1007755333/2500000000 : ℝ)*X 0 2+(4346507231/10000000000 : ℝ)*X 1 0+(468647127/1000000000 : ℝ)*X 1 1+(1007755333/2500000000 : ℝ)*X 1 2+(4346507231/10000000000 : ℝ)*X 2 0+(468647127/1000000000 : ℝ)*X 2 1+(1007755333/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (120037572224889436648341999/22114062500000000000000000000000 : ℝ) := by norm_num
    linear_combination (265443501/25000000000000 : ℝ)*(base19) + (97798669/5000000000000 : ℝ)*(base23) + (59457917/50000000000000 : ℝ)*(upper2) + (330190133/50000000000000 : ℝ)*(upper3) + (139271451/50000000000000 : ℝ)*(upper4) + (7091046190717/312500000000 : ℝ)*(major0) + (7091046190717/312500000000 : ℝ)*(major1) + (7091046190717/312500000000 : ℝ)*(major2) + (3032739981314341/100000000000000 : ℝ)*(sp0) + (1516388888886091/50000000000000 : ℝ)*(sp1) + (3032776883572807/100000000000000 : ℝ)*(sp2) + (301093854370019/20000000000000 : ℝ)*(sp3) + (7771646369/20000000000000 : ℝ)*(sp4) + (10634862791/50000000000000 : ℝ)*(sp7) + (376372635393919/25000000000000 : ℝ)*(f.failure) + (1516389419773093/50000000000000 : ℝ)*(f.sum) + (33463943063609/14153000000000000000000000000 : ℝ)*base66 + (20149475402072599/11057031250000000000000000000000 : ℝ)*base68 + (8992507771993931/2764257812500000000000000000000 : ℝ)*base70 + (103979257575993979/44228125000000000000000000000000 : ℝ)*base71 + (51691398801607/14153000000000000000000000000 : ℝ)*base74 + (18813815735667073/22114062500000000000000000000000 : ℝ)*base76 + (282541672197631021/44228125000000000000000000000000 : ℝ)*base78 + (265238797324318521/44228125000000000000000000000000 : ℝ)*base80 + (50006355359307/14153000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (1718053/625000000000000000000 : ℝ)*base89 + (1718053/625000000000000000000 : ℝ)*base91 + (1718053/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (195264045448095649995372267/110570312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (335373931/50000000000000 : ℝ)*(base19) + (958566983/100000000000000 : ℝ)*(base23) + (27969231/50000000000000 : ℝ)*(upper2) + (27085909/25000000000000 : ℝ)*(upper3) + (37020841/100000000000000 : ℝ)*(upper5) + (1149775263920577/50000000000000 : ℝ)*(major0) + (1149775263920577/50000000000000 : ℝ)*(major1) + (1149775263920577/50000000000000 : ℝ)*(major2) + (3074246217/50000000000000 : ℝ)*(sp1) + (11127931311/100000000000000 : ℝ)*(sp2) + (3073430684729773/100000000000000 : ℝ)*(sp4) + (1536711932744739/50000000000000 : ℝ)*(sp5) + (3073418598231479/100000000000000 : ℝ)*(sp6) + (305134062417361/20000000000000 : ℝ)*(sp7) + (305134062417361/20000000000000 : ℝ)*(f.failure) + (3073430684729773/100000000000000 : ℝ)*(f.sum) + (142538698668447/35382500000000000000000000000 : ℝ)*base66 + (1266025110933288411/442281250000000000000000000000000 : ℝ)*base68 + (2624345358358711589/442281250000000000000000000000000 : ℝ)*base69 + (3564695351156257161/442281250000000000000000000000000 : ℝ)*base72 + (6963797474133/35382500000000000000000000000 : ℝ)*base73 + (2519330688499913411/442281250000000000000000000000000 : ℝ)*base76 + (1198127133678788411/442281250000000000000000000000000 : ℝ)*base78 + (471846032042007161/442281250000000000000000000000000 : ℝ)*base80 + (73872059826063/35382500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1584693/500000000000000000000 : ℝ)*base90 + (1584693/500000000000000000000 : ℝ)*base92 + (1584693/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1206_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37680987/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20153/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3/50 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (187/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16319/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1206_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1206_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37680987/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (187/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16319/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1206_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1206_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1206_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37680987/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (187/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16319/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1206_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
