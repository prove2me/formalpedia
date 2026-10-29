-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1594_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:37:42.671+00:00
-- url     : https://prove2.me/submissions/9e576e23-1bab-4080-ac8b-7a86afdfb993

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
theorem support_rectangle_w1594_s3_0 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-872608111/5000000000 : ℝ)*x 0 + (5465309411/10000000000 : ℝ)*x 1 + (5178339397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (872608111/5000000000 : ℝ)^4695 ≤ (10724284903497/100000000000000 : ℝ)^3671 := by
    have hnat : (872608111 : ℕ)^4695*100000000000000^3671 ≤ 10724284903497^3671*5000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872608111 5000000000 10724284903497 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5465309411/10000000000 : ℝ)^4695 ≤ (9235367977063/20000000000000 : ℝ)^3671 := by
    have hnat : (5465309411 : ℕ)^4695*20000000000000^3671 ≤ 9235367977063^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5465309411 10000000000 9235367977063 20000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5178339397/10000000000 : ℝ)^4695 ≤ (43098875197679/100000000000000 : ℝ)^3671 := by
    have hnat : (5178339397 : ℕ)^4695*100000000000000^3671 ≤ 43098875197679^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178339397 10000000000 43098875197679 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-872608111/5000000000 : ℝ), (5465309411/10000000000 : ℝ), (5178339397/10000000000 : ℝ)] ![(10724284903497/100000000000000 : ℝ), (9235367977063/20000000000000 : ℝ), (43098875197679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-872608111/5000000000 : ℝ)|^4695 ≤ (10724284903497/100000000000000 : ℝ)^3671
        have hw : |(-872608111/5000000000 : ℝ)|=(872608111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5465309411/10000000000 : ℝ)|^4695 ≤ (9235367977063/20000000000000 : ℝ)^3671
        have hw : |(5465309411/10000000000 : ℝ)|=(5465309411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5178339397/10000000000 : ℝ)|^4695 ≤ (43098875197679/100000000000000 : ℝ)^3671
        have hw : |(5178339397/10000000000 : ℝ)|=(5178339397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_s3_1 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2678016533/5000000000 : ℝ)*x 0 + (-473331819/2500000000 : ℝ)*x 1 + (1035667881/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2678016533/5000000000 : ℝ)^4695 ≤ (11249830071433/25000000000000 : ℝ)^3671 := by
    have hnat : (2678016533 : ℕ)^4695*25000000000000^3671 ≤ 11249830071433^3671*5000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2678016533 5000000000 11249830071433 25000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (473331819/2500000000 : ℝ)^4695 ≤ (5950902205727/50000000000000 : ℝ)^3671 := by
    have hnat : (473331819 : ℕ)^4695*50000000000000^3671 ≤ 5950902205727^3671*2500000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      473331819 2500000000 5950902205727 50000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1035667881/2000000000 : ℝ)^4695 ≤ (8619775056567/20000000000000 : ℝ)^3671 := by
    have hnat : (1035667881 : ℕ)^4695*20000000000000^3671 ≤ 8619775056567^3671*2000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035667881 2000000000 8619775056567 20000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2678016533/5000000000 : ℝ), (-473331819/2500000000 : ℝ), (1035667881/2000000000 : ℝ)] ![(11249830071433/25000000000000 : ℝ), (5950902205727/50000000000000 : ℝ), (8619775056567/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2678016533/5000000000 : ℝ)|^4695 ≤ (11249830071433/25000000000000 : ℝ)^3671
        have hw : |(2678016533/5000000000 : ℝ)|=(2678016533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-473331819/2500000000 : ℝ)|^4695 ≤ (5950902205727/50000000000000 : ℝ)^3671
        have hw : |(-473331819/2500000000 : ℝ)|=(473331819/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1035667881/2000000000 : ℝ)|^4695 ≤ (8619775056567/20000000000000 : ℝ)^3671
        have hw : |(1035667881/2000000000 : ℝ)|=(1035667881/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_s3_2 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2678016533/5000000000 : ℝ)*x 0 + (517833939/1000000000 : ℝ)*x 1 + (-1893327297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2678016533/5000000000 : ℝ)^4695 ≤ (11249830071433/25000000000000 : ℝ)^3671 := by
    have hnat : (2678016533 : ℕ)^4695*25000000000000^3671 ≤ 11249830071433^3671*5000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2678016533 5000000000 11249830071433 25000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (517833939/1000000000 : ℝ)^4695 ≤ (43098875123167/100000000000000 : ℝ)^3671 := by
    have hnat : (517833939 : ℕ)^4695*100000000000000^3671 ≤ 43098875123167^3671*1000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517833939 1000000000 43098875123167 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1893327297/10000000000 : ℝ)^4695 ≤ (11901804580287/100000000000000 : ℝ)^3671 := by
    have hnat : (1893327297 : ℕ)^4695*100000000000000^3671 ≤ 11901804580287^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1893327297 10000000000 11901804580287 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2678016533/5000000000 : ℝ), (517833939/1000000000 : ℝ), (-1893327297/10000000000 : ℝ)] ![(11249830071433/25000000000000 : ℝ), (43098875123167/100000000000000 : ℝ), (11901804580287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2678016533/5000000000 : ℝ)|^4695 ≤ (11249830071433/25000000000000 : ℝ)^3671
        have hw : |(2678016533/5000000000 : ℝ)|=(2678016533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(517833939/1000000000 : ℝ)|^4695 ≤ (43098875123167/100000000000000 : ℝ)^3671
        have hw : |(517833939/1000000000 : ℝ)|=(517833939/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1893327297/10000000000 : ℝ)|^4695 ≤ (11901804580287/100000000000000 : ℝ)^3671
        have hw : |(-1893327297/10000000000 : ℝ)|=(1893327297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_s3_3 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4225816979/10000000000 : ℝ)*x 0 + (1945885411/5000000000 : ℝ)*x 1 + (2291060267/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4225816979/10000000000 : ℝ)^4695 ≤ (33232350708651/100000000000000 : ℝ)^3671 := by
    have hnat : (4225816979 : ℕ)^4695*100000000000000^3671 ≤ 33232350708651^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4225816979 10000000000 33232350708651 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1945885411/5000000000 : ℝ)^4695 ≤ (1196414500251/4000000000000 : ℝ)^3671 := by
    have hnat : (1945885411 : ℕ)^4695*4000000000000^3671 ≤ 1196414500251^3671*5000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1945885411 5000000000 1196414500251 4000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2291060267/5000000000 : ℝ)^4695 ≤ (9214321693163/25000000000000 : ℝ)^3671 := by
    have hnat : (2291060267 : ℕ)^4695*25000000000000^3671 ≤ 9214321693163^3671*5000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2291060267 5000000000 9214321693163 25000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4225816979/10000000000 : ℝ), (1945885411/5000000000 : ℝ), (2291060267/5000000000 : ℝ)] ![(33232350708651/100000000000000 : ℝ), (1196414500251/4000000000000 : ℝ), (9214321693163/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4225816979/10000000000 : ℝ)|^4695 ≤ (33232350708651/100000000000000 : ℝ)^3671
        have hw : |(4225816979/10000000000 : ℝ)|=(4225816979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1945885411/5000000000 : ℝ)|^4695 ≤ (1196414500251/4000000000000 : ℝ)^3671
        have hw : |(1945885411/5000000000 : ℝ)|=(1945885411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2291060267/5000000000 : ℝ)|^4695 ≤ (9214321693163/25000000000000 : ℝ)^3671
        have hw : |(2291060267/5000000000 : ℝ)|=(2291060267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_s3_4 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-218161311/1250000000 : ℝ)*x 0 + (518046941/1000000000 : ℝ)*x 1 + (682894619/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218161311/1250000000 : ℝ)^4695 ≤ (67030428547/625000000000 : ℝ)^3671 := by
    have hnat : (218161311 : ℕ)^4695*625000000000^3671 ≤ 67030428547^3671*1250000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218161311 1250000000 67030428547 625000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (518046941/1000000000 : ℝ)^4695 ≤ (43121549493199/100000000000000 : ℝ)^3671 := by
    have hnat : (518046941 : ℕ)^4695*100000000000000^3671 ≤ 43121549493199^3671*1000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518046941 1000000000 43121549493199 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (682894619/1250000000 : ℝ)^4695 ≤ (11538395480301/25000000000000 : ℝ)^3671 := by
    have hnat : (682894619 : ℕ)^4695*25000000000000^3671 ≤ 11538395480301^3671*1250000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682894619 1250000000 11538395480301 25000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-218161311/1250000000 : ℝ), (518046941/1000000000 : ℝ), (682894619/1250000000 : ℝ)] ![(67030428547/625000000000 : ℝ), (43121549493199/100000000000000 : ℝ), (11538395480301/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-218161311/1250000000 : ℝ)|^4695 ≤ (67030428547/625000000000 : ℝ)^3671
        have hw : |(-218161311/1250000000 : ℝ)|=(218161311/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(518046941/1000000000 : ℝ)|^4695 ≤ (43121549493199/100000000000000 : ℝ)^3671
        have hw : |(518046941/1000000000 : ℝ)|=(518046941/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(682894619/1250000000 : ℝ)|^4695 ≤ (11538395480301/25000000000000 : ℝ)^3671
        have hw : |(682894619/1250000000 : ℝ)|=(682894619/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_s3_5 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (264002773/500000000 : ℝ)*x 0 + (-804254927/5000000000 : ℝ)*x 1 + (546315713/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264002773/500000000 : ℝ)^4695 ≤ (44184547562389/100000000000000 : ℝ)^3671 := by
    have hnat : (264002773 : ℕ)^4695*100000000000000^3671 ≤ 44184547562389^3671*500000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264002773 500000000 44184547562389 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (804254927/5000000000 : ℝ)^4695 ≤ (1207733571969/12500000000000 : ℝ)^3671 := by
    have hnat : (804254927 : ℕ)^4695*12500000000000^3671 ≤ 1207733571969^3671*5000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      804254927 5000000000 1207733571969 12500000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (546315713/1000000000 : ℝ)^4695 ≤ (46153583844441/100000000000000 : ℝ)^3671 := by
    have hnat : (546315713 : ℕ)^4695*100000000000000^3671 ≤ 46153583844441^3671*1000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546315713 1000000000 46153583844441 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264002773/500000000 : ℝ), (-804254927/5000000000 : ℝ), (546315713/1000000000 : ℝ)] ![(44184547562389/100000000000000 : ℝ), (1207733571969/12500000000000 : ℝ), (46153583844441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264002773/500000000 : ℝ)|^4695 ≤ (44184547562389/100000000000000 : ℝ)^3671
        have hw : |(264002773/500000000 : ℝ)|=(264002773/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-804254927/5000000000 : ℝ)|^4695 ≤ (1207733571969/12500000000000 : ℝ)^3671
        have hw : |(-804254927/5000000000 : ℝ)|=(804254927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(546315713/1000000000 : ℝ)|^4695 ≤ (46153583844441/100000000000000 : ℝ)^3671
        have hw : |(546315713/1000000000 : ℝ)|=(546315713/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_s3_6 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (660006969/1250000000 : ℝ)*x 0 + (1365789231/2500000000 : ℝ)*x 1 + (-804254869/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660006969/1250000000 : ℝ)^4695 ≤ (2761534417969/6250000000000 : ℝ)^3671 := by
    have hnat : (660006969 : ℕ)^4695*6250000000000^3671 ≤ 2761534417969^3671*1250000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660006969 1250000000 2761534417969 6250000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1365789231/2500000000 : ℝ)^4695 ≤ (2884598851167/6250000000000 : ℝ)^3671 := by
    have hnat : (1365789231 : ℕ)^4695*6250000000000^3671 ≤ 2884598851167^3671*2500000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365789231 2500000000 2884598851167 6250000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (804254869/5000000000 : ℝ)^4695 ≤ (9661867684611/100000000000000 : ℝ)^3671 := by
    have hnat : (804254869 : ℕ)^4695*100000000000000^3671 ≤ 9661867684611^3671*5000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      804254869 5000000000 9661867684611 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660006969/1250000000 : ℝ), (1365789231/2500000000 : ℝ), (-804254869/5000000000 : ℝ)] ![(2761534417969/6250000000000 : ℝ), (2884598851167/6250000000000 : ℝ), (9661867684611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660006969/1250000000 : ℝ)|^4695 ≤ (2761534417969/6250000000000 : ℝ)^3671
        have hw : |(660006969/1250000000 : ℝ)|=(660006969/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1365789231/2500000000 : ℝ)|^4695 ≤ (2884598851167/6250000000000 : ℝ)^3671
        have hw : |(1365789231/2500000000 : ℝ)|=(1365789231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-804254869/5000000000 : ℝ)|^4695 ≤ (9661867684611/100000000000000 : ℝ)^3671
        have hw : |(-804254869/5000000000 : ℝ)|=(804254869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_s3_7 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4225995767/10000000000 : ℝ)*x 0 + (1144249027/2500000000 : ℝ)*x 1 + (1948474663/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4225995767/10000000000 : ℝ)^4695 ≤ (1038567153981/3125000000000 : ℝ)^3671 := by
    have hnat : (4225995767 : ℕ)^4695*3125000000000^3671 ≤ 1038567153981^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4225995767 10000000000 1038567153981 3125000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1144249027/2500000000 : ℝ)^4695 ≤ (18402288840829/50000000000000 : ℝ)^3671 := by
    have hnat : (1144249027 : ℕ)^4695*50000000000000^3671 ≤ 18402288840829^3671*2500000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1144249027 2500000000 18402288840829 50000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1948474663/5000000000 : ℝ)^4695 ≤ (29961273375537/100000000000000 : ℝ)^3671 := by
    have hnat : (1948474663 : ℕ)^4695*100000000000000^3671 ≤ 29961273375537^3671*5000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1948474663 5000000000 29961273375537 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4225995767/10000000000 : ℝ), (1144249027/2500000000 : ℝ), (1948474663/5000000000 : ℝ)] ![(1038567153981/3125000000000 : ℝ), (18402288840829/50000000000000 : ℝ), (29961273375537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4225995767/10000000000 : ℝ)|^4695 ≤ (1038567153981/3125000000000 : ℝ)^3671
        have hw : |(4225995767/10000000000 : ℝ)|=(4225995767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1144249027/2500000000 : ℝ)|^4695 ≤ (18402288840829/50000000000000 : ℝ)^3671
        have hw : |(1144249027/2500000000 : ℝ)|=(1144249027/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1948474663/5000000000 : ℝ)|^4695 ≤ (29961273375537/100000000000000 : ℝ)^3671
        have hw : |(1948474663/5000000000 : ℝ)|=(1948474663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1594_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85141271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16567/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5073/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2577/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8193/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16567/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5073/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16567/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5073/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16567/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5073/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16567/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5073/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16567/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5073/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16567/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5073/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5073/50000 : ℝ) ^ (4691/1024 : ℝ) ≤ (2804028356014357/100000000000000000000 : ℝ) := by
    have hpowers : (5073/50000 : ℝ)^4691 ≤ (2804028356014357/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5073 : ℕ)^4691*100000000000000000000^1024 ≤ 2804028356014357^1024*50000^4691 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5073 50000 2804028356014357 100000000000000000000 4691 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5073/50000 : ℝ)) (X := (2804028356014357/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4691 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16567/100000 : ℝ) ^ (4691/1024 : ℝ) ≤ (13252062806246869/50000000000000000000 : ℝ) := by
    have hpowers : (16567/100000 : ℝ)^4691 ≤ (13252062806246869/50000000000000000000 : ℝ)^1024 := by
      have hnat : (16567 : ℕ)^4691*50000000000000000000^1024 ≤ 13252062806246869^1024*100000^4691 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16567 100000 13252062806246869 50000000000000000000 4691 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16567/100000 : ℝ)) (X := (13252062806246869/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4691 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002804028356014357/50000000000000000000 : ℝ) ≤ (10000122415779197/10000000000000000 : ℝ) ^ (4691/1024 : ℝ) := by
    have hpowers : (50002804028356014357/50000000000000000000 : ℝ)^1024 ≤ (10000122415779197/10000000000000000 : ℝ)^4691 := by
      have hnat : (50002804028356014357 : ℕ)^1024*10000000000000000^4691 ≤ 10000122415779197^4691*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002804028356014357 50000000000000000000 10000122415779197 10000000000000000 1024 4691 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000122415779197/10000000000000000 : ℝ)) (X := (50002804028356014357/50000000000000000000 : ℝ)) (by norm_num) 4691 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20005861630793701619/20000000000000000000 : ℝ) ≤ (10000639695424621/10000000000000000 : ℝ) ^ (4691/1024 : ℝ) := by
    have hpowers : (20005861630793701619/20000000000000000000 : ℝ)^1024 ≤ (10000639695424621/10000000000000000 : ℝ)^4691 := by
      have hnat : (20005861630793701619 : ℕ)^1024*10000000000000000^4691 ≤ 10000639695424621^4691*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20005861630793701619 20000000000000000000 10000639695424621 10000000000000000 1024 4691 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000639695424621/10000000000000000 : ℝ)) (X := (20005861630793701619/20000000000000000000 : ℝ)) (by norm_num) 4691 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013252062806246869/25000000000000000000 : ℝ) ≤ (2000231395014009/2000000000000000 : ℝ) ^ (4691/1024 : ℝ) := by
    have hpowers : (25013252062806246869/25000000000000000000 : ℝ)^1024 ≤ (2000231395014009/2000000000000000 : ℝ)^4691 := by
      have hnat : (25013252062806246869 : ℕ)^1024*2000000000000000^4691 ≤ 2000231395014009^4691*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013252062806246869 25000000000000000000 2000231395014009 2000000000000000 1024 4691 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000231395014009/2000000000000000 : ℝ)) (X := (25013252062806246869/25000000000000000000 : ℝ)) (by norm_num) 4691 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2804028356014357/100000000000000000000 : ℝ) ≤ ((64200289393153280129/64210000000000000000 : ℝ)+2*(32329977839/40131250000000 : ℝ)*(5073/50000 : ℝ))^(4691/1024 : ℝ) := by
    rw [show (64200289393153280129/64210000000000000000 : ℝ)+2*(32329977839/40131250000000 : ℝ)*(5073/50000 : ℝ)=(10000122415779197/10000000000000000 : ℝ) by norm_num, show 1+2*(2804028356014357/100000000000000000000 : ℝ)=(50002804028356014357/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13252062806246869/50000000000000000000 : ℝ)+(2804028356014357/100000000000000000000 : ℝ) ≤ ((64200289393153280129/64210000000000000000 : ℝ)+(32329977839/40131250000000 : ℝ)*((16567/100000 : ℝ)+(5073/50000 : ℝ)))^(4691/1024 : ℝ) := by
    rw [show (64200289393153280129/64210000000000000000 : ℝ)+(32329977839/40131250000000 : ℝ)*((16567/100000 : ℝ)+(5073/50000 : ℝ))=(10000639695424621/10000000000000000 : ℝ) by norm_num, show 1+(13252062806246869/50000000000000000000 : ℝ)+(2804028356014357/100000000000000000000 : ℝ)=(20005861630793701619/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13252062806246869/50000000000000000000 : ℝ) ≤ ((64200289393153280129/64210000000000000000 : ℝ)+2*(32329977839/40131250000000 : ℝ)*(16567/100000 : ℝ))^(4691/1024 : ℝ) := by
    rw [show (64200289393153280129/64210000000000000000 : ℝ)+2*(32329977839/40131250000000 : ℝ)*(16567/100000 : ℝ)=(2000231395014009/2000000000000000 : ℝ) by norm_num, show 1+2*(13252062806246869/50000000000000000000 : ℝ)=(25013252062806246869/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (64200289393153280129/64210000000000000000 : ℝ)*(X 1 0+X 2 0)+(32329977839/40131250000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4691/1024 : ℝ)) (lo := (5073/50000 : ℝ)) (hi := (16567/100000 : ℝ)) (c := (64200289393153280129/64210000000000000000 : ℝ)) (alpha := (32329977839/40131250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (64200289393153280129/64210000000000000000 : ℝ)*(X 0 1+X 2 1)+(32329977839/40131250000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4691/1024 : ℝ)) (lo := (5073/50000 : ℝ)) (hi := (16567/100000 : ℝ)) (c := (64200289393153280129/64210000000000000000 : ℝ)) (alpha := (32329977839/40131250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (64200289393153280129/64210000000000000000 : ℝ)*(X 0 2+X 1 2)+(32329977839/40131250000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4691/1024 : ℝ)) (lo := (5073/50000 : ℝ)) (hi := (16567/100000 : ℝ)) (c := (64200289393153280129/64210000000000000000 : ℝ)) (alpha := (32329977839/40131250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-872608111/5000000000 : ℝ)*X 0 0+(5465309411/10000000000 : ℝ)*X 0 1+(5178339397/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2678016533/5000000000 : ℝ)*X 1 0+(-473331819/2500000000 : ℝ)*X 1 1+(1035667881/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2678016533/5000000000 : ℝ)*X 2 0+(517833939/1000000000 : ℝ)*X 2 1+(-1893327297/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4225816979/10000000000 : ℝ)*X 0 0+(1945885411/5000000000 : ℝ)*X 0 1+(2291060267/5000000000 : ℝ)*X 0 2+(4225816979/10000000000 : ℝ)*X 1 0+(1945885411/5000000000 : ℝ)*X 1 1+(2291060267/5000000000 : ℝ)*X 1 2+(4225816979/10000000000 : ℝ)*X 2 0+(1945885411/5000000000 : ℝ)*X 2 1+(2291060267/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-218161311/1250000000 : ℝ)*X 0 0+(518046941/1000000000 : ℝ)*X 0 1+(682894619/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((264002773/500000000 : ℝ)*X 1 0+(-804254927/5000000000 : ℝ)*X 1 1+(546315713/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((660006969/1250000000 : ℝ)*X 2 0+(1365789231/2500000000 : ℝ)*X 2 1+(-804254869/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4225995767/10000000000 : ℝ)*X 0 0+(1144249027/2500000000 : ℝ)*X 0 1+(1948474663/5000000000 : ℝ)*X 0 2+(4225995767/10000000000 : ℝ)*X 1 0+(1144249027/2500000000 : ℝ)*X 1 1+(1948474663/5000000000 : ℝ)*X 1 2+(4225995767/10000000000 : ℝ)*X 2 0+(1144249027/2500000000 : ℝ)*X 2 1+(1948474663/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9839249417937850452850054881/1605250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1054000593/100000000000000 : ℝ)*(base19) + (993000619/100000000000000 : ℝ)*(base23) + (8167947/25000000000000 : ℝ)*(lower2) + (81102199/50000000000000 : ℝ)*(upper3) + (102046569/100000000000000 : ℝ)*(upper5) + (2466630960691563/100000000000000 : ℝ)*(major0) + (2466630960691563/100000000000000 : ℝ)*(major1) + (2466630960691563/100000000000000 : ℝ)*(major2) + (3484697592722143/100000000000000 : ℝ)*(sp0) + (3484708784690123/100000000000000 : ℝ)*(sp1) + (1742354422845049/50000000000000 : ℝ)*(sp2) + (724273098784223/50000000000000 : ℝ)*(sp3) + (6122984287/50000000000000 : ℝ)*(sp4) + (5680809999/100000000000000 : ℝ)*(sp7) + (362137969594611/25000000000000 : ℝ)*(f.failure) + (871177459672679/25000000000000 : ℝ)*(f.sum) + (170583959986233/32105000000000000000000000000 : ℝ)*base66 + (36027222845279948373/6421000000000000000000000000000000 : ℝ)*base68 + (22806380249519948373/6421000000000000000000000000000000 : ℝ)*base70 + (49284342858207948373/6421000000000000000000000000000000 : ℝ)*base72 + (4457738986917/8026250000000000000000000000 : ℝ)*base74 + (28225142681564051627/6421000000000000000000000000000000 : ℝ)*base75 + (69351080938557948373/6421000000000000000000000000000000 : ℝ)*base78 + (33022523003326948373/6421000000000000000000000000000000 : ℝ)*base80 + (8958090879537/8026250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (2209419/1250000000000000000000 : ℝ)*base90 + (2209419/1250000000000000000000 : ℝ)*base92 + (2209419/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (50768281010015891356402917/16052500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (199554693/100000000000000 : ℝ)*(base19) + (474409263/100000000000000 : ℝ)*(base23) + (46649/312500000000 : ℝ)*(upper3) + (3446441/10000000000000 : ℝ)*(lower4) + (108831221/100000000000000 : ℝ)*(upper5) + (12519909272603/500000000000 : ℝ)*(major0) + (12519909272603/500000000000 : ℝ)*(major1) + (12519909272603/500000000000 : ℝ)*(major2) + (4865365741/100000000000000 : ℝ)*(sp1) + (5834885809/100000000000000 : ℝ)*(sp2) + (3537477066884563/100000000000000 : ℝ)*(sp4) + (110546000061379/3125000000000 : ℝ)*(sp5) + (3537470757589491/100000000000000 : ℝ)*(sp6) + (18381081709191/1250000000000 : ℝ)*(sp7) + (18381081709191/1250000000000 : ℝ)*(f.failure) + (3537477066884563/100000000000000 : ℝ)*(f.sum) + (1574024920143/802625000000000000000000000 : ℝ)*base65 + (411992779663855787/32105000000000000000000000000000 : ℝ)*base67 + (451364900967325787/32105000000000000000000000000000 : ℝ)*base69 + (595739888771875787/32105000000000000000000000000000 : ℝ)*base71 + (7143680190107/1605250000000000000000000000 : ℝ)*base73 + (550574976758580787/32105000000000000000000000000000 : ℝ)*base75 + (364669550048675787/32105000000000000000000000000000 : ℝ)*base77 + (682307750157635787/32105000000000000000000000000000 : ℝ)*base79 + (30460515570651/6421000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (878239/62500000000000000000 : ℝ)*base90 + (878239/62500000000000000000 : ℝ)*base92 + (878239/62500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1594_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85141271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16567/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5073/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2577/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8193/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1594_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1594_s4_0 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1745386821/10000000000 : ℝ)*x 0 + (1092893039/2000000000 : ℝ)*x 1 + (258953521/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1745386821/10000000000 : ℝ)^4695 ≤ (670351604291/6250000000000 : ℝ)^3671 := by
    have hnat : (1745386821 : ℕ)^4695*6250000000000^3671 ≤ 670351604291^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1745386821 10000000000 670351604291 6250000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1092893039/2000000000 : ℝ)^4695 ≤ (46167717574009/100000000000000 : ℝ)^3671 := by
    have hnat : (1092893039 : ℕ)^4695*100000000000000^3671 ≤ 46167717574009^3671*2000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092893039 2000000000 46167717574009 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258953521/500000000 : ℝ)^4695 ≤ (134708302343/312500000000 : ℝ)^3671 := by
    have hnat : (258953521 : ℕ)^4695*312500000000^3671 ≤ 134708302343^3671*500000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258953521 500000000 134708302343 312500000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1745386821/10000000000 : ℝ), (1092893039/2000000000 : ℝ), (258953521/500000000 : ℝ)] ![(670351604291/6250000000000 : ℝ), (46167717574009/100000000000000 : ℝ), (134708302343/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1745386821/10000000000 : ℝ)|^4695 ≤ (670351604291/6250000000000 : ℝ)^3671
        have hw : |(-1745386821/10000000000 : ℝ)|=(1745386821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1092893039/2000000000 : ℝ)|^4695 ≤ (46167717574009/100000000000000 : ℝ)^3671
        have hw : |(1092893039/2000000000 : ℝ)|=(1092893039/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(258953521/500000000 : ℝ)|^4695 ≤ (134708302343/312500000000 : ℝ)^3671
        have hw : |(258953521/500000000 : ℝ)|=(258953521/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_s4_1 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071161673/2000000000 : ℝ)*x 0 + (-1892659669/10000000000 : ℝ)*x 1 + (2589535213/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071161673/2000000000 : ℝ)^4695 ≤ (22498452922969/50000000000000 : ℝ)^3671 := by
    have hnat : (1071161673 : ℕ)^4695*50000000000000^3671 ≤ 22498452922969^3671*2000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071161673 2000000000 22498452922969 50000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1892659669/10000000000 : ℝ)^4695 ≤ (237928746683/2000000000000 : ℝ)^3671 := by
    have hnat : (1892659669 : ℕ)^4695*2000000000000^3671 ≤ 237928746683^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1892659669 10000000000 237928746683 2000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2589535213/5000000000 : ℝ)^4695 ≤ (4310665681363/10000000000000 : ℝ)^3671 := by
    have hnat : (2589535213 : ℕ)^4695*10000000000000^3671 ≤ 4310665681363^3671*5000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589535213 5000000000 4310665681363 10000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071161673/2000000000 : ℝ), (-1892659669/10000000000 : ℝ), (2589535213/5000000000 : ℝ)] ![(22498452922969/50000000000000 : ℝ), (237928746683/2000000000000 : ℝ), (4310665681363/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071161673/2000000000 : ℝ)|^4695 ≤ (22498452922969/50000000000000 : ℝ)^3671
        have hw : |(1071161673/2000000000 : ℝ)|=(1071161673/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1892659669/10000000000 : ℝ)|^4695 ≤ (237928746683/2000000000000 : ℝ)^3671
        have hw : |(-1892659669/10000000000 : ℝ)|=(1892659669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2589535213/5000000000 : ℝ)|^4695 ≤ (4310665681363/10000000000000 : ℝ)^3671
        have hw : |(2589535213/5000000000 : ℝ)|=(2589535213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_s4_2 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677904193/5000000000 : ℝ)*x 0 + (517907041/1000000000 : ℝ)*x 1 + (-1892659661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677904193/5000000000 : ℝ)^4695 ≤ (1406153314737/3125000000000 : ℝ)^3671 := by
    have hnat : (2677904193 : ℕ)^4695*3125000000000^3671 ≤ 1406153314737^3671*5000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677904193 5000000000 1406153314737 3125000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (517907041/1000000000 : ℝ)^4695 ≤ (4310665664331/10000000000000 : ℝ)^3671 := by
    have hnat : (517907041 : ℕ)^4695*10000000000000^3671 ≤ 4310665664331^3671*1000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517907041 1000000000 4310665664331 10000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1892659661/10000000000 : ℝ)^4695 ≤ (11896437269839/100000000000000 : ℝ)^3671 := by
    have hnat : (1892659661 : ℕ)^4695*100000000000000^3671 ≤ 11896437269839^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1892659661 10000000000 11896437269839 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677904193/5000000000 : ℝ), (517907041/1000000000 : ℝ), (-1892659661/10000000000 : ℝ)] ![(1406153314737/3125000000000 : ℝ), (4310665664331/10000000000000 : ℝ), (11896437269839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677904193/5000000000 : ℝ)|^4695 ≤ (1406153314737/3125000000000 : ℝ)^3671
        have hw : |(2677904193/5000000000 : ℝ)|=(2677904193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(517907041/1000000000 : ℝ)|^4695 ≤ (4310665664331/10000000000000 : ℝ)^3671
        have hw : |(517907041/1000000000 : ℝ)|=(517907041/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1892659661/10000000000 : ℝ)|^4695 ≤ (11896437269839/100000000000000 : ℝ)^3671
        have hw : |(-1892659661/10000000000 : ℝ)|=(1892659661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_s4_3 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4225926791/10000000000 : ℝ)*x 0 + (973413419/2500000000 : ℝ)*x 1 + (572526741/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4225926791/10000000000 : ℝ)^4695 ≤ (6646691035243/20000000000000 : ℝ)^3671 := by
    have hnat : (4225926791 : ℕ)^4695*20000000000000^3671 ≤ 6646691035243^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4225926791 10000000000 6646691035243 20000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (973413419/2500000000 : ℝ)^4695 ≤ (1496443551067/5000000000000 : ℝ)^3671 := by
    have hnat : (973413419 : ℕ)^4695*5000000000000^3671 ≤ 1496443551067^3671*2500000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      973413419 2500000000 1496443551067 5000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (572526741/1250000000 : ℝ)^4695 ≤ (4604709222797/12500000000000 : ℝ)^3671 := by
    have hnat : (572526741 : ℕ)^4695*12500000000000^3671 ≤ 4604709222797^3671*1250000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      572526741 1250000000 4604709222797 12500000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4225926791/10000000000 : ℝ), (973413419/2500000000 : ℝ), (572526741/1250000000 : ℝ)] ![(6646691035243/20000000000000 : ℝ), (1496443551067/5000000000000 : ℝ), (4604709222797/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4225926791/10000000000 : ℝ)|^4695 ≤ (6646691035243/20000000000000 : ℝ)^3671
        have hw : |(4225926791/10000000000 : ℝ)|=(4225926791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(973413419/2500000000 : ℝ)|^4695 ≤ (1496443551067/5000000000000 : ℝ)^3671
        have hw : |(973413419/2500000000 : ℝ)|=(973413419/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(572526741/1250000000 : ℝ)|^4695 ≤ (4604709222797/12500000000000 : ℝ)^3671
        have hw : |(572526741/1250000000 : ℝ)|=(572526741/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_s4_4 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1745460117/10000000000 : ℝ)*x 0 + (1036235463/2000000000 : ℝ)*x 1 + (1365584011/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1745460117/10000000000 : ℝ)^4695 ≤ (10726201725013/100000000000000 : ℝ)^3671 := by
    have hnat : (1745460117 : ℕ)^4695*100000000000000^3671 ≤ 10726201725013^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1745460117 10000000000 10726201725013 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036235463/2000000000 : ℝ)^4695 ≤ (43129085819833/100000000000000 : ℝ)^3671 := by
    have hnat : (1036235463 : ℕ)^4695*100000000000000^3671 ≤ 43129085819833^3671*2000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036235463 2000000000 43129085819833 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1365584011/2500000000 : ℝ)^4695 ≤ (46144712437663/100000000000000 : ℝ)^3671 := by
    have hnat : (1365584011 : ℕ)^4695*100000000000000^3671 ≤ 46144712437663^3671*2500000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365584011 2500000000 46144712437663 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1745460117/10000000000 : ℝ), (1036235463/2000000000 : ℝ), (1365584011/2500000000 : ℝ)] ![(10726201725013/100000000000000 : ℝ), (43129085819833/100000000000000 : ℝ), (46144712437663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1745460117/10000000000 : ℝ)|^4695 ≤ (10726201725013/100000000000000 : ℝ)^3671
        have hw : |(-1745460117/10000000000 : ℝ)|=(1745460117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036235463/2000000000 : ℝ)|^4695 ≤ (43129085819833/100000000000000 : ℝ)^3671
        have hw : |(1036235463/2000000000 : ℝ)|=(1036235463/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1365584011/2500000000 : ℝ)|^4695 ≤ (46144712437663/100000000000000 : ℝ)^3671
        have hw : |(1365584011/2500000000 : ℝ)|=(1365584011/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_s4_5 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5280249381/10000000000 : ℝ)*x 0 + (-32187873/200000000 : ℝ)*x 1 + (546233659/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5280249381/10000000000 : ℝ)^4695 ≤ (5523327875313/12500000000000 : ℝ)^3671 := by
    have hnat : (5280249381 : ℕ)^4695*12500000000000^3671 ≤ 5523327875313^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280249381 10000000000 5523327875313 12500000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32187873/200000000 : ℝ)^4695 ≤ (2417164660139/25000000000000 : ℝ)^3671 := by
    have hnat : (32187873 : ℕ)^4695*25000000000000^3671 ≤ 2417164660139^3671*200000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32187873 200000000 2417164660139 25000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (546233659/1000000000 : ℝ)^4695 ≤ (9228943667357/20000000000000 : ℝ)^3671 := by
    have hnat : (546233659 : ℕ)^4695*20000000000000^3671 ≤ 9228943667357^3671*1000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546233659 1000000000 9228943667357 20000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5280249381/10000000000 : ℝ), (-32187873/200000000 : ℝ), (546233659/1000000000 : ℝ)] ![(5523327875313/12500000000000 : ℝ), (2417164660139/25000000000000 : ℝ), (9228943667357/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5280249381/10000000000 : ℝ)|^4695 ≤ (5523327875313/12500000000000 : ℝ)^3671
        have hw : |(5280249381/10000000000 : ℝ)|=(5280249381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-32187873/200000000 : ℝ)|^4695 ≤ (2417164660139/25000000000000 : ℝ)^3671
        have hw : |(-32187873/200000000 : ℝ)|=(32187873/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(546233659/1000000000 : ℝ)|^4695 ≤ (9228943667357/20000000000000 : ℝ)^3671
        have hw : |(546233659/1000000000 : ℝ)|=(546233659/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_s4_6 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (132006241/250000000 : ℝ)*x 0 + (5462336151/10000000000 : ℝ)*x 1 + (-1609393907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132006241/250000000 : ℝ)^4695 ≤ (44186625774467/100000000000000 : ℝ)^3671 := by
    have hnat : (132006241 : ℕ)^4695*100000000000000^3671 ≤ 44186625774467^3671*250000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132006241 250000000 44186625774467 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5462336151/10000000000 : ℝ)^4695 ≤ (23072356796859/50000000000000 : ℝ)^3671 := by
    have hnat : (5462336151 : ℕ)^4695*50000000000000^3671 ≤ 23072356796859^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462336151 10000000000 23072356796859 50000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1609393907/10000000000 : ℝ)^4695 ≤ (9668660615197/100000000000000 : ℝ)^3671 := by
    have hnat : (1609393907 : ℕ)^4695*100000000000000^3671 ≤ 9668660615197^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1609393907 10000000000 9668660615197 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132006241/250000000 : ℝ), (5462336151/10000000000 : ℝ), (-1609393907/10000000000 : ℝ)] ![(44186625774467/100000000000000 : ℝ), (23072356796859/50000000000000 : ℝ), (9668660615197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132006241/250000000 : ℝ)|^4695 ≤ (44186625774467/100000000000000 : ℝ)^3671
        have hw : |(132006241/250000000 : ℝ)|=(132006241/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5462336151/10000000000 : ℝ)|^4695 ≤ (23072356796859/50000000000000 : ℝ)^3671
        have hw : |(5462336151/10000000000 : ℝ)|=(5462336151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1609393907/10000000000 : ℝ)|^4695 ≤ (9668660615197/100000000000000 : ℝ)^3671
        have hw : |(-1609393907/10000000000 : ℝ)|=(1609393907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_s4_7 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (66032851/156250000 : ℝ)*x 0 + (571893189/1250000000 : ℝ)*x 1 + (1949387739/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66032851/156250000 : ℝ)^4695 ≤ (33235222077451/100000000000000 : ℝ)^3671 := by
    have hnat : (66032851 : ℕ)^4695*100000000000000^3671 ≤ 33235222077451^3671*156250000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66032851 156250000 33235222077451 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (571893189/1250000000 : ℝ)^4695 ≤ (7357109353651/20000000000000 : ℝ)^3671 := by
    have hnat : (571893189 : ℕ)^4695*20000000000000^3671 ≤ 7357109353651^3671*1250000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      571893189 1250000000 7357109353651 20000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1949387739/5000000000 : ℝ)^4695 ≤ (2997923112981/10000000000000 : ℝ)^3671 := by
    have hnat : (1949387739 : ℕ)^4695*10000000000000^3671 ≤ 2997923112981^3671*5000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1949387739 5000000000 2997923112981 10000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66032851/156250000 : ℝ), (571893189/1250000000 : ℝ), (1949387739/5000000000 : ℝ)] ![(33235222077451/100000000000000 : ℝ), (7357109353651/20000000000000 : ℝ), (2997923112981/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66032851/156250000 : ℝ)|^4695 ≤ (33235222077451/100000000000000 : ℝ)^3671
        have hw : |(66032851/156250000 : ℝ)|=(66032851/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(571893189/1250000000 : ℝ)|^4695 ≤ (7357109353651/20000000000000 : ℝ)^3671
        have hw : |(571893189/1250000000 : ℝ)|=(571893189/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1949387739/5000000000 : ℝ)|^4695 ≤ (2997923112981/10000000000000 : ℝ)^3671
        have hw : |(1949387739/5000000000 : ℝ)|=(1949387739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1594_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85141271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8193/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2577/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2581/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16369/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8193/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2577/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8193/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2577/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8193/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2577/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8193/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2577/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8193/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2577/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8193/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2577/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2577/25000 : ℝ) ^ (4691/1024 : ℝ) ≤ (3015074201224231/100000000000000000000 : ℝ) := by
    have hpowers : (2577/25000 : ℝ)^4691 ≤ (3015074201224231/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2577 : ℕ)^4691*100000000000000000000^1024 ≤ 3015074201224231^1024*25000^4691 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2577 25000 3015074201224231 100000000000000000000 4691 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2577/25000 : ℝ)) (X := (3015074201224231/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4691 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8193/50000 : ℝ) ^ (4691/1024 : ℝ) ≤ (25203312702356077/100000000000000000000 : ℝ) := by
    have hpowers : (8193/50000 : ℝ)^4691 ≤ (25203312702356077/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8193 : ℕ)^4691*100000000000000000000^1024 ≤ 25203312702356077^1024*50000^4691 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8193 50000 25203312702356077 100000000000000000000 4691 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8193/50000 : ℝ)) (X := (25203312702356077/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4691 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50003015074201224231/50000000000000000000 : ℝ) ≤ (10000131629214091/10000000000000000 : ℝ) ^ (4691/1024 : ℝ) := by
    have hpowers : (50003015074201224231/50000000000000000000 : ℝ)^1024 ≤ (10000131629214091/10000000000000000 : ℝ)^4691 := by
      have hnat : (50003015074201224231 : ℕ)^1024*10000000000000000^4691 ≤ 10000131629214091^4691*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50003015074201224231 50000000000000000000 10000131629214091 10000000000000000 1024 4691 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000131629214091/10000000000000000 : ℝ)) (X := (50003015074201224231/50000000000000000000 : ℝ)) (by norm_num) 4691 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25007054596725895077/25000000000000000000 : ℝ) ≤ (5000307956104667/5000000000000000 : ℝ) ^ (4691/1024 : ℝ) := by
    have hpowers : (25007054596725895077/25000000000000000000 : ℝ)^1024 ≤ (5000307956104667/5000000000000000 : ℝ)^4691 := by
      have hnat : (25007054596725895077 : ℕ)^1024*5000000000000000^4691 ≤ 5000307956104667^4691*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007054596725895077 25000000000000000000 5000307956104667 5000000000000000 1024 4691 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000307956104667/5000000000000000 : ℝ)) (X := (25007054596725895077/25000000000000000000 : ℝ)) (by norm_num) 4691 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50025203312702356077/50000000000000000000 : ℝ) ≤ (10001100195204577/10000000000000000 : ℝ) ^ (4691/1024 : ℝ) := by
    have hpowers : (50025203312702356077/50000000000000000000 : ℝ)^1024 ≤ (10001100195204577/10000000000000000 : ℝ)^4691 := by
      have hnat : (50025203312702356077 : ℕ)^1024*10000000000000000^4691 ≤ 10001100195204577^4691*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025203312702356077 50000000000000000000 10001100195204577 10000000000000000 1024 4691 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001100195204577/10000000000000000 : ℝ)) (X := (50025203312702356077/50000000000000000000 : ℝ)) (by norm_num) 4691 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3015074201224231/100000000000000000000 : ℝ) ≤ ((2025693868804443847/2026000000000000000 : ℝ)+2*(161427665081/202600000000000 : ℝ)*(2577/25000 : ℝ))^(4691/1024 : ℝ) := by
    rw [show (2025693868804443847/2026000000000000000 : ℝ)+2*(161427665081/202600000000000 : ℝ)*(2577/25000 : ℝ)=(10000131629214091/10000000000000000 : ℝ) by norm_num, show 1+2*(3015074201224231/100000000000000000000 : ℝ)=(50003015074201224231/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(25203312702356077/100000000000000000000 : ℝ)+(3015074201224231/100000000000000000000 : ℝ) ≤ ((2025693868804443847/2026000000000000000 : ℝ)+(161427665081/202600000000000 : ℝ)*((8193/50000 : ℝ)+(2577/25000 : ℝ)))^(4691/1024 : ℝ) := by
    rw [show (2025693868804443847/2026000000000000000 : ℝ)+(161427665081/202600000000000 : ℝ)*((8193/50000 : ℝ)+(2577/25000 : ℝ))=(5000307956104667/5000000000000000 : ℝ) by norm_num, show 1+(25203312702356077/100000000000000000000 : ℝ)+(3015074201224231/100000000000000000000 : ℝ)=(25007054596725895077/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(25203312702356077/100000000000000000000 : ℝ) ≤ ((2025693868804443847/2026000000000000000 : ℝ)+2*(161427665081/202600000000000 : ℝ)*(8193/50000 : ℝ))^(4691/1024 : ℝ) := by
    rw [show (2025693868804443847/2026000000000000000 : ℝ)+2*(161427665081/202600000000000 : ℝ)*(8193/50000 : ℝ)=(10001100195204577/10000000000000000 : ℝ) by norm_num, show 1+2*(25203312702356077/100000000000000000000 : ℝ)=(50025203312702356077/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2025693868804443847/2026000000000000000 : ℝ)*(X 1 0+X 2 0)+(161427665081/202600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4691/1024 : ℝ)) (lo := (2577/25000 : ℝ)) (hi := (8193/50000 : ℝ)) (c := (2025693868804443847/2026000000000000000 : ℝ)) (alpha := (161427665081/202600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2025693868804443847/2026000000000000000 : ℝ)*(X 0 1+X 2 1)+(161427665081/202600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4691/1024 : ℝ)) (lo := (2577/25000 : ℝ)) (hi := (8193/50000 : ℝ)) (c := (2025693868804443847/2026000000000000000 : ℝ)) (alpha := (161427665081/202600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2025693868804443847/2026000000000000000 : ℝ)*(X 0 2+X 1 2)+(161427665081/202600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4691/1024 : ℝ)) (lo := (2577/25000 : ℝ)) (hi := (8193/50000 : ℝ)) (c := (2025693868804443847/2026000000000000000 : ℝ)) (alpha := (161427665081/202600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1745386821/10000000000 : ℝ)*X 0 0+(1092893039/2000000000 : ℝ)*X 0 1+(258953521/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1071161673/2000000000 : ℝ)*X 1 0+(-1892659669/10000000000 : ℝ)*X 1 1+(2589535213/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2677904193/5000000000 : ℝ)*X 2 0+(517907041/1000000000 : ℝ)*X 2 1+(-1892659661/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4225926791/10000000000 : ℝ)*X 0 0+(973413419/2500000000 : ℝ)*X 0 1+(572526741/1250000000 : ℝ)*X 0 2+(4225926791/10000000000 : ℝ)*X 1 0+(973413419/2500000000 : ℝ)*X 1 1+(572526741/1250000000 : ℝ)*X 1 2+(4225926791/10000000000 : ℝ)*X 2 0+(973413419/2500000000 : ℝ)*X 2 1+(572526741/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1745460117/10000000000 : ℝ)*X 0 0+(1036235463/2000000000 : ℝ)*X 0 1+(1365584011/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5280249381/10000000000 : ℝ)*X 1 0+(-32187873/200000000 : ℝ)*X 1 1+(546233659/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((132006241/250000000 : ℝ)*X 2 0+(5462336151/10000000000 : ℝ)*X 2 1+(-1609393907/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((66032851/156250000 : ℝ)*X 0 0+(571893189/1250000000 : ℝ)*X 0 1+(1949387739/5000000000 : ℝ)*X 0 2+(66032851/156250000 : ℝ)*X 1 0+(571893189/1250000000 : ℝ)*X 1 1+(1949387739/5000000000 : ℝ)*X 1 2+(66032851/156250000 : ℝ)*X 2 0+(571893189/1250000000 : ℝ)*X 2 1+(1949387739/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (43599550924264398651262899/12662500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (113671701/20000000000000 : ℝ)*(base19) + (553406699/100000000000000 : ℝ)*(base23) + (7683079/50000000000000 : ℝ)*(lower2) + (2387749/3125000000000 : ℝ)*(upper3) + (12588927/20000000000000 : ℝ)*(upper5) + (620059368838339/25000000000000 : ℝ)*(major0) + (620059368838339/25000000000000 : ℝ)*(major1) + (620059368838339/25000000000000 : ℝ)*(major2) + (3503925356012229/100000000000000 : ℝ)*(sp0) + (3503931837433381/100000000000000 : ℝ)*(sp1) + (875982963096297/25000000000000 : ℝ)*(sp2) + (1456539295533039/100000000000000 : ℝ)*(sp3) + (7049779657/100000000000000 : ℝ)*(sp4) + (626921673/20000000000000 : ℝ)*(sp7) + (364135607535351/25000000000000 : ℝ)*(f.failure) + (1751966202895943/50000000000000 : ℝ)*(f.sum) + (26958313020597/5065000000000000000000000000 : ℝ)*base66 + (287693955854259867/50650000000000000000000000000000 : ℝ)*base68 + (5807401813340133/50650000000000000000000000000000 : ℝ)*base69 + (250959102277259867/50650000000000000000000000000000 : ℝ)*base72 + (13798495987157/5065000000000000000000000000 : ℝ)*base74 + (309289652778359867/50650000000000000000000000000000 : ℝ)*base76 + (347323487854209867/50650000000000000000000000000000 : ℝ)*base78 + (851496148059759867/50650000000000000000000000000000 : ℝ)*base80 + (6045361837423/1266250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (11571121/1250000000000000000000 : ℝ)*base89 + (11571121/1250000000000000000000 : ℝ)*base91 + (11571121/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (225346422763290741859433109/25325000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1348330479/100000000000000 : ℝ)*(base19) + (1598584507/100000000000000 : ℝ)*(base23) + (6839903/1250000000000 : ℝ)*(lower1) + (49303469/100000000000000 : ℝ)*(upper2) + (224034891/100000000000000 : ℝ)*(upper3) + (92761349/50000000000000 : ℝ)*(upper5) + (1258790598558649/50000000000000 : ℝ)*(major0) + (1258790598558649/50000000000000 : ℝ)*(major1) + (1258790598558649/50000000000000 : ℝ)*(major2) + (614176603/50000000000000 : ℝ)*(sp1) + (222293076311999/6250000000000 : ℝ)*(sp4) + (1778343322154149/50000000000000 : ℝ)*(sp5) + (889171905601869/25000000000000 : ℝ)*(sp6) + (184809109579573/12500000000000 : ℝ)*(sp7) + (184809109579573/12500000000000 : ℝ)*(f.failure) + (222293076311999/6250000000000 : ℝ)*(f.sum) + (17783197940449/5065000000000000000000000000 : ℝ)*base65 + (652375564346027297/101300000000000000000000000000000 : ℝ)*base68 + (2269944548170027297/101300000000000000000000000000000 : ℝ)*base70 + (721231274902827297/101300000000000000000000000000000 : ℝ)*base72 + (3652791823459/5065000000000000000000000000 : ℝ)*base73 + (5346405934027297/101300000000000000000000000000000 : ℝ)*base76 + (542458173911572703/101300000000000000000000000000000 : ℝ)*base77 + (96220524436827297/101300000000000000000000000000000 : ℝ)*base80 + (62471714761731/5065000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (8357283/625000000000000000000 : ℝ)*base89 + (8357283/625000000000000000000 : ℝ)*base91 + (8357283/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1594_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85141271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8193/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2577/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2581/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16369/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1594_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1594_s5_0 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-87270079/500000000 : ℝ)*x 0 + (2732193639/5000000000 : ℝ)*x 1 + (2589569307/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (87270079/500000000 : ℝ)^4695 ≤ (20948714187/195312500000 : ℝ)^3671 := by
    have hnat : (87270079 : ℕ)^4695*195312500000^3671 ≤ 20948714187^3671*500000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87270079 500000000 20948714187 195312500000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2732193639/5000000000 : ℝ)^4695 ≤ (5770859456149/12500000000000 : ℝ)^3671 := by
    have hnat : (2732193639 : ℕ)^4695*12500000000000^3671 ≤ 5770859456149^3671*5000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732193639 5000000000 5770859456149 12500000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2589569307/5000000000 : ℝ)^4695 ≤ (43107382672999/100000000000000 : ℝ)^3671 := by
    have hnat : (2589569307 : ℕ)^4695*100000000000000^3671 ≤ 43107382672999^3671*5000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589569307 5000000000 43107382672999 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-87270079/500000000 : ℝ), (2732193639/5000000000 : ℝ), (2589569307/5000000000 : ℝ)] ![(20948714187/195312500000 : ℝ), (5770859456149/12500000000000 : ℝ), (43107382672999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-87270079/500000000 : ℝ)|^4695 ≤ (20948714187/195312500000 : ℝ)^3671
        have hw : |(-87270079/500000000 : ℝ)|=(87270079/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2732193639/5000000000 : ℝ)|^4695 ≤ (5770859456149/12500000000000 : ℝ)^3671
        have hw : |(2732193639/5000000000 : ℝ)|=(2732193639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2589569307/5000000000 : ℝ)|^4695 ≤ (43107382672999/100000000000000 : ℝ)^3671
        have hw : |(2589569307/5000000000 : ℝ)|=(2589569307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_s5_1 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338946917/2500000000 : ℝ)*x 0 + (-14785911/78125000 : ℝ)*x 1 + (5179138939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338946917/2500000000 : ℝ)^4695 ≤ (11249170863889/25000000000000 : ℝ)^3671 := by
    have hnat : (1338946917 : ℕ)^4695*25000000000000^3671 ≤ 11249170863889^3671*2500000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338946917 2500000000 11249170863889 25000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (14785911/78125000 : ℝ)^4695 ≤ (743495649789/6250000000000 : ℝ)^3671 := by
    have hnat : (14785911 : ℕ)^4695*6250000000000^3671 ≤ 743495649789^3671*78125000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14785911 78125000 743495649789 6250000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5179138939/10000000000 : ℝ)^4695 ≤ (21553693066311/50000000000000 : ℝ)^3671 := by
    have hnat : (5179138939 : ℕ)^4695*50000000000000^3671 ≤ 21553693066311^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179138939 10000000000 21553693066311 50000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338946917/2500000000 : ℝ), (-14785911/78125000 : ℝ), (5179138939/10000000000 : ℝ)] ![(11249170863889/25000000000000 : ℝ), (743495649789/6250000000000 : ℝ), (21553693066311/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338946917/2500000000 : ℝ)|^4695 ≤ (11249170863889/25000000000000 : ℝ)^3671
        have hw : |(1338946917/2500000000 : ℝ)|=(1338946917/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-14785911/78125000 : ℝ)|^4695 ≤ (743495649789/6250000000000 : ℝ)^3671
        have hw : |(-14785911/78125000 : ℝ)|=(14785911/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5179138939/10000000000 : ℝ)|^4695 ≤ (21553693066311/50000000000000 : ℝ)^3671
        have hw : |(5179138939/10000000000 : ℝ)|=(5179138939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_s5_2 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5355787809/10000000000 : ℝ)*x 0 + (517913871/1000000000 : ℝ)*x 1 + (-946298361/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355787809/10000000000 : ℝ)^4695 ≤ (2812292810663/6250000000000 : ℝ)^3671 := by
    have hnat : (5355787809 : ℕ)^4695*6250000000000^3671 ≤ 2812292810663^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355787809 10000000000 2812292810663 6250000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (517913871/1000000000 : ℝ)^4695 ≤ (43107383694919/100000000000000 : ℝ)^3671 := by
    have hnat : (517913871 : ℕ)^4695*100000000000000^3671 ≤ 43107383694919^3671*1000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517913871 1000000000 43107383694919 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (946298361/5000000000 : ℝ)^4695 ≤ (1486991414131/12500000000000 : ℝ)^3671 := by
    have hnat : (946298361 : ℕ)^4695*12500000000000^3671 ≤ 1486991414131^3671*5000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      946298361 5000000000 1486991414131 12500000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355787809/10000000000 : ℝ), (517913871/1000000000 : ℝ), (-946298361/5000000000 : ℝ)] ![(2812292810663/6250000000000 : ℝ), (43107383694919/100000000000000 : ℝ), (1486991414131/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355787809/10000000000 : ℝ)|^4695 ≤ (2812292810663/6250000000000 : ℝ)^3671
        have hw : |(5355787809/10000000000 : ℝ)|=(5355787809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(517913871/1000000000 : ℝ)|^4695 ≤ (43107383694919/100000000000000 : ℝ)^3671
        have hw : |(517913871/1000000000 : ℝ)|=(517913871/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-946298361/5000000000 : ℝ)|^4695 ≤ (1486991414131/12500000000000 : ℝ)^3671
        have hw : |(-946298361/5000000000 : ℝ)|=(946298361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_s5_3 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4225936927/10000000000 : ℝ)*x 0 + (1946914399/5000000000 : ℝ)*x 1 + (91600733/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4225936927/10000000000 : ℝ)^4695 ≤ (33233557122519/100000000000000 : ℝ)^3671 := by
    have hnat : (4225936927 : ℕ)^4695*100000000000000^3671 ≤ 33233557122519^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4225936927 10000000000 33233557122519 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1946914399/5000000000 : ℝ)^4695 ≤ (14965296301563/50000000000000 : ℝ)^3671 := by
    have hnat : (1946914399 : ℕ)^4695*50000000000000^3671 ≤ 14965296301563^3671*5000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1946914399 5000000000 14965296301563 50000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (91600733/200000000 : ℝ)^4695 ≤ (18417925131997/50000000000000 : ℝ)^3671 := by
    have hnat : (91600733 : ℕ)^4695*50000000000000^3671 ≤ 18417925131997^3671*200000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91600733 200000000 18417925131997 50000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4225936927/10000000000 : ℝ), (1946914399/5000000000 : ℝ), (91600733/200000000 : ℝ)] ![(33233557122519/100000000000000 : ℝ), (14965296301563/50000000000000 : ℝ), (18417925131997/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4225936927/10000000000 : ℝ)|^4695 ≤ (33233557122519/100000000000000 : ℝ)^3671
        have hw : |(4225936927/10000000000 : ℝ)|=(4225936927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1946914399/5000000000 : ℝ)|^4695 ≤ (14965296301563/50000000000000 : ℝ)^3671
        have hw : |(1946914399/5000000000 : ℝ)|=(1946914399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(91600733/200000000 : ℝ)|^4695 ≤ (18417925131997/50000000000000 : ℝ)^3671
        have hw : |(91600733/200000000 : ℝ)|=(91600733/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_s5_4 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1745474553/10000000000 : ℝ)*x 0 + (1295310873/2500000000 : ℝ)*x 1 + (2731130167/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1745474553/10000000000 : ℝ)^4695 ≤ (67039469893/625000000000 : ℝ)^3671 := by
    have hnat : (1745474553 : ℕ)^4695*625000000000^3671 ≤ 67039469893^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1745474553 10000000000 67039469893 625000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1295310873/2500000000 : ℝ)^4695 ≤ (10782447588013/25000000000000 : ℝ)^3671 := by
    have hnat : (1295310873 : ℕ)^4695*25000000000000^3671 ≤ 10782447588013^3671*2500000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295310873 2500000000 10782447588013 25000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2731130167/5000000000 : ℝ)^4695 ≤ (46143894449257/100000000000000 : ℝ)^3671 := by
    have hnat : (2731130167 : ℕ)^4695*100000000000000^3671 ≤ 46143894449257^3671*5000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2731130167 5000000000 46143894449257 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1745474553/10000000000 : ℝ), (1295310873/2500000000 : ℝ), (2731130167/5000000000 : ℝ)] ![(67039469893/625000000000 : ℝ), (10782447588013/25000000000000 : ℝ), (46143894449257/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1745474553/10000000000 : ℝ)|^4695 ≤ (67039469893/625000000000 : ℝ)^3671
        have hw : |(-1745474553/10000000000 : ℝ)|=(1745474553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1295310873/2500000000 : ℝ)|^4695 ≤ (10782447588013/25000000000000 : ℝ)^3671
        have hw : |(1295310873/2500000000 : ℝ)|=(1295310873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2731130167/5000000000 : ℝ)|^4695 ≤ (46143894449257/100000000000000 : ℝ)^3671
        have hw : |(2731130167/5000000000 : ℝ)|=(2731130167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_s5_5 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5280268137/10000000000 : ℝ)*x 0 + (-321894949/2000000000 : ℝ)*x 1 + (273113017/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5280268137/10000000000 : ℝ)^4695 ≤ (44186823739781/100000000000000 : ℝ)^3671 := by
    have hnat : (5280268137 : ℕ)^4695*100000000000000^3671 ≤ 44186823739781^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280268137 10000000000 44186823739781 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (321894949/2000000000 : ℝ)^4695 ≤ (1933856346543/20000000000000 : ℝ)^3671 := by
    have hnat : (321894949 : ℕ)^4695*20000000000000^3671 ≤ 1933856346543^3671*2000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321894949 2000000000 1933856346543 20000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (273113017/500000000 : ℝ)^4695 ≤ (23071947257041/50000000000000 : ℝ)^3671 := by
    have hnat : (273113017 : ℕ)^4695*50000000000000^3671 ≤ 23071947257041^3671*500000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273113017 500000000 23071947257041 50000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5280268137/10000000000 : ℝ), (-321894949/2000000000 : ℝ), (273113017/500000000 : ℝ)] ![(44186823739781/100000000000000 : ℝ), (1933856346543/20000000000000 : ℝ), (23071947257041/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5280268137/10000000000 : ℝ)|^4695 ≤ (44186823739781/100000000000000 : ℝ)^3671
        have hw : |(5280268137/10000000000 : ℝ)|=(5280268137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-321894949/2000000000 : ℝ)|^4695 ≤ (1933856346543/20000000000000 : ℝ)^3671
        have hw : |(-321894949/2000000000 : ℝ)|=(321894949/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(273113017/500000000 : ℝ)|^4695 ≤ (23071947257041/50000000000000 : ℝ)^3671
        have hw : |(273113017/500000000 : ℝ)|=(273113017/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_s5_6 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5280268099/10000000000 : ℝ)*x 0 + (2731130161/5000000000 : ℝ)*x 1 + (-201184353/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5280268099/10000000000 : ℝ)^4695 ≤ (11046705833271/25000000000000 : ℝ)^3671 := by
    have hnat : (5280268099 : ℕ)^4695*25000000000000^3671 ≤ 11046705833271^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280268099 10000000000 11046705833271 25000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2731130161/5000000000 : ℝ)^4695 ≤ (23071947159803/50000000000000 : ℝ)^3671 := by
    have hnat : (2731130161 : ℕ)^4695*50000000000000^3671 ≤ 23071947159803^3671*5000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2731130161 5000000000 23071947159803 50000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (201184353/1250000000 : ℝ)^4695 ≤ (1933856467943/20000000000000 : ℝ)^3671 := by
    have hnat : (201184353 : ℕ)^4695*20000000000000^3671 ≤ 1933856467943^3671*1250000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201184353 1250000000 1933856467943 20000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5280268099/10000000000 : ℝ), (2731130161/5000000000 : ℝ), (-201184353/1250000000 : ℝ)] ![(11046705833271/25000000000000 : ℝ), (23071947159803/50000000000000 : ℝ), (1933856467943/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5280268099/10000000000 : ℝ)|^4695 ≤ (11046705833271/25000000000000 : ℝ)^3671
        have hw : |(5280268099/10000000000 : ℝ)|=(5280268099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2731130161/5000000000 : ℝ)|^4695 ≤ (23071947159803/50000000000000 : ℝ)^3671
        have hw : |(2731130161/5000000000 : ℝ)|=(2731130161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-201184353/1250000000 : ℝ)|^4695 ≤ (1933856467943/20000000000000 : ℝ)^3671
        have hw : |(-201184353/1250000000 : ℝ)|=(201184353/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_s5_7 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4226112467/10000000000 : ℝ)*x 0 + (4574973577/10000000000 : ℝ)*x 1 + (974736257/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4226112467/10000000000 : ℝ)^4695 ≤ (8308830671807/25000000000000 : ℝ)^3671 := by
    have hnat : (4226112467 : ℕ)^4695*25000000000000^3671 ≤ 8308830671807^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4226112467 10000000000 8308830671807 25000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4574973577/10000000000 : ℝ)^4695 ≤ (36783778754933/100000000000000 : ℝ)^3671 := by
    have hnat : (4574973577 : ℕ)^4695*100000000000000^3671 ≤ 36783778754933^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4574973577 10000000000 36783778754933 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (974736257/2500000000 : ℝ)^4695 ≤ (29980898545581/100000000000000 : ℝ)^3671 := by
    have hnat : (974736257 : ℕ)^4695*100000000000000^3671 ≤ 29980898545581^3671*2500000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      974736257 2500000000 29980898545581 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4226112467/10000000000 : ℝ), (4574973577/10000000000 : ℝ), (974736257/2500000000 : ℝ)] ![(8308830671807/25000000000000 : ℝ), (36783778754933/100000000000000 : ℝ), (29980898545581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4226112467/10000000000 : ℝ)|^4695 ≤ (8308830671807/25000000000000 : ℝ)^3671
        have hw : |(4226112467/10000000000 : ℝ)|=(4226112467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4574973577/10000000000 : ℝ)|^4695 ≤ (36783778754933/100000000000000 : ℝ)^3671
        have hw : |(4574973577/10000000000 : ℝ)|=(4574973577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(974736257/2500000000 : ℝ)|^4695 ≤ (29980898545581/100000000000000 : ℝ)^3671
        have hw : |(974736257/2500000000 : ℝ)|=(974736257/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1594_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85141271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16369/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2581/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (413/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16367/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16369/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2581/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16369/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2581/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16369/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2581/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16369/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2581/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16369/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2581/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16369/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2581/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2581/25000 : ℝ) ^ (4691/1024 : ℝ) ≤ (607314617851087/20000000000000000000 : ℝ) := by
    have hpowers : (2581/25000 : ℝ)^4691 ≤ (607314617851087/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2581 : ℕ)^4691*20000000000000000000^1024 ≤ 607314617851087^1024*25000^4691 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2581 25000 607314617851087 20000000000000000000 4691 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2581/25000 : ℝ)) (X := (607314617851087/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4691 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16369/100000 : ℝ) ^ (4691/1024 : ℝ) ≤ (25083750944484121/100000000000000000000 : ℝ) := by
    have hpowers : (16369/100000 : ℝ)^4691 ≤ (25083750944484121/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16369 : ℕ)^4691*100000000000000000000^1024 ≤ 25083750944484121^1024*100000^4691 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16369 100000 25083750944484121 100000000000000000000 4691 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16369/100000 : ℝ)) (X := (25083750944484121/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4691 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000607314617851087/10000000000000000000 : ℝ) ≤ (10000132567769621/10000000000000000 : ℝ) ^ (4691/1024 : ℝ) := by
    have hpowers : (10000607314617851087/10000000000000000000 : ℝ)^1024 ≤ (10000132567769621/10000000000000000 : ℝ)^4691 := by
      have hnat : (10000607314617851087 : ℕ)^1024*10000000000000000^4691 ≤ 10000132567769621^4691*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000607314617851087 10000000000000000000 10000132567769621 10000000000000000 1024 4691 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000132567769621/10000000000000000 : ℝ)) (X := (10000607314617851087/10000000000000000000 : ℝ)) (by norm_num) 4691 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25007030081008434889/25000000000000000000 : ℝ) ≤ (5000306886031417/5000000000000000 : ℝ) ^ (4691/1024 : ℝ) := by
    have hpowers : (25007030081008434889/25000000000000000000 : ℝ)^1024 ≤ (5000306886031417/5000000000000000 : ℝ)^4691 := by
      have hnat : (25007030081008434889 : ℕ)^1024*5000000000000000^4691 ≤ 5000306886031417^4691*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007030081008434889 25000000000000000000 5000306886031417 5000000000000000 1024 4691 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000306886031417/5000000000000000 : ℝ)) (X := (25007030081008434889/25000000000000000000 : ℝ)) (by norm_num) 4691 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50025083750944484121/50000000000000000000 : ℝ) ≤ (10001094976356047/10000000000000000 : ℝ) ^ (4691/1024 : ℝ) := by
    have hpowers : (50025083750944484121/50000000000000000000 : ℝ)^1024 ≤ (10001094976356047/10000000000000000 : ℝ)^4691 := by
      have hnat : (50025083750944484121 : ℕ)^1024*10000000000000000^4691 ≤ 10001094976356047^4691*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025083750944484121 50000000000000000000 10001094976356047 10000000000000000 1024 4691 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001094976356047/10000000000000000 : ℝ)) (X := (50025083750944484121/50000000000000000000 : ℝ)) (by norm_num) 4691 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(607314617851087/20000000000000000000 : ℝ) ≤ ((20146955155307032307/20150000000000000000 : ℝ)+2*(160401431071/201500000000000 : ℝ)*(2581/25000 : ℝ))^(4691/1024 : ℝ) := by
    rw [show (20146955155307032307/20150000000000000000 : ℝ)+2*(160401431071/201500000000000 : ℝ)*(2581/25000 : ℝ)=(10000132567769621/10000000000000000 : ℝ) by norm_num, show 1+2*(607314617851087/20000000000000000000 : ℝ)=(10000607314617851087/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(25083750944484121/100000000000000000000 : ℝ)+(607314617851087/20000000000000000000 : ℝ) ≤ ((20146955155307032307/20150000000000000000 : ℝ)+(160401431071/201500000000000 : ℝ)*((16369/100000 : ℝ)+(2581/25000 : ℝ)))^(4691/1024 : ℝ) := by
    rw [show (20146955155307032307/20150000000000000000 : ℝ)+(160401431071/201500000000000 : ℝ)*((16369/100000 : ℝ)+(2581/25000 : ℝ))=(5000306886031417/5000000000000000 : ℝ) by norm_num, show 1+(25083750944484121/100000000000000000000 : ℝ)+(607314617851087/20000000000000000000 : ℝ)=(25007030081008434889/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(25083750944484121/100000000000000000000 : ℝ) ≤ ((20146955155307032307/20150000000000000000 : ℝ)+2*(160401431071/201500000000000 : ℝ)*(16369/100000 : ℝ))^(4691/1024 : ℝ) := by
    rw [show (20146955155307032307/20150000000000000000 : ℝ)+2*(160401431071/201500000000000 : ℝ)*(16369/100000 : ℝ)=(10001094976356047/10000000000000000 : ℝ) by norm_num, show 1+2*(25083750944484121/100000000000000000000 : ℝ)=(50025083750944484121/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (20146955155307032307/20150000000000000000 : ℝ)*(X 1 0+X 2 0)+(160401431071/201500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4691/1024 : ℝ)) (lo := (2581/25000 : ℝ)) (hi := (16369/100000 : ℝ)) (c := (20146955155307032307/20150000000000000000 : ℝ)) (alpha := (160401431071/201500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (20146955155307032307/20150000000000000000 : ℝ)*(X 0 1+X 2 1)+(160401431071/201500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4691/1024 : ℝ)) (lo := (2581/25000 : ℝ)) (hi := (16369/100000 : ℝ)) (c := (20146955155307032307/20150000000000000000 : ℝ)) (alpha := (160401431071/201500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (20146955155307032307/20150000000000000000 : ℝ)*(X 0 2+X 1 2)+(160401431071/201500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4691/1024 : ℝ)) (lo := (2581/25000 : ℝ)) (hi := (16369/100000 : ℝ)) (c := (20146955155307032307/20150000000000000000 : ℝ)) (alpha := (160401431071/201500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-87270079/500000000 : ℝ)*X 0 0+(2732193639/5000000000 : ℝ)*X 0 1+(2589569307/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338946917/2500000000 : ℝ)*X 1 0+(-14785911/78125000 : ℝ)*X 1 1+(5179138939/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5355787809/10000000000 : ℝ)*X 2 0+(517913871/1000000000 : ℝ)*X 2 1+(-946298361/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4225936927/10000000000 : ℝ)*X 0 0+(1946914399/5000000000 : ℝ)*X 0 1+(91600733/200000000 : ℝ)*X 0 2+(4225936927/10000000000 : ℝ)*X 1 0+(1946914399/5000000000 : ℝ)*X 1 1+(91600733/200000000 : ℝ)*X 1 2+(4225936927/10000000000 : ℝ)*X 2 0+(1946914399/5000000000 : ℝ)*X 2 1+(91600733/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1745474553/10000000000 : ℝ)*X 0 0+(1295310873/2500000000 : ℝ)*X 0 1+(2731130167/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5280268137/10000000000 : ℝ)*X 1 0+(-321894949/2000000000 : ℝ)*X 1 1+(273113017/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5280268099/10000000000 : ℝ)*X 2 0+(2731130161/5000000000 : ℝ)*X 2 1+(-201184353/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4226112467/10000000000 : ℝ)*X 0 0+(4574973577/10000000000 : ℝ)*X 0 1+(974736257/2500000000 : ℝ)*X 0 2+(4226112467/10000000000 : ℝ)*X 1 0+(4574973577/10000000000 : ℝ)*X 1 1+(974736257/2500000000 : ℝ)*X 1 2+(4226112467/10000000000 : ℝ)*X 2 0+(4574973577/10000000000 : ℝ)*X 2 1+(974736257/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8949038479926327422726671089/1007500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (59463109/5000000000000 : ℝ)*(base19) + (1208654801/100000000000000 : ℝ)*(base23) + (4880591/12500000000000 : ℝ)*(lower2) + (242804257/100000000000000 : ℝ)*(upper3) + (119408721/100000000000000 : ℝ)*(upper5) + (2481521472792397/100000000000000 : ℝ)*(major0) + (2481521472792397/100000000000000 : ℝ)*(major1) + (2481521472792397/100000000000000 : ℝ)*(major2) + (219108155090713/6250000000000 : ℝ)*(sp0) + (175287249535583/5000000000000 : ℝ)*(sp1) + (1752872485659519/50000000000000 : ℝ)*(sp2) + (145728975183693/10000000000000 : ℝ)*(sp3) + (245289413/1562500000000 : ℝ)*(sp4) + (3358846669/50000000000000 : ℝ)*(sp7) + (1457296469530269/100000000000000 : ℝ)*(f.failure) + (43821827249673/1250000000000 : ℝ)*(f.sum) + (25990534560687/10075000000000000000000000000 : ℝ)*base65 + (254701499160897683/155000000000000000000000000000000 : ℝ)*base67 + (942971461510897683/155000000000000000000000000000000 : ℝ)*base69 + (1308294205350897683/155000000000000000000000000000000 : ℝ)*base71 + (14415070190737/10075000000000000000000000000 : ℝ)*base73 + (793079030810897683/155000000000000000000000000000000 : ℝ)*base75 + (2052573381740897683/155000000000000000000000000000000 : ℝ)*base77 + (905800542300897683/155000000000000000000000000000000 : ℝ)*base79 + (47042719497587/10075000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (25631899/5000000000000000000000 : ℝ)*base89 + (25631899/5000000000000000000000 : ℝ)*base91 + (25631899/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1146280895524579471501039431/251875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (184986877/20000000000000 : ℝ)*(base19) + (917321067/100000000000000 : ℝ)*(base23) + (15780213/5000000000000 : ℝ)*(lower1) + (47438061/50000000000000 : ℝ)*(upper3) + (2506791/20000000000000 : ℝ)*(lower4) + (18410079/25000000000000 : ℝ)*(upper5) + (1259429134992689/50000000000000 : ℝ)*(major0) + (1259429134992689/50000000000000 : ℝ)*(major1) + (1259429134992689/50000000000000 : ℝ)*(major2) + (5018103/1250000000000 : ℝ)*(sp1) + (355849353876403/10000000000000 : ℝ)*(sp4) + (889623053095351/25000000000000 : ℝ)*(sp5) + (1779246310721481/50000000000000 : ℝ)*(sp6) + (739611424753507/50000000000000 : ℝ)*(sp7) + (739611424753507/50000000000000 : ℝ)*(f.failure) + (355849353876403/10000000000000 : ℝ)*(f.sum) + (6299424639369/5037500000000000000000000000 : ℝ)*base65 + (144969254379900271/77500000000000000000000000000000 : ℝ)*base67 + (338433165105099729/77500000000000000000000000000000 : ℝ)*base70 + (945341950859900271/77500000000000000000000000000000 : ℝ)*base71 + (51719536373/39355468750000000000000000 : ℝ)*base73 + (487348810644900271/77500000000000000000000000000000 : ℝ)*base75 + (322874306684900271/77500000000000000000000000000000 : ℝ)*base77 + (1109258276569900271/77500000000000000000000000000000 : ℝ)*base79 + (565794993981/5037500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2312603/2500000000000000000000 : ℝ)*base90 + (2312603/2500000000000000000000 : ℝ)*base92 + (2312603/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1594_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85141271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16369/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2581/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (413/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16367/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1594_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1594_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85141271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16567/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5073/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (413/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16367/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1594_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1594_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1594_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85141271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16567/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5073/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (413/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16367/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1594_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
