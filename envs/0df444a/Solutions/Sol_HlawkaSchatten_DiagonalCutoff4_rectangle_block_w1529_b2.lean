-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1529_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:04:51.201351+00:00
-- url     : https://prove2.me/submissions/d898cac1-ca51-4ad6-8a5a-9ed2810e294f

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
theorem support_rectangle_w1529_s6_0 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-184319409/1000000000 : ℝ)*x 0 + (5431028787/10000000000 : ℝ)*x 1 + (5218450433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (184319409/1000000000 : ℝ)^4555 ≤ (5643578934057/50000000000000 : ℝ)^3531 := by
    have hnat : (184319409 : ℕ)^4555*50000000000000^3531 ≤ 5643578934057^3531*1000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      184319409 1000000000 5643578934057 50000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5431028787/10000000000 : ℝ)^4555 ≤ (227492544679/500000000000 : ℝ)^3531 := by
    have hnat : (5431028787 : ℕ)^4555*500000000000^3531 ≤ 227492544679^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431028787 10000000000 227492544679 500000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218450433/10000000000 : ℝ)^4555 ≤ (21607166588413/50000000000000 : ℝ)^3531 := by
    have hnat : (5218450433 : ℕ)^4555*50000000000000^3531 ≤ 21607166588413^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218450433 10000000000 21607166588413 50000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-184319409/1000000000 : ℝ), (5431028787/10000000000 : ℝ), (5218450433/10000000000 : ℝ)] ![(5643578934057/50000000000000 : ℝ), (227492544679/500000000000 : ℝ), (21607166588413/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-184319409/1000000000 : ℝ)|^4555 ≤ (5643578934057/50000000000000 : ℝ)^3531
        have hw : |(-184319409/1000000000 : ℝ)|=(184319409/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5431028787/10000000000 : ℝ)|^4555 ≤ (227492544679/500000000000 : ℝ)^3531
        have hw : |(5431028787/10000000000 : ℝ)|=(5431028787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218450433/10000000000 : ℝ)|^4555 ≤ (21607166588413/50000000000000 : ℝ)^3531
        have hw : |(5218450433/10000000000 : ℝ)|=(5218450433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_s6_1 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (214025139/400000000 : ℝ)*x 0 + (-1952029497/10000000000 : ℝ)*x 1 + (5218450473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214025139/400000000 : ℝ)^4555 ≤ (44631493335849/100000000000000 : ℝ)^3531 := by
    have hnat : (214025139 : ℕ)^4555*100000000000000^3531 ≤ 44631493335849^3531*400000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214025139 400000000 44631493335849 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1952029497/10000000000 : ℝ)^4555 ≤ (12154173053553/100000000000000 : ℝ)^3531 := by
    have hnat : (1952029497 : ℕ)^4555*100000000000000^3531 ≤ 12154173053553^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1952029497 10000000000 12154173053553 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218450473/10000000000 : ℝ)^4555 ≤ (4321433360413/10000000000000 : ℝ)^3531 := by
    have hnat : (5218450473 : ℕ)^4555*10000000000000^3531 ≤ 4321433360413^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218450473 10000000000 4321433360413 10000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214025139/400000000 : ℝ), (-1952029497/10000000000 : ℝ), (5218450473/10000000000 : ℝ)] ![(44631493335849/100000000000000 : ℝ), (12154173053553/100000000000000 : ℝ), (4321433360413/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214025139/400000000 : ℝ)|^4555 ≤ (44631493335849/100000000000000 : ℝ)^3531
        have hw : |(214025139/400000000 : ℝ)|=(214025139/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1952029497/10000000000 : ℝ)|^4555 ≤ (12154173053553/100000000000000 : ℝ)^3531
        have hw : |(-1952029497/10000000000 : ℝ)|=(1952029497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218450473/10000000000 : ℝ)|^4555 ≤ (4321433360413/10000000000000 : ℝ)^3531
        have hw : |(5218450473/10000000000 : ℝ)|=(5218450473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_s6_2 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070125681/2000000000 : ℝ)*x 0 + (163076579/312500000 : ℝ)*x 1 + (-1952029517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070125681/2000000000 : ℝ)^4555 ≤ (44631492582623/100000000000000 : ℝ)^3531 := by
    have hnat : (1070125681 : ℕ)^4555*100000000000000^3531 ≤ 44631492582623^3531*2000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070125681 2000000000 44631492582623 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163076579/312500000 : ℝ)^4555 ≤ (43214334191673/100000000000000 : ℝ)^3531 := by
    have hnat : (163076579 : ℕ)^4555*100000000000000^3531 ≤ 43214334191673^3531*312500000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163076579 312500000 43214334191673 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1952029517/10000000000 : ℝ)^4555 ≤ (2430834642839/20000000000000 : ℝ)^3531 := by
    have hnat : (1952029517 : ℕ)^4555*20000000000000^3531 ≤ 2430834642839^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1952029517 10000000000 2430834642839 20000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070125681/2000000000 : ℝ), (163076579/312500000 : ℝ), (-1952029517/10000000000 : ℝ)] ![(44631492582623/100000000000000 : ℝ), (43214334191673/100000000000000 : ℝ), (2430834642839/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070125681/2000000000 : ℝ)|^4555 ≤ (44631492582623/100000000000000 : ℝ)^3531
        have hw : |(1070125681/2000000000 : ℝ)|=(1070125681/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163076579/312500000 : ℝ)|^4555 ≤ (43214334191673/100000000000000 : ℝ)^3531
        have hw : |(163076579/312500000 : ℝ)|=(163076579/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1952029517/10000000000 : ℝ)|^4555 ≤ (2430834642839/20000000000000 : ℝ)^3531
        have hw : |(-1952029517/10000000000 : ℝ)|=(1952029517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_s6_3 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4261920617/10000000000 : ℝ)*x 0 + (4023854029/10000000000 : ℝ)*x 1 + (4511673471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4261920617/10000000000 : ℝ)^4555 ≤ (6656100278011/20000000000000 : ℝ)^3531 := by
    have hnat : (4261920617 : ℕ)^4555*20000000000000^3531 ≤ 6656100278011^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4261920617 10000000000 6656100278011 20000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4023854029/10000000000 : ℝ)^4555 ≤ (30902053575733/100000000000000 : ℝ)^3531 := by
    have hnat : (4023854029 : ℕ)^4555*100000000000000^3531 ≤ 30902053575733^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4023854029 10000000000 30902053575733 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4511673471/10000000000 : ℝ)^4555 ≤ (7163489004469/20000000000000 : ℝ)^3531 := by
    have hnat : (4511673471 : ℕ)^4555*20000000000000^3531 ≤ 7163489004469^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4511673471 10000000000 7163489004469 20000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4261920617/10000000000 : ℝ), (4023854029/10000000000 : ℝ), (4511673471/10000000000 : ℝ)] ![(6656100278011/20000000000000 : ℝ), (30902053575733/100000000000000 : ℝ), (7163489004469/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4261920617/10000000000 : ℝ)|^4555 ≤ (6656100278011/20000000000000 : ℝ)^3531
        have hw : |(4261920617/10000000000 : ℝ)|=(4261920617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4023854029/10000000000 : ℝ)|^4555 ≤ (30902053575733/100000000000000 : ℝ)^3531
        have hw : |(4023854029/10000000000 : ℝ)|=(4023854029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4511673471/10000000000 : ℝ)|^4555 ≤ (7163489004469/20000000000000 : ℝ)^3531
        have hw : |(4511673471/10000000000 : ℝ)|=(4511673471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_s6_4 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-921611179/5000000000 : ℝ)*x 0 + (2609774197/5000000000 : ℝ)*x 1 + (2714961369/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (921611179/5000000000 : ℝ)^4555 ≤ (11287381174037/100000000000000 : ℝ)^3531 := by
    have hnat : (921611179 : ℕ)^4555*100000000000000^3531 ≤ 11287381174037^3531*5000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      921611179 5000000000 11287381174037 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609774197/5000000000 : ℝ)^4555 ≤ (43226062611471/100000000000000 : ℝ)^3531 := by
    have hnat : (2609774197 : ℕ)^4555*100000000000000^3531 ≤ 43226062611471^3531*5000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609774197 5000000000 43226062611471 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2714961369/5000000000 : ℝ)^4555 ≤ (45486556201511/100000000000000 : ℝ)^3531 := by
    have hnat : (2714961369 : ℕ)^4555*100000000000000^3531 ≤ 45486556201511^3531*5000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714961369 5000000000 45486556201511 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-921611179/5000000000 : ℝ), (2609774197/5000000000 : ℝ), (2714961369/5000000000 : ℝ)] ![(11287381174037/100000000000000 : ℝ), (43226062611471/100000000000000 : ℝ), (45486556201511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-921611179/5000000000 : ℝ)|^4555 ≤ (11287381174037/100000000000000 : ℝ)^3531
        have hw : |(-921611179/5000000000 : ℝ)|=(921611179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609774197/5000000000 : ℝ)|^4555 ≤ (43226062611471/100000000000000 : ℝ)^3531
        have hw : |(2609774197/5000000000 : ℝ)|=(2609774197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2714961369/5000000000 : ℝ)|^4555 ≤ (45486556201511/100000000000000 : ℝ)^3531
        have hw : |(2714961369/5000000000 : ℝ)|=(2714961369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_s6_5 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (532748179/1250000000 : ℝ)*x 0 + (1127288499/2500000000 : ℝ)*x 1 + (2013196083/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (532748179/1250000000 : ℝ)^4555 ≤ (16640577148773/50000000000000 : ℝ)^3531 := by
    have hnat : (532748179 : ℕ)^4555*50000000000000^3531 ≤ 16640577148773^3531*1250000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532748179 1250000000 16640577148773 50000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1127288499/2500000000 : ℝ)^4555 ≤ (17895822428563/50000000000000 : ℝ)^3531 := by
    have hnat : (1127288499 : ℕ)^4555*50000000000000^3531 ≤ 17895822428563^3531*2500000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127288499 2500000000 17895822428563 50000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2013196083/5000000000 : ℝ)^4555 ≤ (30927200829329/100000000000000 : ℝ)^3531 := by
    have hnat : (2013196083 : ℕ)^4555*100000000000000^3531 ≤ 30927200829329^3531*5000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2013196083 5000000000 30927200829329 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(532748179/1250000000 : ℝ), (1127288499/2500000000 : ℝ), (2013196083/5000000000 : ℝ)] ![(16640577148773/50000000000000 : ℝ), (17895822428563/50000000000000 : ℝ), (30927200829329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(532748179/1250000000 : ℝ)|^4555 ≤ (16640577148773/50000000000000 : ℝ)^3531
        have hw : |(532748179/1250000000 : ℝ)|=(532748179/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1127288499/2500000000 : ℝ)|^4555 ≤ (17895822428563/50000000000000 : ℝ)^3531
        have hw : |(1127288499/2500000000 : ℝ)|=(1127288499/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2013196083/5000000000 : ℝ)|^4555 ≤ (30927200829329/100000000000000 : ℝ)^3531
        have hw : |(2013196083/5000000000 : ℝ)|=(2013196083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1529_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164738759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10979/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (549/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3871/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10979/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10979/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10979/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10979/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10979/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10979/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10979/100000 : ℝ) ^ (4553/1024 : ℝ) ≤ (1355204433676931/25000000000000000000 : ℝ) := by
    have hpowers : (10979/100000 : ℝ)^4553 ≤ (1355204433676931/25000000000000000000 : ℝ)^1024 := by
      have hnat : (10979 : ℕ)^4553*25000000000000000000^1024 ≤ 1355204433676931^1024*100000^4553 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10979 100000 1355204433676931 25000000000000000000 4553 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10979/100000 : ℝ)) (X := (1355204433676931/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4553 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3871/25000 : ℝ) ^ (4553/1024 : ℝ) ≤ (25002668726756137/100000000000000000000 : ℝ) := by
    have hpowers : (3871/25000 : ℝ)^4553 ≤ (25002668726756137/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3871 : ℕ)^4553*100000000000000000000^1024 ≤ 25002668726756137^1024*25000^4553 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3871 25000 25002668726756137 100000000000000000000 4553 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3871/25000 : ℝ)) (X := (25002668726756137/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4553 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501355204433676931/12500000000000000000 : ℝ) ≤ (10000243825352329/10000000000000000 : ℝ) ^ (4553/1024 : ℝ) := by
    have hpowers : (12501355204433676931/12500000000000000000 : ℝ)^1024 ≤ (10000243825352329/10000000000000000 : ℝ)^4553 := by
      have hnat : (12501355204433676931 : ℕ)^1024*10000000000000000^4553 ≤ 10000243825352329^4553*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501355204433676931 12500000000000000000 10000243825352329 10000000000000000 1024 4553 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000243825352329/10000000000000000 : ℝ)) (X := (12501355204433676931/12500000000000000000 : ℝ)) (by norm_num) 4553 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100030423486461463861/100000000000000000000 : ℝ) ≤ (10000684163795739/10000000000000000 : ℝ) ^ (4553/1024 : ℝ) := by
    have hpowers : (100030423486461463861/100000000000000000000 : ℝ)^1024 ≤ (10000684163795739/10000000000000000 : ℝ)^4553 := by
      have hnat : (100030423486461463861 : ℕ)^1024*10000000000000000^4553 ≤ 10000684163795739^4553*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100030423486461463861 100000000000000000000 10000684163795739 10000000000000000 1024 4553 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000684163795739/10000000000000000 : ℝ)) (X := (100030423486461463861/100000000000000000000 : ℝ)) (by norm_num) 4553 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50025002668726756137/50000000000000000000 : ℝ) ≤ (10001124502239149/10000000000000000 : ℝ) ^ (4553/1024 : ℝ) := by
    have hpowers : (50025002668726756137/50000000000000000000 : ℝ)^1024 ≤ (10001124502239149/10000000000000000 : ℝ)^4553 := by
      have hnat : (50025002668726756137 : ℕ)^1024*10000000000000000^4553 ≤ 10001124502239149^4553*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025002668726756137 50000000000000000000 10001124502239149 10000000000000000 1024 4553 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001124502239149/10000000000000000 : ℝ)) (X := (50025002668726756137/50000000000000000000 : ℝ)) (by norm_num) 4553 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1355204433676931/25000000000000000000 : ℝ) ≤ ((9008285896334369073/9010000000000000000 : ℝ)+2*(44033844341/45050000000000 : ℝ)*(10979/100000 : ℝ))^(4553/1024 : ℝ) := by
    rw [show (9008285896334369073/9010000000000000000 : ℝ)+2*(44033844341/45050000000000 : ℝ)*(10979/100000 : ℝ)=(10000243825352329/10000000000000000 : ℝ) by norm_num, show 1+2*(1355204433676931/25000000000000000000 : ℝ)=(12501355204433676931/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(25002668726756137/100000000000000000000 : ℝ)+(1355204433676931/25000000000000000000 : ℝ) ≤ ((9008285896334369073/9010000000000000000 : ℝ)+(44033844341/45050000000000 : ℝ)*((3871/25000 : ℝ)+(10979/100000 : ℝ)))^(4553/1024 : ℝ) := by
    rw [show (9008285896334369073/9010000000000000000 : ℝ)+(44033844341/45050000000000 : ℝ)*((3871/25000 : ℝ)+(10979/100000 : ℝ))=(10000684163795739/10000000000000000 : ℝ) by norm_num, show 1+(25002668726756137/100000000000000000000 : ℝ)+(1355204433676931/25000000000000000000 : ℝ)=(100030423486461463861/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(25002668726756137/100000000000000000000 : ℝ) ≤ ((9008285896334369073/9010000000000000000 : ℝ)+2*(44033844341/45050000000000 : ℝ)*(3871/25000 : ℝ))^(4553/1024 : ℝ) := by
    rw [show (9008285896334369073/9010000000000000000 : ℝ)+2*(44033844341/45050000000000 : ℝ)*(3871/25000 : ℝ)=(10001124502239149/10000000000000000 : ℝ) by norm_num, show 1+2*(25002668726756137/100000000000000000000 : ℝ)=(50025002668726756137/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9008285896334369073/9010000000000000000 : ℝ)*(X 1 0+X 2 0)+(44033844341/45050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4553/1024 : ℝ)) (lo := (10979/100000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (9008285896334369073/9010000000000000000 : ℝ)) (alpha := (44033844341/45050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9008285896334369073/9010000000000000000 : ℝ)*(X 0 1+X 2 1)+(44033844341/45050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4553/1024 : ℝ)) (lo := (10979/100000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (9008285896334369073/9010000000000000000 : ℝ)) (alpha := (44033844341/45050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9008285896334369073/9010000000000000000 : ℝ)*(X 0 2+X 1 2)+(44033844341/45050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4553/1024 : ℝ)) (lo := (10979/100000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (9008285896334369073/9010000000000000000 : ℝ)) (alpha := (44033844341/45050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-184319409/1000000000 : ℝ)*X 0 0+(5431028787/10000000000 : ℝ)*X 0 1+(5218450433/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((214025139/400000000 : ℝ)*X 1 0+(-1952029497/10000000000 : ℝ)*X 1 1+(5218450473/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070125681/2000000000 : ℝ)*X 2 0+(163076579/312500000 : ℝ)*X 2 1+(-1952029517/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4261920617/10000000000 : ℝ)*X 0 0+(4023854029/10000000000 : ℝ)*X 0 1+(4511673471/10000000000 : ℝ)*X 0 2+(4261920617/10000000000 : ℝ)*X 1 0+(4023854029/10000000000 : ℝ)*X 1 1+(4511673471/10000000000 : ℝ)*X 1 2+(4261920617/10000000000 : ℝ)*X 2 0+(4023854029/10000000000 : ℝ)*X 2 1+(4511673471/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-921611179/5000000000 : ℝ)*X 0 0+(2609774197/5000000000 : ℝ)*X 0 1+(2714961369/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((532748179/1250000000 : ℝ)*X 0 0+(1127288499/2500000000 : ℝ)*X 0 1+(2013196083/5000000000 : ℝ)*X 0 2+(532748179/1250000000 : ℝ)*X 1 0+(1127288499/2500000000 : ℝ)*X 1 1+(2013196083/5000000000 : ℝ)*X 1 2+(532748179/1250000000 : ℝ)*X 2 0+(1127288499/2500000000 : ℝ)*X 2 1+(2013196083/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s6_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (739435929389669372889523251/112625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (309646117/25000000000000 : ℝ)*(base19) + (552586989/50000000000000 : ℝ)*(base23) + (38453681/100000000000000 : ℝ)*(lower2) + (194648227/100000000000000 : ℝ)*(upper3) + (28208379/25000000000000 : ℝ)*(upper5) + (844268221343129/25000000000000 : ℝ)*(major0) + (844268221343129/25000000000000 : ℝ)*(major1) + (844268221343129/25000000000000 : ℝ)*(major2) + (2352084684471729/50000000000000 : ℝ)*(sp0) + (4704187821061633/100000000000000 : ℝ)*(sp1) + (4704187954472123/100000000000000 : ℝ)*(sp2) + (1024973560368077/50000000000000 : ℝ)*(sp3) + (19690702643/100000000000000 : ℝ)*(sp4) + (9371513807/100000000000000 : ℝ)*(sp5) + (2049956492249961/100000000000000 : ℝ)*(f.failure) + (2352094529823051/50000000000000 : ℝ)*(f.sum) + (6769102020443/1126250000000000000000000000 : ℝ)*base65 + (490102886099949417/225250000000000000000000000000000 : ℝ)*base67 + (969044611029550583/225250000000000000000000000000000 : ℝ)*base70 + (737470936447800583/225250000000000000000000000000000 : ℝ)*base72 + (17537487704227/4505000000000000000000000000 : ℝ)*base73 + (266228965605199417/225250000000000000000000000000000 : ℝ)*base75 + (702479281482800583/225250000000000000000000000000000 : ℝ)*base78 + (1549558424039050583/225250000000000000000000000000000 : ℝ)*base80 + (12324061731887/4505000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (92938399/10000000000000000000000 : ℝ)*base89 + (92938399/10000000000000000000000 : ℝ)*base91 + (92938399/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1529_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164738759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10979/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (549/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1529_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1529_box_0 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1632554371/10000000000 : ℝ)*x 0 + (5400998089/10000000000 : ℝ)*x 1 + (2700498851/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1632554371/10000000000 : ℝ)^4555 ≤ (4825774773541/50000000000000 : ℝ)^3531 := by
    have hnat : (1632554371 : ℕ)^4555*50000000000000^3531 ≤ 4825774773541^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1632554371 10000000000 4825774773541 50000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5400998089/10000000000 : ℝ)^4555 ≤ (70584730169/156250000000 : ℝ)^3531 := by
    have hnat : (5400998089 : ℕ)^4555*156250000000^3531 ≤ 70584730169^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400998089 10000000000 70584730169 156250000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2700498851/5000000000 : ℝ)^4555 ≤ (9034844626513/20000000000000 : ℝ)^3531 := by
    have hnat : (2700498851 : ℕ)^4555*20000000000000^3531 ≤ 9034844626513^3531*5000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700498851 5000000000 9034844626513 20000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1632554371/10000000000 : ℝ), (5400998089/10000000000 : ℝ), (2700498851/5000000000 : ℝ)] ![(4825774773541/50000000000000 : ℝ), (70584730169/156250000000 : ℝ), (9034844626513/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1632554371/10000000000 : ℝ)|^4555 ≤ (4825774773541/50000000000000 : ℝ)^3531
        have hw : |(-1632554371/10000000000 : ℝ)|=(1632554371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5400998089/10000000000 : ℝ)|^4555 ≤ (70584730169/156250000000 : ℝ)^3531
        have hw : |(5400998089/10000000000 : ℝ)|=(5400998089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2700498851/5000000000 : ℝ)|^4555 ≤ (9034844626513/20000000000000 : ℝ)^3531
        have hw : |(2700498851/5000000000 : ℝ)|=(2700498851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_box_1 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5270961649/10000000000 : ℝ)*x 0 + (-226632279/1250000000 : ℝ)*x 1 + (2700499183/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5270961649/10000000000 : ℝ)^4555 ≤ (4377610597441/10000000000000 : ℝ)^3531 := by
    have hnat : (5270961649 : ℕ)^4555*10000000000000^3531 ≤ 4377610597441^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5270961649 10000000000 4377610597441 10000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (226632279/1250000000 : ℝ)^4555 ≤ (5524831860977/50000000000000 : ℝ)^3531 := by
    have hnat : (226632279 : ℕ)^4555*50000000000000^3531 ≤ 5524831860977^3531*1250000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226632279 1250000000 5524831860977 50000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2700499183/5000000000 : ℝ)^4555 ≤ (45174230296893/100000000000000 : ℝ)^3531 := by
    have hnat : (2700499183 : ℕ)^4555*100000000000000^3531 ≤ 45174230296893^3531*5000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700499183 5000000000 45174230296893 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5270961649/10000000000 : ℝ), (-226632279/1250000000 : ℝ), (2700499183/5000000000 : ℝ)] ![(4377610597441/10000000000000 : ℝ), (5524831860977/50000000000000 : ℝ), (45174230296893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5270961649/10000000000 : ℝ)|^4555 ≤ (4377610597441/10000000000000 : ℝ)^3531
        have hw : |(5270961649/10000000000 : ℝ)|=(5270961649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-226632279/1250000000 : ℝ)|^4555 ≤ (5524831860977/50000000000000 : ℝ)^3531
        have hw : |(-226632279/1250000000 : ℝ)|=(226632279/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2700499183/5000000000 : ℝ)|^4555 ≤ (45174230296893/100000000000000 : ℝ)^3531
        have hw : |(2700499183/5000000000 : ℝ)|=(2700499183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_box_2 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2635480769/5000000000 : ℝ)*x 0 + (1350249619/2500000000 : ℝ)*x 1 + (-226632279/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2635480769/5000000000 : ℝ)^4555 ≤ (43776104785193/100000000000000 : ℝ)^3531 := by
    have hnat : (2635480769 : ℕ)^4555*100000000000000^3531 ≤ 43776104785193^3531*5000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635480769 5000000000 43776104785193 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1350249619/2500000000 : ℝ)^4555 ≤ (9034846296751/20000000000000 : ℝ)^3531 := by
    have hnat : (1350249619 : ℕ)^4555*20000000000000^3531 ≤ 9034846296751^3531*2500000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350249619 2500000000 9034846296751 20000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (226632279/1250000000 : ℝ)^4555 ≤ (5524831860977/50000000000000 : ℝ)^3531 := by
    have hnat : (226632279 : ℕ)^4555*50000000000000^3531 ≤ 5524831860977^3531*1250000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226632279 1250000000 5524831860977 50000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2635480769/5000000000 : ℝ), (1350249619/2500000000 : ℝ), (-226632279/1250000000 : ℝ)] ![(43776104785193/100000000000000 : ℝ), (9034846296751/20000000000000 : ℝ), (5524831860977/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2635480769/5000000000 : ℝ)|^4555 ≤ (43776104785193/100000000000000 : ℝ)^3531
        have hw : |(2635480769/5000000000 : ℝ)|=(2635480769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1350249619/2500000000 : ℝ)|^4555 ≤ (9034846296751/20000000000000 : ℝ)^3531
        have hw : |(1350249619/2500000000 : ℝ)|=(1350249619/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-226632279/1250000000 : ℝ)|^4555 ≤ (5524831860977/50000000000000 : ℝ)^3531
        have hw : |(-226632279/1250000000 : ℝ)|=(226632279/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_box_3 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4464237159/10000000000 : ℝ)*x 0 + (520954609/1250000000 : ℝ)*x 1 + (4167636591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4464237159/10000000000 : ℝ)^4555 ≤ (17666193187727/50000000000000 : ℝ)^3531 := by
    have hnat : (4464237159 : ℕ)^4555*50000000000000^3531 ≤ 17666193187727^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4464237159 10000000000 17666193187727 50000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (520954609/1250000000 : ℝ)^4555 ≤ (32333808211707/100000000000000 : ℝ)^3531 := by
    have hnat : (520954609 : ℕ)^4555*100000000000000^3531 ≤ 32333808211707^3531*1250000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520954609 1250000000 32333808211707 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4167636591/10000000000 : ℝ)^4555 ≤ (1010431418731/3125000000000 : ℝ)^3531 := by
    have hnat : (4167636591 : ℕ)^4555*3125000000000^3531 ≤ 1010431418731^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4167636591 10000000000 1010431418731 3125000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4464237159/10000000000 : ℝ), (520954609/1250000000 : ℝ), (4167636591/10000000000 : ℝ)] ![(17666193187727/50000000000000 : ℝ), (32333808211707/100000000000000 : ℝ), (1010431418731/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4464237159/10000000000 : ℝ)|^4555 ≤ (17666193187727/50000000000000 : ℝ)^3531
        have hw : |(4464237159/10000000000 : ℝ)|=(4464237159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(520954609/1250000000 : ℝ)|^4555 ≤ (32333808211707/100000000000000 : ℝ)^3531
        have hw : |(520954609/1250000000 : ℝ)|=(520954609/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4167636591/10000000000 : ℝ)|^4555 ≤ (1010431418731/3125000000000 : ℝ)^3531
        have hw : |(4167636591/10000000000 : ℝ)|=(4167636591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_box_4 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-411851083/2000000000 : ℝ)*x 0 + (5244134457/10000000000 : ℝ)*x 1 + (5244134641/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (411851083/2000000000 : ℝ)^4555 ≤ (2604439249011/20000000000000 : ℝ)^3531 := by
    have hnat : (411851083 : ℕ)^4555*20000000000000^3531 ≤ 2604439249011^3531*2000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411851083 2000000000 2604439249011 20000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244134457/10000000000 : ℝ)^4555 ≤ (8697780176387/20000000000000 : ℝ)^3531 := by
    have hnat : (5244134457 : ℕ)^4555*20000000000000^3531 ≤ 8697780176387^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244134457 10000000000 8697780176387 20000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244134641/10000000000 : ℝ)^4555 ≤ (21744451425167/50000000000000 : ℝ)^3531 := by
    have hnat : (5244134641 : ℕ)^4555*50000000000000^3531 ≤ 21744451425167^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244134641 10000000000 21744451425167 50000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-411851083/2000000000 : ℝ), (5244134457/10000000000 : ℝ), (5244134641/10000000000 : ℝ)] ![(2604439249011/20000000000000 : ℝ), (8697780176387/20000000000000 : ℝ), (21744451425167/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-411851083/2000000000 : ℝ)|^4555 ≤ (2604439249011/20000000000000 : ℝ)^3531
        have hw : |(-411851083/2000000000 : ℝ)|=(411851083/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244134457/10000000000 : ℝ)|^4555 ≤ (8697780176387/20000000000000 : ℝ)^3531
        have hw : |(5244134457/10000000000 : ℝ)|=(5244134457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244134641/10000000000 : ℝ)|^4555 ≤ (21744451425167/50000000000000 : ℝ)^3531
        have hw : |(5244134641/10000000000 : ℝ)|=(5244134641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_box_5 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (8608051/16000000 : ℝ)*x 0 + (-1878013177/10000000000 : ℝ)*x 1 + (5244134291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8608051/16000000 : ℝ)^4555 ≤ (22474068320269/50000000000000 : ℝ)^3531 := by
    have hnat : (8608051 : ℕ)^4555*50000000000000^3531 ≤ 22474068320269^3531*16000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8608051 16000000 22474068320269 50000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1878013177/10000000000 : ℝ)^4555 ≤ (5781482118443/50000000000000 : ℝ)^3531 := by
    have hnat : (1878013177 : ℕ)^4555*50000000000000^3531 ≤ 5781482118443^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1878013177 10000000000 5781482118443 50000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244134291/10000000000 : ℝ)^4555 ≤ (43488899106097/100000000000000 : ℝ)^3531 := by
    have hnat : (5244134291 : ℕ)^4555*100000000000000^3531 ≤ 43488899106097^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244134291 10000000000 43488899106097 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8608051/16000000 : ℝ), (-1878013177/10000000000 : ℝ), (5244134291/10000000000 : ℝ)] ![(22474068320269/50000000000000 : ℝ), (5781482118443/50000000000000 : ℝ), (43488899106097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8608051/16000000 : ℝ)|^4555 ≤ (22474068320269/50000000000000 : ℝ)^3531
        have hw : |(8608051/16000000 : ℝ)|=(8608051/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1878013177/10000000000 : ℝ)|^4555 ≤ (5781482118443/50000000000000 : ℝ)^3531
        have hw : |(-1878013177/10000000000 : ℝ)|=(1878013177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244134291/10000000000 : ℝ)|^4555 ≤ (43488899106097/100000000000000 : ℝ)^3531
        have hw : |(5244134291/10000000000 : ℝ)|=(5244134291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_box_6 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2690015751/5000000000 : ℝ)*x 0 + (5244134501/10000000000 : ℝ)*x 1 + (-9390067/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2690015751/5000000000 : ℝ)^4555 ≤ (5618516577567/12500000000000 : ℝ)^3531 := by
    have hnat : (2690015751 : ℕ)^4555*12500000000000^3531 ≤ 5618516577567^3531*5000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2690015751 5000000000 5618516577567 12500000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244134501/10000000000 : ℝ)^4555 ≤ (43488901352639/100000000000000 : ℝ)^3531 := by
    have hnat : (5244134501 : ℕ)^4555*100000000000000^3531 ≤ 43488901352639^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244134501 10000000000 43488901352639 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9390067/50000000 : ℝ)^4555 ≤ (144537075101/1250000000000 : ℝ)^3531 := by
    have hnat : (9390067 : ℕ)^4555*1250000000000^3531 ≤ 144537075101^3531*50000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9390067 50000000 144537075101 1250000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2690015751/5000000000 : ℝ), (5244134501/10000000000 : ℝ), (-9390067/50000000 : ℝ)] ![(5618516577567/12500000000000 : ℝ), (43488901352639/100000000000000 : ℝ), (144537075101/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2690015751/5000000000 : ℝ)|^4555 ≤ (5618516577567/12500000000000 : ℝ)^3531
        have hw : |(2690015751/5000000000 : ℝ)|=(2690015751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244134501/10000000000 : ℝ)|^4555 ≤ (43488901352639/100000000000000 : ℝ)^3531
        have hw : |(5244134501/10000000000 : ℝ)|=(5244134501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-9390067/50000000 : ℝ)|^4555 ≤ (144537075101/1250000000000 : ℝ)^3531
        have hw : |(-9390067/50000000 : ℝ)|=(9390067/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_box_7 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4057102817/10000000000 : ℝ)*x 0 + (437107219/1000000000 : ℝ)*x 1 + (4371071311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4057102817/10000000000 : ℝ)^4555 ≤ (31231838368491/100000000000000 : ℝ)^3531 := by
    have hnat : (4057102817 : ℕ)^4555*100000000000000^3531 ≤ 31231838368491^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4057102817 10000000000 31231838368491 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (437107219/1000000000 : ℝ)^4555 ≤ (3438408526921/10000000000000 : ℝ)^3531 := by
    have hnat : (437107219 : ℕ)^4555*10000000000000^3531 ≤ 3438408526921^3531*1000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437107219 1000000000 3438408526921 10000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4371071311/10000000000 : ℝ)^4555 ≤ (6876815269907/20000000000000 : ℝ)^3531 := by
    have hnat : (4371071311 : ℕ)^4555*20000000000000^3531 ≤ 6876815269907^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4371071311 10000000000 6876815269907 20000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4057102817/10000000000 : ℝ), (437107219/1000000000 : ℝ), (4371071311/10000000000 : ℝ)] ![(31231838368491/100000000000000 : ℝ), (3438408526921/10000000000000 : ℝ), (6876815269907/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4057102817/10000000000 : ℝ)|^4555 ≤ (31231838368491/100000000000000 : ℝ)^3531
        have hw : |(4057102817/10000000000 : ℝ)|=(4057102817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(437107219/1000000000 : ℝ)|^4555 ≤ (3438408526921/10000000000000 : ℝ)^3531
        have hw : |(437107219/1000000000 : ℝ)|=(437107219/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4371071311/10000000000 : ℝ)|^4555 ≤ (6876815269907/20000000000000 : ℝ)^3531
        have hw : |(4371071311/10000000000 : ℝ)|=(4371071311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_box_8 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1968996723/10000000000 : ℝ)*x 0 + (2567027789/5000000000 : ℝ)*x 1 + (216855987/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1968996723/10000000000 : ℝ)^4555 ≤ (122906271107/1000000000000 : ℝ)^3531 := by
    have hnat : (1968996723 : ℕ)^4555*1000000000000^3531 ≤ 122906271107^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1968996723 10000000000 122906271107 1000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2567027789/5000000000 : ℝ)^4555 ≤ (42314899119037/100000000000000 : ℝ)^3531 := by
    have hnat : (2567027789 : ℕ)^4555*100000000000000^3531 ≤ 42314899119037^3531*5000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2567027789 5000000000 42314899119037 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216855987/400000000 : ℝ)^4555 ≤ (45394473749377/100000000000000 : ℝ)^3531 := by
    have hnat : (216855987 : ℕ)^4555*100000000000000^3531 ≤ 45394473749377^3531*400000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216855987 400000000 45394473749377 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1968996723/10000000000 : ℝ), (2567027789/5000000000 : ℝ), (216855987/400000000 : ℝ)] ![(122906271107/1000000000000 : ℝ), (42314899119037/100000000000000 : ℝ), (45394473749377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1968996723/10000000000 : ℝ)|^4555 ≤ (122906271107/1000000000000 : ℝ)^3531
        have hw : |(-1968996723/10000000000 : ℝ)|=(1968996723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2567027789/5000000000 : ℝ)|^4555 ≤ (42314899119037/100000000000000 : ℝ)^3531
        have hw : |(2567027789/5000000000 : ℝ)|=(2567027789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216855987/400000000 : ℝ)|^4555 ≤ (45394473749377/100000000000000 : ℝ)^3531
        have hw : |(216855987/400000000 : ℝ)|=(216855987/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_box_9 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628385651/5000000000 : ℝ)*x 0 + (-1804368189/10000000000 : ℝ)*x 1 + (5421399723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628385651/5000000000 : ℝ)^4555 ≤ (43624134781141/100000000000000 : ℝ)^3531 := by
    have hnat : (2628385651 : ℕ)^4555*100000000000000^3531 ≤ 43624134781141^3531*5000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628385651 5000000000 43624134781141 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1804368189/10000000000 : ℝ)^4555 ≤ (686336933589/6250000000000 : ℝ)^3531 := by
    have hnat : (1804368189 : ℕ)^4555*6250000000000^3531 ≤ 686336933589^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1804368189 10000000000 686336933589 6250000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5421399723/10000000000 : ℝ)^4555 ≤ (45394474267847/100000000000000 : ℝ)^3531 := by
    have hnat : (5421399723 : ℕ)^4555*100000000000000^3531 ≤ 45394474267847^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421399723 10000000000 45394474267847 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628385651/5000000000 : ℝ), (-1804368189/10000000000 : ℝ), (5421399723/10000000000 : ℝ)] ![(43624134781141/100000000000000 : ℝ), (686336933589/6250000000000 : ℝ), (45394474267847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628385651/5000000000 : ℝ)|^4555 ≤ (43624134781141/100000000000000 : ℝ)^3531
        have hw : |(2628385651/5000000000 : ℝ)|=(2628385651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1804368189/10000000000 : ℝ)|^4555 ≤ (686336933589/6250000000000 : ℝ)^3531
        have hw : |(-1804368189/10000000000 : ℝ)|=(1804368189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5421399723/10000000000 : ℝ)|^4555 ≤ (45394474267847/100000000000000 : ℝ)^3531
        have hw : |(5421399723/10000000000 : ℝ)|=(5421399723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_box_10 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1314192799/2500000000 : ℝ)*x 0 + (5421399709/10000000000 : ℝ)*x 1 + (-1804368351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314192799/2500000000 : ℝ)^4555 ≤ (2181206682319/5000000000000 : ℝ)^3531 := by
    have hnat : (1314192799 : ℕ)^4555*5000000000000^3531 ≤ 2181206682319^3531*2500000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314192799 2500000000 2181206682319 5000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5421399709/10000000000 : ℝ)^4555 ≤ (22697237058313/50000000000000 : ℝ)^3531 := by
    have hnat : (5421399709 : ℕ)^4555*50000000000000^3531 ≤ 22697237058313^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421399709 10000000000 22697237058313 50000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1804368351/10000000000 : ℝ)^4555 ≤ (17158425327/156250000000 : ℝ)^3531 := by
    have hnat : (1804368351 : ℕ)^4555*156250000000^3531 ≤ 17158425327^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1804368351 10000000000 17158425327 156250000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314192799/2500000000 : ℝ), (5421399709/10000000000 : ℝ), (-1804368351/10000000000 : ℝ)] ![(2181206682319/5000000000000 : ℝ), (22697237058313/50000000000000 : ℝ), (17158425327/156250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314192799/2500000000 : ℝ)|^4555 ≤ (2181206682319/5000000000000 : ℝ)^3531
        have hw : |(1314192799/2500000000 : ℝ)|=(1314192799/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5421399709/10000000000 : ℝ)|^4555 ≤ (22697237058313/50000000000000 : ℝ)^3531
        have hw : |(5421399709/10000000000 : ℝ)|=(5421399709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1804368351/10000000000 : ℝ)|^4555 ≤ (17158425327/156250000000 : ℝ)^3531
        have hw : |(-1804368351/10000000000 : ℝ)|=(1804368351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_box_11 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (225801981/500000000 : ℝ)*x 0 + (4141145049/10000000000 : ℝ)*x 1 + (1035286299/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (225801981/500000000 : ℝ)^4555 ≤ (35862165566837/100000000000000 : ℝ)^3531 := by
    have hnat : (225801981 : ℕ)^4555*100000000000000^3531 ≤ 35862165566837^3531*500000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225801981 500000000 35862165566837 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4141145049/10000000000 : ℝ)^4555 ≤ (8017229118507/25000000000000 : ℝ)^3531 := by
    have hnat : (4141145049 : ℕ)^4555*25000000000000^3531 ≤ 8017229118507^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4141145049 10000000000 8017229118507 25000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1035286299/2500000000 : ℝ)^4555 ≤ (32068917942521/100000000000000 : ℝ)^3531 := by
    have hnat : (1035286299 : ℕ)^4555*100000000000000^3531 ≤ 32068917942521^3531*2500000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035286299 2500000000 32068917942521 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(225801981/500000000 : ℝ), (4141145049/10000000000 : ℝ), (1035286299/2500000000 : ℝ)] ![(35862165566837/100000000000000 : ℝ), (8017229118507/25000000000000 : ℝ), (32068917942521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(225801981/500000000 : ℝ)|^4555 ≤ (35862165566837/100000000000000 : ℝ)^3531
        have hw : |(225801981/500000000 : ℝ)|=(225801981/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4141145049/10000000000 : ℝ)|^4555 ≤ (8017229118507/25000000000000 : ℝ)^3531
        have hw : |(4141145049/10000000000 : ℝ)|=(4141145049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1035286299/2500000000 : ℝ)|^4555 ≤ (32068917942521/100000000000000 : ℝ)^3531
        have hw : |(1035286299/2500000000 : ℝ)|=(1035286299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_box_12 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-861336433/5000000000 : ℝ)*x 0 + (2753797431/5000000000 : ℝ)*x 1 + (261454821/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (861336433/5000000000 : ℝ)^4555 ≤ (10344260904453/100000000000000 : ℝ)^3531 := by
    have hnat : (861336433 : ℕ)^4555*100000000000000^3531 ≤ 10344260904453^3531*5000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861336433 5000000000 10344260904453 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2753797431/5000000000 : ℝ)^4555 ≤ (11310460321/24414062500 : ℝ)^3531 := by
    have hnat : (2753797431 : ℕ)^4555*24414062500^3531 ≤ 11310460321^3531*5000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2753797431 5000000000 11310460321 24414062500 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (261454821/500000000 : ℝ)^4555 ≤ (43328093610061/100000000000000 : ℝ)^3531 := by
    have hnat : (261454821 : ℕ)^4555*100000000000000^3531 ≤ 43328093610061^3531*500000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261454821 500000000 43328093610061 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-861336433/5000000000 : ℝ), (2753797431/5000000000 : ℝ), (261454821/500000000 : ℝ)] ![(10344260904453/100000000000000 : ℝ), (11310460321/24414062500 : ℝ), (43328093610061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-861336433/5000000000 : ℝ)|^4555 ≤ (10344260904453/100000000000000 : ℝ)^3531
        have hw : |(-861336433/5000000000 : ℝ)|=(861336433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2753797431/5000000000 : ℝ)|^4555 ≤ (11310460321/24414062500 : ℝ)^3531
        have hw : |(2753797431/5000000000 : ℝ)|=(2753797431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(261454821/500000000 : ℝ)|^4555 ≤ (43328093610061/100000000000000 : ℝ)^3531
        have hw : |(261454821/500000000 : ℝ)|=(261454821/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_box_13 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (539048783/1000000000 : ℝ)*x 0 + (-1884064333/10000000000 : ℝ)*x 1 + (5229096481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539048783/1000000000 : ℝ)^4555 ≤ (45060857301447/100000000000000 : ℝ)^3531 := by
    have hnat : (539048783 : ℕ)^4555*100000000000000^3531 ≤ 45060857301447^3531*1000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539048783 1000000000 45060857301447 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1884064333/10000000000 : ℝ)^4555 ≤ (11611048422517/100000000000000 : ℝ)^3531 := by
    have hnat : (1884064333 : ℕ)^4555*100000000000000^3531 ≤ 11611048422517^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1884064333 10000000000 11611048422517 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5229096481/10000000000 : ℝ)^4555 ≤ (8665618852417/20000000000000 : ℝ)^3531 := by
    have hnat : (5229096481 : ℕ)^4555*20000000000000^3531 ≤ 8665618852417^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229096481 10000000000 8665618852417 20000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(539048783/1000000000 : ℝ), (-1884064333/10000000000 : ℝ), (5229096481/10000000000 : ℝ)] ![(45060857301447/100000000000000 : ℝ), (11611048422517/100000000000000 : ℝ), (8665618852417/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(539048783/1000000000 : ℝ)|^4555 ≤ (45060857301447/100000000000000 : ℝ)^3531
        have hw : |(539048783/1000000000 : ℝ)|=(539048783/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1884064333/10000000000 : ℝ)|^4555 ≤ (11611048422517/100000000000000 : ℝ)^3531
        have hw : |(-1884064333/10000000000 : ℝ)|=(1884064333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5229096481/10000000000 : ℝ)|^4555 ≤ (8665618852417/20000000000000 : ℝ)^3531
        have hw : |(5229096481/10000000000 : ℝ)|=(5229096481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_box_14 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5390487889/10000000000 : ℝ)*x 0 + (5229096381/10000000000 : ℝ)*x 1 + (-1884064387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5390487889/10000000000 : ℝ)^4555 ≤ (45060857937677/100000000000000 : ℝ)^3531 := by
    have hnat : (5390487889 : ℕ)^4555*100000000000000^3531 ≤ 45060857937677^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390487889 10000000000 45060857937677 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5229096381/10000000000 : ℝ)^4555 ≤ (43328093193193/100000000000000 : ℝ)^3531 := by
    have hnat : (5229096381 : ℕ)^4555*100000000000000^3531 ≤ 43328093193193^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229096381 10000000000 43328093193193 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1884064387/10000000000 : ℝ)^4555 ≤ (11611048851817/100000000000000 : ℝ)^3531 := by
    have hnat : (1884064387 : ℕ)^4555*100000000000000^3531 ≤ 11611048851817^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1884064387 10000000000 11611048851817 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5390487889/10000000000 : ℝ), (5229096381/10000000000 : ℝ), (-1884064387/10000000000 : ℝ)] ![(45060857937677/100000000000000 : ℝ), (43328093193193/100000000000000 : ℝ), (11611048851817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5390487889/10000000000 : ℝ)|^4555 ≤ (45060857937677/100000000000000 : ℝ)^3531
        have hw : |(5390487889/10000000000 : ℝ)|=(5390487889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5229096381/10000000000 : ℝ)|^4555 ≤ (43328093193193/100000000000000 : ℝ)^3531
        have hw : |(5229096381/10000000000 : ℝ)|=(5229096381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1884064387/10000000000 : ℝ)|^4555 ≤ (11611048851817/100000000000000 : ℝ)^3531
        have hw : |(-1884064387/10000000000 : ℝ)|=(1884064387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_box_15 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (803441927/2000000000 : ℝ)*x 0 + (878110277/2000000000 : ℝ)*x 1 + (4390551257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (803441927/2000000000 : ℝ)^4555 ≤ (30836244297649/100000000000000 : ℝ)^3531 := by
    have hnat : (803441927 : ℕ)^4555*100000000000000^3531 ≤ 30836244297649^3531*2000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      803441927 2000000000 30836244297649 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (878110277/2000000000 : ℝ)^4555 ≤ (6916375698937/20000000000000 : ℝ)^3531 := by
    have hnat : (878110277 : ℕ)^4555*20000000000000^3531 ≤ 6916375698937^3531*2000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      878110277 2000000000 6916375698937 20000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4390551257/10000000000 : ℝ)^4555 ≤ (276655017553/800000000000 : ℝ)^3531 := by
    have hnat : (4390551257 : ℕ)^4555*800000000000^3531 ≤ 276655017553^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4390551257 10000000000 276655017553 800000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(803441927/2000000000 : ℝ), (878110277/2000000000 : ℝ), (4390551257/10000000000 : ℝ)] ![(30836244297649/100000000000000 : ℝ), (6916375698937/20000000000000 : ℝ), (276655017553/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(803441927/2000000000 : ℝ)|^4555 ≤ (30836244297649/100000000000000 : ℝ)^3531
        have hw : |(803441927/2000000000 : ℝ)|=(803441927/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(878110277/2000000000 : ℝ)|^4555 ≤ (6916375698937/20000000000000 : ℝ)^3531
        have hw : |(878110277/2000000000 : ℝ)|=(878110277/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4390551257/10000000000 : ℝ)|^4555 ≤ (276655017553/800000000000 : ℝ)^3531
        have hw : |(4390551257/10000000000 : ℝ)|=(4390551257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1529_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164738759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (549/5000 : ℝ)*pair X i i ≤ pair X i h) :
    -(63763/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(14677/25000 : ℝ) ∧ (161/200 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (8611/10000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (549/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (549/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (549/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (549/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (549/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (549/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (549/5000 : ℝ) ^ (4553/1024 : ℝ) ≤ (1084602681758097/20000000000000000000 : ℝ) := by
    have hpowers : (549/5000 : ℝ)^4553 ≤ (1084602681758097/20000000000000000000 : ℝ)^1024 := by
      have hnat : (549 : ℕ)^4553*20000000000000000000^1024 ≤ 1084602681758097^1024*5000^4553 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        549 5000 1084602681758097 20000000000000000000 4553 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (549/5000 : ℝ)) (X := (1084602681758097/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4553 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3871/25000 : ℝ) ^ (4553/1024 : ℝ) ≤ (25002668726756137/100000000000000000000 : ℝ) := by
    have hpowers : (3871/25000 : ℝ)^4553 ≤ (25002668726756137/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3871 : ℕ)^4553*100000000000000000000^1024 ≤ 25002668726756137^1024*25000^4553 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3871 25000 25002668726756137 100000000000000000000 4553 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3871/25000 : ℝ)) (X := (25002668726756137/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4553 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001084602681758097/10000000000000000000 : ℝ) ≤ (10000243924108371/10000000000000000 : ℝ) ^ (4553/1024 : ℝ) := by
    have hpowers : (10001084602681758097/10000000000000000000 : ℝ)^1024 ≤ (10000243924108371/10000000000000000 : ℝ)^4553 := by
      have hnat : (10001084602681758097 : ℕ)^1024*10000000000000000^4553 ≤ 10000243924108371^4553*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001084602681758097 10000000000000000000 10000243924108371 10000000000000000 1024 4553 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000243924108371/10000000000000000 : ℝ)) (X := (10001084602681758097/10000000000000000000 : ℝ)) (by norm_num) 4553 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50015212841067773311/50000000000000000000 : ℝ) ≤ (2500171053291567/2500000000000000 : ℝ) ^ (4553/1024 : ℝ) := by
    have hpowers : (50015212841067773311/50000000000000000000 : ℝ)^1024 ≤ (2500171053291567/2500000000000000 : ℝ)^4553 := by
      have hnat : (50015212841067773311 : ℕ)^1024*2500000000000000^4553 ≤ 2500171053291567^4553*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015212841067773311 50000000000000000000 2500171053291567 2500000000000000 1024 4553 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500171053291567/2500000000000000 : ℝ)) (X := (50015212841067773311/50000000000000000000 : ℝ)) (by norm_num) 4553 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50025002668726756137/50000000000000000000 : ℝ) ≤ (2000224900444833/2000000000000000 : ℝ) ^ (4553/1024 : ℝ) := by
    have hpowers : (50025002668726756137/50000000000000000000 : ℝ)^1024 ≤ (2000224900444833/2000000000000000 : ℝ)^4553 := by
      have hnat : (50025002668726756137 : ℕ)^1024*2000000000000000^4553 ≤ 2000224900444833^4553*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025002668726756137 50000000000000000000 2000224900444833 2000000000000000 1024 4553 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000224900444833/2000000000000000 : ℝ)) (X := (50025002668726756137/50000000000000000000 : ℝ)) (by norm_num) 4553 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1084602681758097/20000000000000000000 : ℝ) ≤ ((703616091976135701/703750000000000000 : ℝ)+2*(440289057897/450400000000000 : ℝ)*(549/5000 : ℝ))^(4553/1024 : ℝ) := by
    rw [show (703616091976135701/703750000000000000 : ℝ)+2*(440289057897/450400000000000 : ℝ)*(549/5000 : ℝ)=(10000243924108371/10000000000000000 : ℝ) by norm_num, show 1+2*(1084602681758097/20000000000000000000 : ℝ)=(10001084602681758097/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(25002668726756137/100000000000000000000 : ℝ)+(1084602681758097/20000000000000000000 : ℝ) ≤ ((703616091976135701/703750000000000000 : ℝ)+(440289057897/450400000000000 : ℝ)*((3871/25000 : ℝ)+(549/5000 : ℝ)))^(4553/1024 : ℝ) := by
    rw [show (703616091976135701/703750000000000000 : ℝ)+(440289057897/450400000000000 : ℝ)*((3871/25000 : ℝ)+(549/5000 : ℝ))=(2500171053291567/2500000000000000 : ℝ) by norm_num, show 1+(25002668726756137/100000000000000000000 : ℝ)+(1084602681758097/20000000000000000000 : ℝ)=(50015212841067773311/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(25002668726756137/100000000000000000000 : ℝ) ≤ ((703616091976135701/703750000000000000 : ℝ)+2*(440289057897/450400000000000 : ℝ)*(3871/25000 : ℝ))^(4553/1024 : ℝ) := by
    rw [show (703616091976135701/703750000000000000 : ℝ)+2*(440289057897/450400000000000 : ℝ)*(3871/25000 : ℝ)=(2000224900444833/2000000000000000 : ℝ) by norm_num, show 1+2*(25002668726756137/100000000000000000000 : ℝ)=(50025002668726756137/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (703616091976135701/703750000000000000 : ℝ)*(X 1 0+X 2 0)+(440289057897/450400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4553/1024 : ℝ)) (lo := (549/5000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (703616091976135701/703750000000000000 : ℝ)) (alpha := (440289057897/450400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (703616091976135701/703750000000000000 : ℝ)*(X 0 1+X 2 1)+(440289057897/450400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4553/1024 : ℝ)) (lo := (549/5000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (703616091976135701/703750000000000000 : ℝ)) (alpha := (440289057897/450400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (703616091976135701/703750000000000000 : ℝ)*(X 0 2+X 1 2)+(440289057897/450400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4553/1024 : ℝ)) (lo := (549/5000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (703616091976135701/703750000000000000 : ℝ)) (alpha := (440289057897/450400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1632554371/10000000000 : ℝ)*X 0 0+(5400998089/10000000000 : ℝ)*X 0 1+(2700498851/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5270961649/10000000000 : ℝ)*X 1 0+(-226632279/1250000000 : ℝ)*X 1 1+(2700499183/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2635480769/5000000000 : ℝ)*X 2 0+(1350249619/2500000000 : ℝ)*X 2 1+(-226632279/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4464237159/10000000000 : ℝ)*X 0 0+(520954609/1250000000 : ℝ)*X 0 1+(4167636591/10000000000 : ℝ)*X 0 2+(4464237159/10000000000 : ℝ)*X 1 0+(520954609/1250000000 : ℝ)*X 1 1+(4167636591/10000000000 : ℝ)*X 1 2+(4464237159/10000000000 : ℝ)*X 2 0+(520954609/1250000000 : ℝ)*X 2 1+(4167636591/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-411851083/2000000000 : ℝ)*X 0 0+(5244134457/10000000000 : ℝ)*X 0 1+(5244134641/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((8608051/16000000 : ℝ)*X 1 0+(-1878013177/10000000000 : ℝ)*X 1 1+(5244134291/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2690015751/5000000000 : ℝ)*X 2 0+(5244134501/10000000000 : ℝ)*X 2 1+(-9390067/50000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4057102817/10000000000 : ℝ)*X 0 0+(437107219/1000000000 : ℝ)*X 0 1+(4371071311/10000000000 : ℝ)*X 0 2+(4057102817/10000000000 : ℝ)*X 1 0+(437107219/1000000000 : ℝ)*X 1 1+(4371071311/10000000000 : ℝ)*X 1 2+(4057102817/10000000000 : ℝ)*X 2 0+(437107219/1000000000 : ℝ)*X 2 1+(4371071311/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1968996723/10000000000 : ℝ)*X 0 0+(2567027789/5000000000 : ℝ)*X 0 1+(216855987/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2628385651/5000000000 : ℝ)*X 1 0+(-1804368189/10000000000 : ℝ)*X 1 1+(5421399723/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1314192799/2500000000 : ℝ)*X 2 0+(5421399709/10000000000 : ℝ)*X 2 1+(-1804368351/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((225801981/500000000 : ℝ)*X 0 0+(4141145049/10000000000 : ℝ)*X 0 1+(1035286299/2500000000 : ℝ)*X 0 2+(225801981/500000000 : ℝ)*X 1 0+(4141145049/10000000000 : ℝ)*X 1 1+(1035286299/2500000000 : ℝ)*X 1 2+(225801981/500000000 : ℝ)*X 2 0+(4141145049/10000000000 : ℝ)*X 2 1+(1035286299/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-861336433/5000000000 : ℝ)*X 0 0+(2753797431/5000000000 : ℝ)*X 0 1+(261454821/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((539048783/1000000000 : ℝ)*X 1 0+(-1884064333/10000000000 : ℝ)*X 1 1+(5229096481/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5390487889/10000000000 : ℝ)*X 2 0+(5229096381/10000000000 : ℝ)*X 2 1+(-1884064387/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((803441927/2000000000 : ℝ)*X 0 0+(878110277/2000000000 : ℝ)*X 0 1+(4390551257/10000000000 : ℝ)*X 0 2+(803441927/2000000000 : ℝ)*X 1 0+(878110277/2000000000 : ℝ)*X 1 1+(4390551257/10000000000 : ℝ)*X 1 2+(803441927/2000000000 : ℝ)*X 2 0+(878110277/2000000000 : ℝ)*X 2 1+(4390551257/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-63763/100000 : ℝ) ≤ (-11217814932982293420022980769899/17593750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12996779/12500000000000 : ℝ)*(lower0) + (48162829/100000000000000 : ℝ)*(upper1) + (6591059/6250000000000 : ℝ)*(lower4) + (2836591/6250000000000 : ℝ)*(lower5) + (2248373327572691/100000000000000 : ℝ)*(major0) + (2248373327572691/100000000000000 : ℝ)*(major1) + (2248373327572691/100000000000000 : ℝ)*(major2) + (793027651/20000000000000 : ℝ)*(sp1) + (712635671/25000000000000 : ℝ)*(sp2) + (3153188685672041/100000000000000 : ℝ)*(sp4) + (1576592360266893/50000000000000 : ℝ)*(sp5) + (788296458782339/25000000000000 : ℝ)*(sp6) + (682403714534741/50000000000000 : ℝ)*(sp7) + (3949394703/100000000000000 : ℝ)*(sp15) + (272962275692837/20000000000000 : ℝ)*(f.failure) + (3153188685672041/100000000000000 : ℝ)*(f.sum) + (80203066892853/22520000000000000000000000000 : ℝ)*base66 + (171410611184682843/140750000000000000000000000000000 : ℝ)*base68 + (153854351173817157/140750000000000000000000000000000 : ℝ)*base69 + (676600289368682843/140750000000000000000000000000000 : ℝ)*base72 + (63665643029267/22520000000000000000000000000 : ℝ)*base73 + (909333526592567157/140750000000000000000000000000000 : ℝ)*base75 + (374232249277067157/140750000000000000000000000000000 : ℝ)*base77 + (779377567243067157/140750000000000000000000000000000 : ℝ)*base79 + (42090998128627/22520000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (12569283/2000000000000000000000 : ℝ)*base89 + (12569283/2000000000000000000000 : ℝ)*base91 + (12569283/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (14677/25000 : ℝ) ≤ (1032933855472488586122444167571/1759375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (59622401/100000000000000 : ℝ)*(upper0) + (15537843/50000000000000 : ℝ)*(upper2) + (29712977/20000000000000 : ℝ)*(upper3) + (78065537/100000000000000 : ℝ)*(upper4) + (232578363386237/10000000000000 : ℝ)*(major0) + (232578363386237/10000000000000 : ℝ)*(major1) + (232578363386237/10000000000000 : ℝ)*(major2) + (1610098031728191/50000000000000 : ℝ)*(sp0) + (1610095951706573/50000000000000 : ℝ)*(sp1) + (201261519874639/6250000000000 : ℝ)*(sp2) + (705895469983667/50000000000000 : ℝ)*(sp3) + (1040010809/25000000000000 : ℝ)*(sp5) + (11745462157/100000000000000 : ℝ)*(sp6) + (10173492777/100000000000000 : ℝ)*(sp11) + (88237569591257/6250000000000 : ℝ)*(f.failure) + (1610098031728191/50000000000000 : ℝ)*(f.sum) + (4429863248341/2252000000000000000000000000 : ℝ)*base65 + (20936628721784899/14075000000000000000000000000000 : ℝ)*base67 + (56678718472959899/14075000000000000000000000000000 : ℝ)*base69 + (26879519054209899/14075000000000000000000000000000 : ℝ)*base71 + (340147053397/450400000000000000000000000 : ℝ)*base73 + (29093253379859899/14075000000000000000000000000000 : ℝ)*base75 + (21355910965809899/14075000000000000000000000000000 : ℝ)*base77 + (35046432213559899/14075000000000000000000000000000 : ℝ)*base79 + (12663245524253/2252000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (2930063/625000000000000000000 : ℝ)*base89 + (2930063/625000000000000000000 : ℝ)*base91 + (2930063/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (161/200 : ℝ) ≤ (14163404643157068584866337775447/17593750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6094407/10000000000000 : ℝ)*(upper2) + (616001/20000000000000 : ℝ)*(lower4) + (691859/4000000000000 : ℝ)*(lower5) + (1258807026825967/50000000000000 : ℝ)*(major0) + (1258807026825967/50000000000000 : ℝ)*(major1) + (1258807026825967/50000000000000 : ℝ)*(major2) + (993714337/5000000000000 : ℝ)*(sp1) + (376238949/50000000000000 : ℝ)*(sp2) + (733885457/12500000000000 : ℝ)*(sp3) + (336241347/25000000000000 : ℝ)*(sp4) + (1740073131981077/50000000000000 : ℝ)*(sp8) + (1740063867320401/50000000000000 : ℝ)*(sp9) + (3480146856449643/100000000000000 : ℝ)*(sp10) + (764120234055417/50000000000000 : ℝ)*(sp11) + (152824633919449/10000000000000 : ℝ)*(f.failure) + (3480147608927541/100000000000000 : ℝ)*(f.sum) + (108961547823679/11260000000000000000000000000 : ℝ)*base65 + (569543663835967609/70375000000000000000000000000000 : ℝ)*base67 + (687582131798967609/70375000000000000000000000000000 : ℝ)*base69 + (510089412562717609/70375000000000000000000000000000 : ℝ)*base71 + (5038339224999/11260000000000000000000000000 : ℝ)*base73 + (577933727703467609/70375000000000000000000000000000 : ℝ)*base75 + (1094281317519717609/70375000000000000000000000000000 : ℝ)*base77 + (721042177843342609/70375000000000000000000000000000 : ℝ)*base79 + (8159185763661/11260000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (5776209/1000000000000000000000 : ℝ)*base90 + (5776209/1000000000000000000000 : ℝ)*base92 + (5776209/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-8611/10000 : ℝ) ≤ (-1514961184347716180762582589969/1759375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8251867/100000000000000 : ℝ)*(lower0) + (1154941/50000000000000 : ℝ)*(lower2) + (20084129/100000000000000 : ℝ)*(upper3) + (63927461529317/2500000000000 : ℝ)*(major0) + (63927461529317/2500000000000 : ℝ)*(major1) + (63927461529317/2500000000000 : ℝ)*(major2) + (794366923/100000000000000 : ℝ)*(sp4) + (72205289/400000000000 : ℝ)*(sp6) + (104470513/1000000000000 : ℝ)*(sp7) + (32472917/100000000000000 : ℝ)*(sp8) + (179534225193813/5000000000000 : ℝ)*(sp12) + (35906853307161/1000000000000 : ℝ)*(sp13) + (71813345587877/2000000000000 : ℝ)*(sp14) + (776101891974923/50000000000000 : ℝ)*(sp15) + (776107115500573/50000000000000 : ℝ)*(f.failure) + (35906853307161/1000000000000 : ℝ)*(f.sum) + (1450621961833/563000000000000000000000000 : ℝ)*base66 + (15361410988473191/3518750000000000000000000000000 : ℝ)*base68 + (27356741322841941/3518750000000000000000000000000 : ℝ)*base70 + (21019682888529441/3518750000000000000000000000000 : ℝ)*base72 + (1555505650481/563000000000000000000000000 : ℝ)*base74 + (35070099183879441/3518750000000000000000000000000 : ℝ)*base76 + (32295655022591941/3518750000000000000000000000000 : ℝ)*base78 + (33235539010404441/3518750000000000000000000000000 : ℝ)*base80 + (2177743588287/563000000000000000000000000 : ℝ)*base82 + (59808907/5000000000000000000000 : ℝ)*base89 + (59808907/5000000000000000000000 : ℝ)*base91 + (59808907/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1529_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164738759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (549/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63763/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14677/25000 : ℝ) else (161/200 : ℝ) ≤ X j i ∧ X j i ≤ (8611/10000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1529_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1529_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164738759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10979/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63763/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14677/25000 : ℝ) else (161/200 : ℝ) ≤ X j i ∧ X j i ≤ (8611/10000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1529_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1529_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164738759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10979/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63763/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14677/25000 : ℝ) else (161/200 : ℝ) ≤ X j i ∧ X j i ≤ (8611/10000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1529_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
