-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1620_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:54:24.122294+00:00
-- url     : https://prove2.me/submissions/a92cf324-adc2-4fd8-a91d-bb637d65764a

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
theorem support_rectangle_w1620_box_0 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1410179577/10000000000 : ℝ)*x 0 + (54155501/100000000 : ℝ)*x 1 + (2707774809/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1410179577/10000000000 : ℝ)^4799 ≤ (518069568167/6250000000000 : ℝ)^3775 := by
    have hnat : (1410179577 : ℕ)^4799*6250000000000^3775 ≤ 518069568167^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1410179577 10000000000 518069568167 6250000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54155501/100000000 : ℝ)^4799 ≤ (22927723019751/50000000000000 : ℝ)^3775 := by
    have hnat : (54155501 : ℕ)^4799*50000000000000^3775 ≤ 22927723019751^3775*100000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54155501 100000000 22927723019751 50000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707774809/5000000000 : ℝ)^4799 ≤ (45855440851153/100000000000000 : ℝ)^3775 := by
    have hnat : (2707774809 : ℕ)^4799*100000000000000^3775 ≤ 45855440851153^3775*5000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707774809 5000000000 45855440851153 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1410179577/10000000000 : ℝ), (54155501/100000000 : ℝ), (2707774809/5000000000 : ℝ)] ![(518069568167/6250000000000 : ℝ), (22927723019751/50000000000000 : ℝ), (45855440851153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1410179577/10000000000 : ℝ)|^4799 ≤ (518069568167/6250000000000 : ℝ)^3775
        have hw : |(-1410179577/10000000000 : ℝ)|=(1410179577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(54155501/100000000 : ℝ)|^4799 ≤ (22927723019751/50000000000000 : ℝ)^3775
        have hw : |(54155501/100000000 : ℝ)|=(54155501/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707774809/5000000000 : ℝ)|^4799 ≤ (45855440851153/100000000000000 : ℝ)^3775
        have hw : |(2707774809/5000000000 : ℝ)|=(2707774809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_box_1 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050248097/2000000000 : ℝ)*x 0 + (-820477653/5000000000 : ℝ)*x 1 + (5415549591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050248097/2000000000 : ℝ)^4799 ≤ (8818823079733/20000000000000 : ℝ)^3775 := by
    have hnat : (1050248097 : ℕ)^4799*20000000000000^3775 ≤ 8818823079733^3775*2000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050248097 2000000000 8818823079733 20000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (820477653/5000000000 : ℝ)^4799 ≤ (2010088804741/20000000000000 : ℝ)^3775 := by
    have hnat : (820477653 : ℕ)^4799*20000000000000^3775 ≤ 2010088804741^3775*5000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      820477653 5000000000 2010088804741 20000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415549591/10000000000 : ℝ)^4799 ≤ (1146386014013/2500000000000 : ℝ)^3775 := by
    have hnat : (5415549591 : ℕ)^4799*2500000000000^3775 ≤ 1146386014013^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415549591 10000000000 1146386014013 2500000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050248097/2000000000 : ℝ), (-820477653/5000000000 : ℝ), (5415549591/10000000000 : ℝ)] ![(8818823079733/20000000000000 : ℝ), (2010088804741/20000000000000 : ℝ), (1146386014013/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050248097/2000000000 : ℝ)|^4799 ≤ (8818823079733/20000000000000 : ℝ)^3775
        have hw : |(1050248097/2000000000 : ℝ)|=(1050248097/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-820477653/5000000000 : ℝ)|^4799 ≤ (2010088804741/20000000000000 : ℝ)^3775
        have hw : |(-820477653/5000000000 : ℝ)|=(820477653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415549591/10000000000 : ℝ)|^4799 ≤ (1146386014013/2500000000000 : ℝ)^3775
        have hw : |(5415549591/10000000000 : ℝ)|=(5415549591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_box_2 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050248117/2000000000 : ℝ)*x 0 + (2707774897/5000000000 : ℝ)*x 1 + (-1640954889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050248117/2000000000 : ℝ)^4799 ≤ (44094116466127/100000000000000 : ℝ)^3775 := by
    have hnat : (1050248117 : ℕ)^4799*100000000000000^3775 ≤ 44094116466127^3775*2000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050248117 2000000000 44094116466127 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707774897/5000000000 : ℝ)^4799 ≤ (22927721372827/50000000000000 : ℝ)^3775 := by
    have hnat : (2707774897 : ℕ)^4799*50000000000000^3775 ≤ 22927721372827^3775*5000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707774897 5000000000 22927721372827 50000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1640954889/10000000000 : ℝ)^4799 ≤ (2512610194221/25000000000000 : ℝ)^3775 := by
    have hnat : (1640954889 : ℕ)^4799*25000000000000^3775 ≤ 2512610194221^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1640954889 10000000000 2512610194221 25000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050248117/2000000000 : ℝ), (2707774897/5000000000 : ℝ), (-1640954889/10000000000 : ℝ)] ![(44094116466127/100000000000000 : ℝ), (22927721372827/50000000000000 : ℝ), (2512610194221/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050248117/2000000000 : ℝ)|^4799 ≤ (44094116466127/100000000000000 : ℝ)^3775
        have hw : |(1050248117/2000000000 : ℝ)|=(1050248117/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707774897/5000000000 : ℝ)|^4799 ≤ (22927721372827/50000000000000 : ℝ)^3775
        have hw : |(2707774897/5000000000 : ℝ)|=(2707774897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1640954889/10000000000 : ℝ)|^4799 ≤ (2512610194221/25000000000000 : ℝ)^3775
        have hw : |(-1640954889/10000000000 : ℝ)|=(1640954889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_box_3 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (112084809/250000000 : ℝ)*x 0 + (4077421749/10000000000 : ℝ)*x 1 + (4077421597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (112084809/250000000 : ℝ)^4799 ≤ (18033175028601/50000000000000 : ℝ)^3775 := by
    have hnat : (112084809 : ℕ)^4799*50000000000000^3775 ≤ 18033175028601^3775*250000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112084809 250000000 18033175028601 50000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4077421749/10000000000 : ℝ)^4799 ≤ (31966825722921/100000000000000 : ℝ)^3775 := by
    have hnat : (4077421749 : ℕ)^4799*100000000000000^3775 ≤ 31966825722921^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4077421749 10000000000 31966825722921 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4077421597/10000000000 : ℝ)^4799 ≤ (7991706051999/25000000000000 : ℝ)^3775 := by
    have hnat : (4077421597 : ℕ)^4799*25000000000000^3775 ≤ 7991706051999^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4077421597 10000000000 7991706051999 25000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(112084809/250000000 : ℝ), (4077421749/10000000000 : ℝ), (4077421597/10000000000 : ℝ)] ![(18033175028601/50000000000000 : ℝ), (31966825722921/100000000000000 : ℝ), (7991706051999/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(112084809/250000000 : ℝ)|^4799 ≤ (18033175028601/50000000000000 : ℝ)^3775
        have hw : |(112084809/250000000 : ℝ)|=(112084809/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4077421749/10000000000 : ℝ)|^4799 ≤ (31966825722921/100000000000000 : ℝ)^3775
        have hw : |(4077421749/10000000000 : ℝ)|=(4077421749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4077421597/10000000000 : ℝ)|^4799 ≤ (7991706051999/25000000000000 : ℝ)^3775
        have hw : |(4077421597/10000000000 : ℝ)|=(4077421597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_box_4 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-489854741/2500000000 : ℝ)*x 0 + (260731871/500000000 : ℝ)*x 1 + (208585517/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (489854741/2500000000 : ℝ)^4799 ≤ (3148117893409/25000000000000 : ℝ)^3775 := by
    have hnat : (489854741 : ℕ)^4799*25000000000000^3775 ≤ 3148117893409^3775*2500000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      489854741 2500000000 3148117893409 25000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260731871/500000000 : ℝ)^4799 ≤ (43703761513451/100000000000000 : ℝ)^3775 := by
    have hnat : (260731871 : ℕ)^4799*100000000000000^3775 ≤ 43703761513451^3775*500000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260731871 500000000 43703761513451 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208585517/400000000 : ℝ)^4799 ≤ (43703766893917/100000000000000 : ℝ)^3775 := by
    have hnat : (208585517 : ℕ)^4799*100000000000000^3775 ≤ 43703766893917^3775*400000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208585517 400000000 43703766893917 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-489854741/2500000000 : ℝ), (260731871/500000000 : ℝ), (208585517/400000000 : ℝ)] ![(3148117893409/25000000000000 : ℝ), (43703761513451/100000000000000 : ℝ), (43703766893917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-489854741/2500000000 : ℝ)|^4799 ≤ (3148117893409/25000000000000 : ℝ)^3775
        have hw : |(-489854741/2500000000 : ℝ)|=(489854741/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(260731871/500000000 : ℝ)|^4799 ≤ (43703761513451/100000000000000 : ℝ)^3775
        have hw : |(260731871/500000000 : ℝ)|=(260731871/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(208585517/400000000 : ℝ)|^4799 ≤ (43703766893917/100000000000000 : ℝ)^3775
        have hw : |(208585517/400000000 : ℝ)|=(208585517/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_box_5 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2694855253/5000000000 : ℝ)*x 0 + (-863097747/5000000000 : ℝ)*x 1 + (130365937/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2694855253/5000000000 : ℝ)^4799 ≤ (2278874172199/5000000000000 : ℝ)^3775 := by
    have hnat : (2694855253 : ℕ)^4799*5000000000000^3775 ≤ 2278874172199^3775*5000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2694855253 5000000000 2278874172199 5000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (863097747/5000000000 : ℝ)^4799 ≤ (5359377197863/50000000000000 : ℝ)^3775 := by
    have hnat : (863097747 : ℕ)^4799*50000000000000^3775 ≤ 5359377197863^3775*5000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863097747 5000000000 5359377197863 50000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130365937/250000000 : ℝ)^4799 ≤ (8740752430543/20000000000000 : ℝ)^3775 := by
    have hnat : (130365937 : ℕ)^4799*20000000000000^3775 ≤ 8740752430543^3775*250000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130365937 250000000 8740752430543 20000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2694855253/5000000000 : ℝ), (-863097747/5000000000 : ℝ), (130365937/250000000 : ℝ)] ![(2278874172199/5000000000000 : ℝ), (5359377197863/50000000000000 : ℝ), (8740752430543/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2694855253/5000000000 : ℝ)|^4799 ≤ (2278874172199/5000000000000 : ℝ)^3775
        have hw : |(2694855253/5000000000 : ℝ)|=(2694855253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-863097747/5000000000 : ℝ)|^4799 ≤ (5359377197863/50000000000000 : ℝ)^3775
        have hw : |(-863097747/5000000000 : ℝ)|=(863097747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(130365937/250000000 : ℝ)|^4799 ≤ (8740752430543/20000000000000 : ℝ)^3775
        have hw : |(130365937/250000000 : ℝ)|=(130365937/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_box_6 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5389710289/10000000000 : ℝ)*x 0 + (1042927481/2000000000 : ℝ)*x 1 + (-1726195889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5389710289/10000000000 : ℝ)^4799 ≤ (1823099244447/4000000000000 : ℝ)^3775 := by
    have hnat : (5389710289 : ℕ)^4799*4000000000000^3775 ≤ 1823099244447^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389710289 10000000000 1823099244447 4000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1042927481/2000000000 : ℝ)^4799 ≤ (8740752270727/20000000000000 : ℝ)^3775 := by
    have hnat : (1042927481 : ℕ)^4799*20000000000000^3775 ≤ 8740752270727^3775*2000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042927481 2000000000 8740752270727 20000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1726195889/10000000000 : ℝ)^4799 ≤ (167480586153/1562500000000 : ℝ)^3775 := by
    have hnat : (1726195889 : ℕ)^4799*1562500000000^3775 ≤ 167480586153^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1726195889 10000000000 167480586153 1562500000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5389710289/10000000000 : ℝ), (1042927481/2000000000 : ℝ), (-1726195889/10000000000 : ℝ)] ![(1823099244447/4000000000000 : ℝ), (8740752270727/20000000000000 : ℝ), (167480586153/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5389710289/10000000000 : ℝ)|^4799 ≤ (1823099244447/4000000000000 : ℝ)^3775
        have hw : |(5389710289/10000000000 : ℝ)|=(5389710289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1042927481/2000000000 : ℝ)|^4799 ≤ (8740752270727/20000000000000 : ℝ)^3775
        have hw : |(1042927481/2000000000 : ℝ)|=(1042927481/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1726195889/10000000000 : ℝ)|^4799 ≤ (167480586153/1562500000000 : ℝ)^3775
        have hw : |(-1726195889/10000000000 : ℝ)|=(1726195889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_box_7 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1959670451/5000000000 : ℝ)*x 0 + (2179554559/5000000000 : ℝ)*x 1 + (4359108807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1959670451/5000000000 : ℝ)^4799 ≤ (1899978675923/6250000000000 : ℝ)^3775 := by
    have hnat : (1959670451 : ℕ)^4799*6250000000000^3775 ≤ 1899978675923^3775*5000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1959670451 5000000000 1899978675923 6250000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2179554559/5000000000 : ℝ)^4799 ≤ (2175010760151/6250000000000 : ℝ)^3775 := by
    have hnat : (2179554559 : ℕ)^4799*6250000000000^3775 ≤ 2175010760151^3775*5000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179554559 5000000000 2175010760151 6250000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4359108807/10000000000 : ℝ)^4799 ≤ (870004225153/2500000000000 : ℝ)^3775 := by
    have hnat : (4359108807 : ℕ)^4799*2500000000000^3775 ≤ 870004225153^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359108807 10000000000 870004225153 2500000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1959670451/5000000000 : ℝ), (2179554559/5000000000 : ℝ), (4359108807/10000000000 : ℝ)] ![(1899978675923/6250000000000 : ℝ), (2175010760151/6250000000000 : ℝ), (870004225153/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1959670451/5000000000 : ℝ)|^4799 ≤ (1899978675923/6250000000000 : ℝ)^3775
        have hw : |(1959670451/5000000000 : ℝ)|=(1959670451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2179554559/5000000000 : ℝ)|^4799 ≤ (2175010760151/6250000000000 : ℝ)^3775
        have hw : |(2179554559/5000000000 : ℝ)|=(2179554559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4359108807/10000000000 : ℝ)|^4799 ≤ (870004225153/2500000000000 : ℝ)^3775
        have hw : |(4359108807/10000000000 : ℝ)|=(4359108807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_box_8 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-368507673/2000000000 : ℝ)*x 0 + (5070879787/10000000000 : ℝ)*x 1 + (5445373859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (368507673/2000000000 : ℝ)^4799 ≤ (11645407624477/100000000000000 : ℝ)^3775 := by
    have hnat : (368507673 : ℕ)^4799*100000000000000^3775 ≤ 11645407624477^3775*2000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      368507673 2000000000 11645407624477 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5070879787/10000000000 : ℝ)^4799 ≤ (42177877671467/100000000000000 : ℝ)^3775 := by
    have hnat : (5070879787 : ℕ)^4799*100000000000000^3775 ≤ 42177877671467^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5070879787 10000000000 42177877671467 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5445373859/10000000000 : ℝ)^4799 ≤ (2308835734467/5000000000000 : ℝ)^3775 := by
    have hnat : (5445373859 : ℕ)^4799*5000000000000^3775 ≤ 2308835734467^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5445373859 10000000000 2308835734467 5000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-368507673/2000000000 : ℝ), (5070879787/10000000000 : ℝ), (5445373859/10000000000 : ℝ)] ![(11645407624477/100000000000000 : ℝ), (42177877671467/100000000000000 : ℝ), (2308835734467/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-368507673/2000000000 : ℝ)|^4799 ≤ (11645407624477/100000000000000 : ℝ)^3775
        have hw : |(-368507673/2000000000 : ℝ)|=(368507673/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5070879787/10000000000 : ℝ)|^4799 ≤ (42177877671467/100000000000000 : ℝ)^3775
        have hw : |(5070879787/10000000000 : ℝ)|=(5070879787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5445373859/10000000000 : ℝ)|^4799 ≤ (2308835734467/5000000000000 : ℝ)^3775
        have hw : |(5445373859/10000000000 : ℝ)|=(5445373859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_box_9 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (40864713/78125000 : ℝ)*x 0 + (-1627847913/10000000000 : ℝ)*x 1 + (5445373401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (40864713/78125000 : ℝ)^4799 ≤ (5484348931339/12500000000000 : ℝ)^3775 := by
    have hnat : (40864713 : ℕ)^4799*12500000000000^3775 ≤ 5484348931339^3775*78125000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40864713 78125000 5484348931339 12500000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1627847913/10000000000 : ℝ)^4799 ≤ (9948498786079/100000000000000 : ℝ)^3775 := by
    have hnat : (1627847913 : ℕ)^4799*100000000000000^3775 ≤ 9948498786079^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1627847913 10000000000 9948498786079 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5445373401/10000000000 : ℝ)^4799 ≤ (23088354875991/50000000000000 : ℝ)^3775 := by
    have hnat : (5445373401 : ℕ)^4799*50000000000000^3775 ≤ 23088354875991^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5445373401 10000000000 23088354875991 50000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(40864713/78125000 : ℝ), (-1627847913/10000000000 : ℝ), (5445373401/10000000000 : ℝ)] ![(5484348931339/12500000000000 : ℝ), (9948498786079/100000000000000 : ℝ), (23088354875991/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(40864713/78125000 : ℝ)|^4799 ≤ (5484348931339/12500000000000 : ℝ)^3775
        have hw : |(40864713/78125000 : ℝ)|=(40864713/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1627847913/10000000000 : ℝ)|^4799 ≤ (9948498786079/100000000000000 : ℝ)^3775
        have hw : |(-1627847913/10000000000 : ℝ)|=(1627847913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5445373401/10000000000 : ℝ)|^4799 ≤ (23088354875991/50000000000000 : ℝ)^3775
        have hw : |(5445373401/10000000000 : ℝ)|=(5445373401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_box_10 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1046136601/2000000000 : ℝ)*x 0 + (2722686777/5000000000 : ℝ)*x 1 + (-325569611/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1046136601/2000000000 : ℝ)^4799 ≤ (1754991547557/4000000000000 : ℝ)^3775 := by
    have hnat : (1046136601 : ℕ)^4799*4000000000000^3775 ≤ 1754991547557^3775*2000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046136601 2000000000 1754991547557 4000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2722686777/5000000000 : ℝ)^4799 ≤ (46176711401361/100000000000000 : ℝ)^3775 := by
    have hnat : (2722686777 : ℕ)^4799*100000000000000^3775 ≤ 46176711401361^3775*5000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2722686777 5000000000 46176711401361 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (325569611/2000000000 : ℝ)^4799 ≤ (9948499889309/100000000000000 : ℝ)^3775 := by
    have hnat : (325569611 : ℕ)^4799*100000000000000^3775 ≤ 9948499889309^3775*2000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325569611 2000000000 9948499889309 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1046136601/2000000000 : ℝ), (2722686777/5000000000 : ℝ), (-325569611/2000000000 : ℝ)] ![(1754991547557/4000000000000 : ℝ), (46176711401361/100000000000000 : ℝ), (9948499889309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1046136601/2000000000 : ℝ)|^4799 ≤ (1754991547557/4000000000000 : ℝ)^3775
        have hw : |(1046136601/2000000000 : ℝ)|=(1046136601/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2722686777/5000000000 : ℝ)|^4799 ≤ (46176711401361/100000000000000 : ℝ)^3775
        have hw : |(2722686777/5000000000 : ℝ)|=(2722686777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-325569611/2000000000 : ℝ)|^4799 ≤ (9948499889309/100000000000000 : ℝ)^3775
        have hw : |(-325569611/2000000000 : ℝ)|=(325569611/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_box_11 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2282363671/5000000000 : ℝ)*x 0 + (1008883181/2500000000 : ℝ)*x 1 + (1008883221/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2282363671/5000000000 : ℝ)^4799 ≤ (922504103397/2500000000000 : ℝ)^3775 := by
    have hnat : (2282363671 : ℕ)^4799*2500000000000^3775 ≤ 922504103397^3775*5000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2282363671 5000000000 922504103397 2500000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1008883181/2500000000 : ℝ)^4799 ≤ (31549917127941/100000000000000 : ℝ)^3775 := by
    have hnat : (1008883181 : ℕ)^4799*100000000000000^3775 ≤ 31549917127941^3775*2500000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008883181 2500000000 31549917127941 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1008883221/2500000000 : ℝ)^4799 ≤ (31549918718139/100000000000000 : ℝ)^3775 := by
    have hnat : (1008883221 : ℕ)^4799*100000000000000^3775 ≤ 31549918718139^3775*2500000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008883221 2500000000 31549918718139 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2282363671/5000000000 : ℝ), (1008883181/2500000000 : ℝ), (1008883221/2500000000 : ℝ)] ![(922504103397/2500000000000 : ℝ), (31549917127941/100000000000000 : ℝ), (31549918718139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2282363671/5000000000 : ℝ)|^4799 ≤ (922504103397/2500000000000 : ℝ)^3775
        have hw : |(2282363671/5000000000 : ℝ)|=(2282363671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1008883181/2500000000 : ℝ)|^4799 ≤ (31549917127941/100000000000000 : ℝ)^3775
        have hw : |(1008883181/2500000000 : ℝ)|=(1008883181/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1008883221/2500000000 : ℝ)|^4799 ≤ (31549918718139/100000000000000 : ℝ)^3775
        have hw : |(1008883221/2500000000 : ℝ)|=(1008883221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_box_12 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1525690801/10000000000 : ℝ)*x 0 + (5553557917/10000000000 : ℝ)*x 1 + (5194772929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1525690801/10000000000 : ℝ)^4799 ≤ (9161678846783/100000000000000 : ℝ)^3775 := by
    have hnat : (1525690801 : ℕ)^4799*100000000000000^3775 ≤ 9161678846783^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1525690801 10000000000 9161678846783 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5553557917/10000000000 : ℝ)^4799 ≤ (47346094164601/100000000000000 : ℝ)^3775 := by
    have hnat : (5553557917 : ℕ)^4799*100000000000000^3775 ≤ 47346094164601^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5553557917 10000000000 47346094164601 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5194772929/10000000000 : ℝ)^4799 ≤ (43492226975261/100000000000000 : ℝ)^3775 := by
    have hnat : (5194772929 : ℕ)^4799*100000000000000^3775 ≤ 43492226975261^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5194772929 10000000000 43492226975261 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1525690801/10000000000 : ℝ), (5553557917/10000000000 : ℝ), (5194772929/10000000000 : ℝ)] ![(9161678846783/100000000000000 : ℝ), (47346094164601/100000000000000 : ℝ), (43492226975261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1525690801/10000000000 : ℝ)|^4799 ≤ (9161678846783/100000000000000 : ℝ)^3775
        have hw : |(-1525690801/10000000000 : ℝ)|=(1525690801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5553557917/10000000000 : ℝ)|^4799 ≤ (47346094164601/100000000000000 : ℝ)^3775
        have hw : |(5553557917/10000000000 : ℝ)|=(5553557917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5194772929/10000000000 : ℝ)|^4799 ≤ (43492226975261/100000000000000 : ℝ)^3775
        have hw : |(5194772929/10000000000 : ℝ)|=(5194772929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_box_13 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (337713049/625000000 : ℝ)*x 0 + (-1734326783/10000000000 : ℝ)*x 1 + (1298693149/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (337713049/625000000 : ℝ)^4799 ≤ (22862397066409/50000000000000 : ℝ)^3775 := by
    have hnat : (337713049 : ℕ)^4799*50000000000000^3775 ≤ 22862397066409^3775*625000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337713049 625000000 22862397066409 50000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1734326783/10000000000 : ℝ)^4799 ≤ (10782982424153/100000000000000 : ℝ)^3775 := by
    have hnat : (1734326783 : ℕ)^4799*100000000000000^3775 ≤ 10782982424153^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1734326783 10000000000 10782982424153 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1298693149/2500000000 : ℝ)^4799 ≤ (43492223431021/100000000000000 : ℝ)^3775 := by
    have hnat : (1298693149 : ℕ)^4799*100000000000000^3775 ≤ 43492223431021^3775*2500000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298693149 2500000000 43492223431021 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(337713049/625000000 : ℝ), (-1734326783/10000000000 : ℝ), (1298693149/2500000000 : ℝ)] ![(22862397066409/50000000000000 : ℝ), (10782982424153/100000000000000 : ℝ), (43492223431021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(337713049/625000000 : ℝ)|^4799 ≤ (22862397066409/50000000000000 : ℝ)^3775
        have hw : |(337713049/625000000 : ℝ)|=(337713049/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1734326783/10000000000 : ℝ)|^4799 ≤ (10782982424153/100000000000000 : ℝ)^3775
        have hw : |(-1734326783/10000000000 : ℝ)|=(1734326783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1298693149/2500000000 : ℝ)|^4799 ≤ (43492223431021/100000000000000 : ℝ)^3775
        have hw : |(1298693149/2500000000 : ℝ)|=(1298693149/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_box_14 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (675426079/1250000000 : ℝ)*x 0 + (2597386347/5000000000 : ℝ)*x 1 + (-867163429/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (675426079/1250000000 : ℝ)^4799 ≤ (22862396248827/50000000000000 : ℝ)^3775 := by
    have hnat : (675426079 : ℕ)^4799*50000000000000^3775 ≤ 22862396248827^3775*1250000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675426079 1250000000 22862396248827 50000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2597386347/5000000000 : ℝ)^4799 ≤ (4349222447407/10000000000000 : ℝ)^3775 := by
    have hnat : (2597386347 : ℕ)^4799*10000000000000^3775 ≤ 4349222447407^3775*5000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597386347 5000000000 4349222447407 10000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (867163429/5000000000 : ℝ)^4799 ≤ (5391491508473/50000000000000 : ℝ)^3775 := by
    have hnat : (867163429 : ℕ)^4799*50000000000000^3775 ≤ 5391491508473^3775*5000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      867163429 5000000000 5391491508473 50000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(675426079/1250000000 : ℝ), (2597386347/5000000000 : ℝ), (-867163429/5000000000 : ℝ)] ![(22862396248827/50000000000000 : ℝ), (4349222447407/10000000000000 : ℝ), (5391491508473/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(675426079/1250000000 : ℝ)|^4799 ≤ (22862396248827/50000000000000 : ℝ)^3775
        have hw : |(675426079/1250000000 : ℝ)|=(675426079/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2597386347/5000000000 : ℝ)|^4799 ≤ (4349222447407/10000000000000 : ℝ)^3775
        have hw : |(2597386347/5000000000 : ℝ)|=(2597386347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-867163429/5000000000 : ℝ)|^4799 ≤ (5391491508473/50000000000000 : ℝ)^3775
        have hw : |(-867163429/5000000000 : ℝ)|=(867163429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_box_15 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3861944019/10000000000 : ℝ)*x 0 + (1096727883/2500000000 : ℝ)*x 1 + (4386912031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3861944019/10000000000 : ℝ)^4799 ≤ (14917418661551/50000000000000 : ℝ)^3775 := by
    have hnat : (3861944019 : ℕ)^4799*50000000000000^3775 ≤ 14917418661551^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3861944019 10000000000 14917418661551 50000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1096727883/2500000000 : ℝ)^4799 ≤ (8770644698881/25000000000000 : ℝ)^3775 := by
    have hnat : (1096727883 : ℕ)^4799*25000000000000^3775 ≤ 8770644698881^3775*2500000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096727883 2500000000 8770644698881 25000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4386912031/10000000000 : ℝ)^4799 ≤ (8770645967137/25000000000000 : ℝ)^3775 := by
    have hnat : (4386912031 : ℕ)^4799*25000000000000^3775 ≤ 8770645967137^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4386912031 10000000000 8770645967137 25000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3861944019/10000000000 : ℝ), (1096727883/2500000000 : ℝ), (4386912031/10000000000 : ℝ)] ![(14917418661551/50000000000000 : ℝ), (8770644698881/25000000000000 : ℝ), (8770645967137/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3861944019/10000000000 : ℝ)|^4799 ≤ (14917418661551/50000000000000 : ℝ)^3775
        have hw : |(3861944019/10000000000 : ℝ)|=(3861944019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1096727883/2500000000 : ℝ)|^4799 ≤ (8770644698881/25000000000000 : ℝ)^3775
        have hw : |(1096727883/2500000000 : ℝ)|=(1096727883/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4386912031/10000000000 : ℝ)|^4799 ≤ (8770645967137/25000000000000 : ℝ)^3775
        have hw : |(4386912031/10000000000 : ℝ)|=(4386912031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1620_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43621613/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16323/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (21/200 : ℝ)*pair X i i ≤ pair X i h) :
    -(8119/12500 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29151/50000 : ℝ) ∧ (80631/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (43963/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16323/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (21/200 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16323/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (21/200 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16323/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (21/200 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16323/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (21/200 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16323/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (21/200 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16323/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (21/200 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (21/200 : ℝ) ^ (4795/1024 : ℝ) ≤ (104391269687579/4000000000000000000 : ℝ) := by
    have hpowers : (21/200 : ℝ)^4795 ≤ (104391269687579/4000000000000000000 : ℝ)^1024 := by
      have hnat : (21 : ℕ)^4795*4000000000000000000^1024 ≤ 104391269687579^1024*200^4795 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21 200 104391269687579 4000000000000000000 4795 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21/200 : ℝ)) (X := (104391269687579/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4795 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16323/100000 : ℝ) ^ (4795/1024 : ℝ) ≤ (20598882451068987/100000000000000000000 : ℝ) := by
    have hpowers : (16323/100000 : ℝ)^4795 ≤ (20598882451068987/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16323 : ℕ)^4795*100000000000000000000^1024 ≤ 20598882451068987^1024*100000^4795 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16323 100000 20598882451068987 100000000000000000000 4795 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16323/100000 : ℝ)) (X := (20598882451068987/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4795 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000104391269687579/2000000000000000000 : ℝ) ≤ (10000111464511189/10000000000000000 : ℝ) ^ (4795/1024 : ℝ) := by
    have hpowers : (2000104391269687579/2000000000000000000 : ℝ)^1024 ≤ (10000111464511189/10000000000000000 : ℝ)^4795 := by
      have hnat : (2000104391269687579 : ℕ)^1024*10000000000000000^4795 ≤ 10000111464511189^4795*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000104391269687579 2000000000000000000 10000111464511189 10000000000000000 1024 4795 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000111464511189/10000000000000000 : ℝ)) (X := (2000104391269687579/2000000000000000000 : ℝ)) (by norm_num) 4795 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50011604332096629231/50000000000000000000 : ℝ) ≤ (2000099117845841/2000000000000000 : ℝ) ^ (4795/1024 : ℝ) := by
    have hpowers : (50011604332096629231/50000000000000000000 : ℝ)^1024 ≤ (2000099117845841/2000000000000000 : ℝ)^4795 := by
      have hnat : (50011604332096629231 : ℕ)^1024*2000000000000000^4795 ≤ 2000099117845841^4795*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50011604332096629231 50000000000000000000 2000099117845841 2000000000000000 1024 4795 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000099117845841/2000000000000000 : ℝ)) (X := (50011604332096629231/50000000000000000000 : ℝ)) (by norm_num) 4795 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50020598882451068987/50000000000000000000 : ℝ) ≤ (10000879713947221/10000000000000000 : ℝ) ^ (4795/1024 : ℝ) := by
    have hpowers : (50020598882451068987/50000000000000000000 : ℝ)^1024 ≤ (10000879713947221/10000000000000000 : ℝ)^4795 := by
      have hnat : (50020598882451068987 : ℕ)^1024*10000000000000000^4795 ≤ 10000879713947221^4795*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020598882451068987 50000000000000000000 10000879713947221 10000000000000000 1024 4795 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000879713947221/10000000000000000 : ℝ)) (X := (50020598882451068987/50000000000000000000 : ℝ)) (by norm_num) 4795 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(104391269687579/4000000000000000000 : ℝ) ≤ ((6469175826530035283/6470000000000000000 : ℝ)+2*(666883191/1010937500000 : ℝ)*(21/200 : ℝ))^(4795/1024 : ℝ) := by
    rw [show (6469175826530035283/6470000000000000000 : ℝ)+2*(666883191/1010937500000 : ℝ)*(21/200 : ℝ)=(10000111464511189/10000000000000000 : ℝ) by norm_num, show 1+2*(104391269687579/4000000000000000000 : ℝ)=(2000104391269687579/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(20598882451068987/100000000000000000000 : ℝ)+(104391269687579/4000000000000000000 : ℝ) ≤ ((6469175826530035283/6470000000000000000 : ℝ)+(666883191/1010937500000 : ℝ)*((16323/100000 : ℝ)+(21/200 : ℝ)))^(4795/1024 : ℝ) := by
    rw [show (6469175826530035283/6470000000000000000 : ℝ)+(666883191/1010937500000 : ℝ)*((16323/100000 : ℝ)+(21/200 : ℝ))=(2000099117845841/2000000000000000 : ℝ) by norm_num, show 1+(20598882451068987/100000000000000000000 : ℝ)+(104391269687579/4000000000000000000 : ℝ)=(50011604332096629231/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(20598882451068987/100000000000000000000 : ℝ) ≤ ((6469175826530035283/6470000000000000000 : ℝ)+2*(666883191/1010937500000 : ℝ)*(16323/100000 : ℝ))^(4795/1024 : ℝ) := by
    rw [show (6469175826530035283/6470000000000000000 : ℝ)+2*(666883191/1010937500000 : ℝ)*(16323/100000 : ℝ)=(10000879713947221/10000000000000000 : ℝ) by norm_num, show 1+2*(20598882451068987/100000000000000000000 : ℝ)=(50020598882451068987/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6469175826530035283/6470000000000000000 : ℝ)*(X 1 0+X 2 0)+(666883191/1010937500000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4795/1024 : ℝ)) (lo := (21/200 : ℝ)) (hi := (16323/100000 : ℝ)) (c := (6469175826530035283/6470000000000000000 : ℝ)) (alpha := (666883191/1010937500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6469175826530035283/6470000000000000000 : ℝ)*(X 0 1+X 2 1)+(666883191/1010937500000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4795/1024 : ℝ)) (lo := (21/200 : ℝ)) (hi := (16323/100000 : ℝ)) (c := (6469175826530035283/6470000000000000000 : ℝ)) (alpha := (666883191/1010937500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6469175826530035283/6470000000000000000 : ℝ)*(X 0 2+X 1 2)+(666883191/1010937500000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4795/1024 : ℝ)) (lo := (21/200 : ℝ)) (hi := (16323/100000 : ℝ)) (c := (6469175826530035283/6470000000000000000 : ℝ)) (alpha := (666883191/1010937500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1410179577/10000000000 : ℝ)*X 0 0+(54155501/100000000 : ℝ)*X 0 1+(2707774809/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1050248097/2000000000 : ℝ)*X 1 0+(-820477653/5000000000 : ℝ)*X 1 1+(5415549591/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1050248117/2000000000 : ℝ)*X 2 0+(2707774897/5000000000 : ℝ)*X 2 1+(-1640954889/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((112084809/250000000 : ℝ)*X 0 0+(4077421749/10000000000 : ℝ)*X 0 1+(4077421597/10000000000 : ℝ)*X 0 2+(112084809/250000000 : ℝ)*X 1 0+(4077421749/10000000000 : ℝ)*X 1 1+(4077421597/10000000000 : ℝ)*X 1 2+(112084809/250000000 : ℝ)*X 2 0+(4077421749/10000000000 : ℝ)*X 2 1+(4077421597/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-489854741/2500000000 : ℝ)*X 0 0+(260731871/500000000 : ℝ)*X 0 1+(208585517/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2694855253/5000000000 : ℝ)*X 1 0+(-863097747/5000000000 : ℝ)*X 1 1+(130365937/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5389710289/10000000000 : ℝ)*X 2 0+(1042927481/2000000000 : ℝ)*X 2 1+(-1726195889/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1959670451/5000000000 : ℝ)*X 0 0+(2179554559/5000000000 : ℝ)*X 0 1+(4359108807/10000000000 : ℝ)*X 0 2+(1959670451/5000000000 : ℝ)*X 1 0+(2179554559/5000000000 : ℝ)*X 1 1+(4359108807/10000000000 : ℝ)*X 1 2+(1959670451/5000000000 : ℝ)*X 2 0+(2179554559/5000000000 : ℝ)*X 2 1+(4359108807/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-368507673/2000000000 : ℝ)*X 0 0+(5070879787/10000000000 : ℝ)*X 0 1+(5445373859/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((40864713/78125000 : ℝ)*X 1 0+(-1627847913/10000000000 : ℝ)*X 1 1+(5445373401/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1046136601/2000000000 : ℝ)*X 2 0+(2722686777/5000000000 : ℝ)*X 2 1+(-325569611/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2282363671/5000000000 : ℝ)*X 0 0+(1008883181/2500000000 : ℝ)*X 0 1+(1008883221/2500000000 : ℝ)*X 0 2+(2282363671/5000000000 : ℝ)*X 1 0+(1008883181/2500000000 : ℝ)*X 1 1+(1008883221/2500000000 : ℝ)*X 1 2+(2282363671/5000000000 : ℝ)*X 2 0+(1008883181/2500000000 : ℝ)*X 2 1+(1008883221/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1525690801/10000000000 : ℝ)*X 0 0+(5553557917/10000000000 : ℝ)*X 0 1+(5194772929/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((337713049/625000000 : ℝ)*X 1 0+(-1734326783/10000000000 : ℝ)*X 1 1+(1298693149/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((675426079/1250000000 : ℝ)*X 2 0+(2597386347/5000000000 : ℝ)*X 2 1+(-867163429/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3861944019/10000000000 : ℝ)*X 0 0+(1096727883/2500000000 : ℝ)*X 0 1+(4386912031/10000000000 : ℝ)*X 0 2+(3861944019/10000000000 : ℝ)*X 1 0+(1096727883/2500000000 : ℝ)*X 1 1+(4386912031/10000000000 : ℝ)*X 1 2+(3861944019/10000000000 : ℝ)*X 2 0+(1096727883/2500000000 : ℝ)*X 2 1+(4386912031/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-8119/12500 : ℝ) ≤ (-26264149031272777802539511446443/40437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (92011087/100000000000000 : ℝ)*(lower0) + (3924799/100000000000000 : ℝ)*(lower3) + (58233993/50000000000000 : ℝ)*(lower4) + (212661704851831/12500000000000 : ℝ)*(major0) + (212661704851831/12500000000000 : ℝ)*(major1) + (212661704851831/12500000000000 : ℝ)*(major2) + (495036169/10000000000000 : ℝ)*(sp1) + (9523226603/100000000000000 : ℝ)*(sp2) + (612301343649023/25000000000000 : ℝ)*(sp4) + (2449203246386579/100000000000000 : ℝ)*(sp5) + (1224599336760833/50000000000000 : ℝ)*(sp6) + (243754550753229/25000000000000 : ℝ)*(sp7) + (176384511/6250000000000 : ℝ)*(sp12) + (10871917583/100000000000000 : ℝ)*(sp15) + (975029074930499/100000000000000 : ℝ)*(f.failure) + (612302049187067/25000000000000 : ℝ)*(f.sum) + (6994510743423/3235000000000000000000000000 : ℝ)*base66 + (139277491314946827/80875000000000000000000000000000 : ℝ)*base68 + (128808191266321827/80875000000000000000000000000000 : ℝ)*base70 + (622863056074821827/80875000000000000000000000000000 : ℝ)*base72 + (4336817262911/1617500000000000000000000000 : ℝ)*base73 + (670728687214071827/80875000000000000000000000000000 : ℝ)*base76 + (593358691879196827/80875000000000000000000000000000 : ℝ)*base78 + (297869037884946827/80875000000000000000000000000000 : ℝ)*base80 + (524001555961/404375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (29274887/2500000000000000000000 : ℝ)*base89 + (29274887/2500000000000000000000 : ℝ)*base91 + (29274887/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (29151/50000 : ℝ) ≤ (1886155348174328604933780453/3235000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12593783/50000000000000 : ℝ)*(upper0) + (6185323/50000000000000 : ℝ)*(lower1) + (21936467/20000000000000 : ℝ)*(upper4) + (1787483845727463/100000000000000 : ℝ)*(major0) + (1787483845727463/100000000000000 : ℝ)*(major1) + (1787483845727463/100000000000000 : ℝ)*(major2) + (316387884827967/12500000000000 : ℝ)*(sp0) + (253109663920027/10000000000000 : ℝ)*(sp1) + (2531102709416169/100000000000000 : ℝ)*(sp2) + (512210598676991/50000000000000 : ℝ)*(sp3) + (70637199/1562500000000 : ℝ)*(sp6) + (876277613/20000000000000 : ℝ)*(sp7) + (415157317/10000000000000 : ℝ)*(sp8) + (2118199327/20000000000000 : ℝ)*(sp9) + (512212789371023/50000000000000 : ℝ)*(f.failure) + (506221446039381/20000000000000 : ℝ)*(f.sum) + (918988998967/808750000000000000000000000 : ℝ)*base66 + (4508118488402722971/647000000000000000000000000000000 : ℝ)*base68 + (3028179752225722971/647000000000000000000000000000000 : ℝ)*base70 + (2424266426783277029/647000000000000000000000000000000 : ℝ)*base71 + (50160707441343/3235000000000000000000000000 : ℝ)*base74 + (2166713083205277029/647000000000000000000000000000000 : ℝ)*base75 + (1247720232370277029/647000000000000000000000000000000 : ℝ)*base77 + (9862406375174722971/647000000000000000000000000000000 : ℝ)*base80 + (11521142957/808750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (8779901/1250000000000000000000 : ℝ)*base90 + (8779901/1250000000000000000000 : ℝ)*base92 + (8779901/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (80631/100000 : ℝ) ≤ (2608501621146858267469935921/3235000000000000000000000000 : ℝ) := by norm_num
    linear_combination (54062329/100000000000000 : ℝ)*(upper2) + (28351651/100000000000000 : ℝ)*(lower3) + (7345751/100000000000000 : ℝ)*(lower4) + (10775827/20000000000000 : ℝ)*(lower5) + (1890230153771863/100000000000000 : ℝ)*(major0) + (1890230153771863/100000000000000 : ℝ)*(major1) + (1890230153771863/100000000000000 : ℝ)*(major2) + (754170739/20000000000000 : ℝ)*(sp2) + (3158900733/50000000000000 : ℝ)*(sp3) + (4071615423/100000000000000 : ℝ)*(sp4) + (1335133882483131/50000000000000 : ℝ)*(sp8) + (667567959145421/25000000000000 : ℝ)*(sp9) + (267026806572799/10000000000000 : ℝ)*(sp10) + (541652119232799/50000000000000 : ℝ)*(sp11) + (135413819533383/12500000000000 : ℝ)*(f.failure) + (667567959145421/25000000000000 : ℝ)*(f.sum) + (8843539060961/1617500000000000000000000000 : ℝ)*base65 + (362112519373842229/647000000000000000000000000000000 : ℝ)*base67 + (2737121212195157771/647000000000000000000000000000000 : ℝ)*base70 + (14223939348609842229/647000000000000000000000000000000 : ℝ)*base71 + (5527674466889/1617500000000000000000000000 : ℝ)*base74 + (3140922344507842229/647000000000000000000000000000000 : ℝ)*base75 + (2636418013393157771/647000000000000000000000000000000 : ℝ)*base78 + (1143644392718157771/647000000000000000000000000000000 : ℝ)*base80 + (17549850937003/3235000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (1931779/312500000000000000000 : ℝ)*base89 + (1931779/312500000000000000000 : ℝ)*base91 + (1931779/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-43963/50000 : ℝ) ≤ (-142216314990493809469490662905009/161750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3370463/50000000000000 : ℝ)*(upper3) + (30474143/50000000000000 : ℝ)*(lower4) + (26068697/50000000000000 : ℝ)*(upper5) + (1932790566664841/100000000000000 : ℝ)*(major0) + (1932790566664841/100000000000000 : ℝ)*(major1) + (1932790566664841/100000000000000 : ℝ)*(major2) + (2784691/160000000000 : ℝ)*(sp4) + (12964033331/25000000000000 : ℝ)*(sp5) + (32710898739/50000000000000 : ℝ)*(sp6) + (6225059137/20000000000000 : ℝ)*(sp7) + (2787184865854867/100000000000000 : ℝ)*(sp12) + (1393567375076709/50000000000000 : ℝ)*(sp13) + (174195074030579/6250000000000 : ℝ)*(sp14) + (110767124615539/10000000000000 : ℝ)*(sp15) + (44308094858043/4000000000000 : ℝ)*(f.failure) + (1393593303143371/50000000000000 : ℝ)*(f.sum) + (816544444171/3235000000000000000000000000 : ℝ)*base66 + (786481622099014997/647000000000000000000000000000000 : ℝ)*base68 + (1607455998362985003/647000000000000000000000000000000 : ℝ)*base69 + (5116268835611985003/647000000000000000000000000000000 : ℝ)*base71 + (674984979913/101093750000000000000000000 : ℝ)*base74 + (933824294352985003/647000000000000000000000000000000 : ℝ)*base75 + (2145599175513985003/647000000000000000000000000000000 : ℝ)*base77 + (3004791336151985003/647000000000000000000000000000000 : ℝ)*base79 + (12318296175901/3235000000000000000000000000 : ℝ)*base82 + (683359/100000000000000000000 : ℝ)*base89 + (683359/100000000000000000000 : ℝ)*base91 + (683359/100000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1620_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43621613/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16323/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (21/200 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(8119/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(29151/50000 : ℝ) else (80631/100000 : ℝ) ≤ X j i ∧ X j i ≤ (43963/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1620_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1620_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43621613/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16323/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (21/200 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(8119/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(29151/50000 : ℝ) else (80631/100000 : ℝ) ≤ X j i ∧ X j i ≤ (43963/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1620_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43621613/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16323/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (21/200 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(8119/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(29151/50000 : ℝ) else (80631/100000 : ℝ) ≤ X j i ∧ X j i ≤ (43963/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1620_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
