-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1612_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:51:46.773994+00:00
-- url     : https://prove2.me/submissions/af5827e7-838e-4100-9b1a-4654b7eaed84

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
theorem support_rectangle_w1612_s3_0 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1699151827/10000000000 : ℝ)*x 0 + (5459372279/10000000000 : ℝ)*x 1 + (1295133253/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1699151827/10000000000 : ℝ)^4767 ≤ (5231318438581/50000000000000 : ℝ)^3743 := by
    have hnat : (1699151827 : ℕ)^4767*50000000000000^3743 ≤ 5231318438581^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1699151827 10000000000 5231318438581 50000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5459372279/10000000000 : ℝ)^4767 ≤ (46262693107211/100000000000000 : ℝ)^3743 := by
    have hnat : (5459372279 : ℕ)^4767*100000000000000^3743 ≤ 46262693107211^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5459372279 10000000000 46262693107211 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1295133253/2500000000 : ℝ)^4767 ≤ (4327467000693/10000000000000 : ℝ)^3743 := by
    have hnat : (1295133253 : ℕ)^4767*10000000000000^3743 ≤ 4327467000693^3743*2500000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295133253 2500000000 4327467000693 10000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1699151827/10000000000 : ℝ), (5459372279/10000000000 : ℝ), (1295133253/2500000000 : ℝ)] ![(5231318438581/50000000000000 : ℝ), (46262693107211/100000000000000 : ℝ), (4327467000693/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1699151827/10000000000 : ℝ)|^4767 ≤ (5231318438581/50000000000000 : ℝ)^3743
        have hw : |(-1699151827/10000000000 : ℝ)|=(1699151827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5459372279/10000000000 : ℝ)|^4767 ≤ (46262693107211/100000000000000 : ℝ)^3743
        have hw : |(5459372279/10000000000 : ℝ)|=(5459372279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1295133253/2500000000 : ℝ)|^4767 ≤ (4327467000693/10000000000000 : ℝ)^3743
        have hw : |(1295133253/2500000000 : ℝ)|=(1295133253/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1612_s3_1 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676711797/5000000000 : ℝ)*x 0 + (-1842937281/10000000000 : ℝ)*x 1 + (2590266507/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676711797/5000000000 : ℝ)^4767 ≤ (45122314145119/100000000000000 : ℝ)^3743 := by
    have hnat : (2676711797 : ℕ)^4767*100000000000000^3743 ≤ 45122314145119^3743*5000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676711797 5000000000 45122314145119 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1842937281/10000000000 : ℝ)^4767 ≤ (11603015805383/100000000000000 : ℝ)^3743 := by
    have hnat : (1842937281 : ℕ)^4767*100000000000000^3743 ≤ 11603015805383^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1842937281 10000000000 11603015805383 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2590266507/5000000000 : ℝ)^4767 ≤ (2704666876763/6250000000000 : ℝ)^3743 := by
    have hnat : (2590266507 : ℕ)^4767*6250000000000^3743 ≤ 2704666876763^3743*5000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590266507 5000000000 2704666876763 6250000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676711797/5000000000 : ℝ), (-1842937281/10000000000 : ℝ), (2590266507/5000000000 : ℝ)] ![(45122314145119/100000000000000 : ℝ), (11603015805383/100000000000000 : ℝ), (2704666876763/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676711797/5000000000 : ℝ)|^4767 ≤ (45122314145119/100000000000000 : ℝ)^3743
        have hw : |(2676711797/5000000000 : ℝ)|=(2676711797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1842937281/10000000000 : ℝ)|^4767 ≤ (11603015805383/100000000000000 : ℝ)^3743
        have hw : |(-1842937281/10000000000 : ℝ)|=(1842937281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2590266507/5000000000 : ℝ)|^4767 ≤ (2704666876763/6250000000000 : ℝ)^3743
        have hw : |(2590266507/5000000000 : ℝ)|=(2590266507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1612_s3_2 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669177971/1250000000 : ℝ)*x 0 + (103610657/200000000 : ℝ)*x 1 + (-1842937267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669177971/1250000000 : ℝ)^4767 ≤ (5640289501617/12500000000000 : ℝ)^3743 := by
    have hnat : (669177971 : ℕ)^4767*12500000000000^3743 ≤ 5640289501617^3743*1250000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669177971 1250000000 5640289501617 12500000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (103610657/200000000 : ℝ)^4767 ≤ (43274668283477/100000000000000 : ℝ)^3743 := by
    have hnat : (103610657 : ℕ)^4767*100000000000000^3743 ≤ 43274668283477^3743*200000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103610657 200000000 43274668283477 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1842937267/10000000000 : ℝ)^4767 ≤ (5801507846563/50000000000000 : ℝ)^3743 := by
    have hnat : (1842937267 : ℕ)^4767*50000000000000^3743 ≤ 5801507846563^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1842937267 10000000000 5801507846563 50000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669177971/1250000000 : ℝ), (103610657/200000000 : ℝ), (-1842937267/10000000000 : ℝ)] ![(5640289501617/12500000000000 : ℝ), (43274668283477/100000000000000 : ℝ), (5801507846563/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669177971/1250000000 : ℝ)|^4767 ≤ (5640289501617/12500000000000 : ℝ)^3743
        have hw : |(669177971/1250000000 : ℝ)|=(669177971/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(103610657/200000000 : ℝ)|^4767 ≤ (43274668283477/100000000000000 : ℝ)^3743
        have hw : |(103610657/200000000 : ℝ)|=(103610657/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1842937267/10000000000 : ℝ)|^4767 ≤ (5801507846563/50000000000000 : ℝ)^3743
        have hw : |(-1842937267/10000000000 : ℝ)|=(1842937267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1612_s3_3 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (842165831/2000000000 : ℝ)*x 0 + (121190041/312500000 : ℝ)*x 1 + (456508939/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (842165831/2000000000 : ℝ)^4767 ≤ (33235568557639/100000000000000 : ℝ)^3743 := by
    have hnat : (842165831 : ℕ)^4767*100000000000000^3743 ≤ 33235568557639^3743*2000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      842165831 2000000000 33235568557639 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (121190041/312500000 : ℝ)^4767 ≤ (2992759496999/10000000000000 : ℝ)^3743 := by
    have hnat : (121190041 : ℕ)^4767*10000000000000^3743 ≤ 2992759496999^3743*312500000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121190041 312500000 2992759496999 10000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (456508939/1000000000 : ℝ)^4767 ≤ (736736729187/2000000000000 : ℝ)^3743 := by
    have hnat : (456508939 : ℕ)^4767*2000000000000^3743 ≤ 736736729187^3743*1000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      456508939 1000000000 736736729187 2000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(842165831/2000000000 : ℝ), (121190041/312500000 : ℝ), (456508939/1000000000 : ℝ)] ![(33235568557639/100000000000000 : ℝ), (2992759496999/10000000000000 : ℝ), (736736729187/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(842165831/2000000000 : ℝ)|^4767 ≤ (33235568557639/100000000000000 : ℝ)^3743
        have hw : |(842165831/2000000000 : ℝ)|=(842165831/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(121190041/312500000 : ℝ)|^4767 ≤ (2992759496999/10000000000000 : ℝ)^3743
        have hw : |(121190041/312500000 : ℝ)|=(121190041/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(456508939/1000000000 : ℝ)|^4767 ≤ (736736729187/2000000000000 : ℝ)^3743
        have hw : |(456508939/1000000000 : ℝ)|=(456508939/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1612_s3_4 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-849611431/5000000000 : ℝ)*x 0 + (5182613821/10000000000 : ℝ)*x 1 + (272863463/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (849611431/5000000000 : ℝ)^4767 ≤ (10463193946377/100000000000000 : ℝ)^3743 := by
    have hnat : (849611431 : ℕ)^4767*100000000000000^3743 ≤ 10463193946377^3743*5000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849611431 5000000000 10463193946377 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5182613821/10000000000 : ℝ)^4767 ≤ (43296808126051/100000000000000 : ℝ)^3743 := by
    have hnat : (5182613821 : ℕ)^4767*100000000000000^3743 ≤ 43296808126051^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182613821 10000000000 43296808126051 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (272863463/500000000 : ℝ)^4767 ≤ (46239997916579/100000000000000 : ℝ)^3743 := by
    have hnat : (272863463 : ℕ)^4767*100000000000000^3743 ≤ 46239997916579^3743*500000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272863463 500000000 46239997916579 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-849611431/5000000000 : ℝ), (5182613821/10000000000 : ℝ), (272863463/500000000 : ℝ)] ![(10463193946377/100000000000000 : ℝ), (43296808126051/100000000000000 : ℝ), (46239997916579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-849611431/5000000000 : ℝ)|^4767 ≤ (10463193946377/100000000000000 : ℝ)^3743
        have hw : |(-849611431/5000000000 : ℝ)|=(849611431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5182613821/10000000000 : ℝ)|^4767 ≤ (43296808126051/100000000000000 : ℝ)^3743
        have hw : |(5182613821/10000000000 : ℝ)|=(5182613821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(272863463/500000000 : ℝ)|^4767 ≤ (46239997916579/100000000000000 : ℝ)^3743
        have hw : |(272863463/500000000 : ℝ)|=(272863463/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1612_s3_5 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279343369/10000000000 : ℝ)*x 0 + (-313240273/2000000000 : ℝ)*x 1 + (682158637/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279343369/10000000000 : ℝ)^4767 ≤ (44328604321957/100000000000000 : ℝ)^3743 := by
    have hnat : (5279343369 : ℕ)^4767*100000000000000^3743 ≤ 44328604321957^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279343369 10000000000 44328604321957 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (313240273/2000000000 : ℝ)^4767 ≤ (9431399519659/100000000000000 : ℝ)^3743 := by
    have hnat : (313240273 : ℕ)^4767*100000000000000^3743 ≤ 9431399519659^3743*2000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      313240273 2000000000 9431399519659 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (682158637/1250000000 : ℝ)^4767 ≤ (4623999614683/10000000000000 : ℝ)^3743 := by
    have hnat : (682158637 : ℕ)^4767*10000000000000^3743 ≤ 4623999614683^3743*1250000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682158637 1250000000 4623999614683 10000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279343369/10000000000 : ℝ), (-313240273/2000000000 : ℝ), (682158637/1250000000 : ℝ)] ![(44328604321957/100000000000000 : ℝ), (9431399519659/100000000000000 : ℝ), (4623999614683/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279343369/10000000000 : ℝ)|^4767 ≤ (44328604321957/100000000000000 : ℝ)^3743
        have hw : |(5279343369/10000000000 : ℝ)|=(5279343369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-313240273/2000000000 : ℝ)|^4767 ≤ (9431399519659/100000000000000 : ℝ)^3743
        have hw : |(-313240273/2000000000 : ℝ)|=(313240273/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(682158637/1250000000 : ℝ)|^4767 ≤ (4623999614683/10000000000000 : ℝ)^3743
        have hw : |(682158637/1250000000 : ℝ)|=(682158637/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1612_s3_6 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319835899/2500000000 : ℝ)*x 0 + (2728634363/5000000000 : ℝ)*x 1 + (-1566201569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319835899/2500000000 : ℝ)^4767 ≤ (8865721349887/20000000000000 : ℝ)^3743 := by
    have hnat : (1319835899 : ℕ)^4767*20000000000000^3743 ≤ 8865721349887^3743*2500000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319835899 2500000000 8865721349887 20000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2728634363/5000000000 : ℝ)^4767 ≤ (5779999019263/12500000000000 : ℝ)^3743 := by
    have hnat : (2728634363 : ℕ)^4767*12500000000000^3743 ≤ 5779999019263^3743*5000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728634363 5000000000 5779999019263 12500000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1566201569/10000000000 : ℝ)^4767 ≤ (943140108419/10000000000000 : ℝ)^3743 := by
    have hnat : (1566201569 : ℕ)^4767*10000000000000^3743 ≤ 943140108419^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1566201569 10000000000 943140108419 10000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319835899/2500000000 : ℝ), (2728634363/5000000000 : ℝ), (-1566201569/10000000000 : ℝ)] ![(8865721349887/20000000000000 : ℝ), (5779999019263/12500000000000 : ℝ), (943140108419/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319835899/2500000000 : ℝ)|^4767 ≤ (8865721349887/20000000000000 : ℝ)^3743
        have hw : |(1319835899/2500000000 : ℝ)|=(1319835899/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2728634363/5000000000 : ℝ)|^4767 ≤ (5779999019263/12500000000000 : ℝ)^3743
        have hw : |(2728634363/5000000000 : ℝ)|=(2728634363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1566201569/10000000000 : ℝ)|^4767 ≤ (943140108419/10000000000000 : ℝ)^3743
        have hw : |(-1566201569/10000000000 : ℝ)|=(1566201569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1612_s3_7 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (526375471/1250000000 : ℝ)*x 0 + (911992221/2000000000 : ℝ)*x 1 + (3883263239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (526375471/1250000000 : ℝ)^4767 ≤ (33237323811163/100000000000000 : ℝ)^3743 := by
    have hnat : (526375471 : ℕ)^4767*100000000000000^3743 ≤ 33237323811163^3743*1250000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526375471 1250000000 33237323811163 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (911992221/2000000000 : ℝ)^4767 ≤ (4598017768113/12500000000000 : ℝ)^3743 := by
    have hnat : (911992221 : ℕ)^4767*12500000000000^3743 ≤ 4598017768113^3743*2000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      911992221 2000000000 4598017768113 12500000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3883263239/10000000000 : ℝ)^4767 ≤ (1873658376453/6250000000000 : ℝ)^3743 := by
    have hnat : (3883263239 : ℕ)^4767*6250000000000^3743 ≤ 1873658376453^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3883263239 10000000000 1873658376453 6250000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(526375471/1250000000 : ℝ), (911992221/2000000000 : ℝ), (3883263239/10000000000 : ℝ)] ![(33237323811163/100000000000000 : ℝ), (4598017768113/12500000000000 : ℝ), (1873658376453/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(526375471/1250000000 : ℝ)|^4767 ≤ (33237323811163/100000000000000 : ℝ)^3743
        have hw : |(526375471/1250000000 : ℝ)|=(526375471/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(911992221/2000000000 : ℝ)|^4767 ≤ (4598017768113/12500000000000 : ℝ)^3743
        have hw : |(911992221/2000000000 : ℝ)|=(911992221/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3883263239/10000000000 : ℝ)|^4767 ≤ (1873658376453/6250000000000 : ℝ)^3743
        have hw : |(3883263239/10000000000 : ℝ)|=(3883263239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1612_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (173190687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3297/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2579/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10437/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (327/2000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3297/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2579/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3297/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2579/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3297/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2579/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3297/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2579/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3297/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2579/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3297/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2579/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2579/25000 : ℝ) ^ (4763/1024 : ℝ) ≤ (1289582081249743/50000000000000000000 : ℝ) := by
    have hpowers : (2579/25000 : ℝ)^4763 ≤ (1289582081249743/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2579 : ℕ)^4763*50000000000000000000^1024 ≤ 1289582081249743^1024*25000^4763 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2579 25000 1289582081249743 50000000000000000000 4763 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2579/25000 : ℝ)) (X := (1289582081249743/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4763 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3297/20000 : ℝ) ^ (4763/1024 : ℝ) ≤ (2282407775565009/10000000000000000000 : ℝ) := by
    have hpowers : (3297/20000 : ℝ)^4763 ≤ (2282407775565009/10000000000000000000 : ℝ)^1024 := by
      have hnat : (3297 : ℕ)^4763*10000000000000000000^1024 ≤ 2282407775565009^1024*20000^4763 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3297 20000 2282407775565009 10000000000000000000 4763 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3297/20000 : ℝ)) (X := (2282407775565009/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4763 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001289582081249743/25000000000000000000 : ℝ) ≤ (10000110896940217/10000000000000000 : ℝ) ^ (4763/1024 : ℝ) := by
    have hpowers : (25001289582081249743/25000000000000000000 : ℝ)^1024 ≤ (10000110896940217/10000000000000000 : ℝ)^4763 := by
      have hnat : (25001289582081249743 : ℕ)^1024*10000000000000000^4763 ≤ 10000110896940217^4763*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001289582081249743 25000000000000000000 10000110896940217 10000000000000000 1024 4763 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000110896940217/10000000000000000 : ℝ)) (X := (25001289582081249743/25000000000000000000 : ℝ)) (by norm_num) 4763 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12503175405239768697/12500000000000000000 : ℝ) ≤ (5000273045626663/5000000000000000 : ℝ) ^ (4763/1024 : ℝ) := by
    have hpowers : (12503175405239768697/12500000000000000000 : ℝ)^1024 ≤ (5000273045626663/5000000000000000 : ℝ)^4763 := by
      have hnat : (12503175405239768697 : ℕ)^1024*5000000000000000^4763 ≤ 5000273045626663^4763*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503175405239768697 12500000000000000000 5000273045626663 5000000000000000 1024 4763 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000273045626663/5000000000000000 : ℝ)) (X := (12503175405239768697/12500000000000000000 : ℝ)) (by norm_num) 4763 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5002282407775565009/5000000000000000000 : ℝ) ≤ (2000196257113287/2000000000000000 : ℝ) ^ (4763/1024 : ℝ) := by
    have hpowers : (5002282407775565009/5000000000000000000 : ℝ)^1024 ≤ (2000196257113287/2000000000000000 : ℝ)^4763 := by
      have hnat : (5002282407775565009 : ℕ)^1024*2000000000000000^4763 ≤ 2000196257113287^4763*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002282407775565009 5000000000000000000 2000196257113287 2000000000000000 1024 4763 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000196257113287/2000000000000000 : ℝ)) (X := (5002282407775565009/5000000000000000000 : ℝ)) (by norm_num) 4763 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1289582081249743/50000000000000000000 : ℝ) ≤ ((12336341038831226757/12338000000000000000 : ℝ)+2*(435194313109/616900000000000 : ℝ)*(2579/25000 : ℝ))^(4763/1024 : ℝ) := by
    rw [show (12336341038831226757/12338000000000000000 : ℝ)+2*(435194313109/616900000000000 : ℝ)*(2579/25000 : ℝ)=(10000110896940217/10000000000000000 : ℝ) by norm_num, show 1+2*(1289582081249743/50000000000000000000 : ℝ)=(25001289582081249743/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2282407775565009/10000000000000000000 : ℝ)+(1289582081249743/50000000000000000000 : ℝ) ≤ ((12336341038831226757/12338000000000000000 : ℝ)+(435194313109/616900000000000 : ℝ)*((3297/20000 : ℝ)+(2579/25000 : ℝ)))^(4763/1024 : ℝ) := by
    rw [show (12336341038831226757/12338000000000000000 : ℝ)+(435194313109/616900000000000 : ℝ)*((3297/20000 : ℝ)+(2579/25000 : ℝ))=(5000273045626663/5000000000000000 : ℝ) by norm_num, show 1+(2282407775565009/10000000000000000000 : ℝ)+(1289582081249743/50000000000000000000 : ℝ)=(12503175405239768697/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2282407775565009/10000000000000000000 : ℝ) ≤ ((12336341038831226757/12338000000000000000 : ℝ)+2*(435194313109/616900000000000 : ℝ)*(3297/20000 : ℝ))^(4763/1024 : ℝ) := by
    rw [show (12336341038831226757/12338000000000000000 : ℝ)+2*(435194313109/616900000000000 : ℝ)*(3297/20000 : ℝ)=(2000196257113287/2000000000000000 : ℝ) by norm_num, show 1+2*(2282407775565009/10000000000000000000 : ℝ)=(5002282407775565009/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12336341038831226757/12338000000000000000 : ℝ)*(X 1 0+X 2 0)+(435194313109/616900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4763/1024 : ℝ)) (lo := (2579/25000 : ℝ)) (hi := (3297/20000 : ℝ)) (c := (12336341038831226757/12338000000000000000 : ℝ)) (alpha := (435194313109/616900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12336341038831226757/12338000000000000000 : ℝ)*(X 0 1+X 2 1)+(435194313109/616900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4763/1024 : ℝ)) (lo := (2579/25000 : ℝ)) (hi := (3297/20000 : ℝ)) (c := (12336341038831226757/12338000000000000000 : ℝ)) (alpha := (435194313109/616900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12336341038831226757/12338000000000000000 : ℝ)*(X 0 2+X 1 2)+(435194313109/616900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4763/1024 : ℝ)) (lo := (2579/25000 : ℝ)) (hi := (3297/20000 : ℝ)) (c := (12336341038831226757/12338000000000000000 : ℝ)) (alpha := (435194313109/616900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1699151827/10000000000 : ℝ)*X 0 0+(5459372279/10000000000 : ℝ)*X 0 1+(1295133253/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676711797/5000000000 : ℝ)*X 1 0+(-1842937281/10000000000 : ℝ)*X 1 1+(2590266507/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((669177971/1250000000 : ℝ)*X 2 0+(103610657/200000000 : ℝ)*X 2 1+(-1842937267/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((842165831/2000000000 : ℝ)*X 0 0+(121190041/312500000 : ℝ)*X 0 1+(456508939/1000000000 : ℝ)*X 0 2+(842165831/2000000000 : ℝ)*X 1 0+(121190041/312500000 : ℝ)*X 1 1+(456508939/1000000000 : ℝ)*X 1 2+(842165831/2000000000 : ℝ)*X 2 0+(121190041/312500000 : ℝ)*X 2 1+(456508939/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-849611431/5000000000 : ℝ)*X 0 0+(5182613821/10000000000 : ℝ)*X 0 1+(272863463/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5279343369/10000000000 : ℝ)*X 1 0+(-313240273/2000000000 : ℝ)*X 1 1+(682158637/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1319835899/2500000000 : ℝ)*X 2 0+(2728634363/5000000000 : ℝ)*X 2 1+(-1566201569/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((526375471/1250000000 : ℝ)*X 0 0+(911992221/2000000000 : ℝ)*X 0 1+(3883263239/10000000000 : ℝ)*X 0 2+(526375471/1250000000 : ℝ)*X 1 0+(911992221/2000000000 : ℝ)*X 1 1+(3883263239/10000000000 : ℝ)*X 1 2+(526375471/1250000000 : ℝ)*X 2 0+(911992221/2000000000 : ℝ)*X 2 1+(3883263239/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (883990347604906954907698311/77112500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1730621277/100000000000000 : ℝ)*(base19) + (348479311/20000000000000 : ℝ)*(base23) + (56098413/100000000000000 : ℝ)*(lower2) + (66466879/25000000000000 : ℝ)*(upper3) + (217777069/100000000000000 : ℝ)*(upper5) + (315121263235741/12500000000000 : ℝ)*(major0) + (315121263235741/12500000000000 : ℝ)*(major1) + (315121263235741/12500000000000 : ℝ)*(major2) + (448289442268701/12500000000000 : ℝ)*(sp0) + (179316718281083/5000000000000 : ℝ)*(sp1) + (3586334353846383/100000000000000 : ℝ)*(sp2) + (1455594878102381/100000000000000 : ℝ)*(sp3) + (20558093329/100000000000000 : ℝ)*(sp4) + (8855305021/100000000000000 : ℝ)*(sp7) + (727801866703701/50000000000000 : ℝ)*(f.failure) + (1793168048121469/50000000000000 : ℝ)*(f.sum) + (164508087635347/30845000000000000000000000000 : ℝ)*base65 + (590334774437251937/154225000000000000000000000000000 : ℝ)*base67 + (490804494413176937/154225000000000000000000000000000 : ℝ)*base69 + (27097981173873063/154225000000000000000000000000000 : ℝ)*base72 + (174258505273787/30845000000000000000000000000 : ℝ)*base73 + (752535463718723063/154225000000000000000000000000000 : ℝ)*base76 + (312658693838273063/154225000000000000000000000000000 : ℝ)*base78 + (1542899998230773063/154225000000000000000000000000000 : ℝ)*base80 + (55135359017773/7711250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1632587/5000000000000000000000 : ℝ)*base89 + (1632587/5000000000000000000000 : ℝ)*base91 + (1632587/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1233679729941184226351676927/154225000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (330240691/25000000000000 : ℝ)*(base19) + (71629731/5000000000000 : ℝ)*(base23) + (23367717/100000000000000 : ℝ)*(upper2) + (29109711/20000000000000 : ℝ)*(upper3) + (196775399/50000000000000 : ℝ)*(upper5) + (639836744137979/25000000000000 : ℝ)*(major0) + (639836744137979/25000000000000 : ℝ)*(major1) + (639836744137979/25000000000000 : ℝ)*(major2) + (7133475459/50000000000000 : ℝ)*(sp1) + (7911342487/100000000000000 : ℝ)*(sp2) + (728186243000381/20000000000000 : ℝ)*(sp4) + (3640915627088223/100000000000000 : ℝ)*(sp5) + (1820460935532399/50000000000000 : ℝ)*(sp6) + (1477762471461249/100000000000000 : ℝ)*(sp7) + (1477762471461249/100000000000000 : ℝ)*(f.failure) + (728186243000381/20000000000000 : ℝ)*(f.sum) + (32559483813123/15422500000000000000000000000 : ℝ)*base66 + (4110815867938575897/308450000000000000000000000000000 : ℝ)*base68 + (1764318477024025897/308450000000000000000000000000000 : ℝ)*base70 + (650666846374025897/308450000000000000000000000000000 : ℝ)*base72 + (27706948201849/7711250000000000000000000000 : ℝ)*base74 + (2585450304036025897/308450000000000000000000000000000 : ℝ)*base76 + (3729664729154275897/308450000000000000000000000000000 : ℝ)*base78 + (1814336615514425897/308450000000000000000000000000000 : ℝ)*base80 + (16619949185243/3855625000000000000000000000 : ℝ)*base81 + (8188063/10000000000000000000000 : ℝ)*base89 + (8188063/10000000000000000000000 : ℝ)*base91 + (8188063/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1612_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (173190687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3297/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2579/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10437/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (327/2000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1612_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1612_s4_0 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1699262829/10000000000 : ℝ)*x 0 + (5458817963/10000000000 : ℝ)*x 1 + (647626687/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1699262829/10000000000 : ℝ)^4767 ≤ (10463507377563/100000000000000 : ℝ)^3743 := by
    have hnat : (1699262829 : ℕ)^4767*100000000000000^3743 ≤ 10463507377563^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1699262829 10000000000 10463507377563 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5458817963/10000000000 : ℝ)^4767 ≤ (11564177713099/25000000000000 : ℝ)^3743 := by
    have hnat : (5458817963 : ℕ)^4767*25000000000000^3743 ≤ 11564177713099^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5458817963 10000000000 11564177713099 25000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (647626687/1250000000 : ℝ)^4767 ≤ (5409972718849/12500000000000 : ℝ)^3743 := by
    have hnat : (647626687 : ℕ)^4767*12500000000000^3743 ≤ 5409972718849^3743*1250000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647626687 1250000000 5409972718849 12500000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1699262829/10000000000 : ℝ), (5458817963/10000000000 : ℝ), (647626687/1250000000 : ℝ)] ![(10463507377563/100000000000000 : ℝ), (11564177713099/25000000000000 : ℝ), (5409972718849/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1699262829/10000000000 : ℝ)|^4767 ≤ (10463507377563/100000000000000 : ℝ)^3743
        have hw : |(-1699262829/10000000000 : ℝ)|=(1699262829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5458817963/10000000000 : ℝ)|^4767 ≤ (11564177713099/25000000000000 : ℝ)^3743
        have hw : |(5458817963/10000000000 : ℝ)|=(5458817963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(647626687/1250000000 : ℝ)|^4767 ≤ (5409972718849/12500000000000 : ℝ)^3743
        have hw : |(647626687/1250000000 : ℝ)|=(647626687/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1612_s4_1 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669159393/1250000000 : ℝ)*x 0 + (-1842498421/10000000000 : ℝ)*x 1 + (2590506779/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669159393/1250000000 : ℝ)^4767 ≤ (22560360301337/50000000000000 : ℝ)^3743 := by
    have hnat : (669159393 : ℕ)^4767*50000000000000^3743 ≤ 22560360301337^3743*1250000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669159393 1250000000 22560360301337 50000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1842498421/10000000000 : ℝ)^4767 ≤ (2899874245429/25000000000000 : ℝ)^3743 := by
    have hnat : (1842498421 : ℕ)^4767*25000000000000^3743 ≤ 2899874245429^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1842498421 10000000000 2899874245429 25000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2590506779/5000000000 : ℝ)^4767 ≤ (21639891205201/50000000000000 : ℝ)^3743 := by
    have hnat : (2590506779 : ℕ)^4767*50000000000000^3743 ≤ 21639891205201^3743*5000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590506779 5000000000 21639891205201 50000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669159393/1250000000 : ℝ), (-1842498421/10000000000 : ℝ), (2590506779/5000000000 : ℝ)] ![(22560360301337/50000000000000 : ℝ), (2899874245429/25000000000000 : ℝ), (21639891205201/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669159393/1250000000 : ℝ)|^4767 ≤ (22560360301337/50000000000000 : ℝ)^3743
        have hw : |(669159393/1250000000 : ℝ)|=(669159393/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1842498421/10000000000 : ℝ)|^4767 ≤ (2899874245429/25000000000000 : ℝ)^3743
        have hw : |(-1842498421/10000000000 : ℝ)|=(1842498421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2590506779/5000000000 : ℝ)|^4767 ≤ (21639891205201/50000000000000 : ℝ)^3743
        have hw : |(2590506779/5000000000 : ℝ)|=(2590506779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1612_s4_2 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353275119/10000000000 : ℝ)*x 0 + (41448109/80000000 : ℝ)*x 1 + (-1842498363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353275119/10000000000 : ℝ)^4767 ≤ (5640090041789/12500000000000 : ℝ)^3743 := by
    have hnat : (5353275119 : ℕ)^4767*12500000000000^3743 ≤ 5640090041789^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353275119 10000000000 5640090041789 12500000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41448109/80000000 : ℝ)^4767 ≤ (43279783123207/100000000000000 : ℝ)^3743 := by
    have hnat : (41448109 : ℕ)^4767*100000000000000^3743 ≤ 43279783123207^3743*80000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41448109 80000000 43279783123207 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1842498363/10000000000 : ℝ)^4767 ≤ (11599496516681/100000000000000 : ℝ)^3743 := by
    have hnat : (1842498363 : ℕ)^4767*100000000000000^3743 ≤ 11599496516681^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1842498363 10000000000 11599496516681 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353275119/10000000000 : ℝ), (41448109/80000000 : ℝ), (-1842498363/10000000000 : ℝ)] ![(5640090041789/12500000000000 : ℝ), (43279783123207/100000000000000 : ℝ), (11599496516681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353275119/10000000000 : ℝ)|^4767 ≤ (5640090041789/12500000000000 : ℝ)^3743
        have hw : |(5353275119/10000000000 : ℝ)|=(5353275119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(41448109/80000000 : ℝ)|^4767 ≤ (43279783123207/100000000000000 : ℝ)^3743
        have hw : |(41448109/80000000 : ℝ)|=(41448109/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1842498363/10000000000 : ℝ)|^4767 ≤ (11599496516681/100000000000000 : ℝ)^3743
        have hw : |(-1842498363/10000000000 : ℝ)|=(1842498363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1612_s4_3 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4210901209/10000000000 : ℝ)*x 0 + (484918577/1250000000 : ℝ)*x 1 + (4563806807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4210901209/10000000000 : ℝ)^4767 ≤ (6647258572009/20000000000000 : ℝ)^3743 := by
    have hnat : (4210901209 : ℕ)^4767*20000000000000^3743 ≤ 6647258572009^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4210901209 10000000000 6647258572009 20000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (484918577/1250000000 : ℝ)^4767 ≤ (1871253188939/6250000000000 : ℝ)^3743 := by
    have hnat : (484918577 : ℕ)^4767*6250000000000^3743 ≤ 1871253188939^3743*1250000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      484918577 1250000000 1871253188939 6250000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4563806807/10000000000 : ℝ)^4767 ≤ (36823656103003/100000000000000 : ℝ)^3743 := by
    have hnat : (4563806807 : ℕ)^4767*100000000000000^3743 ≤ 36823656103003^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4563806807 10000000000 36823656103003 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4210901209/10000000000 : ℝ), (484918577/1250000000 : ℝ), (4563806807/10000000000 : ℝ)] ![(6647258572009/20000000000000 : ℝ), (1871253188939/6250000000000 : ℝ), (36823656103003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4210901209/10000000000 : ℝ)|^4767 ≤ (6647258572009/20000000000000 : ℝ)^3743
        have hw : |(4210901209/10000000000 : ℝ)|=(4210901209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(484918577/1250000000 : ℝ)|^4767 ≤ (1871253188939/6250000000000 : ℝ)^3743
        have hw : |(484918577/1250000000 : ℝ)|=(484918577/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4563806807/10000000000 : ℝ)|^4767 ≤ (36823656103003/100000000000000 : ℝ)^3743
        have hw : |(4563806807/10000000000 : ℝ)|=(4563806807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1612_s4_4 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-849666387/5000000000 : ℝ)*x 0 + (5183079629/10000000000 : ℝ)*x 1 + (341045631/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (849666387/5000000000 : ℝ)^4767 ≤ (10464055908557/100000000000000 : ℝ)^3743 := by
    have hnat : (849666387 : ℕ)^4767*100000000000000^3743 ≤ 10464055908557^3743*5000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849666387 5000000000 10464055908557 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5183079629/10000000000 : ℝ)^4767 ≤ (21650882139151/50000000000000 : ℝ)^3743 := by
    have hnat : (5183079629 : ℕ)^4767*50000000000000^3743 ≤ 21650882139151^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183079629 10000000000 21650882139151 50000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (341045631/625000000 : ℝ)^4767 ≤ (46234179795357/100000000000000 : ℝ)^3743 := by
    have hnat : (341045631 : ℕ)^4767*100000000000000^3743 ≤ 46234179795357^3743*625000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341045631 625000000 46234179795357 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-849666387/5000000000 : ℝ), (5183079629/10000000000 : ℝ), (341045631/625000000 : ℝ)] ![(10464055908557/100000000000000 : ℝ), (21650882139151/50000000000000 : ℝ), (46234179795357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-849666387/5000000000 : ℝ)|^4767 ≤ (10464055908557/100000000000000 : ℝ)^3743
        have hw : |(-849666387/5000000000 : ℝ)|=(849666387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5183079629/10000000000 : ℝ)|^4767 ≤ (21650882139151/50000000000000 : ℝ)^3743
        have hw : |(5183079629/10000000000 : ℝ)|=(5183079629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(341045631/625000000 : ℝ)|^4767 ≤ (46234179795357/100000000000000 : ℝ)^3743
        have hw : |(341045631/625000000 : ℝ)|=(341045631/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1612_s4_5 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055894189/2000000000 : ℝ)*x 0 + (-1566781833/10000000000 : ℝ)*x 1 + (682091263/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055894189/2000000000 : ℝ)^4767 ≤ (44329968590577/100000000000000 : ℝ)^3743 := by
    have hnat : (1055894189 : ℕ)^4767*100000000000000^3743 ≤ 44329968590577^3743*2000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055894189 2000000000 44329968590577 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1566781833/10000000000 : ℝ)^4767 ≤ (9435851509521/100000000000000 : ℝ)^3743 := by
    have hnat : (1566781833 : ℕ)^4767*100000000000000^3743 ≤ 9435851509521^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1566781833 10000000000 9435851509521 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (682091263/1250000000 : ℝ)^4767 ≤ (11558544970421/25000000000000 : ℝ)^3743 := by
    have hnat : (682091263 : ℕ)^4767*25000000000000^3743 ≤ 11558544970421^3743*1250000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682091263 1250000000 11558544970421 25000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055894189/2000000000 : ℝ), (-1566781833/10000000000 : ℝ), (682091263/1250000000 : ℝ)] ![(44329968590577/100000000000000 : ℝ), (9435851509521/100000000000000 : ℝ), (11558544970421/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055894189/2000000000 : ℝ)|^4767 ≤ (44329968590577/100000000000000 : ℝ)^3743
        have hw : |(1055894189/2000000000 : ℝ)|=(1055894189/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1566781833/10000000000 : ℝ)|^4767 ≤ (9435851509521/100000000000000 : ℝ)^3743
        have hw : |(-1566781833/10000000000 : ℝ)|=(1566781833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(682091263/1250000000 : ℝ)|^4767 ≤ (11558544970421/25000000000000 : ℝ)^3743
        have hw : |(682091263/1250000000 : ℝ)|=(682091263/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1612_s4_6 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279470963/10000000000 : ℝ)*x 0 + (2728365051/5000000000 : ℝ)*x 1 + (-391695453/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279470963/10000000000 : ℝ)^4767 ≤ (22164984391533/50000000000000 : ℝ)^3743 := by
    have hnat : (5279470963 : ℕ)^4767*50000000000000^3743 ≤ 22164984391533^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279470963 10000000000 22164984391533 50000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2728365051/5000000000 : ℝ)^4767 ≤ (23117089930051/50000000000000 : ℝ)^3743 := by
    have hnat : (2728365051 : ℕ)^4767*50000000000000^3743 ≤ 23117089930051^3743*5000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728365051 5000000000 23117089930051 50000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (391695453/2500000000 : ℝ)^4767 ≤ (188717026969/2000000000000 : ℝ)^3743 := by
    have hnat : (391695453 : ℕ)^4767*2000000000000^3743 ≤ 188717026969^3743*2500000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      391695453 2500000000 188717026969 2000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279470963/10000000000 : ℝ), (2728365051/5000000000 : ℝ), (-391695453/2500000000 : ℝ)] ![(22164984391533/50000000000000 : ℝ), (23117089930051/50000000000000 : ℝ), (188717026969/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279470963/10000000000 : ℝ)|^4767 ≤ (22164984391533/50000000000000 : ℝ)^3743
        have hw : |(5279470963/10000000000 : ℝ)|=(5279470963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2728365051/5000000000 : ℝ)|^4767 ≤ (23117089930051/50000000000000 : ℝ)^3743
        have hw : |(2728365051/5000000000 : ℝ)|=(2728365051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-391695453/2500000000 : ℝ)|^4767 ≤ (188717026969/2000000000000 : ℝ)^3743
        have hw : |(-391695453/2500000000 : ℝ)|=(391695453/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1612_s4_7 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1052768359/2500000000 : ℝ)*x 0 + (569839543/1250000000 : ℝ)*x 1 + (242780787/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1052768359/2500000000 : ℝ)^4767 ≤ (33238024136871/100000000000000 : ℝ)^3743 := by
    have hnat : (1052768359 : ℕ)^4767*100000000000000^3743 ≤ 33238024136871^3743*2500000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052768359 2500000000 33238024136871 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (569839543/1250000000 : ℝ)^4767 ≤ (4596419297757/12500000000000 : ℝ)^3743 := by
    have hnat : (569839543 : ℕ)^4767*12500000000000^3743 ≤ 4596419297757^3743*1250000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      569839543 1250000000 4596419297757 12500000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (242780787/625000000 : ℝ)^4767 ≤ (29990621462243/100000000000000 : ℝ)^3743 := by
    have hnat : (242780787 : ℕ)^4767*100000000000000^3743 ≤ 29990621462243^3743*625000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      242780787 625000000 29990621462243 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1052768359/2500000000 : ℝ), (569839543/1250000000 : ℝ), (242780787/625000000 : ℝ)] ![(33238024136871/100000000000000 : ℝ), (4596419297757/12500000000000 : ℝ), (29990621462243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1052768359/2500000000 : ℝ)|^4767 ≤ (33238024136871/100000000000000 : ℝ)^3743
        have hw : |(1052768359/2500000000 : ℝ)|=(1052768359/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(569839543/1250000000 : ℝ)|^4767 ≤ (4596419297757/12500000000000 : ℝ)^3743
        have hw : |(569839543/1250000000 : ℝ)|=(569839543/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(242780787/625000000 : ℝ)|^4767 ≤ (29990621462243/100000000000000 : ℝ)^3743
        have hw : |(242780787/625000000 : ℝ)|=(242780787/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1612_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (173190687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (327/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10437/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (653/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8169/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (327/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10437/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (327/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10437/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (327/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10437/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (327/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10437/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (327/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10437/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (327/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10437/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10437/100000 : ℝ) ^ (4763/1024 : ℝ) ≤ (2722921600084531/100000000000000000000 : ℝ) := by
    have hpowers : (10437/100000 : ℝ)^4763 ≤ (2722921600084531/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10437 : ℕ)^4763*100000000000000000000^1024 ≤ 2722921600084531^1024*100000^4763 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10437 100000 2722921600084531 100000000000000000000 4763 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10437/100000 : ℝ)) (X := (2722921600084531/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4763 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (327/2000 : ℝ) ^ (4763/1024 : ℝ) ≤ (10983792141694299/50000000000000000000 : ℝ) := by
    have hpowers : (327/2000 : ℝ)^4763 ≤ (10983792141694299/50000000000000000000 : ℝ)^1024 := by
      have hnat : (327 : ℕ)^4763*50000000000000000000^1024 ≤ 10983792141694299^1024*2000^4763 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        327 2000 10983792141694299 50000000000000000000 4763 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (327/2000 : ℝ)) (X := (10983792141694299/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4763 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002722921600084531/50000000000000000000 : ℝ) ≤ (10000117077981129/10000000000000000 : ℝ) ^ (4763/1024 : ℝ) := by
    have hpowers : (50002722921600084531/50000000000000000000 : ℝ)^1024 ≤ (10000117077981129/10000000000000000 : ℝ)^4763 := by
      have hnat : (50002722921600084531 : ℕ)^1024*10000000000000000^4763 ≤ 10000117077981129^4763*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002722921600084531 50000000000000000000 10000117077981129 10000000000000000 1024 4763 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000117077981129/10000000000000000 : ℝ)) (X := (50002722921600084531/50000000000000000000 : ℝ)) (by norm_num) 4763 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100024690505883473129/100000000000000000000 : ℝ) ≤ (10000530771114131/10000000000000000 : ℝ) ^ (4763/1024 : ℝ) := by
    have hpowers : (100024690505883473129/100000000000000000000 : ℝ)^1024 ≤ (10000530771114131/10000000000000000 : ℝ)^4763 := by
      have hnat : (100024690505883473129 : ℕ)^1024*10000000000000000^4763 ≤ 10000530771114131^4763*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100024690505883473129 100000000000000000000 10000530771114131 10000000000000000 1024 4763 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000530771114131/10000000000000000 : ℝ)) (X := (100024690505883473129/100000000000000000000 : ℝ)) (by norm_num) 4763 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25010983792141694299/25000000000000000000 : ℝ) ≤ (10000944464247133/10000000000000000 : ℝ) ^ (4763/1024 : ℝ) := by
    have hpowers : (25010983792141694299/25000000000000000000 : ℝ)^1024 ≤ (10000944464247133/10000000000000000 : ℝ)^4763 := by
      have hnat : (25010983792141694299 : ℕ)^1024*10000000000000000^4763 ≤ 10000944464247133^4763*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010983792141694299 25000000000000000000 10000944464247133 10000000000000000 1024 4763 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000944464247133/10000000000000000 : ℝ)) (X := (25010983792141694299/25000000000000000000 : ℝ)) (by norm_num) 4763 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2722921600084531/100000000000000000000 : ℝ) ≤ ((19707352283881377343/19710000000000000000 : ℝ)+2*(206846566501/295650000000000 : ℝ)*(10437/100000 : ℝ))^(4763/1024 : ℝ) := by
    rw [show (19707352283881377343/19710000000000000000 : ℝ)+2*(206846566501/295650000000000 : ℝ)*(10437/100000 : ℝ)=(10000117077981129/10000000000000000 : ℝ) by norm_num, show 1+2*(2722921600084531/100000000000000000000 : ℝ)=(50002722921600084531/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10983792141694299/50000000000000000000 : ℝ)+(2722921600084531/100000000000000000000 : ℝ) ≤ ((19707352283881377343/19710000000000000000 : ℝ)+(206846566501/295650000000000 : ℝ)*((327/2000 : ℝ)+(10437/100000 : ℝ)))^(4763/1024 : ℝ) := by
    rw [show (19707352283881377343/19710000000000000000 : ℝ)+(206846566501/295650000000000 : ℝ)*((327/2000 : ℝ)+(10437/100000 : ℝ))=(10000530771114131/10000000000000000 : ℝ) by norm_num, show 1+(10983792141694299/50000000000000000000 : ℝ)+(2722921600084531/100000000000000000000 : ℝ)=(100024690505883473129/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10983792141694299/50000000000000000000 : ℝ) ≤ ((19707352283881377343/19710000000000000000 : ℝ)+2*(206846566501/295650000000000 : ℝ)*(327/2000 : ℝ))^(4763/1024 : ℝ) := by
    rw [show (19707352283881377343/19710000000000000000 : ℝ)+2*(206846566501/295650000000000 : ℝ)*(327/2000 : ℝ)=(10000944464247133/10000000000000000 : ℝ) by norm_num, show 1+2*(10983792141694299/50000000000000000000 : ℝ)=(25010983792141694299/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19707352283881377343/19710000000000000000 : ℝ)*(X 1 0+X 2 0)+(206846566501/295650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4763/1024 : ℝ)) (lo := (10437/100000 : ℝ)) (hi := (327/2000 : ℝ)) (c := (19707352283881377343/19710000000000000000 : ℝ)) (alpha := (206846566501/295650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19707352283881377343/19710000000000000000 : ℝ)*(X 0 1+X 2 1)+(206846566501/295650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4763/1024 : ℝ)) (lo := (10437/100000 : ℝ)) (hi := (327/2000 : ℝ)) (c := (19707352283881377343/19710000000000000000 : ℝ)) (alpha := (206846566501/295650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19707352283881377343/19710000000000000000 : ℝ)*(X 0 2+X 1 2)+(206846566501/295650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4763/1024 : ℝ)) (lo := (10437/100000 : ℝ)) (hi := (327/2000 : ℝ)) (c := (19707352283881377343/19710000000000000000 : ℝ)) (alpha := (206846566501/295650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1699262829/10000000000 : ℝ)*X 0 0+(5458817963/10000000000 : ℝ)*X 0 1+(647626687/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((669159393/1250000000 : ℝ)*X 1 0+(-1842498421/10000000000 : ℝ)*X 1 1+(2590506779/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353275119/10000000000 : ℝ)*X 2 0+(41448109/80000000 : ℝ)*X 2 1+(-1842498363/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4210901209/10000000000 : ℝ)*X 0 0+(484918577/1250000000 : ℝ)*X 0 1+(4563806807/10000000000 : ℝ)*X 0 2+(4210901209/10000000000 : ℝ)*X 1 0+(484918577/1250000000 : ℝ)*X 1 1+(4563806807/10000000000 : ℝ)*X 1 2+(4210901209/10000000000 : ℝ)*X 2 0+(484918577/1250000000 : ℝ)*X 2 1+(4563806807/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-849666387/5000000000 : ℝ)*X 0 0+(5183079629/10000000000 : ℝ)*X 0 1+(341045631/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1055894189/2000000000 : ℝ)*X 1 0+(-1566781833/10000000000 : ℝ)*X 1 1+(682091263/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5279470963/10000000000 : ℝ)*X 2 0+(2728365051/5000000000 : ℝ)*X 2 1+(-391695453/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1052768359/2500000000 : ℝ)*X 0 0+(569839543/1250000000 : ℝ)*X 0 1+(242780787/625000000 : ℝ)*X 0 2+(1052768359/2500000000 : ℝ)*X 1 0+(569839543/1250000000 : ℝ)*X 1 1+(242780787/625000000 : ℝ)*X 1 2+(1052768359/2500000000 : ℝ)*X 2 0+(569839543/1250000000 : ℝ)*X 2 1+(242780787/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2248134513656100797692350661/492750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (676603813/100000000000000 : ℝ)*(base19) + (581271237/100000000000000 : ℝ)*(base23) + (42034973/100000000000000 : ℝ)*(lower2) + (49610733/50000000000000 : ℝ)*(upper3) + (82338537/100000000000000 : ℝ)*(upper5) + (1265172090155609/50000000000000 : ℝ)*(major0) + (1265172090155609/50000000000000 : ℝ)*(major1) + (1265172090155609/50000000000000 : ℝ)*(major2) + (3599662864455999/100000000000000 : ℝ)*(sp0) + (449958903042461/12500000000000 : ℝ)*(sp1) + (449958914959033/12500000000000 : ℝ)*(sp2) + (1461012788834779/100000000000000 : ℝ)*(sp3) + (9036487501/100000000000000 : ℝ)*(sp4) + (1759381671/50000000000000 : ℝ)*(sp7) + (36525407689953/2500000000000 : ℝ)*(f.failure) + (7199343801887/200000000000 : ℝ)*(f.sum) + (112742594006567/14782500000000000000000000000 : ℝ)*base66 + (9556343262665700661/2956500000000000000000000000000000 : ℝ)*base67 + (5891342744137799339/2956500000000000000000000000000000 : ℝ)*base70 + (23295815591044799339/2956500000000000000000000000000000 : ℝ)*base72 + (5670521571931/7391250000000000000000000000 : ℝ)*base74 + (9559925526586200661/2956500000000000000000000000000000 : ℝ)*base75 + (13014540554080799339/2956500000000000000000000000000000 : ℝ)*base78 + (4067415201555299339/2956500000000000000000000000000000 : ℝ)*base80 + (45744395244589/29565000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1932289/250000000000000000000 : ℝ)*base90 + (1932289/250000000000000000000 : ℝ)*base92 + (1932289/250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (110378972220581446664811839/32850000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (123995793/25000000000000 : ℝ)*(base19) + (2781329/500000000000 : ℝ)*(base23) + (19986847/12500000000000 : ℝ)*(lower1) + (68367203/100000000000000 : ℝ)*(upper3) + (9990829/50000000000000 : ℝ)*(lower4) + (71165061/100000000000000 : ℝ)*(upper5) + (256873775643109/10000000000000 : ℝ)*(major0) + (256873775643109/10000000000000 : ℝ)*(major1) + (256873775643109/10000000000000 : ℝ)*(major2) + (142719961/20000000000000 : ℝ)*(sp2) + (365429070950729/10000000000000 : ℝ)*(sp4) + (1827145106762059/50000000000000 : ℝ)*(sp5) + (913572359910421/25000000000000 : ℝ)*(sp6) + (370796172837961/25000000000000 : ℝ)*(sp7) + (370796172837961/25000000000000 : ℝ)*(f.failure) + (365429070950729/10000000000000 : ℝ)*(f.sum) + (2063923347439/369562500000000000000000000 : ℝ)*base65 + (12079253079892038161/591300000000000000000000000000000 : ℝ)*base67 + (7550364724647438161/591300000000000000000000000000000 : ℝ)*base69 + (34117811944699638161/591300000000000000000000000000000 : ℝ)*base71 + (3421426364809/591300000000000000000000000 : ℝ)*base73 + (37147148026805838161/591300000000000000000000000000000 : ℝ)*base75 + (7039570229699538161/591300000000000000000000000000000 : ℝ)*base77 + (11929583529594138161/591300000000000000000000000000000 : ℝ)*base79 + (22754402621611/5913000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (44730793/2500000000000000000000 : ℝ)*base90 + (44730793/2500000000000000000000 : ℝ)*base92 + (44730793/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1612_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (173190687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (327/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10437/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (653/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8169/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1612_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1612_s5_0 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1699272289/10000000000 : ℝ)*x 0 + (1091753909/2000000000 : ℝ)*x 1 + (2590527819/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1699272289/10000000000 : ℝ)^4767 ≤ (5231790782769/50000000000000 : ℝ)^3743 := by
    have hnat : (1699272289 : ℕ)^4767*50000000000000^3743 ≤ 5231790782769^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1699272289 10000000000 5231790782769 50000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1091753909/2000000000 : ℝ)^4767 ≤ (23128094163273/50000000000000 : ℝ)^3743 := by
    have hnat : (1091753909 : ℕ)^4767*50000000000000^3743 ≤ 23128094163273^3743*2000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091753909 2000000000 23128094163273 50000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2590527819/5000000000 : ℝ)^4767 ≤ (43280230094717/100000000000000 : ℝ)^3743 := by
    have hnat : (2590527819 : ℕ)^4767*100000000000000^3743 ≤ 43280230094717^3743*5000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590527819 5000000000 43280230094717 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1699272289/10000000000 : ℝ), (1091753909/2000000000 : ℝ), (2590527819/5000000000 : ℝ)] ![(5231790782769/50000000000000 : ℝ), (23128094163273/50000000000000 : ℝ), (43280230094717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1699272289/10000000000 : ℝ)|^4767 ≤ (5231790782769/50000000000000 : ℝ)^3743
        have hw : |(-1699272289/10000000000 : ℝ)|=(1699272289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1091753909/2000000000 : ℝ)|^4767 ≤ (23128094163273/50000000000000 : ℝ)^3743
        have hw : |(1091753909/2000000000 : ℝ)|=(1091753909/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2590527819/5000000000 : ℝ)|^4767 ≤ (43280230094717/100000000000000 : ℝ)^3743
        have hw : |(2590527819/5000000000 : ℝ)|=(2590527819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1612_s5_1 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669157781/1250000000 : ℝ)*x 0 + (-921229867/5000000000 : ℝ)*x 1 + (207242229/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669157781/1250000000 : ℝ)^4767 ≤ (45120582170619/100000000000000 : ℝ)^3743 := by
    have hnat : (669157781 : ℕ)^4767*100000000000000^3743 ≤ 45120582170619^3743*1250000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669157781 1250000000 45120582170619 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (921229867/5000000000 : ℝ)^4767 ≤ (11599186796451/100000000000000 : ℝ)^3743 := by
    have hnat : (921229867 : ℕ)^4767*100000000000000^3743 ≤ 11599186796451^3743*5000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      921229867 5000000000 11599186796451 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207242229/400000000 : ℝ)^4767 ≤ (43280231020301/100000000000000 : ℝ)^3743 := by
    have hnat : (207242229 : ℕ)^4767*100000000000000^3743 ≤ 43280231020301^3743*400000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207242229 400000000 43280231020301 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669157781/1250000000 : ℝ), (-921229867/5000000000 : ℝ), (207242229/400000000 : ℝ)] ![(45120582170619/100000000000000 : ℝ), (11599186796451/100000000000000 : ℝ), (43280231020301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669157781/1250000000 : ℝ)|^4767 ≤ (45120582170619/100000000000000 : ℝ)^3743
        have hw : |(669157781/1250000000 : ℝ)|=(669157781/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-921229867/5000000000 : ℝ)|^4767 ≤ (11599186796451/100000000000000 : ℝ)^3743
        have hw : |(-921229867/5000000000 : ℝ)|=(921229867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(207242229/400000000 : ℝ)|^4767 ≤ (43280231020301/100000000000000 : ℝ)^3743
        have hw : |(207242229/400000000 : ℝ)|=(207242229/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1612_s5_2 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353262477/10000000000 : ℝ)*x 0 + (518105559/1000000000 : ℝ)*x 1 + (-921229803/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353262477/10000000000 : ℝ)^4767 ≤ (45120584628817/100000000000000 : ℝ)^3743 := by
    have hnat : (5353262477 : ℕ)^4767*100000000000000^3743 ≤ 45120584628817^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353262477 10000000000 45120584628817 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (518105559/1000000000 : ℝ)^4767 ≤ (865604591681/2000000000000 : ℝ)^3743 := by
    have hnat : (518105559 : ℕ)^4767*2000000000000^3743 ≤ 865604591681^3743*1000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518105559 1000000000 865604591681 2000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (921229803/5000000000 : ℝ)^4767 ≤ (5799592885087/50000000000000 : ℝ)^3743 := by
    have hnat : (921229803 : ℕ)^4767*50000000000000^3743 ≤ 5799592885087^3743*5000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      921229803 5000000000 5799592885087 50000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353262477/10000000000 : ℝ), (518105559/1000000000 : ℝ), (-921229803/5000000000 : ℝ)] ![(45120584628817/100000000000000 : ℝ), (865604591681/2000000000000 : ℝ), (5799592885087/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353262477/10000000000 : ℝ)|^4767 ≤ (45120584628817/100000000000000 : ℝ)^3743
        have hw : |(5353262477/10000000000 : ℝ)|=(5353262477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(518105559/1000000000 : ℝ)|^4767 ≤ (865604591681/2000000000000 : ℝ)^3743
        have hw : |(518105559/1000000000 : ℝ)|=(518105559/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-921229803/5000000000 : ℝ)|^4767 ≤ (5799592885087/50000000000000 : ℝ)^3743
        have hw : |(-921229803/5000000000 : ℝ)|=(921229803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1612_s5_3 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (263181711/625000000 : ℝ)*x 0 + (484932471/1250000000 : ℝ)*x 1 + (912738891/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (263181711/625000000 : ℝ)^4767 ≤ (16618177426111/50000000000000 : ℝ)^3743 := by
    have hnat : (263181711 : ℕ)^4767*50000000000000^3743 ≤ 16618177426111^3743*625000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263181711 625000000 16618177426111 50000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (484932471/1250000000 : ℝ)^4767 ≤ (14970571782379/50000000000000 : ℝ)^3743 := by
    have hnat : (484932471 : ℕ)^4767*50000000000000^3743 ≤ 14970571782379^3743*1250000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      484932471 1250000000 14970571782379 50000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (912738891/2000000000 : ℝ)^4767 ≤ (36822501575391/100000000000000 : ℝ)^3743 := by
    have hnat : (912738891 : ℕ)^4767*100000000000000^3743 ≤ 36822501575391^3743*2000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      912738891 2000000000 36822501575391 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(263181711/625000000 : ℝ), (484932471/1250000000 : ℝ), (912738891/2000000000 : ℝ)] ![(16618177426111/50000000000000 : ℝ), (14970571782379/50000000000000 : ℝ), (36822501575391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(263181711/625000000 : ℝ)|^4767 ≤ (16618177426111/50000000000000 : ℝ)^3743
        have hw : |(263181711/625000000 : ℝ)|=(263181711/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(484932471/1250000000 : ℝ)|^4767 ≤ (14970571782379/50000000000000 : ℝ)^3743
        have hw : |(484932471/1250000000 : ℝ)|=(484932471/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(912738891/2000000000 : ℝ)|^4767 ≤ (36822501575391/100000000000000 : ℝ)^3743
        have hw : |(912738891/2000000000 : ℝ)|=(912738891/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1612_s5_4 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-21241779/125000000 : ℝ)*x 0 + (5183120483/10000000000 : ℝ)*x 1 + (43653463/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21241779/125000000 : ℝ)^4767 ≤ (2616032692953/25000000000000 : ℝ)^3743 := by
    have hnat : (21241779 : ℕ)^4767*25000000000000^3743 ≤ 2616032692953^3743*125000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21241779 125000000 2616032692953 25000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5183120483/10000000000 : ℝ)^4767 ≤ (43302198966739/100000000000000 : ℝ)^3743 := by
    have hnat : (5183120483 : ℕ)^4767*100000000000000^3743 ≤ 43302198966739^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183120483 10000000000 43302198966739 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43653463/80000000 : ℝ)^4767 ≤ (46233670240817/100000000000000 : ℝ)^3743 := by
    have hnat : (43653463 : ℕ)^4767*100000000000000^3743 ≤ 46233670240817^3743*80000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43653463 80000000 46233670240817 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-21241779/125000000 : ℝ), (5183120483/10000000000 : ℝ), (43653463/80000000 : ℝ)] ![(2616032692953/25000000000000 : ℝ), (43302198966739/100000000000000 : ℝ), (46233670240817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-21241779/125000000 : ℝ)|^4767 ≤ (2616032692953/25000000000000 : ℝ)^3743
        have hw : |(-21241779/125000000 : ℝ)|=(21241779/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5183120483/10000000000 : ℝ)|^4767 ≤ (43302198966739/100000000000000 : ℝ)^3743
        have hw : |(5183120483/10000000000 : ℝ)|=(5183120483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(43653463/80000000 : ℝ)|^4767 ≤ (46233670240817/100000000000000 : ℝ)^3743
        have hw : |(43653463/80000000 : ℝ)|=(43653463/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1612_s5_5 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279482181/10000000000 : ℝ)*x 0 + (-97927023/625000000 : ℝ)*x 1 + (109133661/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279482181/10000000000 : ℝ)^4767 ≤ (11082522186557/25000000000000 : ℝ)^3743 := by
    have hnat : (5279482181 : ℕ)^4767*25000000000000^3743 ≤ 11082522186557^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279482181 10000000000 11082522186557 25000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (97927023/625000000 : ℝ)^4767 ≤ (9436239116941/100000000000000 : ℝ)^3743 := by
    have hnat : (97927023 : ℕ)^4767*100000000000000^3743 ≤ 9436239116941^3743*625000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97927023 625000000 9436239116941 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (109133661/200000000 : ℝ)^4767 ≤ (46233672129213/100000000000000 : ℝ)^3743 := by
    have hnat : (109133661 : ℕ)^4767*100000000000000^3743 ≤ 46233672129213^3743*200000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109133661 200000000 46233672129213 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279482181/10000000000 : ℝ), (-97927023/625000000 : ℝ), (109133661/200000000 : ℝ)] ![(11082522186557/25000000000000 : ℝ), (9436239116941/100000000000000 : ℝ), (46233672129213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279482181/10000000000 : ℝ)|^4767 ≤ (11082522186557/25000000000000 : ℝ)^3743
        have hw : |(5279482181/10000000000 : ℝ)|=(5279482181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-97927023/625000000 : ℝ)|^4767 ≤ (9436239116941/100000000000000 : ℝ)^3743
        have hw : |(-97927023/625000000 : ℝ)|=(97927023/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(109133661/200000000 : ℝ)|^4767 ≤ (46233672129213/100000000000000 : ℝ)^3743
        have hw : |(109133661/200000000 : ℝ)|=(109133661/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1612_s5_6 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (211179293/400000000 : ℝ)*x 0 + (2728341449/5000000000 : ℝ)*x 1 + (-78341619/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211179293/400000000 : ℝ)^4767 ≤ (44330090286137/100000000000000 : ℝ)^3743 := by
    have hnat : (211179293 : ℕ)^4767*100000000000000^3743 ≤ 44330090286137^3743*400000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211179293 400000000 44330090286137 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2728341449/5000000000 : ℝ)^4767 ≤ (23116835244503/50000000000000 : ℝ)^3743 := by
    have hnat : (2728341449 : ℕ)^4767*50000000000000^3743 ≤ 23116835244503^3743*5000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728341449 5000000000 23116835244503 50000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (78341619/500000000 : ℝ)^4767 ≤ (4718119604491/50000000000000 : ℝ)^3743 := by
    have hnat : (78341619 : ℕ)^4767*50000000000000^3743 ≤ 4718119604491^3743*500000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78341619 500000000 4718119604491 50000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211179293/400000000 : ℝ), (2728341449/5000000000 : ℝ), (-78341619/500000000 : ℝ)] ![(44330090286137/100000000000000 : ℝ), (23116835244503/50000000000000 : ℝ), (4718119604491/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211179293/400000000 : ℝ)|^4767 ≤ (44330090286137/100000000000000 : ℝ)^3743
        have hw : |(211179293/400000000 : ℝ)|=(211179293/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2728341449/5000000000 : ℝ)|^4767 ≤ (23116835244503/50000000000000 : ℝ)^3743
        have hw : |(2728341449/5000000000 : ℝ)|=(2728341449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-78341619/500000000 : ℝ)|^4767 ≤ (4718119604491/50000000000000 : ℝ)^3743
        have hw : |(-78341619/500000000 : ℝ)|=(78341619/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1612_s5_7 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4211079421/10000000000 : ℝ)*x 0 + (2279303737/5000000000 : ℝ)*x 1 + (485575027/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4211079421/10000000000 : ℝ)^4767 ≤ (8309521075053/25000000000000 : ℝ)^3743 := by
    have hnat : (4211079421 : ℕ)^4767*25000000000000^3743 ≤ 8309521075053^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4211079421 10000000000 8309521075053 25000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2279303737/5000000000 : ℝ)^4767 ≤ (9192558994209/25000000000000 : ℝ)^3743 := by
    have hnat : (2279303737 : ℕ)^4767*25000000000000^3743 ≤ 9192558994209^3743*5000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2279303737 5000000000 9192558994209 25000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (485575027/1250000000 : ℝ)^4767 ≤ (29991679709783/100000000000000 : ℝ)^3743 := by
    have hnat : (485575027 : ℕ)^4767*100000000000000^3743 ≤ 29991679709783^3743*1250000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      485575027 1250000000 29991679709783 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4211079421/10000000000 : ℝ), (2279303737/5000000000 : ℝ), (485575027/1250000000 : ℝ)] ![(8309521075053/25000000000000 : ℝ), (9192558994209/25000000000000 : ℝ), (29991679709783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4211079421/10000000000 : ℝ)|^4767 ≤ (8309521075053/25000000000000 : ℝ)^3743
        have hw : |(4211079421/10000000000 : ℝ)|=(4211079421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2279303737/5000000000 : ℝ)|^4767 ≤ (9192558994209/25000000000000 : ℝ)^3743
        have hw : |(2279303737/5000000000 : ℝ)|=(2279303737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(485575027/1250000000 : ℝ)|^4767 ≤ (29991679709783/100000000000000 : ℝ)^3743
        have hw : |(485575027/1250000000 : ℝ)|=(485575027/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1612_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (173190687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8169/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (653/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (10449/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16337/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8169/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (653/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8169/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (653/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8169/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (653/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8169/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (653/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8169/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (653/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8169/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (653/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (653/6250 : ℝ) ^ (4763/1024 : ℝ) ≤ (2736295817918753/100000000000000000000 : ℝ) := by
    have hpowers : (653/6250 : ℝ)^4763 ≤ (2736295817918753/100000000000000000000 : ℝ)^1024 := by
      have hnat : (653 : ℕ)^4763*100000000000000000000^1024 ≤ 2736295817918753^1024*6250^4763 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        653 6250 2736295817918753 100000000000000000000 4763 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (653/6250 : ℝ)) (X := (2736295817918753/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4763 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8169/50000 : ℝ) ^ (4763/1024 : ℝ) ≤ (5473172681081089/25000000000000000000 : ℝ) := by
    have hpowers : (8169/50000 : ℝ)^4763 ≤ (5473172681081089/25000000000000000000 : ℝ)^1024 := by
      have hnat : (8169 : ℕ)^4763*25000000000000000000^1024 ≤ 5473172681081089^1024*50000^4763 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8169 50000 5473172681081089 25000000000000000000 4763 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8169/50000 : ℝ)) (X := (5473172681081089/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4763 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002736295817918753/50000000000000000000 : ℝ) ≤ (10000117653022581/10000000000000000 : ℝ) ^ (4763/1024 : ℝ) := by
    have hpowers : (50002736295817918753/50000000000000000000 : ℝ)^1024 ≤ (10000117653022581/10000000000000000 : ℝ)^4763 := by
      have hnat : (50002736295817918753 : ℕ)^1024*10000000000000000^4763 ≤ 10000117653022581^4763*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002736295817918753 50000000000000000000 10000117653022581 10000000000000000 1024 4763 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000117653022581/10000000000000000 : ℝ)) (X := (50002736295817918753/50000000000000000000 : ℝ)) (by norm_num) 4763 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100024628986542243109/100000000000000000000 : ℝ) ≤ (10000529448762393/10000000000000000 : ℝ) ^ (4763/1024 : ℝ) := by
    have hpowers : (100024628986542243109/100000000000000000000 : ℝ)^1024 ≤ (10000529448762393/10000000000000000 : ℝ)^4763 := by
      have hnat : (100024628986542243109 : ℕ)^1024*10000000000000000^4763 ≤ 10000529448762393^4763*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100024628986542243109 100000000000000000000 10000529448762393 10000000000000000 1024 4763 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000529448762393/10000000000000000 : ℝ)) (X := (100024628986542243109/100000000000000000000 : ℝ)) (by norm_num) 4763 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12505473172681081089/12500000000000000000 : ℝ) ≤ (2000188248900441/2000000000000000 : ℝ) ^ (4763/1024 : ℝ) := by
    have hpowers : (12505473172681081089/12500000000000000000 : ℝ)^1024 ≤ (2000188248900441/2000000000000000 : ℝ)^4763 := by
      have hnat : (12505473172681081089 : ℕ)^1024*2000000000000000^4763 ≤ 2000188248900441^4763*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505473172681081089 12500000000000000000 2000188248900441 2000000000000000 1024 4763 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000188248900441/2000000000000000 : ℝ)) (X := (12505473172681081089/12500000000000000000 : ℝ)) (by norm_num) 4763 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2736295817918753/100000000000000000000 : ℝ) ≤ ((29446044046261945269/29450000000000000000 : ℝ)+2*(102948934953/147250000000000 : ℝ)*(653/6250 : ℝ))^(4763/1024 : ℝ) := by
    rw [show (29446044046261945269/29450000000000000000 : ℝ)+2*(102948934953/147250000000000 : ℝ)*(653/6250 : ℝ)=(10000117653022581/10000000000000000 : ℝ) by norm_num, show 1+2*(2736295817918753/100000000000000000000 : ℝ)=(50002736295817918753/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5473172681081089/25000000000000000000 : ℝ)+(2736295817918753/100000000000000000000 : ℝ) ≤ ((29446044046261945269/29450000000000000000 : ℝ)+(102948934953/147250000000000 : ℝ)*((8169/50000 : ℝ)+(653/6250 : ℝ)))^(4763/1024 : ℝ) := by
    rw [show (29446044046261945269/29450000000000000000 : ℝ)+(102948934953/147250000000000 : ℝ)*((8169/50000 : ℝ)+(653/6250 : ℝ))=(10000529448762393/10000000000000000 : ℝ) by norm_num, show 1+(5473172681081089/25000000000000000000 : ℝ)+(2736295817918753/100000000000000000000 : ℝ)=(100024628986542243109/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5473172681081089/25000000000000000000 : ℝ) ≤ ((29446044046261945269/29450000000000000000 : ℝ)+2*(102948934953/147250000000000 : ℝ)*(8169/50000 : ℝ))^(4763/1024 : ℝ) := by
    rw [show (29446044046261945269/29450000000000000000 : ℝ)+2*(102948934953/147250000000000 : ℝ)*(8169/50000 : ℝ)=(2000188248900441/2000000000000000 : ℝ) by norm_num, show 1+2*(5473172681081089/25000000000000000000 : ℝ)=(12505473172681081089/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (29446044046261945269/29450000000000000000 : ℝ)*(X 1 0+X 2 0)+(102948934953/147250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4763/1024 : ℝ)) (lo := (653/6250 : ℝ)) (hi := (8169/50000 : ℝ)) (c := (29446044046261945269/29450000000000000000 : ℝ)) (alpha := (102948934953/147250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (29446044046261945269/29450000000000000000 : ℝ)*(X 0 1+X 2 1)+(102948934953/147250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4763/1024 : ℝ)) (lo := (653/6250 : ℝ)) (hi := (8169/50000 : ℝ)) (c := (29446044046261945269/29450000000000000000 : ℝ)) (alpha := (102948934953/147250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (29446044046261945269/29450000000000000000 : ℝ)*(X 0 2+X 1 2)+(102948934953/147250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4763/1024 : ℝ)) (lo := (653/6250 : ℝ)) (hi := (8169/50000 : ℝ)) (c := (29446044046261945269/29450000000000000000 : ℝ)) (alpha := (102948934953/147250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1699272289/10000000000 : ℝ)*X 0 0+(1091753909/2000000000 : ℝ)*X 0 1+(2590527819/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((669157781/1250000000 : ℝ)*X 1 0+(-921229867/5000000000 : ℝ)*X 1 1+(207242229/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353262477/10000000000 : ℝ)*X 2 0+(518105559/1000000000 : ℝ)*X 2 1+(-921229803/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((263181711/625000000 : ℝ)*X 0 0+(484932471/1250000000 : ℝ)*X 0 1+(912738891/2000000000 : ℝ)*X 0 2+(263181711/625000000 : ℝ)*X 1 0+(484932471/1250000000 : ℝ)*X 1 1+(912738891/2000000000 : ℝ)*X 1 2+(263181711/625000000 : ℝ)*X 2 0+(484932471/1250000000 : ℝ)*X 2 1+(912738891/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-21241779/125000000 : ℝ)*X 0 0+(5183120483/10000000000 : ℝ)*X 0 1+(43653463/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5279482181/10000000000 : ℝ)*X 1 0+(-97927023/625000000 : ℝ)*X 1 1+(109133661/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((211179293/400000000 : ℝ)*X 2 0+(2728341449/5000000000 : ℝ)*X 2 1+(-78341619/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4211079421/10000000000 : ℝ)*X 0 0+(2279303737/5000000000 : ℝ)*X 0 1+(485575027/1250000000 : ℝ)*X 0 2+(4211079421/10000000000 : ℝ)*X 1 0+(2279303737/5000000000 : ℝ)*X 1 1+(485575027/1250000000 : ℝ)*X 1 2+(4211079421/10000000000 : ℝ)*X 2 0+(2279303737/5000000000 : ℝ)*X 2 1+(485575027/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2415311596792184164231552701/736250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (502589751/100000000000000 : ℝ)*(base19) + (321780013/50000000000000 : ℝ)*(base23) + (6994231/100000000000000 : ℝ)*(lower2) + (1634263/50000000000000 : ℝ)*(upper3) + (113373667/100000000000000 : ℝ)*(upper5) + (2531168168159043/100000000000000 : ℝ)*(major0) + (2531168168159043/100000000000000 : ℝ)*(major1) + (2531168168159043/100000000000000 : ℝ)*(major2) + (3600834345169799/100000000000000 : ℝ)*(sp0) + (450105455954367/12500000000000 : ℝ)*(sp1) + (180042175333233/5000000000000 : ℝ)*(sp2) + (730744862854533/50000000000000 : ℝ)*(sp3) + (9805054887/100000000000000 : ℝ)*(sp4) + (58775809/2500000000000 : ℝ)*(sp7) + (730746038370713/50000000000000 : ℝ)*(f.failure) + (1800422075112343/50000000000000 : ℝ)*(f.sum) + (4478641656833/14725000000000000000000000000 : ℝ)*base65 + (21788587784030782433/2945000000000000000000000000000000 : ℝ)*base68 + (20022820187015782433/2945000000000000000000000000000000 : ℝ)*base70 + (26617190052530782433/2945000000000000000000000000000000 : ℝ)*base72 + (13195960091779/7362500000000000000000000000 : ℝ)*base73 + (26998263881800782433/2945000000000000000000000000000000 : ℝ)*base76 + (16089600460470782433/2945000000000000000000000000000000 : ℝ)*base78 + (5998878657789217567/2945000000000000000000000000000000 : ℝ)*base79 + (1402256255513/920312500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (4850169/5000000000000000000000 : ℝ)*base90 + (4850169/5000000000000000000000 : ℝ)*base92 + (4850169/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5605453323168070482525459/1840625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (266323643/50000000000000 : ℝ)*(base19) + (796122631/100000000000000 : ℝ)*(base23) + (191715409/100000000000000 : ℝ)*(lower1) + (34210453/50000000000000 : ℝ)*(upper2) + (114253761/100000000000000 : ℝ)*(upper3) + (60536019/100000000000000 : ℝ)*(upper5) + (3211953452913/125000000000 : ℝ)*(major0) + (3211953452913/125000000000 : ℝ)*(major1) + (3211953452913/125000000000 : ℝ)*(major2) + (76416887/3125000000000 : ℝ)*(sp2) + (57116630856733/1562500000000 : ℝ)*(sp4) + (1827731921091813/50000000000000 : ℝ)*(sp5) + (3655461133367897/100000000000000 : ℝ)*(sp6) + (1483661048316299/100000000000000 : ℝ)*(sp7) + (1483661048316299/100000000000000 : ℝ)*(f.failure) + (57116630856733/1562500000000 : ℝ)*(f.sum) + (7975872331/23560000000000000000000000 : ℝ)*base66 + (1503710068931097/3681250000000000000000000000000 : ℝ)*base67 + (9679901192568597/3681250000000000000000000000000 : ℝ)*base69 + (9247727592637347/3681250000000000000000000000000 : ℝ)*base71 + (1399593639417/294500000000000000000000000 : ℝ)*base73 + (21429265055556403/3681250000000000000000000000000 : ℝ)*base76 + (33075321625756403/3681250000000000000000000000000 : ℝ)*base78 + (12439593664368597/3681250000000000000000000000000 : ℝ)*base79 + (21444674271/147250000000000000000000000 : ℝ)*base82 + (17107413/10000000000000000000000 : ℝ)*base89 + (17107413/10000000000000000000000 : ℝ)*base91 + (17107413/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1612_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (173190687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8169/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (653/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10449/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16337/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1612_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1612_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (173190687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3297/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2579/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10449/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16337/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1612_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1612_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1612_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (173190687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3297/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2579/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10449/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16337/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1612_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
